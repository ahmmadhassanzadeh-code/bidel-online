// Bidel (Hearts) online server — zero dependencies.  Run:  node hearts-server.js
// Serves the game page at "/" and runs rooms: HTTP POST for moves, Server-Sent Events for live updates.
const http=require('http'),fs=require('fs'),path=require('path');
const PORT=process.env.PORT||3000,K=process.env.FAST?0:1;
const CORS={'Access-Control-Allow-Origin':'*','Access-Control-Allow-Methods':'GET,POST,OPTIONS','Access-Control-Allow-Headers':'Content-Type'};
const rooms={};
// Simple per-client-IP limits for this small friends-only game.
const rateBuckets=new Map();
function rateAllowed(req,route){
  // Render and similar reverse proxies provide the original client address here.
  const forwarded=String(req.headers['x-forwarded-for']||'').split(',')[0].trim();
  const ip=forwarded||req.socket.remoteAddress||'unknown';
  const key=ip+'|'+route,now=Date.now();
  const limit=route==='/api/join'?20:180,windowMs=60_000;
  let b=rateBuckets.get(key);
  if(!b||now-b.start>=windowMs){b={start:now,count:0};rateBuckets.set(key,b)}
  b.count++;
  if(rateBuckets.size>2000){for(const [k,v] of rateBuckets)if(now-v.start>windowMs)rateBuckets.delete(k)}
  return b.count<=limit;
}
// File snapshots are opt-in: set STATE_FILE only when the host has persistent storage.
// Render's ordinary free filesystem is ephemeral, so writing there is wasted work.
const STATE_FILE=process.env.STATE_FILE?path.resolve(process.env.STATE_FILE):null;
let saveTimer=null;
function saveRooms(){
  if(!STATE_FILE||saveTimer)return;
  saveTimer=setTimeout(()=>{
    saveTimer=null;
    try{
      const data={};
      for(const [k,g] of Object.entries(rooms)){
        const {clients,t,...state}=g;
        data[k]=state;
      }
      fs.mkdirSync(path.dirname(STATE_FILE),{recursive:true});
      const tmp=STATE_FILE+'.tmp';
      fs.writeFileSync(tmp,JSON.stringify(data));
      fs.renameSync(tmp,STATE_FILE);
    }catch(e){console.error('Room snapshot failed:',e.message)}
  },500);
  if(saveTimer.unref)saveTimer.unref();
}
function loadRooms(){
  if(!STATE_FILE)return;
  try{
    if(!fs.existsSync(STATE_FILE))return;
    const data=JSON.parse(fs.readFileSync(STATE_FILE,'utf8'));
    for(const [k,g] of Object.entries(data)){
      g.clients=new Set();g.t=null;g.active=Date.now();rooms[k]=g;
      // Outside the lobby, let bots continue any interrupted hand after a restart.
      // Preserve each former human PID so they can reclaim their seats on reconnect.
      if(g.phase!=='lobby'){
        g.seats=(g.seats||[]).map(s=>s&&!s.bot&&s.pid?{...s,pid:null,humanPid:s.pid,bot:true,human:true}:s);
        if(g.phase==='pass'&&Array.isArray(g.passes)&&Array.isArray(g.H)){
          for(let i=0;i<4;i++)if(isBot(g,i)&&!g.passes[i])g.passes[i]=botPass(g,i);
          maybeExchange(g);
        }
      }
    }
    console.log('Restored '+Object.keys(rooms).length+' room(s)');
  }catch(e){console.error('Room restore failed:',e.message)}
}
// cards are ids 0..51: suit=id/13|0 (0♣ 1♦ 2♠ 3♥), rank=id%13+2.  id 0 = 2♣, id 36 = Q♠
const S=id=>id/13|0,R=id=>id%13+2,QS=36,pv=id=>S(id)===3?1:id===QS?13:0;
const mn=(a,f)=>a.reduce((m,c)=>f(c)<f(m)?c:m),mx=(a,f)=>a.reduce((m,c)=>f(c)>f(m)?c:m);
const OFF=[1,3,2];

function legal(g,p){const h=g.H[p];
  if(!g.trick.length){if(g.first)return h.filter(c=>c===0);const nh=h.filter(c=>S(c)!==3);return g.broken||!nh.length?h:nh}
  const ls=S(g.trick[0].c),f=h.filter(c=>S(c)===ls);if(f.length)return f;
  if(g.first){const np=h.filter(c=>S(c)!==3&&c!==QS);if(np.length)return np}
  return h}
function botPlay(g,p){const L=legal(g,p);if(L.length===1)return L[0];
  if(!g.trick.length){const nq=L.filter(c=>c!==QS),nh=nq.filter(c=>S(c)!==3);return mn(nh.length?nh:nq.length?nq:L,c=>R(c)+(S(c)===2&&R(c)>=12?20:0))}
  const ls=S(g.trick[0].c);
  if(S(L[0])===ls){const cur=Math.max(...g.trick.filter(t=>S(t.c)===ls).map(t=>R(t.c))),tp=g.trick.reduce((a,t)=>a+pv(t.c),0),last=g.trick.length===3;
    if(L.includes(QS)&&cur>12)return QS;
    const lower=L.filter(c=>R(c)<cur),nq=L.filter(c=>c!==QS);
    if(last&&tp===0)return mx(nq.length?nq:L,R);
    if(lower.length)return mx(lower,R);
    return mn(nq.length?nq:L,R)}
  if(L.includes(QS))return QS;const hs=L.filter(c=>S(c)===3);return hs.length?mx(hs,R):mx(L,R)}
const risk=c=>c===QS||(S(c)===2&&R(c)>12)?100+R(c):S(c)===3?R(c)+(R(c)>=10?10:0):R(c);
const botPass=(g,p)=>g.H[p].slice().sort((a,b)=>risk(b)-risk(a)).slice(0,3);

const later=(g,ms,f)=>{clearTimeout(g.t);g.t=setTimeout(f,ms*K)};
const isBot=(g,p)=>g.seats[p]&&g.seats[p].bot;
function newRoom(code){return{code,seats:[null,null,null,null],phase:'lobby',hand:0,tot:[0,0,0,0],clients:new Set(),H:null,trick:[],pts:[0,0,0,0],passes:[],turn:-1,first:true,broken:false,sum:null,active:Date.now()}}
function deal(g){clearTimeout(g.t);const d=[...Array(52).keys()];
  for(let i=51;i>0;i--){const j=Math.random()*(i+1)|0;[d[i],d[j]]=[d[j],d[i]]}
  g.H=[0,1,2,3].map(i=>d.slice(i*13,i*13+13).sort((a,b)=>a-b));g.pts=[0,0,0,0];g.trick=[];g.broken=false;g.first=true;g.sum=null;g.turn=-1;
  g.passes=[null,null,null,null];
  if(g.hand%4===3)beginPlay(g);
  else{g.phase='pass';for(let p=0;p<4;p++)if(isBot(g,p))g.passes[p]=botPass(g,p);maybeExchange(g)}
  push(g)}
function maybeExchange(g){if(g.phase!=='pass'||g.passes.some(x=>!x))return;const off=OFF[g.hand%4];
  const nh=g.H.map((h,p)=>h.filter(c=>!g.passes[p].includes(c)));g.passes.forEach((cs,p)=>nh[(p+off)%4].push(...cs));
  g.H=nh.map(h=>h.sort((a,b)=>a-b));beginPlay(g)}
function beginPlay(g){g.phase='play';g.turn=g.H.findIndex(h=>h.includes(0));schedule(g)}
function schedule(g){if(g.phase==='play'&&g.turn>=0&&isBot(g,g.turn))later(g,700,()=>{if(g.phase==='play'&&g.turn>=0&&isBot(g,g.turn))playCard(g,g.turn,botPlay(g,g.turn))})}
function playCard(g,p,c){g.H[p]=g.H[p].filter(x=>x!==c);g.trick.push({p,c});if(S(c)===3)g.broken=true;
  if(g.trick.length<4){g.turn=(p+1)%4;push(g);schedule(g);return}
  g.turn=-1;push(g);later(g,1300,()=>resolve(g))}
const winner=g=>{const ls=S(g.trick[0].c);let w=g.trick[0];g.trick.forEach(t=>{if(S(t.c)===ls&&R(t.c)>R(w.c))w=t});return w.p};
function resolve(g){const w=winner(g);g.pts[w]+=g.trick.reduce((a,t)=>a+pv(t.c),0);g.trick=[];g.first=false;
  if(!g.H[0].length){endHand(g);return}g.turn=w;push(g);schedule(g)}
function endHand(g){let moon=-1;g.pts.forEach((v,i)=>{if(v===26)moon=i});if(moon>=0)g.pts=g.pts.map((_,i)=>i===moon?0:26);
  g.tot=g.tot.map((v,i)=>v+g.pts[i]);g.hand++;g.turn=-1;
  const m=Math.min(...g.tot),win=g.tot.map((v,i)=>v===m?i:-1).filter(i=>i>=0),over=g.tot.some(v=>v>=100),done=over&&win.length===1;
  g.phase=done?'over':'sum';g.sum={pts:g.pts.slice(),tot:g.tot.slice(),moon,win:done?win[0]:-1,tie:over&&!done};
  push(g);if(!done)later(g,25000,()=>{if(g.phase==='sum')deal(g)})}

const seatOf=(g,pid)=>pid?g.seats.findIndex(s=>s&&(s.pid===pid||s.humanPid===pid)):-1;
const onl=g=>g.seats.map(s=>!!(s&&!s.bot&&[...g.clients].some(c=>c.pid===s.pid)));
function hostSeat(g){
  // Never assign host authority to a bot. Prefer an online human; otherwise
  // retain host authority with the first human seat so it returns on reconnect.
  const online=onl(g),live=online.indexOf(true);
  if(live>=0)return live;
  return g.seats.findIndex(s=>s&&!s.bot&&s.pid);
}
function view(g,me){const on=onl(g);
  return{phase:g.phase,room:g.code,me,names:g.seats.map(s=>s?s.name:null),bot:g.seats.map(s=>!!(s&&s.bot)),on,host:hostSeat(g),
    tot:g.tot,handNo:g.hand,pts:g.pts,trick:g.trick,turn:g.turn,first:g.first,counts:g.H?g.H.map(h=>h.length):[0,0,0,0],
    hand:g.H&&me>=0?g.H[me]:[],legal:g.phase==='play'&&g.turn===me?legal(g,me):[],passed:g.passes.map(x=>!!x),dir:g.hand%4,sum:g.sum,
    tw:g.trick.length===4?winner(g):-1}}
function push(g){g.active=Date.now();for(const c of g.clients)c.res.write('data: '+JSON.stringify(view(g,seatOf(g,c.pid)))+'\n\n');saveRooms()}

function join(b){const room=String(b.room||''),name=String(b.name||'').replace(/[<>]/g,'').trim().slice(0,14),pid=String(b.pid||'');
  if(!/^[\w-]{3,20}$/.test(room)||!name||!/^[a-f0-9]{16,64}$/.test(pid))return{error:'اطلاعات نامعتبر'};
  const g=rooms[room]||(rooms[room]=newRoom(room));let i=seatOf(g,pid);
  if(i<0){i=g.phase==='lobby'?g.seats.findIndex(s=>!s):g.seats.findIndex(s=>s&&s.bot&&s.human);
    if(i<0)return{error:g.phase==='lobby'?'اتاق پر است':'بازی شروع شده است'};g.seats[i]={name,pid,bot:false}}
  else g.seats[i]={name,pid,bot:false};
  push(g);return{seat:i}}
function act(b){const g=rooms[b.room];if(!g)return{error:'اتاق پیدا نشد'};const me=seatOf(g,b.pid);if(me<0)return{error:'وارد اتاق نشده‌ای'};
  const host=hostSeat(g)===me;
  switch(b.type){
    case'start':if(!host||g.phase!=='lobby')return{error:'فقط میزبان می‌تواند شروع کند'};
      g.seats=g.seats.map((s,i)=>s||{name:'ربات '+(i+1),pid:null,bot:true});g.hand=0;g.tot=[0,0,0,0];deal(g);break;
    case'pass':{if(g.phase!=='pass'||g.passes[me])return{error:'الان نمی‌شود'};const ids=b.ids;
      if(!Array.isArray(ids)||ids.length!==3||new Set(ids).size!==3||!ids.every(c=>g.H[me].includes(c)))return{error:'ورق نامعتبر'};
      g.passes[me]=ids;maybeExchange(g);push(g);break}
    case'play':if(g.phase!=='play'||g.turn!==me)return{error:'نوبت تو نیست'};if(!legal(g,me).includes(b.id))return{error:'این ورق مجاز نیست'};playCard(g,me,b.id);break;
    case'next':if(!host||g.phase!=='sum')return{error:'فقط میزبان'};deal(g);break;
    case'newgame':if(!host||g.phase!=='over')return{error:'فقط میزبان'};g.hand=0;g.tot=[0,0,0,0];deal(g);break;
    case'bot':{const t=b.seat,s=Number.isInteger(b.seat)?g.seats[t]:null;if(!host||g.phase==='lobby'||!Number.isInteger(b.seat)||t<0||t>3||!s||s.bot||t===me||onl(g)[t])return{error:'نشد'};
      // Keep the former player's id so the same person can reclaim this seat.
      g.seats[t]={name:s.name,pid:null,humanPid:s.pid||s.humanPid||null,bot:true,human:!!(s.pid||s.humanPid)};
      if(g.phase==='pass'&&!g.passes[t]){g.passes[t]=botPass(g,t);maybeExchange(g)}
      push(g);schedule(g);break}
    default:return{error:'دستور نامعتبر'}}
  return{ok:1}}

const FILES={'/':['hearts-online.html','text/html; charset=utf-8'],'/index.html':['hearts-online.html','text/html; charset=utf-8']};
const MANIFEST=JSON.stringify({name:'بیدل',short_name:'بیدل',start_url:'/',display:'standalone',background_color:'#0d2818',theme_color:'#0d2818',lang:'fa',dir:'rtl',icons:[{src:'/icon.svg',sizes:'any',type:'image/svg+xml',purpose:'any'}]});
const ICON='<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 512 512"><rect width="512" height="512" rx="96" fill="#0d2818"/><text x="256" y="350" font-size="300" text-anchor="middle" fill="#ff5252">♥</text><text x="256" y="470" font-size="90" text-anchor="middle" fill="#ffd700">♠</text></svg>';
http.createServer((q,s)=>{
  const send=(c,b,t)=>{s.writeHead(c,{...CORS,'Content-Type':t||'application/json; charset=utf-8'});s.end(b)};
  const u=new URL(q.url,'http://x');
  if(q.method==='OPTIONS')return send(204,'');
  if(q.method==='GET'&&u.pathname==='/api/stream'){const g=rooms[u.searchParams.get('room')],pid=u.searchParams.get('pid');
    if(!g||seatOf(g,pid)<0)return send(404,'{"error":"no seat"}');
    s.writeHead(200,{...CORS,'Content-Type':'text/event-stream','Cache-Control':'no-cache','Connection':'keep-alive','X-Accel-Buffering':'no'});
    const c={res:s,pid};g.clients.add(c);s.write('retry: 2000\n\n');push(g);s.on('close',()=>{if(g.clients.delete(c))push(g)});return}
  if(q.method==='POST'&&(u.pathname==='/api/join'||u.pathname==='/api/act')){
    if(!rateAllowed(q,u.pathname))return send(429,JSON.stringify({error:'درخواست‌ها بیش از حد مجاز است؛ کمی صبر کن'}));
    let b='';q.on('data',d=>{b+=d;if(b.length>1e4)q.destroy()});
    q.on('end',()=>{let o;try{o=JSON.parse(b)}catch(e){return send(400,'{"error":"bad json"}')}
      try{send(200,JSON.stringify(u.pathname==='/api/join'?join(o):act(o)))}catch(e){console.error(e);send(500,'{"error":"server"}')}});return}
  if(u.pathname==='/manifest.json')return send(200,MANIFEST,'application/manifest+json');
  if(u.pathname==='/icon.svg')return send(200,ICON,'image/svg+xml');
  if(u.pathname==='/sw.js'&&q.method==='GET'){try{return send(200,fs.readFileSync(path.join(__dirname,'sw.js')),'text/javascript; charset=utf-8')}catch(e){return send(500,'{\"error\":\"sw missing\"}')}}
  const f=FILES[u.pathname];if(f){try{return send(200,fs.readFileSync(path.join(__dirname,f[0])),f[1])}catch(e){}}
  send(404,'{}');
}).listen(PORT,()=>console.log('Bidel online on :'+PORT));
loadRooms();
for(const g of Object.values(rooms)){if(g.phase==='play')schedule(g);else if(g.phase==='sum')later(g,25000,()=>{if(g.phase==='sum')deal(g)})}
setInterval(()=>{for(const g of Object.values(rooms))for(const c of g.clients)c.res.write(': ping\n\n')},20000);
setInterval(()=>{let changed=false;for(const k in rooms)if(!rooms[k].clients.size&&Date.now()-rooms[k].active>7200000){clearTimeout(rooms[k].t);delete rooms[k];changed=true}if(changed)saveRooms()},600000);
