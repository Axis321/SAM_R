const HX=4,HZ=3,MAXR=4,G=0.2,NX=40,NZ=30,WR=0.05,TPR=700,L=0.2,RAD=0.3;
let OB=[{t:'bed',x:-2.8,z:-2.3,w:2,d:1},{t:'bed',x:-2.8,z:-0.6,w:2,d:1},{t:'bed',x:2.8,z:-2.3,w:2,d:1},{t:'bed',x:2.8,z:-0.6,w:2,d:1},
{t:'stand',x:-1.45,z:-2.3,w:.3,d:.3},{t:'stand',x:-1.45,z:-0.6,w:.3,d:.3},{t:'stand',x:1.45,z:-2.3,w:.3,d:.3},{t:'stand',x:1.45,z:-0.6,w:.3,d:.3},
{t:'table',x:2.8,z:2.35,w:1.2,d:.6}];
const css=n=>getComputedStyle(document.documentElement).getPropertyValue(n).trim();
const START={x:-0.5,z:2.2,h:-Math.PI/2};
let R,path,pi,wp,state,tmr,paused=false,auto=true,follow=false,simT=0,encL,encR,pts,sweep,servo,past,logs=[],flags,yawG=0,yawE=0,gz=0,known=new Set(),camOn=true,dets=[],rq=[];
const wrap=a=>{while(a>Math.PI)a-=2*Math.PI;while(a<-Math.PI)a+=2*Math.PI;return a};
function log(s){logs.push(s);if(logs.length>6)logs.shift();document.getElementById('log').textContent=logs.join('\n')}

/* ---------- physics helpers ---------- */
const sl=(p,d,lo,hi)=>{if(Math.abs(d)<1e-9)return(p<lo||p>hi)?null:[-1e9,1e9];const a=(lo-p)/d,b=(hi-p)/d;return a<b?[a,b]:[b,a]};
function cast(ox,oz,dx,dz){let b=MAXR;
 if(dx>1e-6)b=Math.min(b,(HX-ox)/dx);else if(dx<-1e-6)b=Math.min(b,(-HX-ox)/dx);
 if(dz>1e-6)b=Math.min(b,(HZ-oz)/dz);else if(dz<-1e-6)b=Math.min(b,(-HZ-oz)/dz);
 for(const o of OB){const A=sl(ox,dx,o.x-o.w/2,o.x+o.w/2),B=sl(oz,dz,o.z-o.d/2,o.z+o.d/2);if(!A||!B)continue;
  const n=Math.max(A[0],B[0],0),f=Math.min(A[1],B[1]);if(n<=f&&n<b)b=n}return b}
const blocked=(x,z,r)=>Math.abs(x)>HX-r||Math.abs(z)>HZ-r||OB.some(o=>Math.abs(x-o.x)<o.w/2+r&&Math.abs(z-o.z)<o.d/2+r);
const clear=(a,b,c,d)=>{const n=Math.ceil(Math.hypot(c-a,d-b)/.1);for(let i=0;i<=n;i++)if(blocked(a+(c-a)*i/n,b+(d-b)*i/n,RAD))return false;return true};
const cx=i=>-HX+(i+.5)*G,cz=j=>-HZ+(j+.5)*G;
function plan(sx,sz,gx,gz){const I=(x,z)=>[Math.min(NX-1,Math.max(0,Math.floor((x+HX)/G))),Math.min(NZ-1,Math.max(0,Math.floor((z+HZ)/G)))];
 const[si,sj]=I(sx,sz),[gi,gj]=I(gx,gz),key=(i,j)=>j*NX+i,cost=new Float32Array(NX*NZ).fill(1e9),prev=new Int32Array(NX*NZ).fill(-1),done=new Uint8Array(NX*NZ);
 const open=[key(si,sj)];cost[open[0]]=0;
 while(open.length){let bi=0,bf=1e9;for(let k=0;k<open.length;k++){const c=open[k],f=cost[c]+Math.hypot(c%NX-gi,((c/NX)|0)-gj);if(f<bf){bf=f;bi=k}}
  const c=open.splice(bi,1)[0];if(done[c])continue;done[c]=1;const i=c%NX,j=(c/NX)|0;if(i==gi&&j==gj)break;
  for(let di=-1;di<=1;di++)for(let dj=-1;dj<=1;dj++){if(!di&&!dj)continue;const a=i+di,b=j+dj;if(a<0||b<0||a>=NX||b>=NZ)continue;const k=key(a,b);
   if(done[k]||blocked(cx(a),cz(b),RAD))continue;if(di&&dj&&(blocked(cx(a),cz(j),RAD)||blocked(cx(i),cz(b),RAD)))continue;
   const nc=cost[c]+Math.hypot(di,dj);if(nc<cost[k]){cost[k]=nc;prev[k]=c;open.push(k)}}}
 if(!done[key(gi,gj)])return null;let p=[],c=key(gi,gj);while(c>=0){p.push({x:cx(c%NX),z:cz((c/NX)|0)});c=prev[c]}p.reverse();p[p.length-1]={x:gx,z:gz};
 const out=[p[0]];let a=0;while(a<p.length-1){let b=p.length-1;while(b>a+1&&!clear(p[a].x,p[a].z,p[b].x,p[b].z))b--;out.push(p[b]);a=b}return out.slice(1)}

/* ---------- three.js scene ---------- */
const cv=document.getElementById('c3'),ren=new THREE.WebGLRenderer({canvas:cv,antialias:true,alpha:true});
const scene=new THREE.Scene(),cam=new THREE.PerspectiveCamera(48,1,.1,60);
scene.add(new THREE.HemisphereLight(0xffffff,0x778899,.85));const sun=new THREE.DirectionalLight(0xffffff,.6);sun.position.set(3,6,2);scene.add(sun);
const M=(c)=>new THREE.MeshLambertMaterial({color:c});
const floor=new THREE.Mesh(new THREE.PlaneGeometry(2*HX,2*HZ),new THREE.MeshBasicMaterial());floor.rotation.x=-Math.PI/2;scene.add(floor);
const grid=new THREE.GridHelper(8,16,0x888888,0x888888);grid.scale.z=.75;grid.position.y=.002;scene.add(grid);
const wallM=new THREE.MeshLambertMaterial({color:0x9aa7b3,transparent:true,opacity:.35});
[[0,-HZ,2*HX,.06],[0,HZ,2*HX,.06],[-HX,0,.06,2*HZ],[HX,0,.06,2*HZ]].forEach(([x,z,w,d])=>{const m=new THREE.Mesh(new THREE.BoxGeometry(w,1.1,d),wallM);m.position.set(x,.55,z);scene.add(m)});
const box=(w,h,d,c,x,y,z,p)=>{const m=new THREE.Mesh(new THREE.BoxGeometry(w,h,d),M(c));m.position.set(x,y,z);p.add(m);return m};
const cyl=(r,h,c,x,y,z,p)=>{const m=new THREE.Mesh(new THREE.CylinderGeometry(r,r,h,14),M(c));m.position.set(x,y,z);p.add(m);return m};
const world=new THREE.Group();scene.add(world);function build(){world.clear();for(const o0 of OB){const o=o0.r?{...o0,w:o0.d,d:o0.w}:o0;const g=new THREE.Group();g.position.set(o0.x,0,o0.z);g.rotation.y=o0.r?Math.PI/2:0;world.add(g);
 if(o.t=='bed'){const s=o.x<0?-1:1;box(o.w,.3,o.d,0x5d7a99,0,.3,0,g);box(o.w-.05,.14,o.d-.05,0xf2f2ee,0,.5,0,g);box(.06,.7,o.d,0x4a6482,s*o.w/2,.55,0,g);box(.4,.1,.6,0xffffff,s*(o.w/2-.3),.62,0,g);
  [[-1,-1],[1,-1],[-1,1],[1,1]].forEach(([a,b])=>cyl(.03,.15,0x333333,a*(o.w/2-.05),.075,b*(o.d/2-.05),g))}
 else if(o.t=='stand'){cyl(.14,.03,0x777777,0,.02,0,g);cyl(.016,1.7,0xb8bec4,0,.88,0,g);box(.12,.2,.04,0x7ec8e3,0,1.62,0,g)}
 else if(o.t=='crate'){box(o.w,.6,o.d,0xb08a5a,0,.3,0,g)}else if(o.t=='counter'){box(o.w,.95,o.d,0x6f8f7a,0,.475,0,g);box(o.w-.1,.05,o.d+.1,0xe8e4da,0,.97,0,g);box(.4,.3,.04,0x222222,0,1.15,0,g)}else{box(o.w,.04,o.d,0x9c7a55,0,.72,0,g);[[-1,-1],[1,-1],[-1,1],[1,1]].forEach(([a,b])=>cyl(.025,.7,0x555555,a*(o.w/2-.05),.35,b*(o.d/2-.05),g))}}}build();
/* robot */
const rob=new THREE.Group();scene.add(rob);box(.28,.08,.2,0x0e8f84,0,.1,0,rob);box(.1,.04,.08,0x222222,-.06,.16,0,rob);
const wheels=[-1,1].map(s=>{const m=new THREE.Mesh(new THREE.CylinderGeometry(WR,WR,.035,18).rotateX(Math.PI/2),M(0x222222));m.position.set(0,WR,s*.115);rob.add(m);
 const sp=new THREE.Mesh(new THREE.BoxGeometry(.02,.1,.04),M(0xeeeeee));m.add(sp);return m});
box(.04,.05,.04,0x888888,.08,.19,0,rob);
const head=new THREE.Group();head.position.set(.08,.24,0);rob.add(head);box(.07,.04,.05,0xd9822b,.02,0,0,head);box(.05,.04,.05,0x2b2b2b,.15,.14,0,rob);box(.012,.025,.025,0x4fc3f7,.178,.14,0,rob);
const beamG=new THREE.BufferGeometry();beamG.setAttribute('position',new THREE.BufferAttribute(new Float32Array(6),3));
const beam=new THREE.Line(beamG,new THREE.LineBasicMaterial({color:0xe5484d}));beam.frustumCulled=false;scene.add(beam);
const MAXP=2500,pg=new THREE.BufferGeometry();pg.setAttribute('position',new THREE.BufferAttribute(new Float32Array(MAXP*3),3));pg.setDrawRange(0,0);
const cloud=new THREE.Points(pg,new THREE.PointsMaterial({size:.05,color:0x0e8f84}));cloud.frustumCulled=false;scene.add(cloud);
const mark=new THREE.Group();scene.add(mark);const ring=new THREE.Mesh(new THREE.RingGeometry(.18,.24,32).rotateX(-Math.PI/2),new THREE.MeshBasicMaterial({color:0xd9822b,side:2}));ring.position.y=.01;mark.add(ring);
const pole=new THREE.Mesh(new THREE.ConeGeometry(.08,.3,12).rotateX(Math.PI),new THREE.MeshBasicMaterial({color:0xd9822b}));pole.position.y=.5;mark.add(pole);mark.visible=false;
const pathG=new THREE.BufferGeometry(),pathL=new THREE.Line(pathG,new THREE.LineBasicMaterial({color:0xd9822b}));pathL.frustumCulled=false;scene.add(pathL);
function theme(){floor.material.color.set(css('--floor'));grid.material.color.set(css('--grid'));cloud.material.color.set(css('--pt'));ren2.setClearColor(css('--bg'))}
matchMedia('(prefers-color-scheme:dark)').addEventListener('change',theme);
/* orbit camera */
let th=.6,ph=.95,rad=9.5;const tgt=new THREE.Vector3();
function setCam(){cam.position.set(tgt.x+rad*Math.sin(ph)*Math.sin(th),tgt.y+rad*Math.cos(ph),tgt.z+rad*Math.sin(ph)*Math.cos(th));cam.lookAt(tgt)}
let dn=null;cv.addEventListener('pointerdown',e=>{dn={x:e.clientX,y:e.clientY,mx:e.clientX,my:e.clientY};cv.setPointerCapture(e.pointerId)});
cv.addEventListener('pointermove',e=>{if(!dn)return;th-=(e.clientX-dn.mx)*.008;ph=Math.min(1.5,Math.max(.15,ph-(e.clientY-dn.my)*.006));dn.mx=e.clientX;dn.my=e.clientY});
cv.addEventListener('pointerup',e=>{if(dn&&Math.hypot(e.clientX-dn.x,e.clientY-dn.y)<5){const r=cv.getBoundingClientRect(),rc=new THREE.Raycaster();
 rc.setFromCamera(new THREE.Vector2((e.clientX-r.left)/r.width*2-1,-(e.clientY-r.top)/r.height*2+1),cam);const v=new THREE.Vector3();
 if(rc.ray.intersectPlane(new THREE.Plane(new THREE.Vector3(0,1,0),0),v))clickAt(v.x,v.z)}dn=null});
cv.addEventListener('wheel',e=>{e.preventDefault();rad=Math.min(16,Math.max(3,rad*(1+Math.sign(e.deltaY)*.08)))},{passive:false});

/* ---------- sim state ---------- */
function reset(){R={...START};path=[];pi=0;wp=null;state='scan';tmr=0;encL=encR=0;pts=[];sweep=new Array(181).fill(null);servo=0;past=[{x:START.x,z:START.z}];flags={};yawG=yawE=START.h;gz=0;known=new Set();dets=[];rq=[];mark.visible=false;pathG.setFromPoints([]);
 pg.setDrawRange(0,0);logs=[];log('boot: ESP32 up, VL53L1X + MPU6050 ok');log('state: SCAN (servo sweeping ToF)')}
function setWP(x,z,who){const p=plan(R.x,R.z,x,z);if(!p){log('waypoint unreachable, ignored');return false}
 wp={x,z};path=p;pi=0;state='drive';mark.visible=true;mark.position.set(x,0,z);past.push({x,z});
 pathG.setFromPoints([new THREE.Vector3(R.x,.03,R.z),...p.map(q=>new THREE.Vector3(q.x,.03,q.z))]);
 log(who+' waypoint ('+x.toFixed(2)+', '+z.toFixed(2)+') m → DRIVE');return true}
function userWP(x,z){if(blocked(x,z,RAD)){log('waypoint inside obstacle, ignored');return}setWP(x,z,'USER')}
function aiPick(){while(rq.length){const q=rq.shift();if(setWP(q[0],q[1],'ROUNDS')){wp.look={x:q[2],z:q[3]};return}}if(camOn&&inspectPick())return;const c=[];for(let i=0;i<80;i++){const x=(Math.random()*2-1)*(HX-.5),z=(Math.random()*2-1)*(HZ-.5),d=Math.hypot(x-R.x,z-R.z);
  if(d<1.2||d>4.2||blocked(x,z,.45))continue;c.push({x,z,s:Math.min(...past.map(p=>Math.hypot(p.x-x,p.z-z)))})}
 c.sort((a,b)=>b.s-a.s);for(const q of c)if(setWP(q.x,q.z,'LLM'))return;state='scan';tmr=0}

function step(dt){simT+=dt;
 servo=1.22*Math.sin(simT*2.4);
 for(let k=0;k<3;k++){const s=1.22*Math.sin((simT-dt+dt*(k+1)/3)*2.4),a=R.h+s,ox=R.x+Math.cos(R.h)*.08,oz=R.z+Math.sin(R.h)*.08;
  let d=cast(ox,oz,Math.cos(a),Math.sin(a));const hit=d<MAXR-.01;d=Math.min(MAXR,Math.max(.04,d+(Math.random()-.5)*.02));
  sweep[Math.round(s*180/Math.PI)+90]={d,hit};
  if(hit&&(pts.length<MAXP)){const px=ox+Math.cos(a)*d,pz=oz+Math.sin(a)*d;if(k==0){pts.push({x:px,z:pz});const i=pts.length-1,A=pg.attributes.position.array;A[i*3]=px;A[i*3+1]=.24;A[i*3+2]=pz;pg.attributes.position.needsUpdate=true;pg.setDrawRange(0,pts.length)}}
  if(k==2){R.lastD=d;R.lastHit=hit;const b=beamG.attributes.position.array;b[0]=ox;b[1]=.25;b[2]=oz;b[3]=ox+Math.cos(a)*d;b[4]=.25;b[5]=oz+Math.sin(a)*d;beamG.attributes.position.needsUpdate=true}}
 let v=0,w=0;
 if(state=='scan'){tmr+=dt;if(tmr>3.2){state='think';tmr=0;flags={};log('state: THINK (ESP32 → PC over Wi-Fi)')}}
 else if(state=='think'){tmr+=dt;if(tmr>.5&&!flags.a){flags.a=1;log('PC: filter ToF + fuse MPU6050 yaw → '+pts.length+' map pts')}
  if(tmr>1.1&&!flags.b){flags.b=1;log('PC → LLM API: map + pose'+(camOn?' + '+known.size+' camera labels':'')+', asking for waypoint')}
  if(tmr>1.9){if(auto||rq.length)aiPick();else{state='scan';tmr=0;log('auto off: click floor or map to set a waypoint')}}}
 else if(state=='face'){const e=wrap(Math.atan2(wp.look.z-R.z,wp.look.x-R.x)-R.h);if(Math.abs(e)<.05){state='scan';tmr=0;log('camera on target, capturing frames')}else w=Math.sign(e)*2.2}else if(state=='drive'){const fd=cast(R.x,R.z,Math.cos(R.h),Math.sin(R.h)),fx=R.x+Math.cos(R.h)*fd,fz=R.z+Math.sin(R.h)*fd;if(fd>.7)R.rp=0;if(fd<.55&&Math.abs(fx)<HX-.05&&Math.abs(fz)<HZ-.05&&!R.rp){R.rp=1;const np=plan(R.x,R.z,wp.x,wp.z);if(!np){state='scan';tmr=0;mark.visible=false;pathG.setFromPoints([]);log('ToF: blocked, no path. rescanning');return}path=np;pi=0;pathG.setFromPoints([new THREE.Vector3(R.x,.03,R.z),...np.map(q=>new THREE.Vector3(q.x,.03,q.z))]);log('ToF: obstacle ahead → replanned path')}const t=path[pi],dx=t.x-R.x,dz=t.z-R.z,d=Math.hypot(dx,dz),err=wrap(Math.atan2(dz,dx)-R.h);
  if(Math.abs(err)>.2){w=Math.sign(err)*2.2}else{v=Math.min(.7,d*2+.15);w=err*3}
  if(d<.12){pi++;if(pi>=path.length){state=wp&&wp.look?'face':'scan';tmr=0;mark.visible=false;pathG.setFromPoints([]);log('arrived. encoders L '+Math.round(encL)+' R '+Math.round(encR));log(state=='face'?'state: FACE (aim camera at target)':'state: SCAN')}}}
 R.h=wrap(R.h+w*dt);gz=w+.012+(Math.random()-.5)*.02;yawG+=gz*dt;R.x+=v*Math.cos(R.h)*dt;R.z+=v*Math.sin(R.h)*dt;
 const dl=(v+w*L/2)*dt,dr=(v-w*L/2)*dt;yawE+=(dl-dr)/L*1.01;encL+=dl/(2*Math.PI*WR)*TPR;encR+=dr/(2*Math.PI*WR)*TPR;wheels[0].rotation.z-=dl/WR;wheels[1].rotation.z-=dr/WR}

/* ---------- 2D windows ---------- */
const cr=document.getElementById('cr'),cm=document.getElementById('cm');
function fit(c,ar){const r=devicePixelRatio||1,w=Math.round(c.clientWidth*r),h=Math.round(w/ar);if(c.width!=w||c.height!=h){c.width=w;c.height=h}return c.getContext('2d')}
function drawRadar(){const g=fit(cr,1.7),W=cr.width,H=cr.height,sc=(H*.86)/MAXR,ox=W/2,oy=H*.94,u=W/600;g.clearRect(0,0,W,H);
 g.lineWidth=u;g.font=(11*u)+'px system-ui';g.fillStyle=css('--mut');g.strokeStyle=css('--line');
 for(let r=1;r<=MAXR;r++){g.beginPath();g.arc(ox,oy,r*sc,Math.PI*1.08,Math.PI*1.92);g.stroke();g.fillText(r+' m',ox+4*u,oy-r*sc+12*u)}
 for(const a of[-70,-35,0,35,70]){const s=a*Math.PI/180;g.beginPath();g.moveTo(ox,oy);g.lineTo(ox+Math.sin(s)*MAXR*sc,oy-Math.cos(s)*MAXR*sc);g.stroke()}
 g.fillStyle=css('--acc');for(let i=0;i<181;i++){const q=sweep[i];if(!q)continue;const s=(i-90)*Math.PI/180;g.globalAlpha=q.hit?1:.25;g.beginPath();g.arc(ox+Math.sin(s)*q.d*sc,oy-Math.cos(s)*q.d*sc,2.2*u,0,7);g.fill()}g.globalAlpha=1;
 const d=R.lastD||0;g.strokeStyle='#e5484d';g.lineWidth=1.6*u;g.beginPath();g.moveTo(ox,oy);g.lineTo(ox+Math.sin(servo)*d*sc,oy-Math.cos(servo)*d*sc);g.stroke();
 g.fillStyle=css('--warn');g.fillRect(ox-7*u,oy-3*u,14*u,8*u);
 document.getElementById('tofR').textContent=R.lastHit?Math.round((R.lastD||0)*1000)+' mm':'out of range'}
function drawMap(){const g=fit(cm,4/3),W=cm.width,sc=W/(2*HX),u=W/600,X=x=>(x+HX)*sc,Z=z=>(z+HZ)*sc;g.clearRect(0,0,W,cm.height);
 g.strokeStyle=css('--line');g.lineWidth=u;g.setLineDash([4*u,4*u]);for(const o of OB)g.strokeRect(X(o.x-o.w/2),Z(o.z-o.d/2),o.w*sc,o.d*sc);g.setLineDash([]);g.strokeRect(0,0,W,cm.height);OB.forEach((o,i)=>{if(!known.has(i))return;g.fillStyle=css('--acc');g.globalAlpha=.18;g.fillRect(X(o.x-o.w/2),Z(o.z-o.d/2),o.w*sc,o.d*sc);g.globalAlpha=1;g.strokeStyle=css('--acc');g.lineWidth=1.5*u;g.strokeRect(X(o.x-o.w/2),Z(o.z-o.d/2),o.w*sc,o.d*sc);g.fillStyle=css('--ink');g.font=(11*u)+'px system-ui';g.textAlign='center';g.fillText(o.t,X(o.x),Z(o.z)+4*u);g.textAlign='left'});
 g.fillStyle=css('--acc');for(const p of pts)g.fillRect(X(p.x)-1.2*u,Z(p.z)-1.2*u,2.4*u,2.4*u);
 if(path.length){g.strokeStyle=css('--warn');g.lineWidth=1.5*u;g.beginPath();g.moveTo(X(R.x),Z(R.z));for(let i=pi;i<path.length;i++)g.lineTo(X(path[i].x),Z(path[i].z));g.stroke()}
 if(wp){g.strokeStyle=css('--warn');g.lineWidth=2*u;g.beginPath();g.arc(X(wp.x),Z(wp.z),8*u,0,7);g.moveTo(X(wp.x)-12*u,Z(wp.z));g.lineTo(X(wp.x)+12*u,Z(wp.z));g.moveTo(X(wp.x),Z(wp.z)-12*u);g.lineTo(X(wp.x),Z(wp.z)+12*u);g.stroke()}
 g.save();g.translate(X(R.x),Z(R.z));g.rotate(R.h);g.fillStyle=css('--warn');g.beginPath();g.moveTo(11*u,0);g.lineTo(-7*u,-7*u);g.lineTo(-7*u,7*u);g.fill();
 g.fillStyle='rgba(229,72,77,.18)';g.beginPath();g.moveTo(0,0);g.arc(0,0,MAXR*sc,-1.22,1.22);g.fill();g.fillStyle='rgba(60,140,230,.16)';g.beginPath();g.moveTo(0,0);g.arc(0,0,3.5*sc,-.57,.57);g.fill();g.restore()}
cm.addEventListener('click',e=>{const r=cm.getBoundingClientRect(),x=(e.clientX-r.left)/r.width*2*HX-HX,z=(e.clientY-r.top)/r.height*2*HZ-HZ;clickAt(x,z)});
const PIPE=[['ESP32: servo + ToF sweep','scan'],['PC: filter + map','think'],['LLM API: waypoint','think'],['Motors + encoders','drive'],['MPU6050: gyro yaw','imu'],['XIAO ESP32 cam: objects','cam']];
const pipe=document.getElementById('pipe');PIPE.forEach(p=>{const s=document.createElement('span');s.className='chip';s.textContent=p[0];pipe.appendChild(s)});
function tel(){const T=(i,v)=>document.getElementById(i).textContent=v,deg=a=>(a*180/Math.PI).toFixed(0)+'°';
 T('tS',state.toUpperCase());T('tP',R.x.toFixed(2)+', '+R.z.toFixed(2));T('tH',deg(R.h));T('tV',deg(servo));T('tL',Math.round(encL));T('tRr',Math.round(encR));T('tG',(gz*180/Math.PI).toFixed(1)+'°/s');T('tYG',deg(yawG));T('tYE',deg(yawE));T('camS','labeled '+known.size+'/'+OB.length);
 [...pipe.children].forEach((c,i)=>{const on=i==4||(i==5&&camOn)||(state=='scan'?i==0:state=='think'?(i==1&&!flags.b||i==2&&flags.b):i==3);c.classList.toggle('a',on)})}

/* ---------- loop + UI ---------- */
let last=performance.now(),acc=0;
function frame(t){const dt=Math.min(.05,(t-last)/1000);last=t;
 if(!paused){const n=+document.getElementById('spd').value;acc+=dt*n;while(acc>=1/60){step(1/60);acc-=1/60}}
 rob.position.set(R.x,0,R.z);rob.rotation.y=-R.h;head.rotation.y=-servo;
 if(follow)tgt.lerp(new THREE.Vector3(R.x,0,R.z),.08);else tgt.lerp(new THREE.Vector3(0,0,0),.08);
 const w=cv.clientWidth,h=cv.clientHeight;if(cv.width!=w*devicePixelRatio){ren.setPixelRatio(devicePixelRatio);ren.setSize(w,h,false);cam.aspect=w/h;cam.updateProjectionMatrix()}
 pole.position.y=.5+Math.sin(t/200)*.05;setCam();ren.render(scene,cam);camView();drawRadar();drawMap();tel();requestAnimationFrame(frame)}
const tog=(id,fn)=>document.getElementById(id).onclick=e=>{fn(e.target)};
tog('bAuto',b=>{auto=!auto;b.classList.toggle('on',auto)});tog('bPause',b=>{paused=!paused;b.textContent=paused?'Resume':'Pause'});
tog('bFollow',b=>{follow=!follow;b.classList.toggle('on',follow)});tog('bReset',()=>reset());
const ren2=new THREE.WebGLRenderer({canvas:document.getElementById('cc'),antialias:false}),cam2=new THREE.PerspectiveCamera(65,4/3,.05,30);ren2.setSize(320,240,false);
function camView(){const ca=Math.cos(R.h),sa=Math.sin(R.h);cam2.position.set(R.x+ca*.17,.2,R.z+sa*.17);cam2.lookAt(R.x+ca*2,.2,R.z+sa*2);
 const hs=[beam,cloud,mark,pathL,rob],vs=hs.map(o=>o.visible);hs.forEach(o=>o.visible=false);ren2.render(scene,cam2);hs.forEach((o,i)=>o.visible=vs[i]);detect()}
function detect(){const g=document.getElementById('co').getContext('2d'),W=320,H=240,cp=cam2.position,v=new THREE.Vector3();g.clearRect(0,0,W,H);dets=[];
 OB.forEach((o,i)=>{const hh=o.t=='stand'?1.7:o.t=='counter'?1.1:o.t=='crate'?.6:.75,d=Math.hypot(o.x-cp.x,o.z-cp.z);if(d>3.6)return;let x0=1e9,y0=1e9,x1=-1e9,y1=-1e9,ok=true;
  for(const sx of[-1,1])for(const sz of[-1,1])for(const y of[0,hh]){v.set(o.x+sx*o.w/2,y,o.z+sz*o.d/2).project(cam2);if(v.z>1){ok=false;continue}x0=Math.min(x0,v.x);x1=Math.max(x1,v.x);y0=Math.min(y0,v.y);y1=Math.max(y1,v.y)}
  if(!ok||x1<-1||x0>1||y1<-1||y0>1)return;if(cast(cp.x,cp.z,(o.x-cp.x)/d,(o.z-cp.z)/d)<d-Math.max(o.w,o.d)/2-.1)return;
  const bx=(Math.max(-1,x0)+1)/2*W,bx2=(Math.min(1,x1)+1)/2*W,by=(1-Math.min(1,y1))/2*H,by2=(1-Math.max(-1,y0))/2*H;if(bx2-bx<14||by2-by<14)return;
  const c=Math.max(.5,.98-d*.1),col=camOn?'#2fd0c0':'#8b97a2',s=o.t+' '+Math.round(c*100)+'% · '+d.toFixed(1)+' m';dets.push({i,d});
  g.strokeStyle=col;g.lineWidth=2;g.strokeRect(bx,by,bx2-bx,by2-by);g.font='12px system-ui';g.fillStyle=col;const ty=Math.max(0,by-16);g.fillRect(bx,ty,g.measureText(s).width+8,16);g.fillStyle='#04201d';g.fillText(s,bx+4,ty+12);
  if(camOn&&!paused&&!known.has(i)){known.add(i);log('CAM: '+o.t+' @ '+d.toFixed(1)+' m → labeled on map')}})}
function inspectPick(){const un=pts.filter(p=>Math.abs(p.x)<HX-.15&&Math.abs(p.z)<HZ-.15&&!OB.some((o,i)=>known.has(i)&&Math.abs(p.x-o.x)<o.w/2+.3&&Math.abs(p.z-o.z)<o.d/2+.3));if(un.length<8)return false;
 const a=un.reduce((m,p)=>Math.hypot(p.x-R.x,p.z-R.z)<Math.hypot(m.x-R.x,m.z-R.z)?p:m),cl=un.filter(p=>Math.hypot(p.x-a.x,p.z-a.z)<.9);if(cl.length<5)return false;
 const mx=cl.reduce((s,p)=>s+p.x,0)/cl.length,mz=cl.reduce((s,p)=>s+p.z,0)/cl.length;
 for(let k=0;k<30;k++){const an=Math.random()*6.283,r=1.3+Math.random()*.5,x=mx+Math.cos(an)*r,z=mz+Math.sin(an)*r;if(blocked(x,z,.45))continue;if(cast(x,z,(mx-x)/r,(mz-z)/r)<r-.5)continue;
  if(setWP(x,z,'LLM+CAM')){wp.look={x:mx,z:mz};log('CAM assist: inspect unlabeled obstacle near ('+mx.toFixed(1)+', '+mz.toFixed(1)+')');return true}}return false}
tog('bCam',b=>{camOn=!camOn;b.classList.toggle('on',camOn);log('camera assist '+(camOn?'ON':'OFF'))});
const E=id=>document.getElementById(id);let mode=false,tool='bed';
const DIM={bed:[2,1],stand:[.3,.3],table:[1.2,.6],crate:[.8,.8],counter:[2.4,.8]};
const sc=(obs,x,z)=>({obs,start:{x,z,h:-Math.PI/2}});
const SC={ward:sc(JSON.parse(JSON.stringify(OB)),-.5,2.2),
 nursing:sc([{t:'counter',x:0,z:-2.3,w:3,d:.8},{t:'bed',x:-2.9,z:-.9,w:2,d:1},{t:'bed',x:-2.9,z:1.2,w:2,d:1},{t:'bed',x:2.9,z:-.9,w:2,d:1},{t:'bed',x:2.9,z:1.2,w:2,d:1},{t:'stand',x:-1.65,z:-.9,w:.3,d:.3},{t:'stand',x:-1.65,z:1.2,w:.3,d:.3},{t:'stand',x:1.65,z:-.9,w:.3,d:.3},{t:'stand',x:1.65,z:1.2,w:.3,d:.3},{t:'crate',x:3.2,z:-2.4,w:1,d:.6}],0,2.3),
 course:sc([{t:'crate',x:-2.2,z:.6,w:3.2,d:.4},{t:'crate',x:2.2,z:.6,w:3.2,d:.4},{t:'crate',x:-2.6,z:-1.4,w:.8,d:.8},{t:'crate',x:.4,z:-1.7,w:1,d:.6},{t:'crate',x:2.6,z:-1.3,w:.8,d:.8},{t:'stand',x:-.9,z:1.8,w:.3,d:.3},{t:'bed',x:-2.8,z:2.35,w:2,d:1}],1.5,2.3),
 empty:sc([],0,2.2)};
function fixStart(){if(!blocked(START.x,START.z,.3))return;let b=null;for(let i=0;i<NX;i++)for(let j=0;j<NZ;j++){const x=cx(i),z=cz(j);if(blocked(x,z,.35))continue;const d=Math.hypot(x-START.x,z-START.z);if(!b||d<b.d)b={x,z,d}}if(b){START.x=b.x;START.z=b.z}}
function loadScn(k){if(k=='custom')return;const s=SC[k];OB=JSON.parse(JSON.stringify(s.obs));Object.assign(START,s.start);build();fixStart();reset();log('scenario loaded: '+k)}
function relayout(m){build();fixStart();reset();E('scn').value='custom';log('layout: '+m+' → map cleared')}
function overlapAny(o,skip){return OB.some((p,i)=>i!=skip&&Math.abs(o.x-p.x)<(o.w+p.w)/2&&Math.abs(o.z-p.z)<(o.d+p.d)/2)||(Math.abs(o.x-START.x)<o.w/2+.35&&Math.abs(o.z-START.z)<o.d/2+.35)}
function hitObj(x,z){return OB.findIndex(o=>Math.abs(x-o.x)<=o.w/2+.15&&Math.abs(z-o.z)<=o.d/2+.15)}
function clickAt(x,z){mode?editClick(x,z):userWP(x,z)}
function editClick(x,z){const sn=v=>Math.round(v*4)/4,i=hitObj(x,z);
 if(tool=='del'){if(i>=0){const t=OB[i].t;OB.splice(i,1);relayout('removed '+t)}return}
 if(tool=='rot'){if(i>=0){const o=OB[i];[o.w,o.d]=[o.d,o.w];o.r=o.r?0:1;if(Math.abs(o.x)>HX-o.w/2||Math.abs(o.z)>HZ-o.d/2||overlapAny(o,i)){[o.w,o.d]=[o.d,o.w];o.r=o.r?0:1;log('no room to rotate');return}relayout('rotated '+o.t)}return}
 if(tool=='start'){if(blocked(x,z,.3)){log('start position blocked');return}START.x=x;START.z=z;relayout('start moved');return}
 const[w,d]=DIM[tool],o={t:tool,x:sn(x),z:sn(z),w,d};if(Math.abs(o.x)>HX-w/2||Math.abs(o.z)>HZ-d/2||overlapAny(o,-1)){log('cannot place '+tool+' there');return}OB.push(o);relayout('placed '+tool)}
function dropAhead(){let tx=Math.cos(R.h),tz=Math.sin(R.h),dist=1.5;if(state=='drive'&&path[pi]){const dx=path[pi].x-R.x,dz=path[pi].z-R.z,d=Math.hypot(dx,dz)||1;tx=dx/d;tz=dz/d;dist=Math.min(1.5,d*.7)}
 for(const k of[1,.8,1.2,.6]){const o={t:'crate',x:Math.round((R.x+tx*dist*k)*4)/4,z:Math.round((R.z+tz*dist*k)*4)/4,w:.8,d:.8};if(Math.abs(o.x)<=HX-.4&&Math.abs(o.z)<=HZ-.4&&Math.hypot(o.x-R.x,o.z-R.z)>.9&&!overlapAny(o,-1)){OB.push(o);build();E('scn').value='custom';log('crate dropped in path at ('+o.x.toFixed(2)+', '+o.z.toFixed(2)+')');return}}log('no space to drop a crate')}
function runRounds(){const tg=OB.filter(o=>o.t=='bed'||o.t=='counter');if(!tg.length){log('no beds to visit');return}
 let cur={x:R.x,z:R.z},left=tg.slice(),q=[];while(left.length){left.sort((a,b)=>Math.hypot(a.x-cur.x,a.z-cur.z)-Math.hypot(b.x-cur.x,b.z-cur.z));const o=left.shift();let best=null;
  for(const[dx,dz]of[[1,0],[-1,0],[0,1],[0,-1]]){const x=o.x+dx*(o.w/2+.8),z=o.z+dz*(o.d/2+.8);if(!blocked(x,z,.4)&&plan(cur.x,cur.z,x,z)){const d=Math.hypot(x-cur.x,z-cur.z);if(!best||d<best.d)best={x,z,d}}}
  if(best){q.push([best.x,best.z,o.x,o.z]);cur=best}}
 rq=q;state='scan';tmr=2.9;mark.visible=false;pathG.setFromPoints([]);log('ROUNDS: '+q.length+' stops queued')}
E('scn').onchange=e=>loadScn(e.target.value);
E('bEdit').onclick=e=>{mode=!mode;e.target.classList.toggle('on',mode);E('ed').style.display=mode?'flex':'none';log(mode?'EDIT: pick a tool, click floor or map':'edit mode off')};
document.querySelectorAll('#ed [data-t]').forEach(b=>b.onclick=()=>{tool=b.dataset.t;document.querySelectorAll('#ed [data-t]').forEach(x=>x.classList.toggle('on',x==b))});
E('bClear').onclick=()=>{OB=[];relayout('cleared all')};E('bDrop').onclick=dropAhead;E('bRounds').onclick=runRounds;
theme();reset();requestAnimationFrame(frame);
