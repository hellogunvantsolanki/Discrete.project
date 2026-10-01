const $=id=>document.getElementById(id);
const NS="http://www.w3.org/2000/svg";
const EX=[
 ["Divisors of 12","div","1, 2, 3, 4, 6, 12",""],
 ["Divisors of 30","div","1, 2, 3, 5, 6, 10, 15, 30",""],
 ["Divisors of 60","div","1,2,3,4,5,6,10,12,15,20,30,60",""],
 ["P({a,b,c}) ⊆","sub","{}, {a}, {b}, {c}, {a,b}, {a,c}, {b,c}, {a,b,c}",""],
 ["Chain 1..5","le","1, 2, 3, 4, 5",""],
 ["Custom (N shape)","custom","a, b, c, d","a<c, b<c, b<d"],
];
const HINTS={div:"Enter positive integers. Example: 1, 2, 3, 4, 6, 12",le:"Any numbers allowed. Example: 1, 2, 3, 4",sub:"Write each set inside braces. Example: {}, {a}, {b}, {a,b}",custom:"List the elements, then pairs like a<b (meaning a ≤ b). Reflexive and transitive relations are added automatically."};

function splitTop(s){const out=[];let d=0,cur="";for(const ch of s){if(ch==="{")d++;if(ch==="}")d--;if(ch===","&&d===0){out.push(cur.trim());cur=""}else cur+=ch}if(cur.trim()!==""||out.length)out.push(cur.trim());return out.filter(x=>x!=="")}
function parseSet(t){t=t.replace(/∅/g,"{}");if(!/^\{.*\}$/.test(t))throw new Error(`"${t}" is not a set. Use braces, e.g. {a,b}`);const inner=t.slice(1,-1).trim();return new Set(inner?inner.split(",").map(x=>x.trim()).filter(Boolean):[])}
const fmtSet=s=>s.size?"{"+[...s].sort().join(",")+"}":"∅";

function build(){
  const type=$("rel").value;
  let raw=splitTop($("els").value);
  let labels=[],le;
  if(type==="div"||type==="le"){
    const nums=raw.map(x=>{const n=Number(x);if(!isFinite(n)||x==="")throw new Error(`"${x}" is not a number`);if(type==="div"&&(!Number.isInteger(n)||n<=0))throw new Error("Divisibility requires positive integers only");return n});
    const u=[...new Set(nums)].sort((a,b)=>a-b);labels=u.map(String);
    le=type==="div"?(i,j)=>u[j]%u[i]===0:(i,j)=>u[i]<=u[j];
  }else if(type==="sub"){
    const sets=raw.map(parseSet),seen=new Set(),u=[];
    for(const s of sets){const k=fmtSet(s);if(!seen.has(k)){seen.add(k);u.push(s)}}
    u.sort((a,b)=>a.size-b.size);labels=u.map(fmtSet);
    le=(i,j)=>[...u[i]].every(x=>u[j].has(x));
  }else{
    const set=new Set(raw);const pr=[];
    $("pairs").value.split(/[,;\n]+/).map(s=>s.trim()).filter(Boolean).forEach(p=>{
      const m=p.split(/<=|≤|->|→|<|-/).map(x=>x.trim()).filter(Boolean);
      if(m.length<2)throw new Error(`Could not understand the pair "${p}". Use the format a<b`);
      for(let k=0;k<m.length-1;k++){pr.push([m[k],m[k+1]]);set.add(m[k]);set.add(m[k+1])}
    });
    labels=[...set];const idx={};labels.forEach((l,i)=>idx[l]=i);
    const n=labels.length,R=Array.from({length:n},(_,i)=>Array.from({length:n},(_,j)=>i===j));
    pr.forEach(([a,b])=>R[idx[a]][idx[b]]=true);
    for(let k=0;k<n;k++)for(let i=0;i<n;i++)if(R[i][k])for(let j=0;j<n;j++)if(R[k][j])R[i][j]=true;
    for(let i=0;i<n;i++)for(let j=i+1;j<n;j++)if(R[i][j]&&R[j][i])throw new Error(`Antisymmetry fails: ${labels[i]} ≤ ${labels[j]} and ${labels[j]} ≤ ${labels[i]} both hold. This is not a partial order.`);
    le=(i,j)=>R[i][j];
  }
  if(!labels.length)throw new Error("No elements provided");
  if(labels.length>40)throw new Error("Max 40 elements allowed");
  return {labels,le};
}

function analyze({labels,le}){
  const n=labels.length,lt=(i,j)=>i!==j&&le(i,j);
  const covers=[];
  for(let i=0;i<n;i++)for(let j=0;j<n;j++)if(lt(i,j)){let c=true;for(let k=0;k<n;k++)if(lt(i,k)&&lt(k,j)){c=false;break}if(c)covers.push([i,j])}
  const below=Array.from({length:n},()=>[]);covers.forEach(([i,j])=>below[j].push(i));
  const rank=new Array(n).fill(-1);
  const rk=j=>rank[j]>=0?rank[j]:(rank[j]=below[j].length?1+Math.max(...below[j].map(rk)):0);
  for(let j=0;j<n;j++)rk(j);
  const H=Math.max(...rank),levels=Array.from({length:H+1},()=>[]);
  rank.forEach((r,i)=>levels[r].push(i));
  // reduce crossings: barycenter sweeps
  const pos=new Array(n),setPos=()=>levels.forEach(L=>L.forEach((v,k)=>pos[v]=k));setPos();
  const up=Array.from({length:n},()=>[]);covers.forEach(([i,j])=>up[i].push(j));
  for(let it=0;it<6;it++){
    for(let r=1;r<=H;r++){levels[r].sort((a,b)=>bc(a,below)-bc(b,below));setPos()}
    for(let r=H-1;r>=0;r--){levels[r].sort((a,b)=>bc(a,up)-bc(b,up));setPos()}
  }
  function bc(v,nb){return nb[v].length?nb[v].reduce((s,x)=>s+pos[x],0)/nb[v].length:pos[v]}
  const mins=[],maxs=[];
  for(let i=0;i<n;i++){let mn=true,mx=true;for(let j=0;j<n;j++){if(lt(j,i))mn=false;if(lt(i,j))mx=false}if(mn)mins.push(i);if(mx)maxs.push(i)}
  const least=[...Array(n).keys()].filter(i=>[...Array(n).keys()].every(j=>le(i,j)));
  const greatest=[...Array(n).keys()].filter(i=>[...Array(n).keys()].every(j=>le(j,i)));
  return {covers,levels,rank,mins,maxs,least,greatest,H};
}

function draw(data,A){
  const {labels}=data,{levels,covers,rank,mins,maxs}=A;
  const maxW=Math.max(...levels.map(l=>l.length));
  const rx=i=>Math.max(20,labels[i].length*4.6+12);
  const colW=Math.max(90,...labels.map((_,i)=>rx(i)*2+30));
  const W=Math.max(360,maxW*colW+60),rowH=95,H=levels.length*rowH+30;
  const xy={};
  levels.forEach((L,r)=>L.forEach((v,k)=>{xy[v]=[W/2+(k-(L.length-1)/2)*colW,H-rowH/2-15-r*rowH]}));
  const svg=document.createElementNS(NS,"svg");
  svg.setAttribute("viewBox",`0 0 ${W} ${H}`);svg.setAttribute("width",W);svg.setAttribute("xmlns",NS);
  const mk=(t,a,p)=>{const e=document.createElementNS(NS,t);for(const k in a)e.setAttribute(k,a[k]);(p||svg).appendChild(e);return e};
  const css=getComputedStyle(document.documentElement);
  const col=v=>css.getPropertyValue(v).trim();
  const defs=mk("defs",{}),fl=mk("filter",{id:"gl",x:"-50%",y:"-50%",width:"200%",height:"200%"},defs);mk("feDropShadow",{dx:0,dy:0,stdDeviation:4,"flood-color":"#ff1e3c","flood-opacity":.7},fl);const g=mk("linearGradient",{id:"gr",x1:0,y1:0,x2:1,y2:1},defs);
  mk("stop",{offset:"0%","stop-color":col("--ac")},g);mk("stop",{offset:"100%","stop-color":col("--ac2")},g);
  covers.forEach(([i,j])=>mk("line",{x1:xy[i][0],y1:xy[i][1],x2:xy[j][0],y2:xy[j][1],stroke:col("--edge"),"stroke-width":2.2,"stroke-linecap":"round",opacity:.85}));
  labels.forEach((l,i)=>{
    const special=mins.includes(i)||maxs.includes(i);
    mk("ellipse",{cx:xy[i][0],cy:xy[i][1],rx:rx(i),ry:19,fill:special?"#2a0a10":col("--node"),stroke:special?"#ff1e3c":col("--edge"),"stroke-width":special?3:2,filter:special?"url(#gl)":""});
    const t=mk("text",{x:xy[i][0],y:xy[i][1]+5,"text-anchor":"middle","font-size":14,"font-weight":600,fill:col("--tx"),"font-family":"system-ui,sans-serif"});
    t.textContent=l;
  });
  $("stage").replaceChildren(svg);
}

function info(data,A){
  const L=data.labels,f=a=>a.length?a.map(i=>L[i]).join(", "):"none";
  const items=[
    ["Elements",L.length],["Covering pairs (edges)",A.covers.length],["Height (levels)",A.H+1],
    ["Minimal",f(A.mins)],["Maximal",f(A.maxs)],
    ["Least element",f(A.least)],["Greatest element",f(A.greatest)],
    ["Covers (a ⋖ b)",A.covers.map(([i,j])=>`${L[i]}→${L[j]}`).join(", ")||"none"],
  ];
  $("info").replaceChildren(...items.map(([k,v])=>{const d=document.createElement("div");const b=document.createElement("b");b.textContent=k;d.append(b,String(v));return d}));
}

function run(){
  const e=$("err");e.style.display="none";
  try{const d=build(),A=analyze(d);draw(d,A);info(d,A)}
  catch(x){e.textContent="⚠ "+x.message;e.style.display="block"}
}
function sync(){
  const t=$("rel").value;$("pairsBox").style.display=t==="custom"?"block":"none";
  $("hint").textContent=HINTS[t];
  $("elsL").textContent=t==="custom"?"Elements (optional extra, comma separated)":"Elements (comma separated)";
}
EX.forEach(([name,rel,els,pairs])=>{const b=document.createElement("button");b.className="chip";b.textContent=name;b.onclick=()=>{$("rel").value=rel;$("els").value=els;if(pairs)$("pairs").value=pairs;sync();run()};$("chips").appendChild(b)});
$("rel").onchange=sync;$("go").onclick=run;
$("dl").onclick=()=>{const s=$("stage").querySelector("svg");if(!s)return;const url=URL.createObjectURL(new Blob([new XMLSerializer().serializeToString(s)],{type:"image/svg+xml"}));const a=document.createElement("a");a.href=url;a.download="hasse.svg";a.click();URL.revokeObjectURL(url)};
sync();run();