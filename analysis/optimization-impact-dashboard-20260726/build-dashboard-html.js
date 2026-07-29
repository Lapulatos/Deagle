#!/usr/bin/env node

const fs = require("fs");
const path = require("path");

const here = __dirname;
const data = JSON.parse(
  fs.readFileSync(path.join(here, "optimization-impact-data.json"), "utf8")
);
const embedded = JSON.stringify(data).replace(/</g, "\\u003c");
const latestVersion = data.rows.at(-1).version;

const html = String.raw`<!doctype html>
<html lang="zh-CN">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>Deagle Optimization Ledger · V1–V${latestVersion}</title>
  <style>
    :root {
      --ink: #07131d;
      --panel: #0c1c28;
      --panel-2: #102633;
      --line: #234151;
      --paper: #e9f2ed;
      --muted: #87a2a8;
      --success: #56e39f;
      --failure: #ff647c;
      --audit: #f4bb55;
      --baseline: #72d8ff;
      --missing: #526c78;
      --shadow: rgba(0, 0, 0, .34);
    }
    * { box-sizing: border-box; }
    html { background: var(--ink); color-scheme: dark; }
    body {
      margin: 0;
      min-width: 320px;
      color: var(--paper);
      font-family: "Avenir Next", "Gill Sans", "Segoe UI", sans-serif;
      background:
        linear-gradient(rgba(114,216,255,.035) 1px, transparent 1px),
        linear-gradient(90deg, rgba(114,216,255,.035) 1px, transparent 1px),
        radial-gradient(circle at 85% 6%, rgba(86,227,159,.14), transparent 28rem),
        var(--ink);
      background-size: 32px 32px, 32px 32px, auto;
    }
    button, input, select { font: inherit; }
    .shell { max-width: 1620px; margin: 0 auto; padding: 28px 28px 80px; }
    header {
      display: grid;
      grid-template-columns: minmax(0, 1.3fr) minmax(330px, .7fr);
      gap: 30px;
      align-items: end;
      padding: 34px 0 28px;
      border-bottom: 1px solid var(--line);
    }
    .eyebrow {
      color: var(--baseline);
      font: 700 12px/1.4 "SFMono-Regular", Consolas, monospace;
      letter-spacing: .18em;
      text-transform: uppercase;
    }
    h1 {
      margin: 10px 0 12px;
      max-width: 980px;
      font: 700 clamp(42px, 6vw, 92px)/.92 "Iowan Old Style", "Palatino Linotype", serif;
      letter-spacing: -.055em;
    }
    .lede {
      max-width: 920px;
      margin: 0;
      color: #b9cccd;
      font-size: 17px;
      line-height: 1.65;
    }
    .protocol {
      padding: 18px;
      border: 1px solid var(--line);
      border-left: 4px solid var(--baseline);
      background: rgba(12, 28, 40, .82);
      box-shadow: 0 18px 50px var(--shadow);
    }
    .protocol strong { display: block; margin-bottom: 8px; color: var(--baseline); }
    .protocol code { color: #d8e6e2; font: 12px/1.8 "SFMono-Regular", Consolas, monospace; }
    .stats {
      display: grid;
      grid-template-columns: repeat(6, minmax(120px, 1fr));
      gap: 1px;
      margin: 28px 0;
      background: var(--line);
      border: 1px solid var(--line);
    }
    .stat { padding: 18px; background: var(--panel); }
    .stat span { display: block; color: var(--muted); font-size: 12px; letter-spacing: .08em; text-transform: uppercase; }
    .stat b { display: block; margin-top: 7px; font: 700 30px/1 "Iowan Old Style", serif; }
    .stat small { display: block; margin-top: 6px; color: #9bb1b4; }
    .dashboard {
      border: 1px solid var(--line);
      background: rgba(12, 28, 40, .93);
      box-shadow: 0 24px 80px var(--shadow);
    }
    .controls {
      display: flex;
      flex-wrap: wrap;
      gap: 10px;
      align-items: center;
      padding: 16px;
      border-bottom: 1px solid var(--line);
    }
    .metric-tabs, .status-tabs, .mode-tabs { display: flex; flex-wrap: wrap; gap: 6px; }
    .controls button {
      min-height: 36px;
      padding: 7px 12px;
      color: #a9bec0;
      border: 1px solid #2b4b5c;
      background: #0b1a24;
      cursor: pointer;
      transition: .18s ease;
    }
    .controls button:hover { color: white; border-color: #658494; transform: translateY(-1px); }
    .controls button.active { color: var(--ink); background: var(--paper); border-color: var(--paper); }
    .controls .divider { width: 1px; height: 28px; margin: 0 3px; background: var(--line); }
    .status-toggle[data-status="successful"].active { background: var(--success); border-color: var(--success); }
    .status-toggle[data-status="failed"].active { background: var(--failure); border-color: var(--failure); }
    .status-toggle[data-status="audit"].active { background: var(--audit); border-color: var(--audit); }
    .range {
      margin-left: auto;
      display: grid;
      grid-template-columns: auto 72px auto 72px;
      gap: 7px;
      align-items: center;
      color: var(--muted);
      font-size: 12px;
    }
    .range input {
      width: 72px;
      padding: 7px;
      color: var(--paper);
      border: 1px solid var(--line);
      background: var(--ink);
    }
    .chart-wrap { position: relative; min-height: 570px; padding: 14px 14px 4px; overflow: hidden; }
    #chart { width: 100%; height: 550px; display: block; overflow: visible; }
    .axis { stroke: #385668; stroke-width: 1; }
    .grid { stroke: #1c3746; stroke-width: 1; stroke-dasharray: 3 7; }
    .tick { fill: #77949d; font: 11px "SFMono-Regular", Consolas, monospace; }
    .axis-title { fill: #b7c9c9; font: 700 12px "SFMono-Regular", Consolas, monospace; letter-spacing: .08em; }
    .promoted-line { fill: none; stroke: var(--success); stroke-width: 2.4; opacity: .7; }
    .all-line { fill: none; stroke: #537484; stroke-width: 1.1; stroke-dasharray: 3 5; opacity: .72; }
    .baseline-line { stroke: var(--baseline); stroke-width: 1.4; stroke-dasharray: 8 6; opacity: .75; }
    .point { cursor: crosshair; transition: filter .15s ease; }
    .point:hover { filter: drop-shadow(0 0 8px currentColor); }
    .timeline-label { fill: #6f8d96; font: 10px "SFMono-Regular", Consolas, monospace; }
    .timeline-axis { stroke: #294653; stroke-width: 1; }
    .tooltip {
      position: fixed;
      z-index: 20;
      width: min(380px, calc(100vw - 28px));
      pointer-events: none;
      opacity: 0;
      transform: translate(12px, 10px);
      padding: 15px;
      border: 1px solid #4c6d7b;
      background: rgba(4, 16, 24, .97);
      box-shadow: 0 14px 44px rgba(0,0,0,.52);
      transition: opacity .12s ease;
    }
    .tooltip.visible { opacity: 1; }
    .tooltip .tag { font: 700 11px "SFMono-Regular", Consolas, monospace; letter-spacing: .12em; text-transform: uppercase; }
    .tooltip h3 { margin: 7px 0 10px; font: 700 21px/1.15 "Iowan Old Style", serif; }
    .tooltip p { margin: 0 0 9px; color: #b6c9ca; font-size: 13px; line-height: 1.45; }
    .tooltip dl { display: grid; grid-template-columns: 1fr auto; gap: 5px 14px; margin: 0; font: 12px/1.45 "SFMono-Regular", Consolas, monospace; }
    .tooltip dt { color: #78959e; } .tooltip dd { margin: 0; color: #eaf2ef; text-align: right; }
    .chart-note {
      display: flex;
      justify-content: space-between;
      gap: 20px;
      padding: 12px 18px 17px;
      color: var(--muted);
      font-size: 12px;
      border-top: 1px solid rgba(35,65,81,.55);
    }
    .legend { display: flex; flex-wrap: wrap; gap: 16px; }
    .legend span::before { content: ""; display: inline-block; width: 9px; height: 9px; margin-right: 7px; }
    .legend .success::before { border-radius: 50%; background: var(--success); }
    .legend .failure::before { background: var(--failure); transform: rotate(45deg); }
    .legend .audit::before { background: var(--audit); clip-path: polygon(50% 0, 100% 100%, 0 100%); }
    .legend .baseline::before { background: var(--baseline); }
    .section-head {
      display: flex;
      justify-content: space-between;
      gap: 20px;
      align-items: end;
      margin: 56px 0 16px;
    }
    .section-head h2 { margin: 0; font: 700 35px/1 "Iowan Old Style", serif; }
    .section-head p { max-width: 700px; margin: 0; color: var(--muted); }
    .search {
      min-width: min(420px, 100%);
      padding: 11px 13px;
      color: var(--paper);
      border: 1px solid var(--line);
      background: var(--panel);
    }
    .ledger { display: grid; gap: 1px; background: var(--line); border: 1px solid var(--line); }
    .ledger-row {
      display: grid;
      grid-template-columns: 74px minmax(280px, 1.4fr) 100px repeat(4, minmax(95px, .55fr)) minmax(190px, .85fr);
      gap: 16px;
      align-items: center;
      min-height: 66px;
      padding: 12px 16px;
      background: var(--panel);
      transition: background .15s ease;
    }
    .ledger-row:hover, .ledger-row.focused { background: var(--panel-2); }
    .ledger-row.header {
      min-height: auto;
      color: #79969f;
      font: 10px "SFMono-Regular", Consolas, monospace;
      letter-spacing: .1em;
      text-transform: uppercase;
      position: sticky;
      top: 0;
      z-index: 3;
      background: #091721;
    }
    .version { font: 700 14px "SFMono-Regular", Consolas, monospace; }
    .method-name { font-weight: 650; }
    .method-desc { margin-top: 4px; color: #819ca3; font-size: 12px; line-height: 1.4; }
    .status-pill { display: inline-flex; align-items: center; gap: 7px; font: 700 10px "SFMono-Regular", Consolas, monospace; letter-spacing: .08em; text-transform: uppercase; }
    .status-pill::before { content:""; width: 8px; height: 8px; }
    .status-pill.successful { color: var(--success); } .status-pill.successful::before { border-radius: 50%; background: var(--success); }
    .status-pill.failed { color: var(--failure); } .status-pill.failed::before { background: var(--failure); transform: rotate(45deg); }
    .status-pill.audit { color: var(--audit); } .status-pill.audit::before { background: var(--audit); clip-path: polygon(50% 0, 100% 100%, 0 100%); }
    .status-pill.missing { color: var(--missing); } .status-pill.missing::before { background: var(--missing); }
    .status-pill.baseline { color: var(--baseline); } .status-pill.baseline::before { background: var(--baseline); }
    .metric-cell { font: 12px "SFMono-Regular", Consolas, monospace; color: #c5d5d3; }
    .metric-cell.missing { color: #526c78; }
    .time-cell { color: #9db4b7; font: 10px/1.55 "SFMono-Regular", Consolas, monospace; }
    .time-cell strong { color: #d7e5e2; font-size: 12px; }
    .caveats { display: grid; grid-template-columns: repeat(2, 1fr); gap: 1px; margin-top: 18px; background: var(--line); border: 1px solid var(--line); }
    .caveat { padding: 18px; background: var(--panel); color: #9eb3b5; line-height: 1.55; }
    footer { margin-top: 50px; padding-top: 18px; border-top: 1px solid var(--line); color: #6f8990; font: 11px/1.7 "SFMono-Regular", Consolas, monospace; }
    @media (max-width: 1000px) {
      header { grid-template-columns: 1fr; }
      .stats { grid-template-columns: repeat(2, 1fr); }
      .range { width: 100%; margin-left: 0; justify-content: start; }
      .ledger-row { grid-template-columns: 62px 1fr 100px; }
      .ledger-row > :nth-child(n+4) { display: none; }
      .caveats { grid-template-columns: 1fr; }
    }
    @media (max-width: 620px) {
      .shell { padding: 18px 12px 60px; }
      h1 { font-size: 48px; }
      .stats { grid-template-columns: 1fr 1fr; }
      .chart-wrap { padding-inline: 2px; }
      .section-head { align-items: stretch; flex-direction: column; }
      .search { min-width: 0; width: 100%; }
    }
  </style>
</head>
<body>
  <main class="shell">
    <header>
      <div>
        <div class="eyebrow">Research optimization ledger · V1–V${latestVersion}</div>
        <h1>Deagle<br>优化影响图谱</h1>
        <p class="lede">从最初克隆版基线开始，统一展示每个优化、原型和负结果对验证完成数、CPU、wall与内存的影响。没有725任务全量实验的版本仍保留在方法时间轴中，但不会被画成零开销。</p>
      </div>
      <aside class="protocol">
        <strong>可比全量实验口径</strong>
        <code>725 tasks · 48 workers<br>1 core/task · 4 GB/task<br>60 s/task · 1 development round</code>
      </aside>
    </header>

    <section class="stats" id="stats"></section>

    <section class="dashboard" aria-label="optimization impact chart">
      <div class="controls">
        <div class="metric-tabs" id="metricTabs"></div>
        <span class="divider"></span>
        <div class="mode-tabs" id="modeTabs"></div>
        <span class="divider"></span>
        <div class="status-tabs">
          <button class="status-toggle active" data-status="successful">成功</button>
          <button class="status-toggle active" data-status="failed">失败</button>
          <button class="status-toggle active" data-status="audit">审计</button>
          <button class="status-toggle active" data-status="missing">缺失记录</button>
        </div>
        <div class="range">
          <span>版本</span><input id="rangeMin" type="number" min="0" max="${latestVersion}" value="0">
          <span>至</span><input id="rangeMax" type="number" min="0" max="${latestVersion}" value="${latestVersion}">
        </div>
      </div>
      <div class="chart-wrap">
        <svg id="chart" role="img" aria-label="Deagle optimization line chart"></svg>
        <div class="tooltip" id="tooltip"></div>
      </div>
      <div class="chart-note">
        <div class="legend">
          <span class="baseline">基线</span><span class="success">成功/已接受</span>
          <span class="failure">失败/已拒绝</span><span class="audit">审计或门禁</span>
        </div>
        <div>上方为可比全量指标；下方窄轨道保留所有方法版本。</div>
      </div>
    </section>

    <div class="section-head">
      <div><div class="eyebrow">Method index</div><h2>全部版本明细</h2></div>
      <input class="search" id="search" type="search" placeholder="搜索版本、方法或结论…">
    </div>
    <section class="ledger" id="ledger"></section>

    <div class="section-head">
      <div><div class="eyebrow">Evidence boundary</div><h2>解释边界</h2></div>
      <p>这是一份描述性研究台账，不把单轮服务器波动解释成统计显著性，也不把内部操作数下降替代为真实时空优化。</p>
    </div>
    <section class="caveats" id="caveats"></section>

    <footer>
      数据源：/data3/sujie/experiments 的结论、笔记与summary快照。<br>
      生成文件：optimization-impact-data.json / optimization-impact-data.csv / deagle-optimization-impact.html
    </footer>
  </main>
  <script>
    const DATA = ${embedded};
    const rows = DATA.rows;
    const colors = {baseline:"#72d8ff", successful:"#56e39f", failed:"#ff647c", audit:"#f4bb55", missing:"#526c78"};
    const labels = {baseline:"基线", successful:"成功", failed:"失败", audit:"审计/门禁", missing:"记录缺失"};
    const metricDefs = {
      correct: {label:"正确验证数", unit:"项", field:"correct", better:"up"},
      cpu: {label:"CPU总时长", unit:"s", field:"cpu_s", better:"down"},
      wall: {label:"Wall总时长", unit:"s", field:"wall_s", better:"down"},
      memory: {label:"配对内存变化", unit:"%", field:"paired_memory_delta_pct", better:"down"},
      totalMemory: {label:"总内存开销", unit:"GB", field:"memory_sum_b", better:"down"},
      duration: {label:"研发与验收墙钟跨度", unit:"min", field:"duration_minutes", better:"down"}
    };
    const latestVersion = rows.at(-1).version;
    const state = {metric:"correct", mode:"absolute", statuses:new Set(["successful","failed","audit","missing"]), min:0, max:latestVersion, query:""};
    const svgNS = "http://www.w3.org/2000/svg";
    const q = (s) => document.querySelector(s);
    const el = (tag, attrs={}) => { const node=document.createElementNS(svgNS,tag); Object.entries(attrs).forEach(([k,v])=>node.setAttribute(k,v)); return node; };
    const fmt = (v, digits=2) => v == null || Number.isNaN(v) ? "—" : new Intl.NumberFormat("zh-CN",{maximumFractionDigits:digits}).format(v);
    const signed = (v, digits=2) => v == null ? "—" : (v>0?"+":"")+fmt(v,digits);
    const fmtTime = (iso) => iso ? new Intl.DateTimeFormat("zh-CN",{timeZone:"Asia/Shanghai",month:"2-digit",day:"2-digit",hour:"2-digit",minute:"2-digit",hour12:false}).format(new Date(iso)) : "—";
    const metricValue = (row) => {
      const m=row.metrics, def=metricDefs[state.metric];
      if(state.metric==="duration")
        return state.mode==="absolute" && row.timing.available
          ? row.timing.duration_minutes
          : null;
      if (state.mode==="absolute") {
        const raw=m[def.field];
        return state.metric==="totalMemory" && raw!=null ? raw/1e9 : raw;
      }
      if (state.mode==="baseline") {
        if(state.metric==="correct") return m.correct_vs_baseline;
        if(state.metric==="cpu") return m.cpu_vs_baseline_pct;
        if(state.metric==="wall") return m.wall_vs_baseline_pct;
        if(state.metric==="totalMemory") return m.memory_sum_vs_baseline_pct;
        return m.paired_memory_delta_pct;
      }
      if(state.metric==="correct") return m.correct_vs_previous_success;
      if(state.metric==="cpu") return m.cpu_vs_previous_success_pct;
      if(state.metric==="wall") return m.wall_vs_previous_success_pct;
      return null;
    };
    function metricUnit() {
      if(state.mode!=="absolute" && state.metric!=="correct") return "%";
      return metricDefs[state.metric].unit;
    }
    function statusShape(group,row,x,y,size=6) {
      const color=colors[row.status], common={class:"point",fill:color,stroke:"#07131d","stroke-width":"1.5","data-version":row.version,tabindex:"0"};
      let node;
      if(row.status==="failed") node=el("rect",{...common,x:x-size,y:y-size,width:size*2,height:size*2,transform:\`rotate(45 \${x} \${y})\`});
      else if(row.status==="audit") node=el("path",{...common,d:\`M \${x} \${y-size-1} L \${x+size+1} \${y+size} L \${x-size-1} \${y+size} Z\`});
      else if(row.status==="missing") node=el("path",{...common,fill:"none",stroke:color,"stroke-width":"2",d:\`M \${x-size} \${y-size} L \${x+size} \${y+size} M \${x+size} \${y-size} L \${x-size} \${y+size}\`});
      else if(row.status==="baseline") node=el("rect",{...common,x:x-size,y:y-size,width:size*2,height:size*2});
      else node=el("circle",{...common,cx:x,cy:y,r:size});
      node.addEventListener("mouseenter",(e)=>showTooltip(row,e));
      node.addEventListener("mousemove",moveTooltip);
      node.addEventListener("mouseleave",hideTooltip);
      node.addEventListener("focus",(e)=>showTooltip(row,e));
      node.addEventListener("blur",hideTooltip);
      node.addEventListener("click",()=>focusLedger(row.version));
      group.appendChild(node);
    }
    function showTooltip(row,event) {
      const v=metricValue(row), unit=metricUnit(), m=row.metrics;
      q("#tooltip").innerHTML=\`
        <div class="tag" style="color:\${colors[row.status]}">\${row.label} · \${labels[row.status]}</div>
        <h3>\${row.method}</h3>
        <p>\${row.description}</p>
        <dl>
          <dt>当前图指标</dt><dd>\${v==null?"无可比全量数据":fmt(v)} \${v==null?"":unit}</dd>
          <dt>正确验证</dt><dd>\${fmt(m.correct,0)}</dd>
          <dt>CPU / Wall</dt><dd>\${fmt(m.cpu_s)} / \${fmt(m.wall_s)} s</dd>
          <dt>725任务总内存</dt><dd>\${m.memory_sum_b==null?"—":fmt(m.memory_sum_b/1e9,3)+" GB"}</dd>
          <dt>优化开始</dt><dd>\${fmtTime(row.timing.start_iso)}</dd>
          <dt>优化结束</dt><dd>\${fmtTime(row.timing.end_iso)}</dd>
          <dt>研发与验收墙钟跨度</dt><dd>\${row.timing.available?fmt(row.timing.duration_minutes,2)+" min":row.timing.in_progress?"进行中":"不可确定"}</dd>
          <dt>相对最初基线</dt><dd>\${signed(m.correct_vs_baseline,0)} 项 · CPU \${signed(m.cpu_vs_baseline_pct)}%</dd>
          <dt>证据范围</dt><dd>\${row.scope==="exact725"?"exact725":"目标门禁/审计"}</dd>
        </dl>\`;
      q("#tooltip").classList.add("visible"); moveTooltip(event);
    }
    function moveTooltip(event) {
      if(!event.clientX) return;
      const tip=q("#tooltip"), pad=18, w=tip.offsetWidth||360, h=tip.offsetHeight||240;
      let x=event.clientX+14,y=event.clientY+12;
      if(x+w>innerWidth-pad)x=event.clientX-w-14;
      if(y+h>innerHeight-pad)y=event.clientY-h-12;
      tip.style.left=\`\${Math.max(pad,x)}px\`; tip.style.top=\`\${Math.max(pad,y)}px\`;
    }
    function hideTooltip(){q("#tooltip").classList.remove("visible");}
    function renderChart() {
      const svg=q("#chart"), W=Math.max(900,svg.clientWidth||1200), H=550;
      svg.setAttribute("viewBox",\`0 0 \${W} \${H}\`); svg.innerHTML="";
      const margin={l:76,r:26,t:28,b:105}, plot={x:margin.l,y:margin.t,w:W-margin.l-margin.r,h:H-margin.t-margin.b};
      const visible=rows.filter(r=>
        r.version>=state.min&&
        r.version<=state.max&&
        r.scope!=="wrapper_certificate_only"&&
        (r.status==="baseline"||state.statuses.has(r.status))
      );
      const points=visible.filter(r=>metricValue(r)!=null);
      let values=points.map(metricValue);
      if(!values.length) values=[0,1];
      let min=Math.min(...values),max=Math.max(...values);
      if(min===max){min-=1;max+=1;}
      const pad=(max-min)*.1; min-=pad;max+=pad;
      if(state.mode!=="absolute"){min=Math.min(min,0);max=Math.max(max,0);}
      const x=v=>plot.x+((v-state.min)/Math.max(1,state.max-state.min))*plot.w;
      const y=v=>plot.y+plot.h-((v-min)/(max-min))*plot.h;
      const grid=el("g");
      for(let i=0;i<=5;i++){const val=min+(max-min)*i/5, yy=y(val);grid.appendChild(el("line",{class:"grid",x1:plot.x,y1:yy,x2:plot.x+plot.w,y2:yy}));const t=el("text",{class:"tick",x:plot.x-11,y:yy+4,"text-anchor":"end"});t.textContent=fmt(val, state.metric==="correct"?0:2);grid.appendChild(t);}
      for(let i=0;i<=8;i++){const val=Math.round(state.min+(state.max-state.min)*i/8),xx=x(val);grid.appendChild(el("line",{class:"grid",x1:xx,y1:plot.y,x2:xx,y2:plot.y+plot.h}));const t=el("text",{class:"tick",x:xx,y:plot.y+plot.h+20,"text-anchor":"middle"});t.textContent=val===0?"Base":\`V\${val}\`;grid.appendChild(t);}
      svg.appendChild(grid);
      svg.appendChild(el("line",{class:"axis",x1:plot.x,y1:plot.y+plot.h,x2:plot.x+plot.w,y2:plot.y+plot.h}));
      svg.appendChild(el("line",{class:"axis",x1:plot.x,y1:plot.y,x2:plot.x,y2:plot.y+plot.h}));
      const title=el("text",{class:"axis-title",x:plot.x,y:14});title.textContent=\`\${metricDefs[state.metric].label} · \${state.mode==="absolute"?"绝对值":state.mode==="baseline"?"相对最初基线":"相对上一成功版"} (\${metricUnit()})\`;svg.appendChild(title);
      const baseline=rows[0], baseValue=metricValue(baseline);
      if(baseValue!=null&&baseValue>=min&&baseValue<=max) svg.appendChild(el("line",{class:"baseline-line",x1:plot.x,y1:y(baseValue),x2:plot.x+plot.w,y2:y(baseValue)}));
      const full=state.metric==="duration"
        ? points
        : points.filter(r=>r.scope==="exact725");
      const linePath=full.map((r,i)=>\`\${i?"L":"M"} \${x(r.version)} \${y(metricValue(r))}\`).join(" ");
      if(linePath)svg.appendChild(el("path",{class:"all-line",d:linePath}));
      const promoted=full.filter(r=>r.status==="successful"||r.status==="baseline");
      const promotedPath=promoted.map((r,i)=>\`\${i?"L":"M"} \${x(r.version)} \${y(metricValue(r))}\`).join(" ");
      if(promotedPath)svg.appendChild(el("path",{class:"promoted-line",d:promotedPath}));
      const pointGroup=el("g"); full.forEach(r=>statusShape(pointGroup,r,x(r.version),y(metricValue(r)),6)); svg.appendChild(pointGroup);
      const laneY=H-42;svg.appendChild(el("line",{class:"timeline-axis",x1:plot.x,y1:laneY,x2:plot.x+plot.w,y2:laneY}));
      const lane=el("g");visible.forEach(r=>statusShape(lane,r,x(r.version),laneY,r.status==="missing"?3:4));svg.appendChild(lane);
      const laneTitle=el("text",{class:"timeline-label",x:plot.x,y:H-17});laneTitle.textContent="全部方法版本（无全量数据的版本只出现在此轨道）";svg.appendChild(laneTitle);
    }
    function renderStats(){
      const exact=rows.filter(r=>r.scope==="exact725"), success=rows.filter(r=>r.status==="successful"), failed=rows.filter(r=>r.status==="failed"), timed=rows.filter(r=>r.timing.available), latest=exact.at(-1), base=rows[0];
      const cards=[
        ["记录版本",rows.length-1,\`V1–V\${latestVersion}\`],
        ["成功优化",success.length,"通过接受门禁"],
        ["失败优化",failed.length,"包含无全量负结果"],
        ["exact725点",exact.length,"含基线与失败全量"],
        ["当前最好覆盖",latest.metrics.correct,\`较基线 +\${latest.metrics.correct-base.metrics.correct}\`],
        ["时间可追溯",timed.length,\`共 \${rows.length-1} 个优化版本\`]
      ];
      q("#stats").innerHTML=cards.map(c=>\`<div class="stat"><span>\${c[0]}</span><b>\${c[1]}</b><small>\${c[2]}</small></div>\`).join("");
    }
    function renderControls(){
      q("#metricTabs").innerHTML=Object.entries(metricDefs).map(([k,v])=>\`<button data-metric="\${k}" class="\${k===state.metric?"active":""}">\${v.label}</button>\`).join("");
      q("#modeTabs").innerHTML=[["absolute","绝对值"],["baseline","相对基线"],["previous","相对上一成功版"]].map(([k,v])=>\`<button data-mode="\${k}" class="\${k===state.mode?"active":""}">\${v}</button>\`).join("");
      q("#metricTabs").onclick=e=>{const b=e.target.closest("button");if(!b)return;state.metric=b.dataset.metric;if(state.metric==="duration")state.mode="absolute";else if(state.metric==="memory"||state.metric==="totalMemory")state.mode=state.mode==="previous"?"absolute":state.mode;renderControls();renderChart();};
      q("#modeTabs").onclick=e=>{const b=e.target.closest("button");if(!b)return;if(state.metric==="duration")return;if(b.dataset.mode==="previous"&&(state.metric==="memory"||state.metric==="totalMemory"))return;state.mode=b.dataset.mode;renderControls();renderChart();};
    }
    function ledgerMetric(v,unit="",digits=2){return v==null?'<span class="metric-cell missing">无全量数据</span>':\`<span class="metric-cell">\${fmt(v,digits)}\${unit}</span>\`;}
    function renderLedger(){
      const query=state.query.toLowerCase();
      const filtered=rows.filter(r=>(r.label+" "+r.method+" "+r.description).toLowerCase().includes(query));
      q("#ledger").innerHTML=\`<div class="ledger-row header"><div>版本</div><div>方法 / 结论</div><div>状态</div><div>正确数</div><div>CPU</div><div>Wall</div><div>总内存</div><div>研发验收起止 / 墙钟跨度</div></div>\`+filtered.map(r=>\`<article class="ledger-row" id="row-\${r.version}">
        <div class="version">\${r.label}</div>
        <div><div class="method-name">\${r.method}</div><div class="method-desc">\${r.description}</div></div>
        <div><span class="status-pill \${r.status}">\${labels[r.status]}</span></div>
        <div>\${ledgerMetric(r.metrics.correct,"",0)}</div>
        <div>\${ledgerMetric(r.metrics.cpu_s," s")}</div>
        <div>\${ledgerMetric(r.metrics.wall_s," s")}</div>
        <div>\${ledgerMetric(r.metrics.memory_sum_b==null?null:r.metrics.memory_sum_b/1e9," GB",3)}</div>
        <div class="time-cell">\${r.timing.available?\`\${fmtTime(r.timing.start_iso)} → \${fmtTime(r.timing.end_iso)}<br><strong>\${fmt(r.timing.duration_minutes,2)} min</strong>\`:r.timing.in_progress?\`\${fmtTime(r.timing.start_iso)} → 进行中<br><strong>尚未结束</strong>\`:'<span class="metric-cell missing">时间不可确定</span>'}</div>
      </article>\`).join("");
    }
    function focusLedger(version){const row=q(\`#row-\${version}\`);if(!row)return;row.scrollIntoView({behavior:"smooth",block:"center"});row.classList.add("focused");setTimeout(()=>row.classList.remove("focused"),1800);}
    document.querySelectorAll(".status-toggle").forEach(button=>button.onclick=()=>{const s=button.dataset.status;if(state.statuses.has(s))state.statuses.delete(s);else state.statuses.add(s);button.classList.toggle("active",state.statuses.has(s));renderChart();});
    q("#rangeMin").onchange=e=>{state.min=Math.max(0,Math.min(Number(e.target.value),state.max));e.target.value=state.min;renderChart();};
    q("#rangeMax").onchange=e=>{state.max=Math.min(latestVersion,Math.max(Number(e.target.value),state.min));e.target.value=state.max;renderChart();};
    q("#search").oninput=e=>{state.query=e.target.value;renderLedger();};
    q("#caveats").innerHTML=DATA.caveats.map((c,i)=>\`<div class="caveat"><strong>0\${i+1}</strong><br>\${c}</div>\`).join("");
    renderStats();renderControls();renderLedger();renderChart();
    addEventListener("resize",()=>requestAnimationFrame(renderChart));
  </script>
</body>
</html>`;

// String.raw keeps the escapes needed to nest client-side template literals
// inside this generator. Remove only those two generator-level escapes in the
// final standalone document.
const finalHtml = html
  .replace(/\\`/g, "`")
  .replace(/\\\$\{/g, "${");
fs.writeFileSync(
  path.join(here, "deagle-optimization-impact.html"),
  finalHtml
);
console.log(
  JSON.stringify({
    output: path.join(here, "deagle-optimization-impact.html"),
    bytes: Buffer.byteLength(finalHtml),
    embedded_rows: data.rows.length,
  })
);
