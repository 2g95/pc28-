
/* ============ 常量 ============ */
var PERIOD = 210;
var LOG_KEY = 'pc28_formula_v1';
var W = 30;
var SUM_N = 4;
var FM = ['大单','小单','大双','小双'];
var TYPE_NAME = ['单门','组合','杀组','三门','2期计划','3期计划'];
var SUM_RANGE = { 0:[15,17,19,21,23,25,27], 1:[1,3,5,7,9,11,13], 2:[14,16,18,20,22,24,26], 3:[0,2,4,6,8,10,12] };
/* 理论真值：三角分布 */
var TH_FORMS = (function(){
  var c=new Array(28).fill(0);
  for(var a=0;a<=9;a++) for(var b=0;b<=9;b++) for(var c2=0;c2<=9;c2++) c[a+b+c2]++;
  var p=c.map(function(x){return x/1000;});
  var f=[0,0,0,0];
  for(var k=0;k<28;k++){ var big=k>=14?1:0, odd=k&1; f[(big?0:1)+(odd?0:2)]+=p[k]; }
  return f;
})();

/* ============ 工具 ============ */
function $(id){ return document.getElementById(id); }
function pad(n,w){ var s=''+n; while(s.length<w) s='0'+s; return s; }
function mmss(s){ if(s<0) s=0; var m=Math.floor(s/60),x=Math.floor(s%60); return pad(m,2)+':'+pad(x,2); }
function fmtBJ(ts){ var d=new Date((ts+8*3600)*1000); return pad(d.getUTCMonth()+1,2)+'-'+pad(d.getUTCDate(),2)+' '+pad(d.getUTCHours(),2)+':'+pad(d.getUTCMinutes(),2); }
function lsGet(k){ try{ return localStorage.getItem(k); }catch(e){ return null; } }
function lsSet(k,v){ try{ localStorage.setItem(k,v); }catch(e){} }
function fmtInt(s){ var n=parseInt(s,10); return isNaN(n)?0:n; }
function dispPad(f){ return pad(f.fid,5); }
function sumCls(s){ return s>=14?'big':'small'; }
function formCls(f){ return 'hf f'+f; }

/* ============ 数据模型 ============ */
var APP = { recs:null, log:[], cdTimer:null, lastFetch:0, src:'—',
  list:null, smart:2, rankTab:2, liveTab:2, shown:{}, userPicked:false, cur:null, smartF:null, previewFid:null, seedBase:0, planFormula:null };

function recFrom(a,b,c,issue,ts){
  var sum=a+b+c, big=sum>=14?1:0, odd=sum&1;
  return { a:a,b:b,c:c,sum:sum,big:big,odd:odd,form:(big?0:1)+(odd?0:2),issue:String(issue),ts:ts||0 };
}
function buildRecs(rows){
  var recs=[];
  for(var i=0;i<rows.length;i++){
    var r=rows[i];
    var a,b,c;
    if(r.a!=null && r.b!=null && r.c!=null){ a=+r.a; b=+r.b; c=+r.c; }
    else { var num=String(r.num!=null?r.num:''); a=+num[0]; b=+num[1]; c=+num[2]; }
    if(isNaN(a)||isNaN(b)||isNaN(c)) continue;
    recs.push(recFrom(a,b,c,r.issue,r.ts));
  }
  recs.sort(function(x,y){ return fmtInt(y.issue)-fmtInt(x.issue); });
  if(recs.length && recs[0].ts){
    for(var j=1;j<recs.length;j++){
      var dI=fmtInt(recs[j-1].issue)-fmtInt(recs[j].issue);
      recs[j].ts = recs[j-1].ts - dI*PERIOD;
    }
  }
  return recs;
}

/* ============ 公式引擎 ============ */
/* 规则：每个规则 = (rule, w 窗口, off 偏移) → 预测
   type 0=单门 1=组合 2=杀组 3=三门 */
function h32(a,b,c){
  var h=2166136261 ^ (a|0);
  h=Math.imul(h^(b|0),16777619);
  h=Math.imul(h^(c|0),2246822519);
  h^=h>>>13; h=Math.imul(h,3266489917); h^=h>>>16;
  return h>>>0;
}
function feats(recs, p, w){
  var hist=recs.slice(p+1), m=Math.min(w,hist.length);
  var fc=[0,0,0,0], sum=0, big=0, odd=0;
  for(var i=0;i<m;i++){ fc[hist[i].form]++; sum+=hist[i].sum; big+=hist[i].big; odd+=hist[i].odd; }
  var last=hist[0]||recs[p];
  var issue=fmtInt(recs[p].issue);
  return { fc:fc, m:m, sum:sum, big:big, odd:odd, last:last, issue:issue };
}
function argmin(a){ var r=0; for(var i=1;i<a.length;i++) if(a[i]<a[r]) r=i; return r; }
function argmax(a){ var r=0; for(var i=1;i<a.length;i++) if(a[i]>a[r]) r=i; return r; }
function aliveForms(kill){ var f=[]; for(var j=0;j<4;j++) if(j!==kill) f.push(j); return f; }
function killPred(kill){ return { type:2, kill:kill, forms:aliveForms(kill), label:'杀'+FM[kill] }; }
function formsPred(forms){ return { type:1, forms:forms, label:FM[forms[0]]+'·'+FM[forms[1]] }; }
function gatePred(gateName, gate, code){
  var forms = gate===0 ? (code?[0,2]:[1,3]) : (code?[0,1]:[2,3]);
  return { type:0, gate:gate, gateName:gateName, forms:forms, label:gateName };
}

/* 规则评估：返回预测对象 */
function evalRule(rule, w, off, recs, p){
  var f=feats(recs, p, w);
  if(!f.m) return null;
  switch(rule){
    case 0: return killPred(argmin(f.fc));                       // 杀最低频
    case 1: { var c=f.fc.slice(), k=argmin(c); c[k]=99; return killPred(argmin(c)); } // 杀次低频
    case 2: return killPred(argmax(f.fc));                       // 杀最高频
    case 3: return gatePred(f.big*2>=f.m?'大':'小', 0, f.big*2>=f.m?1:0); // 大小跟随
    case 4: return gatePred(f.big*2>=f.m?'小':'大', 0, f.big*2>=f.m?0:1); // 大小反转
    case 5: return gatePred(f.odd*2>=f.m?'单':'双', 1, f.odd*2>=f.m?1:0); // 单双跟随
    case 6: return gatePred(f.odd*2>=f.m?'双':'单', 1, f.odd*2>=f.m?0:1); // 单双反转
    case 7: { var o=[0,1,2,3].sort(function(a,b){return f.fc[b]-f.fc[a]||a-b;}); return formsPred([o[0],o[1]].sort(function(a,b){return a-b;})); } // top2
    case 8: { var o2=[0,1,2,3].sort(function(a,b){return f.fc[a]-f.fc[b]||a-b;}); return formsPred([o2[0],o2[1]].sort(function(a,b){return a-b;})); } // 低频2
    case 9: { var avg=f.sum/f.m; return gatePred(avg>=13.5?'小':'大', 0, avg>=13.5?0:1); } // 均值回归
    case 10: { var k=(f.issue%((off%4)+1))%4; return killPred((k+f.last.form)%4); } // 期号杀
    case 11: { var k2=argmin(f.fc); return { type:3, kill:k2, forms:aliveForms(k2), label:aliveForms(k2).map(function(x){return FM[x];}).join('·') }; } // 三门
    case 12: { var k3=argmax(f.fc); var af=aliveForms(k3); return formsPred([af[0],af[1]].sort(function(a,b){return a-b;})); } // 杀最高频取2
    case 13: { var k4=(f.last.form+(off%3)+1)%4; return killPred(k4); } // 上期顺延杀
  }
  return null;
}
/* 规则 → 类型映射 */
var RULE_TYPE = [2,2,2,0,0,0,0,1,1,0,2,3,1,2];
var RULE_NAME = ['杀最低频','杀次低频','杀最高频','大小跟随','大小反转','单双跟随','单双反转','top2形态','低频2形态','均值回归','期号杀','三门杀','杀热取2','顺延杀'];

function hitOf(pred, rec){
  if(pred.type===0) return (pred.gate===0 ? (rec.big===pred.code) : (rec.odd===pred.code)) ? 1 : 0;
  if(pred.forms) return pred.forms.indexOf(rec.form)>=0 ? 1 : 0;
  return 0;
}
/* 预测对象归一：补充 code */
function normPred(pred){
  if(pred.type===0 && pred.code===undefined){
    pred.code = (pred.gate===0 ? (pred.label==='大'?1:0) : (pred.label==='单'?1:0));
  }
  return pred;
}

/* 生成公式池 */
function buildPool(recs, W){
  var pool=[], fid=0;
  var wins=[8,15,25,40,70,120,200,Math.min(400,recs.length)];
  for(var rule=0; rule<RULE_TYPE.length; rule++){
    var type=RULE_TYPE[rule];
    for(var wi=0; wi<wins.length; wi++){
      for(var off=0; off<3; off++){
        var f={ fid:fid++, rule:rule, type:type, w:wins[wi], off:off };
        f.hit=0; f.maxMiss=0; f.detail=new Uint8Array(W);
        var run=0;
        for(var p=W-1; p>=0; p--){
          var pred=evalRule(f.rule, f.w, f.off, recs, p);
          if(!pred){ continue; }
          pred=normPred(pred);
          var ok=hitOf(pred, recs[p]);
          f.detail[p]=ok;
          if(ok){ f.hit++; run=0; } else { run++; if(run>f.maxMiss) f.maxMiss=run; }
        }
        pool.push(f);
      }
    }
  }
  return pool;
}
/* 按类型过滤 + 命中排序 */
function sorted(type){
  return APP.list.filter(function(f){ return f.type===type; })
    .sort(function(a,b){ return b.hit-a.hit || a.fid-b.fid; });
}
function curForType(type){
  var arr=sorted(type);
  return arr.length?arr[0]:null;
}
function findFormula(fid){
  for(var i=0;i<APP.list.length;i++) if(APP.list[i].fid===fid) return APP.list[i];
  return null;
}
function fLabel(f){ return RULE_NAME[f.rule] + ' · 窗'+f.w; }

/* 预测下一期（用最新历史） */
function predictNext(f){
  var nextIssue = fmtInt(APP.recs[0].issue)+1;
  var p = evalRule(f.rule, f.w, f.off, APP.recs, 0);
  if(!p) return null;
  p = normPred(p);
  p.sums = pickSums(p);
  return p;
}
/* 和值推荐 */
function pickSums(pred){
  var cand=[], forms = pred.forms || aliveForms(pred.kill!==undefined?pred.kill:0);
  for(var i=0;i<forms.length;i++){
    var rg=SUM_RANGE[forms[i]];
    for(var q=0;q<rg.length;q++) if(cand.indexOf(rg[q])<0) cand.push(rg[q]);
  }
  /* 近期热门排序：近 500 期高频优先 */
  var win=Math.min(500, APP.recs.length), freq=[];
  for(var k=0;k<28;k++) freq[k]=0;
  for(var j=0;j<win;j++) freq[APP.recs[j].sum]++;
  var scored=cand.map(function(s){ return { s:s, sc:freq[s] + s*1e-9 }; });
  scored.sort(function(a,b){ return b.sc-a.sc; });
  var out=[];
  for(var i=0;i<scored.length && out.length<SUM_N;i++) out.push(scored[i].s);
  return out.sort(function(a,b){ return a-b; });
}

/* ============ 渲染 ============ */
function renderDraw(){
  var r=APP.recs[0];
  $('drawBalls').innerHTML=[r.a,r.b,r.c].map(function(x,i){ return '<div class="ball'+(i===1?' b2':i===2?' b3':'')+'">'+x+'</div>'; }).join('');
  $('drawIssue').textContent='第 '+r.issue+' 期';
  $('drawTime').textContent=r.ts?('开奖 '+fmtBJ(r.ts)+'（北京时间）'):'—';
  $('drawSum').textContent=r.sum;
  $('drawTags').innerHTML='<span class="tagx '+(r.big?'t-big':'t-small')+'">'+(r.big?'大':'小')+'</span><span class="tagx '+(r.odd?'t-odd':'t-even')+'">'+(r.odd?'单':'双')+'</span><span class="tagx t-form">'+FM[r.form]+'</span>';
  $('drawBadge').textContent='近 '+APP.recs.length+' 期 · '+APP.src;
}
function renderSmart(){
  if(!APP.list) return;
  var type=APP.smart;
  if(type===4 || type===5){ renderPlan(type); return; }
  var f;
  if(APP.userPicked && APP.cur && APP.cur.type===type) f=APP.cur;
  else f=curForType(type);
  if(!f) return;
  APP.smartF=f;
  var nextIssue=fmtInt(APP.recs[0].issue)+1;
  var p=predictNext(f);
  $('smNo').textContent=dispPad(f);
  $('smTy').textContent=TYPE_NAME[f.type]+' · '+fLabel(f);
  $('smHit').textContent=f.hit+'/'+W;
  $('smPct').textContent=Math.round(f.hit/W*100)+'%';
  $('smNext').textContent=nextIssue;
  $('smVal').className='pv'+(f.type===2?' kill':'');
  if(p){
    if(f.type===3){
      var t3=aliveForms(p.kill);
      $('smVal').innerHTML=t3.map(function(x){ return '<span style="color:var(--c'+x+')">'+FM[x]+'</span>'; }).join(' · ');
      $('smPl').textContent='三门预测 · 三形态直给';
    } else {
      $('smVal').textContent=p.label;
      $('smPl').textContent=(f.type===0?'单门预测':(f.type===1?'双形态预测':'杀组预测'))+' · '+fLabel(f);
    }
    $('smSums').innerHTML=(p.sums||[]).map(function(v){ return '<div class="sum '+(v>=14?'s-big':'')+'"><span class="sv">'+v+'</span><span class="st">'+(v>=14?'大':'小')+(v%2?'单':'双')+'</span></div>'; }).join('');
  } else {
    $('smVal').textContent='—';
    $('smSums').innerHTML='';
  }
  $('smFp').textContent='#'+pad(f.rule,2)+'-'+pad(f.off,1);
  $('smMaxMiss').textContent='连挂 '+f.maxMiss+' 期';
  $('smBadge').textContent=W+' 期 · '+APP.recs[Math.min(W-1,APP.recs.length-1)].issue+'~'+APP.recs[0].issue;
  $('histBadge').textContent='近 '+W+' 期 · 公式 '+dispPad(f);
  var theo=TH_FORMS;
  if(f.type===2){
    var kill=p?p.kill:0;
    $('truth').innerHTML='『杀组』理论命中率 <b>'+(100-theo[kill]*100).toFixed(1)+'%</b>（杀'+FM[kill]+'，其理论概率 '+(theo[kill]*100).toFixed(1)+'%）。杀组是唯一真实边缘——但命中率高≠赚钱：每项公平赔率 3.90，平台压价即负期望。回测 '+f.hit+'/'+W+' 是样本值，长期收敛到理论。';
  } else if(f.type===0){
    $('truth').innerHTML='『单门』大小/单双理论各 <b>50%</b>，无边缘。此公式是趋势/回归类规则，长期收敛到 50%，回测 '+f.hit+'/'+W+' 是样本波动。';
  } else if(f.type===1){
    $('truth').innerHTML='『组合 top2』理论命中率 <b>53.8%</b>（押小单+大双）。三角分布真实边缘 3.8pp。回测 '+f.hit+'/'+W+'。';
  } else {
    $('truth').innerHTML='『三门』= 杀组押 3 形态，理论命中率 <b>76.9%</b>。三形态直给，不含和值匹配。';
  }
  renderHist(f);
  $('useNo').textContent=dispPad(f);
  $('useTy').textContent=TYPE_NAME[f.type];
  $('useHit').textContent=f.hit+'/'+W;
  $('useBadge').textContent=APP.userPicked?'手动锁定':'自适应';
  $('cancelPickBtn').classList.toggle('on',!!APP.userPicked);
}
function planStage(N, type){
  var kills=APP.log.filter(function(e){ return e.ty===type && e.state==='done'; })
    .sort(function(a,b){ return fmtInt(b.issue)-fmtInt(a.issue); });
  var miss=0;
  for(var i=0;i<kills.length;i++){ if(kills[i].hit) break; miss++; }
  return Math.min(miss+1, N);
}
function renderPlan(type){
  var N = (type===4)?2:3;
  var stage = planStage(N, type);
  var f = APP.planFormula || curForType(0);
  var p = f ? predictNext(f) : null;
  var label = p ? p.label : '大';
  var forms = p ? p.forms : [0,2];
  var nextIssue=fmtInt(APP.recs[0].issue)+1;
  var bet = 1 << (stage-1);
  $('smNo').textContent = 'P'+pad(type,2);
  $('smTy').textContent = TYPE_NAME[type]+' · 单门';
  $('smHit').textContent = f ? (f.hit+'/'+W) : '';
  $('smPct').textContent = f ? Math.round(f.hit/W*100)+'%' : '';
  $('smNext').textContent = nextIssue;
  $('smVal').className='pv';
  $('smVal').textContent = label;
  $('smPl').textContent = N+'期单门计划 · 第'+stage+'期 · 押'+bet+'倍';
  var pred={ forms:forms };
  var sums=pickSums(pred);
  $('smSums').innerHTML=sums.map(function(v){ return '<div class="sum '+(v>=14?'s-big':'')+'"><span class="sv">'+v+'</span><span class="st">'+(v>=14?'大':'小')+(v%2?'单':'双')+'</span></div>'; }).join('');
  $('smFp').textContent='倍投';
  $('smMaxMiss').textContent='连挂 '+(stage-1)+' 期';
  $('smBadge').textContent=N+'期单门倍投';
  $('histBadge').textContent='计划 · 单门 50%';
  $('truth').innerHTML='『'+N+'期单门计划』= 单门倍投追号（本期押 <b>'+label+'</b>）。当前第 <b>'+stage+'</b> 期（连续挂 '+(stage-1)+' 期），本期押 <b>'+bet+'</b> 倍。第1期中→直接更新下一期重来；没中→下一期翻倍。单门理论 50%，<b>倍投不改变负期望</b>。';
  renderPlanHist(f, N);
  $('useNo').textContent='P'+pad(type,2);
  $('useTy').textContent=TYPE_NAME[type]+' · 单门';
  $('useHit').textContent='';
  $('useBadge').textContent='计划';
  $('cancelPickBtn').classList.toggle('on',false);
}
function buildPlanCycles(records, N, maxCycles){
  var cycles=[], i=0;
  while(i<records.length && cycles.length<(maxCycles||20)){
    var r0=records[i];
    var startIssue=r0.issue, endIssue=r0.issue, hitStage=0, label=r0.label, marks='';
    for(var s=0;s<N && i<records.length;s++){
      var r=records[i];
      endIssue=r.issue;
      var done=(r.state==='done');
      if(done){ marks += (r.hit?'✓':'✗'); } else { marks += '⏳'; }
      i++;
      if(done && r.hit){ hitStage=s+1; break; }
      if(!done) break;
    }
    var rng=(startIssue===endIssue)?startIssue.slice(-5):(startIssue.slice(-5)+'-'+endIssue.slice(-5));
    cycles.push({ range:rng, stage:hitStage, hit:hitStage>0, label:label, marks:marks, N:N });
  }
  return cycles;
}
function renderPlanHist(f, N){
  var records=[];
  var lim=Math.min(60, APP.recs.length);
  for(var i=0;i<lim;i++){
    var rec=APP.recs[i];
    var pred=evalRule(f.rule, f.w, f.off, APP.recs, i);
    if(!pred) continue;
    pred=normPred(pred);
    records.push({ issue:rec.issue, label:pred.label, hit:hitOf(pred,rec), state:'done' });
  }
  var cycles=buildPlanCycles(records, N, 20);
  var html='';
  for(var c=0;c<cycles.length;c++){
    var cy=cycles[c];
    var st=cy.hit?('第'+cy.stage+'期中'):(N+'期全挂');
    html+='<div class="hrow'+(cy.hit?'':' miss')+'"><span class="hi">'+cy.range+'</span><span class="hn">'+cy.marks+'</span><span class="hs">'+cy.label+'</span><span class="hf">'+N+'期</span><span class="hp">'+st+'</span><span class="hk"></span><span class="hm">'+(cy.hit?'☑️':'❌')+'</span></div>';
  }
  $('hist').innerHTML=html||'<div style="padding:16px;text-align:center;color:var(--text-3);font-size:11px">暂无数据</div>';
}
function renderHist(f){
  if(!f) f=APP.smartF;
  if(!f) return;
  var html='';
  for(var i=0;i<W;i++){
    var rec=APP.recs[i];
    var pred=evalRule(f.rule, f.w, f.off, APP.recs, i);
    if(!pred){ continue; }
    pred=normPred(pred);
    var fh=hitOf(pred, rec);
    var sums=(pred.type===0)?[]:pickSumsAt(pred, i);
    var sh = sums.length ? (sums.indexOf(rec.sum)>=0 ? 1 : 0) : 0;
    var mark=(fh && sh)?'☑️🐔':(fh?'☑️':'❌');
    html+='<div class="hrow'+(fh?'':' miss')+'"><span class="hi">'+rec.issue.slice(-5)+'</span><span class="hn">'+rec.a+'+'+rec.b+'+'+rec.c+'</span><span class="hs '+sumCls(rec.sum)+'">'+rec.sum+(sh?'🐔':'')+'</span><span class="'+formCls(rec.form)+'">'+FM[rec.form]+'</span><span class="hp">'+pred.label+'</span><span class="hk">'+sums.join('·')+'</span><span class="hm">'+mark+'</span></div>';
  }
  $('hist').innerHTML=html;
}
function pickSumsAt(pred, p){
  var cand=[], forms = pred.forms || aliveForms(pred.kill!==undefined?pred.kill:0);
  for(var i=0;i<forms.length;i++){
    var rg=SUM_RANGE[forms[i]];
    for(var q=0;q<rg.length;q++) if(cand.indexOf(rg[q])<0) cand.push(rg[q]);
  }
  var win=Math.min(500, APP.recs.length-p-1), freq=[];
  for(var k=0;k<28;k++) freq[k]=0;
  for(var j=p+1;j<Math.min(p+1+win,APP.recs.length);j++) freq[APP.recs[j].sum]++;
  var scored=cand.map(function(s){ return { s:s, sc:freq[s] + s*1e-9 }; });
  scored.sort(function(a,b){ return b.sc-a.sc; });
  var out=[];
  for(var i=0;i<scored.length && out.length<SUM_N;i++) out.push(scored[i].s);
  return out.sort(function(a,b){ return a-b; });
}
function renderRank(){
  if(!APP.list) return;
  var t=APP.rankTab;
  var title=['单门 · 命中排行','组合 · 命中排行','杀组 · 命中排行','三门 · 三形态直给','2期计划 · 公式','3期计划 · 公式'][t];
  $('rankTitle').textContent=title;
  var arr=(t===4||t===5)?sorted(0):sorted(t);
  var lim=APP.shown[t]||20;
  var show=arr.slice(0,lim);
  $('rankBadge').textContent='前 '+show.length;
  $('rankStat').textContent=arr.length+' 条';
  var html='';
  for(var i=0;i<show.length;i++){
    var f=show[i];
    var rate=f.hit/W;
    var cls=rate>=0.80?'r30':rate>=0.65?'r29':rate>=0.55?'r28':'rx';
    html+='<div class="fbox'+(APP.smartF&&APP.smartF.fid===f.fid?' on':'')+'" onclick="previewFormula('+f.fid+')"><div class="no">'+dispPad(f)+'</div><div class="rt '+cls+'">'+f.hit+'/'+W+'</div></div>';
  }
  $('rankGrid').innerHTML=html;
  $('rankMore').style.display=(arr.length<=lim)?'none':'block';
  $('rankMore').textContent='展开更多公式（已显示 '+show.length+'/'+arr.length+'）';
  var f2=APP.smartF||APP.cur;
  if(f2){
    $('useNo').textContent=dispPad(f2);
    $('useTy').textContent=TYPE_NAME[f2.type]+' · '+fLabel(f2);
    $('useHit').textContent=f2.hit+'/'+W;
    $('useBadge').textContent=APP.userPicked?'手动锁定':'自适应';
    $('cancelPickBtn').classList.toggle('on',!!APP.userPicked);
  }
}
function renderLog(){
  var t=APP.liveTab;
  var names=['单门','组合','杀组','三门','2期计划','3期计划'];
  var theory=[50.0, 53.8, 76.9, 76.9, 50.0, 50.0];
  var list=APP.log.filter(function(e){ return e.ty===t; }).sort(function(a,b){ return fmtInt(b.issue)-fmtInt(a.issue); });
  var done=list.filter(function(e){ return e.state==='done'; });
  if(done.length){
    var h=done.filter(function(e){ return e.hit; }).length, rate=h/done.length*100;
    $('liveStat').innerHTML=names[t]+'已开奖 <b>'+done.length+'</b> 期 · 命中 <b>'+h+'</b> 期 · 命中率 <b>'+rate.toFixed(1)+'%</b><br><span style="font-size:9px;color:var(--text-3)">理论 '+theory[t].toFixed(1)+'% · 偏离 '+(rate-theory[t]).toFixed(1)+'pp</span>';
  } else {
    $('liveStat').innerHTML=names[t]+'等待首期开奖…<br><span style="font-size:9px;color:var(--text-3)">理论 '+theory[t].toFixed(1)+'%</span>';
  }
  $('liveBadge').textContent=done.length?(names[t]+' · 已开奖 '+done.length+' 期'):(names[t]+' · 等待首期');
  var html='';
  if(t===4 || t===5){
    var N=(t===4)?2:3;
    var cycles=buildPlanCycles(list, N, 30);
    for(var c=0;c<cycles.length;c++){
      var cy=cycles[c];
      var mark=cy.hit?'☑️':'❌';
      var st=cy.hit?('第'+cy.stage+'期中'):(N+'期全挂');
      html+='<div class="lrow"><span class="i">'+cy.range+'</span><span class="p">'+cy.label+' · '+cy.marks+'</span><span class="a">'+st+'</span><span class="m">'+mark+'</span></div>';
    }
  } else {
    var all=list.slice(0,30);
    for(var i=0;i<all.length;i++){
      var e=all[i], mark=e.state==='done'?(e.hit&&e.sHit?'☑️🐔':(e.hit?'☑️':'❌')):(e.state==='skip'?'—':'⏳');
      html+='<div class="lrow"><span class="i">'+e.issue.slice(-5)+'</span><span class="p">'+e.name+' · '+e.label+'</span><span class="a">'+(e.actual!==undefined?FM[e.actual]:'—')+'</span><span class="m">'+mark+'</span></div>';
    }
  }
  $('liveRows').innerHTML=html||'<div style="padding:16px;text-align:center;color:var(--text-3);font-size:11px">暂无记录</div>';
}
function setLiveTab(t){
  APP.liveTab=t;
  var bs=$('liveTabs').children;
  for(var i=0;i<bs.length;i++){ var lt=parseInt(bs[i].getAttribute('data-lt'),10); bs[i].classList.toggle('on',lt===t); }
  renderLog();
}

/* ============ 交互 ============ */
function go(i){
  var ps=['p-home','p-rank'];
  for(var k=0;k<2;k++){ $(ps[k]).classList.toggle('active',k===i); $('tb'+k).classList.toggle('on',k===i); }
  window.scrollTo(0,0);
  if(i===1) renderRank();
}
function setSmart(m){
  APP.smart=m;
  for(var i=0;i<6;i++){ var b=$('sm'+i); if(b) b.classList.toggle('on',i===m); }
  renderSmart(); renderLog();
}
function setRankTab(t){
  APP.rankTab=t;
  var bs=$('rankTabs').children;
  for(var i=0;i<bs.length;i++){ var rk=parseInt(bs[i].getAttribute('data-rk'),10); bs[i].classList.toggle('on',rk===t); }
  renderRank();
}
function moreRank(){
  var t=APP.rankTab;
  APP.shown[t]=(APP.shown[t]||20)+60;
  renderRank();
}
function setSumN(n){ SUM_N=(n===6?6:4); $('sn4').classList.toggle('on',n===4); $('sn6').classList.toggle('on',n===6); renderSmart(); }
function previewFormula(fid){
  var f=findFormula(fid);
  if(!f) return;
  APP.previewFid=fid;
  var nextIssue=fmtInt(APP.recs[0].issue)+1;
  var p=predictNext(f);
  $('pvNo').textContent=dispPad(f);
  $('pvTy').textContent=TYPE_NAME[f.type]+' · '+fLabel(f);
  $('pvHit').textContent=f.hit+'/'+W+'（'+Math.round(f.hit/W*100)+'%）';
  $('pvIssue').textContent=nextIssue;
  var body='';
  if(p){
    body+='<div class="pv-row"><span class="pv-k">预测</span><span class="pv-v'+(f.type===2?' kill':'')+'">'+p.label+'</span></div>';
    body+='<div class="pv-row"><span class="pv-k">覆盖形态</span><span class="pv-v">'+(p.forms||[]).map(function(x){return FM[x];}).join(' · ')+'</span></div>';
    body+='<div class="pv-row"><span class="pv-k">推荐和值</span><span class="pv-v sum">'+(p.sums||[]).join(' · ')+'</span></div>';
  } else {
    body='<div class="pv-row"><span class="pv-v">无法生成预测</span></div>';
  }
  var det=f.detail, tail=[];
  if(det) for(var i=0;i<Math.min(10,W);i++) tail.push(det[i]?'✓':'✗');
  if(tail.length) body+='<div class="pv-row"><span class="pv-k">近10期</span><span class="pv-v st">'+tail.join('')+'</span></div>';
  body+='<div class="pv-row"><span class="pv-k">最大连挂</span><span class="pv-v">'+f.maxMiss+' 期</span></div>';
  $('pvBody').innerHTML=body;
  $('pvBox').classList.add('show');
}
function cancelPreview(){ $('pvBox').classList.remove('show'); APP.previewFid=null; }
function applyPreview(){
  if(APP.previewFid==null) return;
  useFormula(APP.previewFid);
  cancelPreview();
}
function useFormula(fid){
  var f=findFormula(fid);
  if(!f) return;
  APP.userPicked=true;
  APP.cur=f;
  if(APP.rankTab===4 || APP.rankTab===5){
    APP.planFormula=f;
    APP.smart=APP.rankTab;
  } else {
    APP.planFormula=null;
    APP.smart=f.type;
  }
  for(var i=0;i<6;i++){ var b=$('sm'+i); if(b) b.classList.toggle('on',i===APP.smart); }
  renderSmart(); renderRank(); renderLog();
  go(0);
}
function cancelPick(){
  APP.userPicked=false;
  APP.cur=null;
  APP.planFormula=null;
  renderSmart(); renderRank();
}
function clearLog(){
  var btn=$('clrBtn');
  if(!APP._arm){ APP._arm=1; btn.textContent='再点一次确认清空'; btn.classList.add('armed'); setTimeout(function(){ APP._arm=0; btn.textContent='清空记录'; btn.classList.remove('armed'); },3000); return; }
  APP._arm=0; btn.textContent='清空记录'; btn.classList.remove('armed');
  APP.log=[]; try{ localStorage.removeItem(LOG_KEY); }catch(e){}
  renderLog();
}

/* ============ 实战记录 ============ */
function loadLog(){ try{ var raw=lsGet(LOG_KEY); if(!raw) return []; var a=JSON.parse(raw); return Array.isArray(a)?a:[]; }catch(e){ return []; } }
function saveLog(){ try{ lsSet(LOG_KEY, JSON.stringify(APP.log.slice(-300))); }catch(e){} }
function syncLog(){
  if(!APP.recs||!APP.recs.length) return;
  var idx={}; for(var i=0;i<APP.recs.length;i++) idx[APP.recs[i].issue]=i;
  for(var k=0;k<APP.log.length;k++){
    var e=APP.log[k];
    if(e.state==='pending' && idx[e.issue]!==undefined){ var r=APP.recs[idx[e.issue]]; e.actual=r.form; e.hit=(e.forms.indexOf(r.form)>=0)?1:0; e.sHit=(e.sums&&e.sums.length)?(e.sums.indexOf(r.sum)>=0?1:0):0; e.state='done'; }
    if(e.state==='pending' && fmtInt(e.issue)<fmtInt(APP.recs[0].issue)) e.state='skip';
  }
  var nextIssue=String(fmtInt(APP.recs[0].issue)+1);
  var names=['单门','组合','杀组','三门','2期计划','3期计划'];
  for(var t=0;t<6;t++){
    var has=APP.log.some(function(e){ return e.issue===nextIssue && e.ty===t; });
    if(has) continue;
    var f=null;
    if(t===4 || t===5){
      f=APP.planFormula || curForType(0);
    } else {
      f=(APP.userPicked&&APP.cur&&APP.cur.type===t)?APP.cur:curForType(t);
    }
    if(!f) continue;
    var p=predictNext(f);
    if(!p) continue;
    APP.log.push({ issue:nextIssue, ty:t, name:names[t], fid:f.fid, label:p.label, forms:(p.forms||[]).slice(), sums:(p.sums||[]).slice(), ts:Date.now(), state:'pending' });
  }
  saveLog();
}

/* ============ 倒计时 ============ */
function startCd(){
  if(APP.cdTimer) clearInterval(APP.cdTimer);
  function tick(){
    if(!APP.recs||!APP.recs.length) return;
    var now=Math.floor(Date.now()/1000), last=APP.recs[0];
    if(!last.ts){ $('cdVal').textContent='--:--'; return; }
    var nextIssue=fmtInt(last.issue)+1, nextTs=last.ts+PERIOD, left=nextTs-now;
    if(left<-PERIOD){ var rem=(-left)%PERIOD; left=PERIOD-rem; }
    var hot=left<=30;
    $('cdVal').textContent=hot?('封盘 '+mmss(left)):mmss(left);
    $('cdNext').textContent='第 '+nextIssue+' 期';
    $('cdBox').className='cdbox'+(hot?' warn':'');
    $('liveTxt').textContent=hot?'开奖中':'在线';
    if(left<=0 && Date.now()-(APP.lastFetch||0)>12000){ APP.lastFetch=Date.now(); silentRefresh(); }
  }
  tick(); APP.cdTimer=setInterval(tick,1000);
}

/* ============ 数据源 ============ */
/* 内置真实历史数据（离线兜底，开奖数据真实可对上） */
var BUILTIN_ROWS=[["3490843","908",10070006],["3490842","779",10070002],["3490841","025",10062359],["3490840","600",10062355],["3490839","002",10062352],["3490838","338",10062348],["3490837","313",10062345],["3490836","404",10062341],["3490835","970",10062338],["3490834","974",10062334],["3490833","420",10062331],["3490832","785",10062327],["3490831","059",10062324],["3490830","336",10062320],["3490829","825",10062317],["3490828","271",10062313],["3490827","087",10062310],["3490826","620",10062306],["3490825","517",10062303],["3490824","246",10062259],["3490823","072",10062256],["3490822","931",10062252],["3490821","611",10062249],["3490820","212",10062245],["3490819","729",10062242],["3490818","847",10062238],["3490817","052",10062235],["3490816","987",10062231],["3490815","199",10062228],["3490814","735",10062224],["3490813","688",10062221],["3490812","944",10062217],["3490811","617",10062214],["3490810","220",10062210],["3490809","191",10062207],["3490808","882",10062203],["3490807","703",10062200],["3490806","242",10062156],["3490805","540",10062153],["3490804","145",10062149],["3490803","193",10062146],["3490802","814",10062142],["3490801","334",10062139],["3490800","481",10062135],["3490799","943",10062132],["3490798","310",10062128],["3490797","728",10062125],["3490796","348",10062121],["3490795","639",10062118],["3490794","225",10062114],["3490793","004",10062111],["3490792","449",10062107],["3490791","257",10062104],["3490790","177",10062100],["3490789","297",10062057],["3490788","669",10062053],["3490787","792",10062050],["3490786","915",10062046],["3490785","479",10062043],["3490784","325",10062039],["3490783","115",10062036],["3490782","056",10062032],["3490781","469",10062029],["3490780","579",10062025],["3490779","523",10062022],["3490778","361",10062018],["3490777","240",10062015],["3490776","546",10062011],["3490775","710",10062008],["3490774","904",10062004],["3490773","127",10062001],["3490772","585",10061957],["3490771","961",10061954],["3490770","173",10061950],["3490769","983",10061947],["3490768","325",10061943],["3490767","341",10061940],["3490766","295",10061936],["3490765","133",10061933],["3490764","565",10061856],["3490763","910",10061853],["3490762","851",10061849],["3490761","280",10061846],["3490760","485",10061842],["3490759","134",10061839],["3490758","738",10061835],["3490757","862",10061832],["3490756","974",10061828],["3490755","316",10061825],["3490754","632",10061821],["3490753","414",10061818],["3490752","717",10061814],["3490751","243",10061811],["3490750","937",10061807],["3490749","169",10061804],["3490748","563",10061800],["3490747","596",10061757],["3490746","083",10061753],["3490745","910",10061750],["3490744","521",10061746],["3490743","139",10061743],["3490742","726",10061739],["3490741","193",10061736],["3490740","747",10061732],["3490739","788",10061729],["3490738","203",10061725],["3490737","891",10061722],["3490736","406",10061718],["3490735","096",10061715],["3490734","944",10061711],["3490733","542",10061708],["3490732","212",10061704],["3490731","743",10061701],["3490730","275",10061657],["3490729","372",10061654],["3490728","792",10061650],["3490727","281",10061647],["3490726","055",10061643],["3490725","752",10061640],["3490724","069",10061636],["3490723","108",10061633],["3490722","242",10061629],["3490721","804",10061626],["3490720","420",10061622],["3490719","469",10061619],["3490718","627",10061615],["3490717","248",10061612],["3490716","336",10061608],["3490715","272",10061605],["3490714","469",10061601],["3490713","470",10061558],["3490712","811",10061554],["3490711","238",10061551],["3490710","107",10061547],["3490709","373",10061544],["3490708","155",10061540],["3490707","614",10061537],["3490706","219",10061533],["3490705","382",10061530],["3490704","919",10061526],["3490703","781",10061523],["3490702","418",10061519],["3490701","670",10061516],["3490700","714",10061512],["3490699","616",10061509],["3490698","433",10061505],["3490697","071",10061502],["3490696","375",10061458],["3490695","798",10061455],["3490694","184",10061451],["3490693","321",10061448],["3490692","039",10061444],["3490691","558",10061441],["3490690","326",10061437],["3490689","552",10061434],["3490688","263",10061430],["3490687","954",10061427],["3490686","413",10061423],["3490685","293",10061420],["3490684","127",10061416],["3490683","880",10061413],["3490682","403",10061409],["3490681","792",10061406],["3490680","977",10061402],["3490679","855",10061359],["3490678","820",10061355],["3490677","112",10061352],["3490676","324",10061348],["3490675","189",10061345],["3490674","422",10061341],["3490673","857",10061338],["3490672","273",10061334],["3490671","475",10061331],["3490670","984",10061327],["3490669","129",10061324],["3490668","695",10061320],["3490667","262",10061317],["3490666","660",10061313],["3490665","040",10061310],["3490664","004",10061306],["3490663","399",10061303],["3490662","225",10061259],["3490661","711",10061256],["3490660","837",10061252],["3490659","113",10061249],["3490658","309",10061245],["3490657","901",10061242],["3490656","124",10061238],["3490655","045",10061235],["3490654","932",10061231],["3490653","379",10061228],["3490652","952",10061224],["3490651","680",10061221],["3490650","482",10061217],["3490649","283",10061214],["3490648","587",10061210],["3490647","951",10061207],["3490646","287",10061203],["3490645","393",10061200],["3490644","467",10061156],["3490643","480",10061153],["3490642","083",10061149],["3490641","785",10061146],["3490640","346",10061142],["3490639","625",10061139],["3490638","452",10061135],["3490637","808",10061132],["3490636","552",10061128],["3490635","137",10061125],["3490634","134",10061121],["3490633","606",10061118],["3490632","135",10061114],["3490631","050",10061111],["3490630","295",10061107],["3490629","053",10061104],["3490628","269",10061100],["3490627","654",10061057],["3490626","012",10061053],["3490625","002",10061050],["3490624","991",10061046],["3490623","430",10061043],["3490622","777",10061039],["3490621","629",10061036],["3490620","906",10061032],["3490619","507",10061029],["3490618","679",10061025],["3490617","922",10061022],["3490616","646",10061018],["3490615","571",10061015],["3490614","431",10061011],["3490613","641",10061008],["3490612","978",10061004],["3490611","859",10061001],["3490610","668",10060957],["3490609","448",10060954],["3490608","048",10060950],["3490607","168",10060947],["3490606","082",10060943],["3490605","526",10060940],["3490604","456",10060936],["3490603","110",10060933],["3490602","998",10060929],["3490601","877",10060926],["3490600","002",10060922],["3490599","349",10060919],["3490598","772",10060915],["3490597","831",10060912],["3490596","577",10060908],["3490595","292",10060905],["3490594","050",10060901],["3490593","358",10060858],["3490592","359",10060854],["3490591","934",10060851],["3490590","466",10060847],["3490589","180",10060844],["3490588","867",10060840],["3490587","065",10060837],["3490586","799",10060833],["3490585","573",10060830],["3490584","649",10060826],["3490583","584",10060823],["3490582","219",10060819],["3490581","331",10060816],["3490580","934",10060812],["3490579","387",10060809],["3490578","146",10060805],["3490577","720",10060802],["3490576","015",10060758],["3490575","595",10060755],["3490574","698",10060751],["3490573","036",10060748],["3490572","868",10060744],["3490571","559",10060741],["3490570","858",10060737],["3490569","785",10060734],["3490568","516",10060730],["3490567","978",10060727],["3490566","544",10060723],["3490565","271",10060720],["3490564","598",10060716],["3490563","306",10060713],["3490562","975",10060709],["3490561","691",10060706],["3490560","731",10060702],["3490559","511",10060659],["3490558","411",10060655],["3490557","277",10060652],["3490556","946",10060648],["3490555","022",10060645],["3490554","013",10060641],["3490553","974",10060638],["3490552","120",10060634],["3490551","655",10060631],["3490550","351",10060627],["3490549","383",10060624],["3490548","641",10060620],["3490547","081",10060617],["3490546","372",10060613],["3490545","264",10060610],["3490544","692",10060606],["3490543","231",10060603],["3490542","507",10060559],["3490541","832",10060556],["3490540","684",10060552],["3490539","896",10060549],["3490538","990",10060545],["3490537","482",10060542],["3490536","262",10060538],["3490535","178",10060535],["3490534","018",10060531],["3490533","212",10060528],["3490532","901",10060524],["3490531","810",10060521],["3490530","970",10060517],["3490529","346",10060514],["3490528","291",10060510],["3490527","147",10060507],["3490526","476",10060503],["3490525","199",10060500],["3490524","447",10060456],["3490523","602",10060453],["3490522","772",10060449],["3490521","738",10060446],["3490520","326",10060442],["3490519","314",10060439],["3490518","978",10060435],["3490517","643",10060432],["3490516","642",10060428],["3490515","726",10060425],["3490514","435",10060421],["3490513","393",10060418],["3490512","042",10060414],["3490511","024",10060411],["3490510","230",10060407],["3490509","714",10060404],["3490508","186",10060400],["3490507","947",10060357],["3490506","742",10060353],["3490505","785",10060350],["3490504","450",10060346],["3490503","805",10060343],["3490502","762",10060339],["3490501","833",10060336],["3490500","947",10060332],["3490499","292",10060329],["3490498","937",10060325],["3490497","871",10060322],["3490496","679",10060318],["3490495","693",10060315],["3490494","013",10060311],["3490493","608",10060308],["3490492","976",10060304],["3490491","943",10060301],["3490490","293",10060257],["3490489","968",10060254],["3490488","773",10060250],["3490487","048",10060247],["3490486","112",10060243],["3490485","771",10060240],["3490484","352",10060236],["3490483","584",10060233],["3490482","485",10060229],["3490481","169",10060226],["3490480","860",10060222],["3490479","967",10060219],["3490478","956",10060215],["3490477","923",10060212],["3490476","525",10060208],["3490475","479",10060205],["3490474","103",10060201],["3490473","852",10060158],["3490472","770",10060154],["3490471","357",10060151],["3490470","829",10060147],["3490469","245",10060144],["3490468","649",10060140],["3490467","631",10060137],["3490466","301",10060133],["3490465","448",10060130],["3490464","278",10060126],["3490463","696",10060123],["3490462","596",10060119],["3490461","999",10060116],["3490460","011",10060112],["3490459","763",10060109],["3490458","358",10060105],["3490457","842",10060102],["3490456","476",10060058],["3490455","614",10060055],["3490454","768",10060051],["3490453","208",10060048],["3490452","822",10060044],["3490451","033",10060041],["3490450","265",10060037],["3490449","269",10060034],["3490448","923",10060030],["3490447","967",10060027],["3490446","415",10060023],["3490445","528",10060020],["3490444","099",10060016]];
var API_JND='https://super.pc28998.com/history/JND28';
var API_HELP='https://pc28.help/api/kj.json?nbr=600';
function prox(u){ return encodeURIComponent(u); }
var SOURCES=[
  { n:'超管源', t:'jnd', u:API_JND },
  { n:'助手源', t:'help', u:API_HELP },
  { n:'超管镜像1', t:'jnd', u:'https://api.allorigins.win/raw?url='+prox(API_JND) },
  { n:'助手镜像1', t:'help', u:'https://api.allorigins.win/raw?url='+prox(API_HELP) },
  { n:'超管镜像2', t:'jnd', u:'https://api.codetabs.com/v1/proxy?quest='+prox(API_JND) },
  { n:'助手镜像2', t:'help', u:'https://api.codetabs.com/v1/proxy?quest='+prox(API_HELP) },
  { n:'超管镜像3', t:'jnd', u:'https://corsproxy.io/?url='+prox(API_JND) },
  { n:'助手镜像3', t:'help', u:'https://corsproxy.io/?url='+prox(API_HELP) }
];
function parseRaw(j, type){
  var arr=[];
  if(type==='jnd'){
    if(!j || j.code!==1 || !Array.isArray(j.data)) return null;
    for(var i=0;i<j.data.length;i++){
      var it=j.data[i]; if(!it) continue;
      var ns=String(it.opencode||'').split(/[,+]/).map(Number);
      if(ns.length!==3 || ns.some(isNaN)) continue;
      arr.push({ issue:String(it.expect), a:ns[0], b:ns[1], c:ns[2], ts:+(it.opentime)||0 });
    }
  } else {
    if(!j || j.message!=='success' || !Array.isArray(j.data)) return null;
    for(var k=0;k<j.data.length;k++){
      var m=j.data[k]; if(!m) continue;
      var nn=String(m.number||'').split(/[+,\s]/).map(Number);
      if(nn.length!==3 || nn.some(isNaN)) continue;
      var ts=0;
      if(m.date && m.time){
        var iso=String(m.date).trim()+'T'+String(m.time).trim()+'+08:00';
        var v=new Date(iso).getTime();
        if(!isNaN(v)) ts=Math.floor(v/1000);
      }
      arr.push({ issue:String(m.nbr), a:nn[0], b:nn[1], c:nn[2], ts:ts });
    }
  }
  if(arr.length<20) return null;
  arr.sort(function(x,y){ return fmtInt(y.issue)-fmtInt(x.issue); });
  var seen={}, out=[];
  for(var q=0;q<arr.length;q++){ if(!seen[arr[q].issue]){ seen[arr[q].issue]=1; out.push(arr[q]); } }
  return out.slice(0,600);
}
function fillTimes(rows){
  var base=-1;
  for(var i=0;i<rows.length;i++) if(rows[i].ts>0){ base=i; break; }
  if(base<0){ var now=Math.floor(Date.now()/1000); for(var i=0;i<rows.length;i++) rows[i].ts=now-i*PERIOD; return rows; }
  for(var i=base+1;i<rows.length;i++){ if(!rows[i].ts) rows[i].ts=rows[i-1].ts-(fmtInt(rows[i-1].issue)-fmtInt(rows[i].issue))*PERIOD; }
  for(var i=base-1;i>=0;i--){ if(!rows[i].ts) rows[i].ts=rows[i+1].ts+(fmtInt(rows[i].issue)-fmtInt(rows[i+1].issue))*PERIOD; }
  return rows;
}
function builtinRows(){
  var out=[];
  for(var i=0;i<BUILTIN_ROWS.length;i++){
    var r=BUILTIN_ROWS[i], n=r[1];
    var a=+n.charAt(0), b=+n.charAt(1), c=+n.charAt(2);
    if(isNaN(a)||isNaN(b)||isNaN(c)) continue;
    out.push({ issue:String(r[0]), a:a, b:b, c:c, ts:+r[2]||0 });
  }
  return out;
}
function fetchOnce(src){
  return new Promise(function(resolve){
    var done=false, ctrl=null, to=null;
    function fin(v){ if(done) return; done=true; if(to) clearTimeout(to); resolve(v); }
    try {
      ctrl=(typeof AbortController!=='undefined')?new AbortController():null;
      to=setTimeout(function(){ try{ctrl.abort();}catch(e){} },4000);
      var o={ cache:'no-store' }; if(ctrl) o.signal=ctrl.signal;
      fetch(src.u+(src.u.indexOf('?')>=0?'&':'?')+'_='+Date.now(), o)
        .then(function(r){ if(!r.ok) throw new Error('HTTP'+r.status); return r.json(); })
        .then(function(j){ var rows=parseRaw(j,src.t); fin(rows?{rows:rows,name:src.n}:null); })
        .catch(function(){ fin(null); });
    } catch(e){ fin(null); }
  });
}
function loadData(){
  return new Promise(function(resolve){
    var done=false, ok=0, total=SOURCES.length;
    function fin(v){ if(done) return; done=true; resolve(v); }
    var hard=setTimeout(function(){ fin({ rows:builtinRows(), name:'内置数据', builtin:1 }); },8000);
    for(var i=0;i<total;i++){
      (function(src){
        fetchOnce(src).then(function(r){
          if(done) return;
          if(r){ clearTimeout(hard); fin({ rows:r.rows, name:r.name }); }
          else { ok++; if(ok>=total){ clearTimeout(hard); fin({ rows:builtinRows(), name:'内置数据', builtin:1 }); } }
        });
      })(SOURCES[i]);
    }
  });
}
function applyData(rows, src, isDemo){
  rows=fillTimes(rows);
  APP.recs=buildRecs(rows);
  APP.src=src;
  $('liveBox').classList.toggle('off',!!isDemo);
  $('srcName').textContent=src;
  $('srcMeta').textContent=APP.recs.length+' 期';
  APP.lastFetch=Date.now();
  $('ldpct').textContent='...';
  $('mstat').textContent='正在生成公式池…';
  setTimeout(function(){
    APP.seedBase=(Math.random()*0x7fffffff)>>>0;
    APP.list=buildPool(APP.recs, W);
    $('ldwrap').classList.add('hide');
    syncLog(); renderSmart(); renderDraw(); renderLog();
    startCd();
  },30);
}
function boot(){
  var cached=lsGet('pc28_cache');
  if(cached){ try{ var c=JSON.parse(cached); if(c&&c.rows&&c.rows.length>=20) applyData(c.rows, c.name||'本地缓存', true); }catch(e){} }
  if(!APP.recs){ applyData(builtinRows(),'内置数据（离线）',true); }
  setTimeout(function(){ refresh(); },60);
}
function refresh(){
  return loadData().then(function(r){
    if(!r) return false;
    applyData(r.rows, r.name, !!r.builtin);
    if(!r.builtin){ lsSet('pc28_cache', JSON.stringify({rows:r.rows,name:r.name})); }
    return true;
  });
}
function manualRefresh(){ refresh(); }
function silentRefresh(){ if(!APP._polling) refresh(); }

/* ============ 启动 ============ */
APP.log=loadLog();
APP.rankTab=2;
APP.smart=2;
boot();
