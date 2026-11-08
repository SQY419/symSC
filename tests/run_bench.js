const fs=require('fs'); const VM=require('scratch-vm');
console.log=()=>{};console.warn=()=>{};
const out=(s)=>process.stdout.write(s+'\n');
const vm=new VM();
const t0=Date.now();
vm.loadProject(fs.readFileSync('tests/bench.sb3')).then(async()=>{
  const load=Date.now()-t0;
  vm.start(); vm.greenFlag();
  const t1=Date.now();
  let target=null, list=null;
  const end=Date.now()+30000;
  while(Date.now()<end){
    target=vm.runtime.targets.find(t=>t.getName()==='bench');
    list=target && Object.values(target.variables).find(v=>v.type==='list'&&v.name==='bench');
    if(list && list.value.includes('DONE')) break;
    await new Promise(r=>setTimeout(r,50));
  }
  const total=Date.now()-t1;
  out('load_ms='+load);
  out('run_ms='+total);
  for(const row of (list?list.value:[])) out(String(row));
  process.exit(0);
}).catch(e=>{out('ERR '+e);process.exit(1)});
