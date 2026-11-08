const fs = require('fs');
const VM = require('scratch-vm');
console.log = () => {}; console.warn = () => {}; console.error = () => {};
const output = s => process.stdout.write(s + '\n');
const vm = new VM();
let q = false, pending = null;
function answerNext(a) {
  pending = a;
  if (q) { const x = pending; pending = null; q = false; setTimeout(() => vm.runtime.emit('ANSWER', x), 20); }
}
function getV(target, name) {
  return Object.values(target.variables).find(v => (v.type === 'list' || v.type === '') && v.name === name);
}
async function waitFor(fn, ms, label) {
  const end = Date.now() + ms;
  while (Date.now() < end) { const v = fn(); if (v) return v; await new Promise(r => setTimeout(r, 25)); }
  throw new Error('timeout: ' + label);
}
const cases = [
  ['a=1', 'a = 1'],
  ['b=x^2+1', 'b = x^2 + 1'],
  ['a+b', 'x^2 + 2'],
  ['v=[1,2,3]', 'v = [1, 2, 3]'],
  ['v[2]', '2'],
  ['makelist(x+1,x,0,3)', '{1, 2, 3, 4}'],
  ['makelist(x^2,x,1,3)[2]', '4'],
  ['a=114514', 'a = 114514'],
  ['purge(a)', '114514'],
  ['purge(a)', '']
];
vm.loadProject(fs.readFileSync(process.argv[2])).then(async () => {
  const rt = vm.runtime;
  rt._primitives.pen_stamp = () => {};
  rt._primitives.pen_clear = () => {};
  rt.on('QUESTION', () => {
    q = true;
    if (pending !== null) { const x = pending; pending = null; q = false; setTimeout(() => rt.emit('ANSWER', x), 20); }
  });
  vm.start();
  answerNext(cases[0][0]);
  vm.greenFlag();
  const main = rt.targets.find(t => t.getName() === 'main');
  const results = getV(main, 'results');
  await waitFor(() => results.value.length === 1, 10000, 'first result');
  for (let i = 0; i < cases.length; i++) {
    const [input, expected] = cases[i];
    await waitFor(() => results.value.length === 1 && String(results.value[0]) === expected, 10000, input);
    output('defs ' + (i + 1) + ': ' + input + ' => ' + results.value[0]);
    if (i + 1 < cases.length) { await new Promise(r => setTimeout(r, 250)); answerNext(cases[i + 1][0]); }
  }
  output('DEFS_SMOKE_OK');
  process.exit(0);
}).catch(e => { output('DEFS_SMOKE_FAIL: ' + e.message); process.exit(1); });
