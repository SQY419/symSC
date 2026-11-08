const fs = require('fs');
const VM = require('scratch-vm');
console.log = () => {}; console.warn = () => {}; console.error = () => {};
const output = (s) => process.stdout.write(s + '\n');
const vm = new VM();
let questionOpen = false;
let pendingAnswer = null;
let stamps = 0;
function answerNext(a) {
  pendingAnswer = a;
  if (questionOpen) {
    const x = pendingAnswer; pendingAnswer = null; questionOpen = false;
    vm.runtime.emit('ANSWER', x);
  }
}
function getList(target, name) {
  return Object.values(target.variables).find(v => v.type === 'list' && v.name === name);
}
async function waitFor(fn, ms, label) {
  const end = Date.now() + ms;
  while (Date.now() < end) {
    const v = fn();
    if (v) return v;
    await new Promise(r => setTimeout(r, 25));
  }
  throw new Error('timeout: ' + label);
}
const cases = [
  ['1+1', '2'], ['diff(5^x)', 'ln(5)*5^x'], ['sqrt(0)', '0'], ['sqrt(8)', '2*sqrt(2)'],
  ['sqrt(x)^4', 'x^2'], ['0', '0'], ['1/0', 'oo'], ['gcd(x^3+y^3,x^5+y^5)', 'x + y'],
  ['simplify((x^3+y^3)/(x^5+y^5))', '(x^2 + y^2 - x*y)/(x^4 + y^4 - x^3*y - x*y^3 + x^2*y^2)'],
  ['simplify(((x+y+z)^2)/((x+y+z)^3))', '1/(x + y + z)'], ['limit((1+1/x)^x,x,oo)', 'e'],
  ['sin(pi/6)', '1/2'], ['texpand(sin(x+y))', 'sin(x)*cos(y) + sin(y)*cos(x)'],
  ['trigcos(sin(x)^2)', '-cos(x)^2 + 1']
];
vm.loadProject(fs.readFileSync(process.argv[2])).then(async () => {
  const runtime = vm.runtime;
  runtime._primitives.pen_stamp = () => { stamps++; };
  runtime._primitives.pen_clear = () => {};
  const target = runtime.targets.find(t => t.getName() === 'main');
  const stage = runtime.targets.find(t => t.getName() === 'Stage');
  runtime.on('QUESTION', () => {
    questionOpen = true;
    if (pendingAnswer !== null) {
      const x = pendingAnswer; pendingAnswer = null; questionOpen = false;
      setTimeout(() => runtime.emit('ANSWER', x), 20);
    }
  });
  vm.start();
  answerNext(cases[0][0]);
  vm.greenFlag();
  const results = getList(target, 'results');
  const terminal = getList(stage, 'term_lines');
  await waitFor(() => terminal.value.some(v => String(v) === 'Scratch CAS v0.1'), 10000, 'banner');
  await waitFor(() => stamps > 0, 5000, 'banner stamps');
  for (let i = 0; i < cases.length; i++) {
    const [input, expected] = cases[i];
    await waitFor(() => results.value.length === 1 && String(results.value[0]) === expected, 30000, input + ' result');
    await waitFor(() => terminal.value.map(String).join('').includes('= ' + expected), 5000, input + ' terminal');
    output('case ' + (i + 1) + ': ' + results.value[0]);
    if (i + 1 < cases.length) {
      await new Promise(r => setTimeout(r, 300));
      answerNext(cases[i + 1][0]);
    }
  }
  await waitFor(() => stamps > 0, 5000, 'stamp calls');
  const history = getList(target, 'history');
  output('history: ' + history.value.length);
  output('UI_SMOKE_OK');
  process.exit(0);
}).catch(e => { output('UI_SMOKE_FAIL: ' + e.message); process.exit(1); });
