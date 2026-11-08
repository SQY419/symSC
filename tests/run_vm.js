const fs = require('fs');
const path = require('path');
const VM = require('scratch-vm');
console.log = () => {};
console.warn = () => {};
console.error = () => {};
const output = (x) => process.stdout.write(x + '\n');

const sb3 = process.argv[2];
const casesFile = process.argv[3];
const expectedFile = process.argv[4];
const cases = fs.readFileSync(casesFile, 'utf8').split(/\r?\n/).filter((x, i, a) => !(i === a.length - 1 && x === ''));
const expected = expectedFile && fs.existsSync(expectedFile)
  ? fs.readFileSync(expectedFile, 'utf8').split(/\r?\n/).filter((x, i, a) => !(i === a.length - 1 && x === ''))
  : null;

const vm = new VM();
vm.loadProject(fs.readFileSync(sb3)).then(async () => {
  vm.start();
  vm.greenFlag();
  const deadline = Date.now() + 120000;
  let target = null;
  let out = null;
  while (Date.now() < deadline) {
    target = vm.runtime.targets.find(t => t.getName() === 'tests');
    if (target) {
      const lists = Object.values(target.variables).filter(v => v.type === 'list');
      const done = lists.find(v => v.name === 'finished');
      out = lists.find(v => v.name === 'results');
      if (done && done.value.length > 0 && out) break;
    }
    await new Promise(r => setTimeout(r, 50));
  }
  if (!out) { console.error('NO_OUTPUT'); process.exit(1); }
  const actual = out.value.map(v => String(v));
  if (!expected) {
    output(JSON.stringify(actual, null, 2));
    process.exit(0);
  }
  let fail = 0;
  const n = Math.max(cases.length, actual.length, expected.length);
  for (let i = 0; i < n; i++) {
    if (actual[i] !== expected[i]) {
      fail++;
      output(`FAIL #${i+1}: ${cases[i]}\n  expected: ${JSON.stringify(expected[i])}\n  actual  : ${JSON.stringify(actual[i])}`);
    }
  }
  output(`${n - fail}/${n} passed`);
  process.exit(fail ? 1 : 0);
}).catch(e => { console.error(e); process.exit(1); });
