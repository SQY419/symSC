#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
GOBOSCRIPT="${GOBOSCRIPT:-../goboscript-bin/goboscript}"
rm -rf tests/project/lib
cp -r lib tests/project/lib
cp assets/blank.svg tests/project/blank.svg
python3 - <<'PY'
import json
cases = [line for line in open('tests/project/cases.txt', encoding='utf-8').read().splitlines() if line != '']
with open('tests/project/data/cases.gs', 'w', encoding='utf-8') as f:
    f.write('list cases = ' + json.dumps(cases, ensure_ascii=False) + ';\n')
PY
"$GOBOSCRIPT" build
"$GOBOSCRIPT" build -i tests/project -o tests/tests.sb3
node tests/run_vm.js tests/tests.sb3 tests/project/cases.txt tests/expected.txt
node tests/ui_smoke.js cas.sb3
node tests/defs_smoke.js cas.sb3
