#!/usr/bin/env bash
set -euo pipefail

if [[ $# -lt 1 ]]; then
  echo "Usage: $0 <log_file> [--all]" >&2
  exit 1
fi

log_file="$1"
mode="${2:-}"

python3 - "$log_file" "$mode" <<'PY'
from __future__ import print_function
import os
import re
import sys

log_file = sys.argv[1]
mode = sys.argv[2] if len(sys.argv) > 2 else ""

prop_re = re.compile(
	r"property_result\(engine='([^']+)', prop_no=(\d+), result='([^']+)', depth=(\d+), cex=\[(.*?)(?:\]\)|\]|$)"
)
json_re = re.compile(r"json_result\(engine='([^']+)', json=\{(.*)\}\)")
status_re = re.compile(r"status': u?'([^']+)'")
propno_re = re.compile(r"prop_no': (\d+)")
cex_re = re.compile(r"cex': \[(.*)\]")

results = []

base = os.path.basename(log_file)
root, _ext = os.path.splitext(base)
out_path = os.path.join(os.path.dirname(log_file), root + "_res.txt")

with open(log_file, 'r') as fin:
	for line in fin:
		line = line.strip()

		m = prop_re.search(line)
		if m:
			engine, prop_no, result, depth, cex = m.groups()
			if result == 'failed':
				status = 'SAT'
			elif result == 'proved':
				status = 'UNSAT'
			else:
				status = 'UNKNOWN'
			results.append({
				'status': status,
				'engine': engine,
				'prop_no': prop_no,
				'depth': depth,
				'cex': cex.strip(),
			})
			continue

		m = json_re.search(line)
		if m:
			engine, body = m.groups()
			sm = status_re.search(body)
			pm = propno_re.search(body)
			cm = cex_re.search(body)
			status = sm.group(1) if sm else 'UNKNOWN'
			prop_no = pm.group(1) if pm else '0'
			cex = cm.group(1).strip() if cm else ''
			results.append({
				'status': status,
				'engine': engine,
				'prop_no': prop_no,
				'depth': 'N/A',
				'cex': cex,
			})

if not results:
	with open(out_path, 'w') as fout:
		fout.write("No result entries found in log.\n")
	print("Wrote: %s" % out_path)
	sys.exit(0)

def dump(res, fout):
	fout.write("final_result: %s\n" % res['status'])
	fout.write("engine: %s\n" % res['engine'])
	fout.write("prop_no: %s\n" % res['prop_no'])
	fout.write("depth: %s\n" % res['depth'])
	fout.write("cex: %s\n" % (res['cex'] if res['cex'] else '(none)'))

with open(out_path, 'w') as fout:
	if mode == '--all':
		for i, res in enumerate(results, 1):
			fout.write("-- result %d --\n" % i)
			dump(res, fout)
	else:
		dump(results[-1], fout)

print("Wrote: %s" % out_path)
PY
