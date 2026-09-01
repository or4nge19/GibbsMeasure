#!/usr/bin/env bash
# Verify that every \lean{...} name in the blueprint resolves to a real declaration.
# Usage: ./scripts/check_blueprint_decls.sh
set -uo pipefail
cd "$(dirname "$0")/.."
# NOTE: \lean{...} may span several lines, so the extraction must not be line-based.
python3 - <<'EOF' > blueprint/lean_decls
import glob, re
names = set()
for f in glob.glob('blueprint/src/chapter/**/*.tex', recursive=True):
    for g in re.findall(r'\\lean\{([^}]*)\}', open(f).read(), re.S):
        for n in g.split(','):
            n = n.strip()
            if n:
                names.add(n)
print('\n'.join(sorted(names)))
EOF
n=$(wc -l < blueprint/lean_decls | tr -d ' ')
{ echo 'import GibbsMeasure'
  while read -r d; do echo "#check @$d"; done < blueprint/lean_decls
} > blueprint/.check_decls.lean
out=$(lake env lean blueprint/.check_decls.lean 2>&1 | grep -E "error" || true)
rm -f blueprint/.check_decls.lean
if [ -n "$out" ]; then
  echo "BLUEPRINT DECLARATION CHECK FAILED ($n names):"
  echo "$out"
  exit 1
fi
echo "blueprint declaration check: all $n names resolve"
