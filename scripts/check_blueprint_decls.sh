#!/usr/bin/env bash
# Verify that every \lean{...} name in the blueprint resolves to a real declaration.
# Usage: ./scripts/check_blueprint_decls.sh
set -uo pipefail
cd "$(dirname "$0")/.."
grep -rho '\\lean{[^}]*}' blueprint/src/chapter/ \
  | sed 's/\\lean{//;s/}//' | tr ',' '\n' \
  | sed 's/^ *//;s/ *$//' | grep -v '^$' | sort -u > blueprint/lean_decls
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
