#!/usr/bin/env bash
set -euo pipefail

proof_dir="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
# Optional dependency project permits offline replay without changing that project.
dependency_project="${1:-$proof_dir}"
cd "$dependency_project"
{
  compiler_version="$(lake env lean --version)"
  printf '%s\n' "$compiler_version"
  case "$compiler_version" in
    'Lean (version 4.30.0-rc2,'*) ;;
    *) printf 'Unexpected Lean version; use the included lean-toolchain.\n' >&2; exit 1 ;;
  esac
  mathlib_revision="$(git -C .lake/packages/mathlib rev-parse HEAD)"
  printf 'Mathlib revision: '
  printf '%s\n' "$mathlib_revision"
  if [ "$mathlib_revision" != '9977002c3c9492b622fb469b0d18acc7e73aed3e' ]; then
    printf 'Unexpected Mathlib revision; use the included lakefile.toml.\n' >&2
    exit 1
  fi
  printf 'Proof SHA256: '
  proof_hash="$(shasum -a 256 "$proof_dir/RankEncoding.lean")"
  printf '%s\n' "${proof_hash%% *}"
  lake env lean "$proof_dir/RankEncoding.lean"
} 2>&1 | tee "$proof_dir/build.log"

# Lean permits incomplete proofs with warnings, so do not equate exit zero
# with a complete proof. The printed dependency closures must be sorry-free.
if grep -Eq 'sorryAx|declaration uses .sorry.' "$proof_dir/build.log"; then
  printf 'Incomplete proof or sorryAx dependency detected.\n' >&2
  exit 1
fi
# Restrict every printed dependency closure to Lean's standard logical axioms.
# The pinned Lean version prints each axiom list on one line.
awk '/ depends on axioms: / {
  axioms = $0
  sub(/^.* depends on axioms: \[/, "", axioms)
  sub(/\]$/, "", axioms)
  count = split(axioms, names, /, */)
  for (i = 1; i <= count; i++) {
    if (names[i] != "propext" && names[i] != "Classical.choice" && names[i] != "Quot.sound") {
      print "Unexpected axiom dependency: " names[i] > "/dev/stderr"
      failed = 1
    }
  }
}
END { exit failed }' "$proof_dir/build.log"
for theorem in scc_encoding_sound_and_complete exact_scc_encoding_sound_and_complete; do
  if ! grep -Fq "'EggLpRank.$theorem' depends on axioms:" "$proof_dir/build.log"; then
    printf 'Missing main-theorem axiom report: %s\n' "$theorem" >&2
    exit 1
  fi
done
printf 'Proof replay passed; all reported dependency closures are complete.\n' \
  | tee -a "$proof_dir/build.log"
