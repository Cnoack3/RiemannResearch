#!/usr/bin/env bash
# Review proposal: run only in a new, disposable checkout. Never cleans a workspace.
# Usage: bash verify_november_research.sh SOURCE EXPECTED_SHA SCOPE EVIDENCE_DIR
# SCOPE: infimum | november | full. Requires Linux, elan, Python 3 and GNU time.
set -euo pipefail
verifier_path=$(realpath "${BASH_SOURCE[0]}")

if [[ $# != 4 ]]; then
  echo 'Usage: verify_november_research.sh SOURCE EXPECTED_SHA {infimum|november|full} EVIDENCE_DIR' >&2
  exit 2
fi
source_dir=$(realpath "$1")
expected=$2
scope=$3
evidence=$(realpath -m "$4")
[[ $expected =~ ^[0-9a-f]{40}$ ]] || { echo 'Expected SHA must be 40 lowercase hex digits' >&2; exit 2; }
case "$scope" in infimum|november|full) ;; *) echo 'Unknown scope' >&2; exit 2 ;; esac
case "$evidence/" in "$source_dir/"*) echo 'Evidence must be outside the source checkout' >&2; exit 2 ;; esac
mkdir -p "$evidence"
[[ ! -e "$evidence/status.json" ]] || { echo 'Use a new evidence directory' >&2; exit 2; }
stage=preflight
started=$(date -u +%FT%TZ)
finish() {
  local rc=$?
  trap - EXIT
  local state=failed
  [[ $rc == 0 ]] && state=succeeded
  printf '{"state":"%s","exit_code":%s,"stage":"%s","scope":"%s","expected_sha":"%s","started_utc":"%s","finished_utc":"%s"}\n' \
    "$state" "$rc" "$stage" "$scope" "$expected" "$started" "$(date -u +%FT%TZ)" > "$evidence/status.json"
  df -h "$source_dir" > "$evidence/disk-final.txt" 2>&1 || true
  free -h > "$evidence/memory-final.txt" 2>&1 || true
  exit "$rc"
}
trap finish EXIT
printf '{"state":"incomplete","scope":"%s","expected_sha":"%s"}\n' "$scope" "$expected" > "$evidence/status.json"
cd "$source_dir"
[[ $(git rev-parse HEAD) == "$expected" ]] || { echo 'Source SHA mismatch' >&2; exit 1; }
[[ -z $(git status --porcelain --untracked-files=all) ]] || { echo 'Source checkout is dirty' >&2; exit 1; }
[[ ! -e .lake && ! -L .lake ]] || { echo 'Refusing existing .lake; use a fresh checkout' >&2; exit 1; }
[[ -x /usr/bin/time ]] || { echo 'GNU /usr/bin/time is required' >&2; exit 1; }
export LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-2}
[[ $LEAN_NUM_THREADS =~ ^[1-8]$ ]] || { echo 'LEAN_NUM_THREADS must be 1 through 8' >&2; exit 2; }

run_stage() {
  stage=$1
  shift
  printf '%s\n' "$stage" > "$evidence/current-stage.txt"
  printf '%q ' "$@" > "$evidence/$stage.command.txt"
  printf '\n' >> "$evidence/$stage.command.txt"
  set +e
  /usr/bin/time -v -o "$evidence/$stage.resources.txt" "$@" 2>&1 | tee "$evidence/$stage.log"
  local statuses=("${PIPESTATUS[@]}")
  set -e
  printf '%s\n' "${statuses[0]}" > "$evidence/$stage.exit-code.txt"
  [[ ${statuses[0]} == 0 ]] || return "${statuses[0]}"
  [[ ${statuses[1]} == 0 ]] || return "${statuses[1]}"
}

git rev-parse HEAD HEAD^{tree} > "$evidence/source.txt"
sha256sum "$verifier_path" > "$evidence/verifier-sha256.txt"
sha256sum lean-toolchain lakefile.toml lake-manifest.json > "$evidence/input-sha256.txt"
cp lean-toolchain lakefile.toml lake-manifest.json "$evidence/"
uname -a > "$evidence/platform.txt"
printf 'LEAN_NUM_THREADS=%s\n' "$LEAN_NUM_THREADS" >> "$evidence/platform.txt"
df -h . > "$evidence/disk-initial.txt"
free -h > "$evidence/memory-initial.txt"
run_stage lean-version lean --version
run_stage lake-version lake --version
# This is the upstream Mathlib executable cache, not the private project cache.
run_stage dependency-cache lake --no-cache exe cache get
stage=dependency-pins
python3 - <<'PY' | tee "$evidence/dependency-revisions.txt"
import json, pathlib, subprocess
manifest = json.loads(pathlib.Path('lake-manifest.json').read_text())
for package in manifest['packages']:
    if package['type'] != 'git':
        raise SystemExit('Unexpected non-git dependency: ' + package['name'])
    path = pathlib.Path(manifest['packagesDir']) / package['name']
    actual = subprocess.check_output(['git', '-C', str(path), 'rev-parse', 'HEAD'], text=True).strip()
    print(package['name'], actual, flush=True)
    if actual != package['rev']:
        raise SystemExit('Dependency revision mismatch: ' + package['name'])
PY
git diff --exit-code -- lean-toolchain lakefile.toml lake-manifest.json
[[ ! -e .lake/build/lib/lean/RiemannResearch && ! -e .lake/build/lib/lean/RiemannResearch.olean ]] || {
  echo 'Project artifacts appeared before source build; independent replay refused' >&2; exit 1;
}

modules=(RiemannResearch.RH.QTensorCertificateInfimum)
endpoints=(
  RiemannResearch.RH.QTensorCertificate.columnInfimum_eq_zero_iff
  RiemannResearch.RH.QTensorCertificate.anchoredInfimum_eq_zero_iff
  RiemannResearch.RH.QTensorCertificate.riemannHypothesis_of_columnInfimum_zero
  RiemannResearch.RH.QTensorCertificate.riemannHypothesis_of_anchoredInfimum_zero
  RiemannResearch.RH.QTensorCertificate.anchoredCertificate_projection_eq_error
  RiemannResearch.RH.QTensorCertificate.anchoredInfimum_eq_legalErrorInfimum
  RiemannResearch.RH.QTensorCertificate.legalErrorInfimum_le_columnInfimum
  RiemannResearch.RH.QTensorCertificate.riemannHypothesis_of_legalErrorInfimum_zero
  RiemannResearch.RH.QTensorCertificate.legalErrorInfimum_lt_benchmark
  RiemannResearch.RH.QTensorCertificate.anchoredInfimum_lt_benchmark
  RiemannResearch.RH.QTensorCertificate.Benchmark.complete_norm_lt
)
if [[ $scope != infimum ]]; then
  modules+=(
    RiemannResearch.Analysis.FiniteTensorTail
    RiemannResearch.Analysis.HeavyAtomVariance
    RiemannResearch.Analysis.FiniteWeightedLegalProjection
    RiemannResearch.RH.QDivisorGcdCutoff
    RiemannResearch.RH.QSquarefreeAnalysisObstruction
    RiemannResearch.RH.QTensorCertificate
    RiemannResearch.RH.PeriodicArithmeticCumulative
    RiemannResearch.RH.SquarefreeWeightedPrimitives
    RiemannResearch.RH.WeightedCRTLegalObstruction
    RiemannResearch.RH.WeightedResidueRHCriterion
    RiemannResearch.RH.WeightedLegalPrimitiveProjection
    RiemannResearch.RH.ConditionalMeanFiniteCutoff
    RiemannResearch.RH.MeanNeutralMobiusFiniteCutoff
    RiemannResearch.RH.MultiRangeCertificateConvergence
  )
  endpoints+=(
    RiemannResearch.Analysis.FiniteTensorTail.anchored_split
    RiemannResearch.Analysis.FiniteTensorTail.tail_inner_eq
    RiemannResearch.Analysis.FiniteTensorTail.weighted_diagonal_majorant
    RiemannResearch.Analysis.FiniteTensorTail.columnCertificate_add_row_le
    RiemannResearch.Analysis.FiniteTensorTail.block_certificate
    RiemannResearch.Analysis.HeavyAtomVariance.variance_le
    RiemannResearch.Analysis.FiniteWeightedLegalProjection.weightedProjection_completion
    RiemannResearch.Analysis.FiniteWeightedLegalProjection.constrainedProjection_completion
    RiemannResearch.RH.QDivisorHilbert.divisorWavelet_cutoff_span_eq
    RiemannResearch.RH.QSquarefreeAnalysisObstruction.residue_three_not_mem
    RiemannResearch.RH.ArithmeticCumulative.cumulative_periodic_of_zero_period
    RiemannResearch.RH.SquarefreeWeightedPrimitives.legalPrimitive_pullback
    RiemannResearch.RH.WeightedCRTLegalObstruction.weighted_adjoint_not_legal
    RiemannResearch.RH.WeightedResidueRHCriterion.riemannHypothesis_of_legal_residue_lower_growth
    RiemannResearch.RH.WeightedLegalPrimitiveProjection.legalProjection_completion
    RiemannResearch.RH.WeightedLegalPrimitiveProjection.constrainedLegalProjection_completion
    RiemannResearch.RH.Pareto.normalized_lowerLogGrowth_zero_iff_finitePrefix
    RiemannResearch.RH.Pareto.meanNeutralMobiusHead_finite_certificate
    RiemannResearch.RH.Pareto.riemannHypothesis_of_meanNeutral_certifiedPrefix_lower_growth
  )
fi
targets=()
for module in "${modules[@]}"; do targets+=("+$module"); done
[[ $scope != full ]] || targets=(RiemannResearch "${targets[@]}")
printf '%s\n' "${targets[@]}" > "$evidence/targets.txt"
run_stage source-build lake --no-cache build "${targets[@]}"

printf '%s\n' "${endpoints[@]}" > "$evidence/expected-endpoints.txt"
for module in "${modules[@]}"; do printf 'import %s\n' "$module"; done > "$evidence/Audit.lean"
for endpoint in "${endpoints[@]}"; do
  printf '#check %s\n#print axioms %s\n' "$endpoint" "$endpoint"
done >> "$evidence/Audit.lean"
run_stage endpoint-audit lake --no-cache env lean "$evidence/Audit.lean"
stage=axiom-allowlist
python3 - "$evidence" <<'PY'
import json, pathlib, re, sys
directory = pathlib.Path(sys.argv[1])
expected = directory.joinpath('expected-endpoints.txt').read_text().splitlines()
output = directory.joinpath('endpoint-audit.log').read_text()
found = {}
for name, axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", output, re.S):
    if name in found:
        raise SystemExit('Duplicate axiom result: ' + name)
    found[name] = [x.strip() for x in axioms.split(',') if x.strip()]
for name in re.findall(r"'([^']+)' does not depend on any axioms", output):
    if name in found:
        raise SystemExit('Duplicate axiom result: ' + name)
    found[name] = []
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for name in expected:
    if name not in found:
        raise SystemExit('Missing axiom result: ' + name)
    unexpected = set(found[name]) - allowed
    if unexpected:
        raise SystemExit('Unexpected axiom(s) in ' + name + ': ' + ', '.join(sorted(unexpected)))
directory.joinpath('axioms.json').write_text(json.dumps({name: found[name] for name in expected}, indent=2) + '\n')
PY
stage=source-unchanged
[[ $(git rev-parse HEAD) == "$expected" ]]
[[ -z $(git status --porcelain --untracked-files=all) ]]
sha256sum -c "$evidence/input-sha256.txt" > "$evidence/input-unchanged.txt"
stage=complete
echo 'Source build and the named endpoint audits completed; inspect types for mathematical hypotheses.'
