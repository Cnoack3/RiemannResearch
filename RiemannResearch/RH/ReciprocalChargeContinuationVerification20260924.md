# Reciprocal-charge continuation: verification record (2026-09-24)

Starting commit: `171ed70a08cb9842e2432c10c489a93da5cbf3fb`.
Tracking: [CHR-5](https://linear.app/stubbypeeps33/issue/CHR-5/formalize-reciprocal-charge-norm-limit-and-audit-remaining-rh).

## Scope and proved results

This continuation executes the norm-limit handoff and formalizes an arithmetic extension.
It does not prove RH. No mathematical novelty is claimed.

All final results concern the existing physical Hilbert vectors
`RiemannResearch.RH.Pareto.reciprocalChargeRiesz N`.

- `reciprocalChargeRiesz_norm_sq_tendsto`: squared norms tend to `15 / Real.pi ^ 2`.
- `reciprocalChargeRiesz_distance_sq_tendsto`: squared distance from a fixed vector tends to its squared norm plus `15/pi^2`.
- `reciprocalChargeRiesz_no_norm_convergent_subsequence`: no subsequence whose indices tend to infinity converges in norm.
- `reciprocalChargeRiesz_dilation_inner_tendsto`: for every positive integer h, the signed inner product at cutoffs N and hN tends to `(1/h) * sum_d mu(d)*mu(h*d)/d^2`.
- `reciprocalChargeRiesz_prime_dilation_inner_tendsto`: for a prime p this limit is `-15*p / ((p^2+1)*pi^2)`.
- `reciprocalChargeRiesz_two_dilation_inner_tendsto` and `reciprocalChargeRiesz_three_dilation_inner_tendsto`: the exact limits are `-6/pi^2` and `-9/(2*pi^2)`.

## Module structure

| Module | Role |
|---|---|
| NumberTheory/QuotientWindowEnergySplit | Exact low/isolated finite partition |
| NumberTheory/QuotientWindowEnergyLimit | Summable domination and limiting square energy |
| Analysis/BoundedSquareEnergy | General correction limits and interval-sum helpers |
| NumberTheory/QuotientKernelEnergyLimit | General kernel-energy identity and scaled limit |
| RH/ReciprocalChargeNormLimit | Actual norm, distance, and subsequence results |
| RH/ReciprocalChargeDilationArithmetic | Arithmetic charges and exact dilation kernel |
| RH/ReciprocalChargeDilationSeries | Summable signed series and exact square expansion |
| RH/ReciprocalChargeDilationKernelLimit | All arithmetic hypotheses of the scaled limit |
| RH/ReciprocalChargeDilationNorm | Exact transfer to the Hilbert norm of a sum |
| RH/PrimeReciprocalChargeCorrelation | Exact prime partition and evaluated signed series |
| RH/ReciprocalChargeDilationCorrelation | Polarization and final signed limits |

The existing `NumberTheory/SquarefreeEulerSeries` supplies the evaluated Euler series.
The existing PNT and weak-zero results supply the analytic limits. No unproved
arithmetic premise is introduced into the final norm or correlation declarations.
All eleven modules are exported by `RiemannResearch.lean`.

## Validation

The complete combined Lean source passed in job
`job_b53aYD1ZjepaqjaMGOUDtZTtXuEwG2ZH`, with compiler exit code 0 and
`verified: true` (118.309 seconds). Source SHA-256:
`7869268f7fb443c82571bc9bffb6eef8034a0a8aeffeec8f3818a294c0cd61c4`.

Axiom inspection of the norm limit, no-convergent-subsequence result, general
integer-dilation correlation, and the two explicit specializations returned
only `propext`, `Classical.choice`, and `Quot.sound`. No `sorryAx` or
new axiom appears in those dependencies. Independent module import and
namespace audits found no reliance on the concatenated source environment.

The publication checkpoint separately validates the affected modules in the
repository. Its final result and published commit are recorded in the
user-facing continuation report and in CHR-5.

## Research beyond the formal boundary

The companion `ReciprocalCharge_DilationAndPeriodicSource_20260924.md` derives
general rational-dilation correlations, explicit finite averages using 2 and 3,
a rescaled energy profile, and periodic Gram-source decay on paper. These
extensions are not claimed as Lean-verified. In particular, the logarithmic
Möbius mean needed for the constant source mode still needs a formal provider.

The original `ReciprocalChargeNormLimit20260924.md` is retained with its status updated.
The earlier agenda report remains historical.

## Open RH obligations

The actual residual sign condition, signed Schur saturation, growing
inverse-Gram control, and independently optimized approximation estimates for
weights approaching 1 remain open. Dual-vector cancellation does not establish
legal primal approximation. Burnol projection and full BSY boundary passage
remain separate formal import tasks.

## Source audit

- [Balazard, arXiv:1812.04309](https://arxiv.org/pdf/1812.04309), Propositions 5–7.
- [NIST DLMF 27.11.15](https://dlmf.nist.gov/27.11.E15), logarithmic Möbius mean.
- [Manzur–Noor–Quintero, arXiv:2606.16097](https://arxiv.org/html/2606.16097v1),
  Theorem 3.1 is for boundary parameter alpha>1; it does not supply the missing
  uniform estimate toward alpha=1/2.

Wolfram checked the finite square algebra and numerical signed correlations.
These checks support the arithmetic exploration; the proof status is determined by Lean.
