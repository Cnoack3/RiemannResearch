# Mesoscopic gamma drift and actual-zero phase attempt — 2026-11-18

## Formal declarations

Source module: Analysis/MicroscopicGammaDrift.lean, namespace
RiemannResearch.Analysis.ActualZeroDiscrepancy.

- **microscopicGammaDrift_mean_sq_le** exposes a single constant C >= 0
  valid for every T > 1 and 0 <= R <= log(T)/(2*pi):
  \[
    T^{-1}\int_0^T d_{T,R}(t)^2\,dt
    \le C R^2/(\log T)^2.
  \]
  Here d is the exact smooth gamma-count increment minus R. This retains
  the width dependence hidden by the earlier bounded-width estimate.
- **microscopicGammaDrift_mean_sq_tendsto_zero** proves that this energy
  tends to zero for every eventually nonnegative R(T) with R(T)/log(T) -> 0.
  The width may grow. These are genuine hypotheses on the chosen width,
  not unproved hypotheses on the zero distribution.
- **microscopicGammaDrift_mean_sq_bound** and the existing bounded-width
  vanishing theorem follow from the strengthened finite-height estimate.

The argument uses the existing proved gamma-factor estimates. No RH,
pair-correlation, DPP-limit, or zero-statistical hypothesis occurs in these
new theorem statements. The mandatory managed checkpoint determines
publication and full-project verification status.

## Analytic research, separate from the formal declarations

The companion note RH/MellinModularQuadraticAttempt20261118.md contains a
publication audit and complete analytic deductions using published inputs:

1. Actual zero phase energies are uniformly bounded on every translated
   fixed frequency band, at normalization N_T.
2. Every subsequential spectral limit has an atom of exactly mass one at
   the origin, and its remaining mass in [-epsilon,epsilon] is
   O(epsilon^2 log(2+1/epsilon)).
3. The prime-polynomial part of the microscopic count variance is evaluated
   through cutoff n <= T. The signed residual covariance is retained.
4. Actual counts and the sine process have the same leading variance for
   growing unfolded windows. This is not an absolute fixed-width limit.
5. A sharper horizontal-energy bound follows from uniform Selberg density;
   the little-o strengthening needed by a restricted-support transfer
   remains open in this attempt.

These analytic deductions and external analytic inputs are **not** claimed
to have been formalized by this checkpoint.

## Conditional research reduction and open obligations

For each fixed R > 0, write the argument increment as P_{T,R}+E_{T,R},
with P the explicit prime-power cosine polynomial in the companion note.
The actual second-moment comparison requires
\[
  2\langle P_{T,R}E_{T,R}\rangle_T+
  \langle E_{T,R}^2\rangle_T
  \longrightarrow
  \frac1{\pi^2}\int_1^\infty
       \frac{1-\cos(2\pi R\alpha)}{\alpha^2}\,d\alpha.
\]

**Open:** this fixed-width signed residual asymptotic.
**Open:** identification of the full non-atomic spectral limit as
min(|alpha|,1) d alpha.
**Open:** a full actual-zero/Mellin-DPP second-moment comparison.
No PCC or RH proof is claimed.

## Provenance

The gamma proof extends the existing Stirling-based integration argument.
The count/argument comparison is discussed in Goldston–Lee–Schettler–
Suriajaya, Proposition 2, https://doi.org/10.1112/mtk.70127.
The companion note gives theorem-level references for the analytic inputs,
including Selberg, Fujii, Maples–Rodgers, FMZ, BGSTB, and Lamzouri's
10 November 2026 sparse-deletion estimate.
