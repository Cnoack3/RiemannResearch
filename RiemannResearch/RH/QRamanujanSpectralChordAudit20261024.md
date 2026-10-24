# Spectral chord bounds and dependency audit

Date: 24 October 2026. Base: `fccabcdaa64eb5f6f566a451ad484538230a77f1`.

## Result and exact remainder

For a real finite positive contraction A, let
`tau = trace(I-A)`. Suppose its eigenvalues satisfy
`epsilon <= lambda_i <= 1`, with `0 < epsilon < 1`. Define

```text
s_i = log(lambda_i) - ((1-lambda_i)/(1-epsilon))*log(epsilon).
```

Logarithm concavity on [epsilon,1] gives s_i >= 0. The complete identity is

```text
det A = exp(tau/(1-epsilon)*log(epsilon) + sum_i s_i).
```

Consequently

```text
exp(-tau/epsilon)
  <= exp(tau/(1-epsilon)*log(epsilon))
  <= det A
  <= exp(-tau).
```

The first comparison is proved explicitly. The new lower bound uses the total
trace defect, with no dimension factor. The scalar gap vanishes at both
endpoints epsilon and 1; the formalization includes these endpoint identities.
The exact product identity only requires positive eigenvalues bounded below
by epsilon; the nonnegative remainder and lower estimate additionally use
epsilon<1 and the contraction condition.

The endpoint epsilon=1 is deliberately excluded from the chord estimate.
A positive contraction with all eigenvalues >=1 has every eigenvalue equal
to 1 and determinant 1, so no division by 1-epsilon is needed there.

For small trace defect, the existing lower bound 1-tau can be stronger.
Both valid lower bounds may be used; no dominance over the union bound is claimed.

## Genuine complete-Q application

For the projected orthonormal auxiliary heads in `QRamanujanDPPTraceBounds`,
tau is the actual `headLoss`, and det A is `headMass`. The new exact
identity is specialized to those quantities, including the full spectral
remainder.

When the target is qOne, the existing exact vacancy identity and mass comparison
give the explicit new estimate

```text
packetError <= conditionedVacancy
  <= exp(-headLoss/(1-epsilon)*log(epsilon))*packetError.
```

Positive mass and projected-head independence are derived from the new lower
bound; they are not extra assumptions of `conditionedVacancy_le_chord`.
Orthonormality, target identification, and the eigenvalue lower bound remain
explicit hypotheses. This controls the amplification caused by conditioning;
it does not establish that packetError or conditionedVacancy tends to zero.

## Declarations

Established without RH hypotheses:

- `RiemannResearch.LinearAlgebra.DeterminantTrace.trace_chord_le_log`
- `logChordGap`, `logChordGap_nonneg`, `logChordGap_endpoints`
- `prod_eq_exp_trace_chord_add_gap`, `exp_trace_chord_le_prod`
- `exp_neg_defect_div_le_exp_trace_chord`
- `Matrix.PosSemidef.det_eq_exp_trace_chord_add_gap`
- `Matrix.PosSemidef.exp_trace_chord_le_det`
- `RiemannResearch.RH.QRamanujanDPP.headMass_eq_exp_trace_chord_add_gap`
- `headMass_chord_lower_bound`, `conditionedVacancy_le_chord`

Definitions and the general estimates live in
`LinearAlgebra/DeterminantTraceBounds.lean`; actual-Q consumers live in
`RH/QRamanujanDPPTraceBounds.lean`.

## Dependency repair

The two general matrix declarations
`Matrix.PosSemidef.eigenvalues_le_one` and `eigenvalues_mem_Icc` now live
in `LinearAlgebra/PositiveContractionSpectrum.lean`, importing
`Mathlib.Analysis.Matrix.PosDef` and the directly used algebraic module
`Mathlib.LinearAlgebra.Matrix.PosDef`. Their names and statements are unchanged.
They were removed from `Probability/DeterminantalSpectralCount.lean`,
which now imports their actual owning module. General determinant bounds
therefore no longer import the probability generating-function development
through that spectral-count module. The new module is exported from
`RiemannResearch.lean`; no forwarding or relocation wrappers were added.

This is a dependency-graph improvement. No build-time or cache-hit improvement
has been measured. No toolchain, lakefile, or dependency-version changes
were needed for this update.

## Wolfram cross-check

Wolfram Language evaluated the exact spectrum (1/4,1/2,3/4,1):

| Quantity | Value |
|---|---:|
| epsilon | 1/4 |
| tau | 3/2 |
| determinant | 3/32 = 0.09375 |
| earlier exponential lower bound | exp(-6), approximately 0.00247875218 |
| chord lower bound | 1/16 = 0.0625 |
| union lower bound | -1/2 |
| exponential upper bound | exp(-3/2), approximately 0.22313016015 |

The ratio of the actual determinant to the chord lower bound is 3/2, so the
exact sum of logarithmic gaps is log(3/2). This numerical computation is a
cross-check, not a Lean proof about an actual arithmetic probe family.

The endpoint spectrum (1/4,1/4,1,1) has the same epsilon and tau and attains the
chord bound 1/16. This elementary example explains sharpness for these data;
the general cap-constrained optimizer has not been formalized in this update.

## Verification and open obligations

The combined scalar and matrix proof candidate passed server job
`job_ci1r_z5hCxT5leCp-WL9B5aimZ65jnPf`, reported execution 5.357 seconds.
An isolated candidate check is not the acceptance gate for the persisted
project. The final publication checkpoint must validate the saved modules,
their consumers, and any integrated source before pushing. Its terminal
receipt and exact published commit are reported in the task completion.
The saved modules and their directly imported consumers subsequently passed
server job `job_cLq9HxqcZThh8ub3hKyyjICVDhGgypfe`, with reported execution
19.283 seconds and exit code 0. This covered the moved eigenvalue lemmas,
the updated DPP spectral-count consumer, the new determinant identities,
and the genuine-Q amplification theorem. Their printed axioms were the
standard three foundations listed below. This remains a targeted check;
the final checkpoint is the publication gate.

Reported server execution time does not measure workspace opening,
transport, or polling delays.

Axiom inspection of the main candidate bound reports only
`propext`, `Classical.choice`, and `Quot.sound`. Local hypotheses must
still be read in the declaration types.

Open:
- quantitative spectral or whole-span estimates for a specified useful
  growing arithmetic family;
- decay of its actual conditioned target vacancy or canonical packetError;
- the RH-to-Baez-Duarte provider retained in existing conditional RH reductions.

No RH proof, target-closure provider, or general arithmetic spectral bound is
asserted by this update.

## Sources and scope

The proof of the new estimate is elementary logarithm concavity, implemented
with Mathlib's `strictConcaveOn_log_Ioi`. Exact spectral factorization uses
Mathlib's Hermitian spectral theorem. The dependency relocation preserves
existing project proofs.

For standard DPP terminology, inclusion probabilities, and conditioning, see
Alex Kulesza and Ben Taskar, *Determinantal Point Processes for Machine Learning*,
arXiv:1207.6083, https://arxiv.org/abs/1207.6083.
This reference supports the probabilistic framework, not a claim that it
proves the new arithmetic hypotheses or an RH theorem. No novelty claim is made.
