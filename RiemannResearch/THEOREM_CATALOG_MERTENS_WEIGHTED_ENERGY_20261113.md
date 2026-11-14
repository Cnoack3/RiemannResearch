# Reciprocal density, weak compactness, and actual Mertens energy

13 November 2026. Source: the user-provided
`Reciprocal_Residue_Density_and_Direct_RH_Agenda (1).tex`.

The finite-matrix and signed-energy part of Step 1 is formalized. Weak-star
compactness simplifies the bounded-lifting argument without separability.
Step 2 now includes the direct analytic zero-exclusion theorem and the implication
from all positive weighted Mertens energies to RH. The proof uses the actual
first-difference Dirichlet series and no external analytic provider.
**The small-damping arithmetic energy bound and the reverse RH-to-energy
implication remain Open. No unconditional proof of RH is claimed.**

The existing `RH/QReciprocalFullDensity.lean` supplies the unconditional
full-conductor reciprocal density and its physical P transfer. Its finite
factorial sieve and coordinate recovery are reused as established context;
this change does not reprove them or infer an undamped norm bound from them.

## Weak-star compactness: what is gained

The existing `Analysis/HilbertWeakCompactness.lean` transports Mathlib's
Banach--Alaoglu theorem through Riesz representation. For a complete real
Hilbert subspace S, its norm ball is weakly compact.

`Submodule.exists_mem_of_bounded_test_limits` now maps that compact ball into
the product of all prescribed scalar test values. The image is compact and
therefore closed in the Hausdorff product. A pointwise limit of the test values
belongs to the image. This proves simultaneous interpolation with the same
norm bound, without choosing a subsequence or assuming separability.

The strengthened existing declarations are:

- `Submodule.exists_mem_of_bounded_test_limits`
- `Submodule.bounded_finite_test_feasibility_iff`
- `Submodule.bounded_lp_head_image_feasibility_iff`
- `Submodule.exists_mem_of_bounded_image_tendsto`
- `Submodule.mem_of_bounded_injective_image_tendsto`
- `Submodule.mem_of_bounded_subsequence_injective_image_tendsto`

They live in `Analysis/BoundedWeakInterpolation.lean` and
`Analysis/BoundedInjectiveLift.lean`. The corresponding physical D statements
in `RH/QReciprocalTargetLift.lean` also lose the unnecessary separability
premise. The distinct weak-subsequence extraction theorem retains its
separability assumption; it has not been silently generalized.

For a bounded linear injective T, the exact conclusion is

\[
v_j\in S,\quad \|v_j\|\le C,\quad Tv_j\longrightarrow Tx
\quad\Longrightarrow\quad x\in S,\quad\|x\|\le C.
\]

Compactness of T is unnecessary. The source-norm bound is indispensable.
The previously formalized `QReciprocalMeanZeroCounterexample` and
`QReciprocalLiftDivergence` remain relevant. A bound on Tv_j or a separate bound
on each finite coordinate head does not supply the bound above.

For the physical operator Df(n)=f(n)/n, `bounded_D_lift_iff_mem` already
identifies bounded approximate lifting with membership. Thus using compactness
does not turn unconditional density of the damped atoms into undamped density.

## Finite identities: actual Mobius coefficients throughout

The new generic module is
`LinearAlgebra/FiniteCumulativeSignedEnergy.lean`, in namespace
`RiemannResearch.LinearAlgebra.CumulativeCellEnergy`.

With A_j=sum_{i<j} a_i and W_{N,j}=sum_{j<=n<N} w_n, it proves

\[
\sum_{n<N}w_n A_{n+1}^2
=\sum_{j<N}a_j^2W_{N,j}
+2\sum_{j<N}\sum_{i<j}a_i a_j W_{N,j}.
\]

Principal declarations:

- `tailWeight_eq_sum_ite`
- `weighted_cumulative_eq_sum_tail`
- `weightedPrefixEnergy_eq_diagonal_add_offDiagonal`
- `offDiagonalEnergy_eq_pair_sum`
- `diagonalEnergy_le_linear_weight`
- `bounded_prefixEnergy_iff_bounded_offDiagonal`
- `summable_prefixEnergy_iff_bounded_offDiagonal`

The arithmetic module is `RH/MertensWeightedEnergy.lean`, in namespace
`RiemannResearch.RH.MertensWeightedEnergy`. Its coordinate n represents
the positive integer n+1. `mertensPrefix_eq_mobius_sum` identifies its prefix
with the literal sum of mu(k), 1<=k<=N.

| Exact result | Declaration |
|---|---|
| L_N mu_N = 1 | `floorMatrix_mulVec_mobius` |
| det L_N = 1 and L_N inverse applied to 1 equals mu_N | `floorMatrix_det`, `floorMatrix_inv_one` |
| C_N applies cumulative summation | `cumulativeMatrix_mulVec` |
| K_N = C_N transpose W_N C_N is positive definite | `gramMatrix_posDef` |
| K_N(i,j) equals the complete finite suffix weight | `gramMatrix_entry` |
| E_epsilon(N) = mu_N transpose K_N mu_N | `finiteEnergy_eq_mobius_gram` |
| E_epsilon(N) = 1 transpose L_N inverse-transpose K_N L_N inverse 1 | `finiteEnergy_eq_inverse_floor_quadratic` |
| Exact diagonal plus signed off-diagonal decomposition | `finiteEnergy_identity`, `offDiagonal_pair_sum` |
| Nonnegativity and monotonicity in N | `finiteEnergy_nonneg`, `finiteEnergy_monotone` |
| Diagonal bounded by the convergent p-series sum n^(-1-2epsilon) | `diagonal_le_pseries` |
| Finite total energy iff bounded finite energies | `hasFiniteEnergy_iff_bounded_finiteEnergy` |
| For epsilon>0, finite total energy iff uniformly upper-bounded signed cross terms | `hasFiniteEnergy_iff_bounded_offDiagonal` |

`HasFiniteEnergy` is a `Summable` proposition. It does not mistake Lean's
totalized real `tsum` for a finite value when a series diverges. No absolute
values replace the off-diagonal signs. The matrix claims also handle N=0.
There is no uniform norm bound for L_N inverse in these statements.

## First analytic implication

`RH/MertensWeightedMoments.lean` proves
`summable_absolute_mertens_moment`:

\[
\sum_{n\ge1}M(n)^2 n^{-2-2\varepsilon}<\infty,
\qquad \sigma>\tfrac12+\varepsilon
\quad\Longrightarrow\quad
\sum_{n\ge1}|M(n)|n^{-1-\sigma}<\infty.
\]

The proof factors each summand into two square-summable factors and uses
the elementary square inequality. The strict half-plane margin is exactly
what makes the second p-series converge. The declaration does not assume
RH. Its downstream consumer `RH/MertensEnergyRH.lean` now constructs the
holomorphic reciprocal-zeta extension from these moments.

## Agenda coverage and remaining obligations

| Step | Status after this work | Remaining task |
|---|---|---|
| 1: finite identities | Formalized | No uniform arithmetic estimate follows from positivity. |
| 2: direct zero exclusion | Formalized in MertensEnergyRH | Supply the arithmetic energy premise; the analytic continuation is no longer an external input. |
| 3: dyadic Mertens estimate | Exact energy/block reductions formalized | Prove the arithmetic bound uniformly over all dyadic blocks and positive exponent losses approaching zero. |
| 4: CRT cross terms | Complete signed block identity formalized; CRT estimate Open | Control the actual signed correlations together with the inherited head and its interaction. |
| 5: weaker damping | Open beyond previously checked reciprocal density | Formalize the alpha>1/2 paper extension and investigate the critical range without assuming an RH-level provider. |
| 6: existing minimizers | Open | Derive a comparison with the complete residue inverse-Gram costs; these matrices are different. |
| 7: reverse implication | Open formalization | Supply the RH-to-Mertens growth theorem or its analytic ingredients in Lean. |

The precise remaining arithmetic target is

\[
\forall\varepsilon>0\ \exists B_\varepsilon\in\mathbb R\ \forall N,
\quad \mathcal O_\varepsilon(N)\le B_\varepsilon.
\]

The checked equivalence identifies this with the all-epsilon weighted-energy
condition, and the new checked analytic bridge proves that it implies RH.
The converse from RH remains an open formalization task; no RH iff is claimed.
A positive sequence of damping exponents tending to zero suffices. At each
damping, a single upper bound need hold only at arbitrarily late cutoffs.

## Sources and external computation

- Mathlib's [weak-dual module](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Normed/Module/WeakDual.html)
  supplies the Banach--Alaoglu theorem used by the existing Hilbert transport.
- K. Soundararajan, *Partial sums of the Mobius function*, J. reine angew.
  Math. 631 (2009), 141-152, [arXiv:0705.0723](https://arxiv.org/abs/0705.0723),
  introduction. This records the classical RH/Mertens growth equivalence.
  Its RH-dependent estimates are not unconditional arithmetic providers.
- Wolfram Language checked the exact floor inversion, cumulative Gram energy,
  signed splitting, and positive definiteness for N=4,8,16 at epsilon=1/2.
  For N=4 it returned E=1819/1728, diagonal=811/576, and off-diagonal=-307/864.
  These finite checks are external corroboration, not an asymptotic proof.

## Verification

The full finite algebra, inverse-floor quadratic, kernel-entry identity,
and the strengthened compactness modules passed focused Bazel/BuildBuddy
verification in `job_-GvBMutAsX8T5vEORGHvfn7BHkFt1u-O` (25.273 seconds of
server verification). Earlier focused acceptance was
`job_R4oSPsLwVy9fzsjGKC1PCx3fGdkQTw5d` (28.199 seconds).

The persisted moment theorem and physical D specialization passed the focused
import check `job_2tEDQ_URB-W17TkcvQoIbOiEbaIcpgW1` (102.953 seconds of server
verification). These times exclude workspace creation and polling delays.

The queued axiom guard `job_43m8gj7FZBxrNHVKhDqaUnSoBfjlNC7L` passed with
`#guard_msgs` checking the exact `#print axioms` output for the interpolation,
injective lifting, signed-energy equivalence, inverse-floor quadratic,
Gram positivity, kernel entry, and absolute-moment theorem. Every checked
list was exactly `propext`, `Classical.choice`, and `Quot.sound`. This guard
also recompiled the final arithmetic source with its helper kept private;
server verification took 43.972 seconds. Axiom inspection does not discharge
the explicit energy or boundedness hypotheses of these theorems.

The baseline full-project checkpoint `job_cUjCOE-AuUI43XxJ8qLUr4xLgR0gzzkX`
completed successfully (verified=true, exit_code=0), with 390.413 seconds
of server verification, and pushed commit
`4f21b88349ebc98a8d98d5ee2ef032924c289633`:
https://app.buildbuddy.io/invocation/b7b9bf84-0720-4eb5-8cc4-3f39a03f224f .
The retained terminal record was reread for this continuation. Subsequent
changes require their own full-project checkpoint.

## Direct analytic bridge: 13 November follow-up

New module: `RH/MertensEnergyRH.lean`. Namespace:
`RiemannResearch.RH.MertensWeightedEnergy`.

Define the actual series

    F(s) = sum_{n>=1} M(n) [n^(-s) - (n+1)^(-s)].

Finite Abel summation retains the complete boundary term:

    sum_{n=1}^N mu(n)n^(-s)
      = sum_{n=1}^N M(n)[n^(-s)-(n+1)^(-s)] + M(N)(N+1)^(-s).

The elementary bound |M(N)|<=N makes the boundary tend to zero for Re(s)>1.
The weighted-energy moment theorem makes F normally convergent locally on
Re(s)>1/2+epsilon, for epsilon>=0. Initial equality with 1/zeta(s) follows
from the actual Mobius L-series. Analytic continuation uses the proved
regularZetaRatio identity; the pole at s=1 is handled by that regularization.

| Result | Exact declaration |
|---|---|
| Finite Abel identity including boundary | `finite_mertens_abel` |
| Boundary convergence in the initial half-plane | `mertens_abel_boundary_tendsto` |
| Absolute convergence from energy | `mertensTransform_summable` |
| Local analyticity on Re(s)>1/2+epsilon | `mertensTransform_analyticOnNhd` |
| Initial reciprocal-zeta identity | `mertensTransform_eq_inv_zeta` |
| Continued regularized identity | `regularZetaRatio_mul_mertensTransform` |
| One finite energy excludes zeros strictly to its right | `zeta_ne_zero_of_hasFiniteEnergy` |
| A zero forces failure of the corresponding energy | `not_hasFiniteEnergy_of_zero` |
| A zero forces full energies to tend to +infinity | `finiteEnergy_tendsto_atTop_of_zero` |
| For epsilon>0, it also forces signed off-diagonal sums to +infinity | `offDiagonal_tendsto_atTop_of_zero` |
| All positive energies imply RH | `riemannHypothesis_of_hasFiniteEnergy_forall` |
| All positive signed uniform bounds imply RH | `riemannHypothesis_of_bounded_offDiagonal_forall` |
| A damping sequence tending to zero suffices | `riemannHypothesis_of_energy_along_damping` |
| Positive damping sequence plus frequent signed bounds implies RH | `riemannHypothesis_of_frequently_bounded_offDiagonal_along_damping` |

Four supporting results are added to the owning energy module:

- `mertensPrefix_abs_le`: the actual elementary arithmetic bound.
- `hasFiniteEnergy_mono`: increasing the damping preserves finite energy.
- `hasFiniteEnergy_of_half_lt`: unconditional finiteness for epsilon>1/2.
- `hasFiniteEnergy_iff_frequently_bounded_offDiagonal`: for epsilon>0,
  one upper bound at arbitrarily late cutoffs is equivalent to finite energy.
  This uses monotonicity of total energy and the proved diagonal bound;
  it does not assert monotonicity of the signed cross term.

Together the change adds 19 theorems and the definition `mertensTransform`.
The single-zero results retain epsilon>=0, Re(s)>1/2+epsilon and s!=1.
The signed divergence result requires epsilon>0. No simplicity assumption
or assertion that an off-line zero exists is made.

### Exact remaining arithmetic obligation

Choose epsilon_j>0 with epsilon_j->0. Prove, for each j, one finite B_j
such that for every cutoff K some N>=K satisfies

    offDiagonal epsilon_j N <= B_j.

The bound may depend on j, but not on N or K. Equivalently, establish finite
weighted Mertens energy along this damping sequence. This is a
**conditional research reduction** until an arithmetic provider is proved.
The elementary epsilon>1/2 baseline does not supply dampings tending to zero.
The existing CRT canonical-growth, Q-only forcing and density leakage
obligations are not discharged by this analytic bridge.

### Follow-up verification

The coherent 20-declaration candidate passed queued Bazel/BuildBuddy acceptance
in `job_LUj2kNdYHCn5ndP_-rotIlGb8VkYM2FS` (19.019 server seconds):
https://app.buildbuddy.io/invocation/9d59792f-b588-4b9d-b0d5-8d650a3e11f3 .
This is focused candidate evidence. The persisted module split is separately
audited, and publication requires the terminal full-project checkpoint.


The persisted owning modules and eight pivotal declarations passed exact
`#guard_msgs (whitespace := lax)` axiom guards in `job_aCQpBd-SmaZ59rI0lH1gRjVjzY2bXSBB`
(38.15 server seconds, verified=true, exit_code=0):
https://app.buildbuddy.io/invocation/91490f1f-9405-4dc3-8d05-b35239dcdfd3 .
The guards require exactly `propext`, `Classical.choice`, and `Quot.sound`
for analyticity, finite Abel summation, initial reciprocal-zeta equality,
zero exclusion, signed divergence, the unconditional baseline, frequent-bound
equivalence, and the final damping-sequence RH criterion. They do not discharge
the explicit energy or arithmetic boundedness hypotheses. The audit source
SHA-256 is `4ca8b9ecd3fb36faee2b328e6269828443b3fdb187934623befc5aaa94305b49`.

## Reusable Mellin convergence and exact pole normalization

Continuation of `Mertens_Weighted_Energy_Weak_Star_Continuation(1).md`.
The direct analytic bridge published concurrently at
`f3380fd6b8e228d87757e1c08ced9eda210b3a05` is retained as the canonical
implementation. Its stronger damping-sequence and signed-divergence results
are preserved. No competing Mertens series or duplicate RH criteria are introduced.

The new general-purpose module `Analysis/FirstMellinSeries.lean` takes
arbitrary complex coefficients a(n) and proves that

    sum_{n>=1} ||a(n)|| n^(-1-q) < infinity, q>0

implies convergence of sum a(n)[n^(-s)-(n+1)^(-s)] for Re(s)>=q and
analyticity for Re(s)>q. Its local majorant controls the full infinite series,
not just individual terms. The actual Mertens analyticity theorem now applies
this reusable result to the previously checked absolute-moment theorem.

| Result | Exact declaration | Hypotheses |
|---|---|---|
| Absolute convergence | `Cesaro.firstMellinSeries_summable` | q>0, summable absolute moment, Re(s)>=q |
| Local complex differentiability | `Cesaro.firstMellinSeries_differentiableAt` | Same moment, Re(s)>q |
| Analyticity on the open half-plane | `Cesaro.firstMellinSeries_analyticOnNhd` | q>0 and summable absolute moment |
| Reciprocal value at one | `mertensTransform_one_eq_zero` | 0<=epsilon<1/2, HasFiniteEnergy epsilon |
| Simple zero with derivative one | `mertensTransform_hasDerivAt_one` | 0<=epsilon<1/2, HasFiniteEnergy epsilon |
| Reciprocal identity on the full energy half-plane | `mertensTransform_eq_inv_zeta_of_hasFiniteEnergy` | epsilon>=0, HasFiniteEnergy epsilon, Re(s)>1/2+epsilon, s!=1 |

The generic declarations have namespace
`RiemannResearch.Analysis.Cesaro`; the arithmetic declarations retain
`RiemannResearch.RH.MertensWeightedEnergy`.

The statements F(1)=0 and F'(1)=1 concern the analytic extension of
1/zeta. They use the regularized identity and
`Burnol.regularZetaRatio_one`. They do not evaluate the pole through
Lean's totalized value of `riemannZeta 1`.

### Arithmetic investigation and remaining boundary

Wolfram corroborated the exact finite Abel identity at N=4,8,16 for s=3+2i.
An independent finite numerical scan retained the signs in
E_epsilon=diagonal+offDiagonal. At N=10000 it gave:

| epsilon | E_epsilon(N) | diagonal | offDiagonal |
|---|---:|---:|---:|
| 0.05 | 1.86519392921 | 4.94362740640 | -3.07843347719 |
| 0.10 | 1.67168110517 | 3.77416705182 | -2.10248594665 |
| 0.25 | 1.34630873086 | 2.28166493550 | -0.93535620464 |

These finite computations do not prove boundedness at arbitrarily large
cutoffs. Soundararajan's cited paper was reread: its strengthened growth
estimate assumes RH, so it supplies no unconditional arithmetic input here.
Weak-star compactness still requires the complete undamped source-norm bound.
The exact remaining target is the positive damping sequence and frequent
signed bound recorded above; neither pole normalization nor the holomorphy
refactor proves that target.

### Continuation verification

The three arithmetic extensions passed focused Bazel/BuildBuddy acceptance
in `job_mog80ZZonhE4BAgzk5FO4YP-B4nIZcLn` (33.143 server seconds,
verified=true, exit_code=0):
https://app.buildbuddy.io/invocation/865cb404-9cbb-46e2-bfbf-1e48129fe9e2 .

After persistence, eight pivotal declarations passed exact axiom guards in
`job_T3GtVAcGSOE6HDNwypgjNERN3LXTIyuW` (22.083 server seconds,
verified=true, exit_code=0):
https://app.buildbuddy.io/invocation/c67e8819-5671-4bc3-a16d-b5f00132b119 .
The audited declarations are the generic analyticity theorem, actual Mertens
analyticity, the value and derivative at one, the extended reciprocal identity,
finite Abel summation, signed divergence, and the final frequently bounded
damping-sequence RH criterion. Each list is exactly
`propext`, `Classical.choice`, and `Quot.sound`.
Audit code SHA-256:
`635ccb6c92f2e5f879730a9ab8e940f10d3142722eb927db7deb8be2c5d8d2a8`.

No `sorry`, `admit`, or new axiom is used. All energy premises remain
explicit; the axiom audit does not discharge them.

The final publication evidence is the terminal checkpoint attached to the
commit containing this section. No full-project success is inferred from
focused verification alone.

## Dyadic energy and complete block cancellation: 14 November continuation

The handoff was reconciled against published main
`24c7355cf07d2f756cf7103b01232977c4cc8300`. The analytic bridge, exact
normalization at s=1, signed convergence, and unconditional epsilon=1/2
endpoint were already present. This continuation adds 23 theorems and four
definitions without duplicating those results.

New arithmetic module: `RH/MertensDyadicEnergy.lean`.
The RH applications extend `RH/MertensEnergyRH.lean`.
Both use namespace `RiemannResearch.RH.MertensWeightedEnergy`.
Two general shifted-prefix identities extend the existing namespace
`RiemannResearch.LinearAlgebra.CumulativeCellEnergy` in
`LinearAlgebra/FiniteCumulativeSignedEnergy.lean`.

### Exact dyadic reduction

For X=2^j, put

    H(X) = sum_{X < n <= 2X} M(n)^2,
    A_epsilon(j) = X^(-2-2epsilon) H(X).

The exact finite grouping retains the initial M(1)^2=1. The weighted block
sum lies between 2^(-2-2epsilon) A_epsilon(j) and A_epsilon(j) when
epsilon>=0. Consequently:

    HasFiniteEnergy epsilon
      iff Summable (fun j => A_epsilon(j)).

In particular A_epsilon(j)->0 under that energy premise. A mere bound on
A_epsilon at a single exponent does not establish its summability.

For every positive epsilon, finite energy is equivalent, as a family of
conditions, to

    for every delta>0 there is a finite C_delta such that
    for every j, H(2^j) <= C_delta (2^j)^(2+2delta).

The sufficient direction uses a strict margin delta<epsilon; the normalized
block majorant is C_delta [2^(2delta-2epsilon)]^j. This margin is not omitted.
A single positive sequence delta_k->0 suffices, with one constant for each
k and the bound holding on every dyadic scale. These are **conditional
research reductions**: no small-loss arithmetic provider is supplied.

| Result | Exact declaration |
|---|---|
| Exact finite dyadic decomposition, including the initial term | `finiteEnergy_dyadic_identity` |
| Fixed-damping energy iff summable normalized blocks | `hasFiniteEnergy_iff_summable_dyadic` |
| Block bound with strict exponent margin gives finite energy | `hasFiniteEnergy_of_dyadic_block_bound` |
| Finite energy gives a uniform bound at its own exponent | `dyadic_block_bound_of_hasFiniteEnergy` |
| All positive energies iff all positive-loss block bounds | `energy_forall_iff_dyadic_block_bounds` |
| Normalized blocks vanish under finite energy | `dyadicNormalizedEnergy_tendsto_zero` |
| Dyadic block bounds imply RH | `riemannHypothesis_of_dyadic_block_bounds` |
| A countable positive loss sequence tending to zero suffices | `riemannHypothesis_of_dyadic_bounds_along_damping` |
| A zero beyond 1/2+delta forces normalized dyadic blocks to be unbounded | `dyadicNormalizedEnergy_unbounded_of_zero` |

The last theorem requires delta>=0, Re(s)>1/2+delta, s!=1, and zeta(s)=0.
It concludes that for every real C there is a scale j with C<A_delta(j).
It does not assume a zero exists, or claim A_delta(j)->infinity.

### Complete signed block identity

With positive-integer indexing, let

    D(X) = sum_{j=1}^X (X-j+1) mu(X+j)^2,

    C(X) = 2 M(X) sum_{j=1}^X (X-j+1) mu(X+j)
         + 2 sum_{1<=i<j<=X} (X-j+1) mu(X+i) mu(X+j).

Then `blockSquareSum_signed_identity` proves exactly

    H(X) = X M(X)^2 + D(X) + C(X).

Here D is `blockDiagonal`, and C is `signedBlockCross`.
The first term in C is the interaction with the inherited head M(X).
The second preserves all signed within-block pairs. Both are needed.

The unconditional bounds 0<=D(X)<=X^2 imply that the all-positive-loss
block condition is equivalent to the signed condition

    for every delta>0 there is C_delta such that, for every dyadic X,
    X M(X)^2 + C(X) <= C_delta X^(2+2delta).

This equivalence is `dyadic_block_bounds_iff_signed_cancellation`;
its RH consequence is `riemannHypothesis_of_dyadic_signed_cancellation`.
The head square has not been removed from the arithmetic obligation.

The general `shifted_weightedPrefixEnergy_identity` proves the full
head-square, head-interaction, diagonal and off-diagonal decomposition
for arbitrary real weights and coefficients, without positivity assumptions.
The companion prefix identity is `cumulative_add_shift`.

### External computation and the open arithmetic step

Wolfram independently checked the exact block decomposition at
X=2,4,8,16,32. At X=32 it returned

    H=136, head square=512, head interaction=-560,
    diagonal=344, within-block cross=-160.

Thus 136=512-560+344-160. This illustrates the signed cancellation that
would be lost by deleting the head interaction or replacing signs by
absolute values. A further finite scan through X=131072 gave
H(X)/X^2=0.02538249071 and
[X M(X)^2+C(X)]/X^2=-0.2785395929 at that last scale.
These are external finite computations, not an asymptotic proof.

Soundararajan, *Partial sums of the Mobius function*,
https://arxiv.org/abs/0705.0723, introduction and Theorem 1, was reread.
Its strengthened Mertens growth estimate assumes RH. It cannot supply the
unconditional small-loss block bound needed here.

**Open:** prove one of the equivalent arithmetic bounds at losses tending
to zero, uniformly over all dyadic scales. The current epsilon=1/2 endpoint
and its logarithmic refinements do not supply that. The existing weak-star
lifting theorem still needs a complete undamped source-norm bound.
No CRT correlation estimate, RH-to-Mertens converse, or RH proof is claimed.

### Verification for this continuation

The coherent 23-theorem candidate passed Bazel/BuildBuddy acceptance in
`job_aLCQOBSqguPgcreu1ponvbSoMR76YN9E` (45.458 server seconds,
verified=true, exit_code=0):
https://app.buildbuddy.io/invocation/595730d4-e487-43aa-9555-0ae796b30740 .

The persisted modules and eight pivotal declarations passed exact axiom
guards in `job_0ZWOsyunMWBszszzdUhKOAPCAKiwoZlf` (37.716 server seconds,
verified=true, exit_code=0):
https://app.buildbuddy.io/invocation/12075b9b-0d71-4d8e-a958-eed21837541d .
Each audited dependency list is exactly `propext`, `Classical.choice`,
and `Quot.sound`. The guards cover the shifted identity, exact finite
grouping, fixed-energy equivalence, all-energy block equivalence, complete
signed identity, signed-condition equivalence, damping-sequence RH criterion,
and zero obstruction. They do not discharge the arithmetic hypotheses.
Audit source SHA-256:
`9640d60cd56e11a5a2ae47831663a7ef5978db16c727c239544abd4f6b7722de`.

Final publication is gated by the terminal full-project checkpoint attached
to the commit containing this section. Focused acceptance is not represented
as full-project verification.
