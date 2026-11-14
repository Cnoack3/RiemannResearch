# Reciprocal density, weak compactness, and actual Mertens energy

13 November 2026. Source: the user-provided
`Reciprocal_Residue_Density_and_Direct_RH_Agenda (1).tex`.

The finite-matrix and signed-energy part of Step 1 is formalized. Weak-star
compactness simplifies the bounded-lifting argument and removes its unnecessary
separability assumption. The first discrete absolute-moment implication in
Step 2 is formalized. **The uniform arithmetic bound, the direct analytic
zero-exclusion theorem, and an RH equivalence for these energies remain open
formalization/research obligations. No proof of RH is claimed.**

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
RH and does not construct or identify a holomorphic reciprocal zeta function.

## Agenda coverage and remaining obligations

| Step | Status after this work | Remaining task |
|---|---|---|
| 1: finite identities | Formalized | No uniform arithmetic estimate follows from positivity. |
| 2: direct zero exclusion | Absolute moment input formalized | Construct the locally holomorphic Mellin expression, identify it with 1/(s zeta(s)), and exclude zeros. |
| 3: dyadic Mertens estimate | Open | Prove the bound uniformly over all blocks and every positive exponent loss. |
| 4: CRT cross terms | Open | Derive and control the actual signed induced correlations. Finite positivity is insufficient. |
| 5: weaker damping | Open beyond previously checked reciprocal density | Formalize the alpha>1/2 paper extension and investigate the critical range without assuming an RH-level provider. |
| 6: existing minimizers | Open | Derive a comparison with the complete residue inverse-Gram costs; these matrices are different. |
| 7: reverse implication | Open formalization | Supply the RH-to-Mertens growth theorem or its analytic ingredients in Lean. |

The precise remaining arithmetic target is

\[
\forall\varepsilon>0\ \exists B_\varepsilon\in\mathbb R\ \forall N,
\quad \mathcal O_\varepsilon(N)\le B_\varepsilon.
\]

The checked equivalence identifies this with the all-epsilon weighted-energy
condition, not yet with a checked direct RH iff. The attached paper supplies
the informal analytic bridge; it is not inserted as a Lean hypothesis named
like an established theorem.

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

The final persisted sources, moment implication, and downstream consumers are
subject to the final full-project checkpoint. Its retained job record is the
publication evidence; focused checks alone do not certify the whole project.
