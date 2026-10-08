# Exact optimizer cancellation: Lean coverage and remaining providers

Source: the user-directed `Exact_Optimizer_Cancellation_20261008.tex` research
continuation. This note distinguishes exact checked declarations from the
remaining physical and arithmetic assembly. No proof of RH is claimed.

## Exact arithmetic and special-function results

- `RH/ZetaTwoPolygammaResidues.lean` identifies all reciprocal-power residue
  weights with the actual iterated derivatives of real `Complex.digamma`.
  It proves summability, positive weights, exact prefix/shifted-tail identities,
  and complete finite-period formulas for literal infinite arithmetic means
  and mixed moments. The representative of residue zero is retained as `L`.
- `RH/ZetaTwoMobiusQuarticFloor.lean` uses the actual finite Möbius trial and
  squarefree support. It retains both the complete floor tail and the full
  quotient-level summatory difference. It proves
  `0 <= squarefreeQuarticFloor N <= u_N^2 + 1/(3*zetaTwo*N)` for positive `N`.
  The variational floor is defined using literal infinite quartic energies.
- `RH/ZetaTwoMobiusQuarticFloorDecay.lean` calls the existing unconditional
  Mertens provider to prove `squarefreeQuarticFloor N * (6+log N)^a -> 0`
  for every fixed real `a`. No uniformity in `a` is asserted.
- `RH/ZetaTwoConductorFour.lean` proves the full finite-support-to-infinite-sum
  bridge for `f4=(1,-4,-9,16)`. Its squared norm is `30/Z`, its quadratic
  reciprocal-coordinate energy `<f4,D f4>` is `10/Z`, its target mean is zero,
  and its complete optimizer
  reciprocal row is `(5-4*c2-c3)/(12*Z)`.
- `RH/ZetaTwoDualBlock.lean` proves the full conductor-four/nine Gram and
  reciprocal Gram matrices, the determinants `4715` and `7164`, exact marked
  rows, and vanishing of all larger-conductor couplings.

## Exact Hilbert geometry

`Analysis/SignedOptimizerMoment.lean` defines the weighted floor, optimizer
mismatch and screening as actual squared Hilbert norms. Finite normal-equation
solutions exist even for redundant dictionaries. The complete identity is

\[
M_N=\varepsilon_N+\Gamma_N,
\qquad
\Gamma_N=\delta_N-s_N.
\]

For the reciprocal-coordinate multiplier, `M_N` is the unnormalized screened
second moment. The theorem identifies its norm representation with the actual
twice-compressed operator pairing when the multiplier is symmetric. Both
positive squares in `Gamma` remain in every identity. In particular

\[
-\varepsilon_N\le\Gamma_N,
\qquad
\Gamma_N^- /e_N\le\varepsilon_N/e_N.
\]

With the explicit input `epsilon_N/e_N -> 0`, the normalized second moment
vanishes exactly when either the complete normalized signed correction or
its positive part vanishes.

`Analysis/CompressedMomentZeroCriterion.lean` proves that cofinal normalized
screened-moment decay forces a strongly convergent residual sequence to have
zero limit, provided the continuous multiplier has a faithful quadratic form.
No monotonicity of normalized moments or extra norm bound is required.
The finite-dictionary consumer uses the actual normal equations and the
complete signed correction.

`LinearAlgebra/WeightedOptimizerResolvent.lean` proves the exact moving
weighted-optimizer resolvent identity using actual orthogonal projections.
The weighted normal equations, inverse metric relation and realizing linear
equivalence are exposed explicitly. Weighted optimizer completion retains
the entire displacement energy.

`LinearAlgebra/RankOneAnnihilatorSchur.lean` retains the rank-one square in
`K=D_A-(3/4)bb*`, its complete block normal equations, the marked first moment
and the higher-moment recurrence. Full ambient positivity supplies the
coupling inequality, hence `(3/4)D_A <= K <= D_A` at the quadratic-form level.
The conductor-four correction denominator is exactly `5760*Z*e`.

`LinearAlgebra/TwoVectorGramCompletion.lean` retains both the signed cross term
and the complete remainder:

\[
\|x\|^2=
\frac{158L_4^2-10L_4L_9+30L_9^2}{4715Z}
+\|x-\alpha f_4-\beta f_9\|^2.
\]

## Actual inverse-square optimizer and normalized floor

`RH/ZetaTwoHilbertSpace.lean` realizes the literal inverse-square probability
norm and its entire infinite pairing on real ℓ². It constructs the constant
target, actual residue atoms and reciprocal-coordinate continuous linear
operator, proving the latter symmetric, positive and faithful.

`RH/ZetaTwoReciprocalCompactness.lean` proves weak-to-strong convergence for
that actual operator from an exact finite-head/full-tail bound. The normalized
projection lemmas prove canonical unit residuals converge weakly to zero
when the unnormalized projection residual converges strongly to zero.

`RH/ZetaTwoOptimizerStage.lean` defines the actual cumulative squarefree
stages, their ordinary projection optimizer, and the weighted optimizer as
the projection of `D qOne` onto the corresponding `D`-image stage. Every
finite ordinary projection error is positive. The ordinary projection
residual converges strongly to the actual closed-span residual. The complete
Möbius trial energy is the weighted floor plus its full optimizer displacement square.
This discharges absolute quartic floor decay unconditionally.

Normalized floor decay is also unconditional. If the limiting residual is
nonzero, its error has a positive limit and ordinary division applies. If the
limiting residual is zero, canonical normalized residuals are weak-zero and
the actual reciprocal operator sends them strongly to zero. Trial domination
then gives `quarticFloor N / error N -> 0`, without an inverse-log lower bound.
Logarithmic rates for this normalized ratio still require a quantitative
provider; the compactness argument supplies the unconditional limit.
The negative part of the signed correction therefore also vanishes after
the same normalization. The actual squarefree closure criterion is exactly

\[
qOne\in\overline{\operatorname{span}\{g_d:d\ge2,\ d\text{ squarefree}\}}
\quad\Longleftrightarrow\quad
\Gamma_N^+/e_N\longrightarrow0,
\]

and its cofinal version has the same conclusion. No monotonicity of the
normalized moments or signed correction is used.

`RH/ZetaTwoParetoTransfer.lean` preserves the entire physical sequence under
the bounded map to Pareto space, with full norm comparison
`||toPareto f||² <= zetaTwo * ||f||²`. It preserves the target and residue
atoms, transfers the actual squarefree closure into the existing Mellin
theorem, and proves `riemannHypothesis_of_cofinal_positiveCorrection_decay`.
The positive correction decay is the remaining arithmetic hypothesis.

## Resolvent moment certificates

`Analysis/FiniteResolventRadau.lean` and `Analysis/ResolventRadauIntegral.lean`
prove the complete-square identity and both endpoint Radau remainders.
The second module uses actual integrals against arbitrary measures, including
infinite support. Nonnegative weights, normalization, support and polynomial
and reciprocal integrability are explicit. The four-moment normal equations
remain visible; the finite module also supplies exact Cramer coefficients
when its displayed determinant is nonzero. No decimal certificate is imported.

## Conditional research reductions and Open providers

| Obligation | Status and precise role |
|---|---|
| Positive signed cancellation `Gamma_N^+/e_N -> 0`, possibly cofinally | **Open**. This is the remaining arithmetic provider. It is not inferred from independence or individual positive-term bounds. |
| Actual lower bound `c <= e_N*(6+log N)` with `c>0` | **Open formal provider for relative logarithmic rates** here. Plain normalized floor convergence is supplied unconditionally by the actual compact projection geometry. The existing conditional transfer lemma also proves plain normalized convergence under this displayed lower bound. Stronger normalized logarithmic rate theorems are not claimed. |
| Bundled inverse-square optimizer specialization | Actual Hilbert space, multiplier, ordinary and `D`-image stages and optimizers, strong convergence of the ordinary projection residual, complete signed identity and unconditional normalized floor decay are supplied. The separate abstract inverse-metric resolvent equivalence remains an explicit operator input. |
| Actual spectral measure and rational caps for compressed physical operators | **Open assembly/certification** here. The Radau lemmas apply to a supplied actual measure; they do not construct it or prove the `3/16` and `3/20` caps. |
| RH-to-squarefree-approximation converse | **Open formal provider** in the existing squarefree transfer modules. No new unconditional RH equivalence is claimed without this input. |
| All-conductor Möbius dual totality specifically in a bundled inverse-square Hilbert space | **Open assembly** here. Existing Pareto totality is not mislabeled as the inverse-square representer theorem. |
| Cubic weighted floor and complete decimal stage certificates | Paper/computational material; not claimed as kernel-verified by these modules. |

The physical signed identity and the absolute floor estimate make the target
precise. They do not supply the target's positive cancellation estimate.

## Verification and scope

The continuation adds 20 Lean modules and 242 public theorems. Coherent
full-body source checks verify the complete proofs. The axiom audit visits
every public declaration, checks that it exists in the environment, and
rejects every dependency outside `propext`, `Classical.choice`, and
`Quot.sound`. Failed intermediate checks are not counted as verified results.
Native import and root-export checking is the publication checkpoint gate.

The central actual theorem is
`RiemannResearch.RH.ZetaTwoParetoTransfer.riemannHypothesis_of_cofinal_positiveCorrection_decay`.
Its cofinal positive signed-correction decay is an explicit hypothesis.
No such arithmetic decay proof, and no unconditional RH proof, is supplied.

## Provenance

- User-provided exact optimizer cancellation argument, 8 October 2026, supports
  the specialized statements and research agenda.
- NIST DLMF 5.15.1 supports the polygamma series terminology and classical
  formula: https://dlmf.nist.gov/5.15#E1. The Lean proof reuses actual derivative
  declarations in `CRTPolygammaSigns`, rather than a special-function axiom.
- Jean-François Burnol, *A lower bound in an approximation problem involving the
  zeros of the Riemann zeta function*, Advances in Mathematics 170 (2002), 56–70,
  https://arxiv.org/abs/math/0103058. This reference concerns the remaining
  lower-bound formal provider; it is not an imported Lean assumption.
