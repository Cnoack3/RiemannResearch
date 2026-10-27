# Countable prime resampling: formal results and the RH obligation

27 October 2026. Continuation of `PrimeResamplingResearch20261027.md` in
`Cnoack3/RiemannResearch`. The development consists of 32 focused Lean modules.
The mathematical conclusions below concern the actual inverse-square law and
actual squarefree correction from the repository.

## Definitions and normalization

On positive integers, let
\[
Q(n)=\frac1{\zeta(2)n^2},\qquad
a(n)=\frac{n}{(8+\log n)^2},\qquad (Bf)(n)=\frac{f(n)}{n+1}.
\]
The null state zero is assigned zero weight. Write
\(n_{\perp p}=n/p^{v_p(n)}\) and \(R_p(n,k)=n_{\perp p}p^k\).
The complete transition at prime \(p\) replaces the exponent by the law
\(\pi_p(k)=(1-p^{-2})p^{-2k}\). Its positive rows sum to one, it satisfies
detailed balance, and it preserves Q. Self-loops are removed before summing
the conductances over all primes:
\[
W(n,m)=\sum_p Q(n)K_p(n,m)\mathbf1_{n\ne m}.
\]
The full countable form is an extended nonnegative real, rather than a real
infinite sum that would silently equal zero on nonsummable inputs:
\[
\mathcal D(g)=\frac12\sum_{n,m}W(n,m)(g(n)-g(m))^2\in[0,\infty].
\]

## Established results

1. **Actual averaging and exact energy.** For every QHilbert vector,
   \[
   (C_pf)(n)=\sum_{k\ge0}\pi_p(k)f(R_p(n,k)),\qquad
   \mathcal D(f)=\sum_p\|f-C_pf\|_Q^2.
   \]
   Each displayed geometric average is absolutely convergent. The operators
   are self-adjoint orthogonal projections, preserve the mean, and commute.
   Their common fixed space consists exactly of the constants. Signed
   rearrangements in the Dirichlet identity have proved summability premises.

2. **Sharp Poincare without an integrability premise.** For every real
   function on the nonnegative integers (zero has null weight),
   \[
   \frac12\sum_{n,m}Q(n)Q(m)(g(n)-g(m))^2\le\mathcal D(g).
   \]
   Both sides may be infinite. On L2(Q), the left side is the ordinary
   variance. Finite energy itself implies square integrability; an explicit
   anchor estimate is
   \[
   \mathbb E_Q g^2\le4\zeta(2)\operatorname{PairVar}_Q(g)+2g(1)^2.
   \]
   The centered dyadic residue is nonzero and saturates the inequality.
   Thus constant one is optimal. This strengthens the agenda's L1 formulation.

3. **Unconditional full raw-source bound.** The actual countable kernel has
   \(\sum_mW(n,m)\le Q(n)(n+1)\), and
   \[
   \mathcal D(\sqrt a\,Bf)\le\|f\|_Q^2/32.
   \]
   No kernel, rate, or independence provider remains as a hypothesis here.

4. **Zero-or-infinity correction criterion.** For the actual closed
   squarefree span V, let \(r=1-P_V1\) and \(b=P_VBr\). Then
   \[
   \boxed{\mathcal D(\sqrt a\,b)<\infty
      \iff r=0\iff\mathcal D(\sqrt a\,b)=0.}
   \]
   Equivalently, a nonzero r forces this complete Dirichlet energy to be
   infinite. Finite energy implies Mathlib's `RiemannHypothesis` through the
   existing squarefree-density bridge. No RH-to-squarefree-density implication
   is used or asserted.

5. **Weaker finite-grid criterion.** Put \(b_N=P_NBr_N\), and define
   \(\mathcal D_S(g)=\frac12\sum_{n,m\in S}W(n,m)(g(n)-g(m))^2\).
   Zero residual is equivalent to
   \[
   \exists C<\infty\;\forall S\subset\mathbb N\text{ finite}\;
   \forall N_0\;\exists N\ge N_0:\quad
   \mathcal D_S(\sqrt a\,b_N)\le C.
   \]
   The good stages may depend on S. These tests use only interior pairs and
   require no cutoff-boundary budget. If r is nonzero, these finite-grid
   energies diverge along every physical-head schedule H(N) tending to
   infinity, however slowly it grows.

6. **Actual legal-family obstruction.** In the repository's mixed-conductor
   legal family, the full projected prime energy diverges while the raw
   prime energy is at most 1/128 and residual norm is at most 1/2. Consequently
   no finite common C controls
   \(\mathcal D(\sqrt a\,PBr)\le C(\mathcal D(\sqrt a\,Br)+\|r\|^2)\)
   over that family. This rules out a universal legal-subspace transfer; it
   does not refute a special estimate for the canonical nested stages.

## Proof organization

The proof uses finite tensorization of commuting orthogonal projections and
Mathlib's projection convergence theorem. Prime-factor invariance identifies
the joint fixed space directly. No unproved infinite-product or tail-sigma-field
premise is introduced. A finite-grid clipping argument extends bounded-function
energy comparisons to arbitrary real functions without convergence of means.
The positive atom at one supplies square integrability from finite pair energy.
The repository's logarithmic residual-tail theorem then supplies the correction
criterion.

Principal declarations, under `RiemannResearch.RH`:

| Declaration | Owning file under `RH/` |
|---|---|
| `PrimeResampling.primeTransition_stationary` | `PrimeResamplingTransition.lean` |
| `QPrimeResampling.qSequence_C` | `QPrimeResamplingFormula.lean` |
| `QPrimeResampling.dirichletEnergy_qSequence_eq` | `QPrimeJumpEnergyIdentity.lean` |
| `QPrimeResampling.prime_resampling_poincare` | `QPrimeResamplingPoincare.lean` |
| `QPrimeResampling.prime_resampling_poincare_equality_witness` | `QPrimeDirichletSharpness.lean` |
| `QCountableJumpEnergy.rawSourceDirichletEnergy_le` | `QPrimeRawSourceEnergy.lean` |
| `QSquarefreePrimeDirichletCriterion.correctionDirichletEnergy_ne_top_iff_residual_zero` | `QSquarefreePrimeDirichletCriterion.lean` |
| `QSquarefreePrimeDirichletCriterion.riemannHypothesis_of_correctionDirichletEnergy_ne_top` | `QSquarefreePrimeDirichletCriterion.lean` |
| `QSquarefreePrimeDirichletCriterion.residual_zero_iff_frequently_finiteGrid_bound` | `QSquarefreePrimeFiniteGrid.lean` |
| `QLegalMixedConductor.no_uniform_prime_dirichlet_transfer` | `QLegalMixedConductorJumpObstruction.lean` |

## Remaining RH obligation

**Open:** establish one finite common C in the actual canonical finite-grid
criterion, or directly establish finite energy of the weighted limiting
correction. The raw-source estimate and generic projection properties do not
provide this bound. The mixture and near-pole covariance arguments in the
research agenda remain paper derivations. No unconditional proof of RH is
claimed.

## Provenance and verification

The requested statements originate in the user's `PrimeResamplingResearch20261027.md`.
Countable-product Poincare context: Decreusefond and Halconruy,
*Malliavin and Dirichlet structures for independent random variables*,
[arXiv:1707.07915](https://arxiv.org/abs/1707.07915).
Projection-limit proof input: Mathlib's
[`Projection.Submodule`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/Projection/Submodule.html).
Wolfram independently checked the elementary geometric normalization, zero-
valuation exit mass, dyadic mean 3/8 and variance 3/64; those computations
are sanity checks, not formal proof inputs.

The source modules are exported by `RiemannResearch.lean`. Publication uses
the repository's server checkpoint gate, including source audit and aggregate
plus changed-module compilation. Exact verification job and commit details
are supplied with the publication result.

Before publication, the saved modules compiled and eleven principal theorem
types and axiom dependencies passed audit job
`job_UgZYLTx-ZcCx4MXWI0bDZXIKscjgAmm2` (`verified: true`, exit code 0).
The audit reported 6.343 seconds of server verification, excluding request
round trips and polling. The inspected dependencies are exactly `propext`,
`Classical.choice`, and `Quot.sound`; no domain-specific axiom was introduced.
The active workspace was reused, so no workspace-opening request was needed.
