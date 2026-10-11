# Unconditional zeta-ordinate harmonic continuation

Date: 2026-10-11. Source agenda: `Zeta_Zero_Unconditional_Open_Research_Agenda_20261011(1).md`.

## Scope and logical status

This continuation develops priorities 1, 2 and 4, and a polynomial-level
approximation result relevant to priority 3. It does not formalize every paper
in the agenda's bibliography. It proves neither RH nor the full-zero shifted-zeta
approximation, BSY vanishing, Bagchi recurrence, or unrestricted correlation
conjectures. Unproved inputs occur as explicit theorem hypotheses; no axioms
stand in for the missing mathematics. Statements mentioning RH below are
unconditional equivalences or conditional implications, never uses of RH as
an established premise.

The companion `MovingFrequencyMobiusLaws20261011.md` contains paper proofs
from the unconditional FMZ lemmas. Its analytic limit laws are not represented
as completely formalized theorems. The Lean modules formalize the finite
algebra, actual-zero Gram construction, convergent positive energies, kernel
tails and the precise endpoint reduction described below.

## 1. A frequency-sensitive remainder without losing the negative square

For finite real weights and frequencies, Lean proves the exact identity

\[
\sum_{i,j}w_iw_j(u_i-u_j)^2
=2\Bigl(\sum_iw_i\Bigr)\Bigl(\sum_iw_i u_i^2\Bigr)
-2\Bigl(\sum_iw_i u_i\Bigr)^2.
\]

The identity allows signed weights and is invariant under common frequency
translation. For a complex Gram remainder with
`||R(i,j)|| <= eta + kappa*(u_i-u_j)^2`, it gives

\[
\left|\sum_{i,j}\overline{a_i}R_{ij}a_j\right|
\le\eta W^2+\kappa(2WU_2-2U_1^2),
\quad W=\sum|a_i|,\quad U_k=\sum|a_i|u_i^k.
\]

`FrequencySensitiveGramBounds.lean` proves this estimate, exact splitting
into diagonal, signed arithmetic matrix and remainder, and growing-support
convergence under convergence of the displayed complete budget. The entrywise
provider remains explicit. Positivity of eta or kappa is not needed separately
when the stated pointwise majorization is available.

`ActualDirichletPolynomialGram.lean` constructs the polynomial from actual
logarithmic integer frequencies, sums its squared modulus over actual zeta
zeros with analytic multiplicity, and proves the exact Gram equality. Its
prime-remainder theorem uses the existing signed von Mangoldt covariance
matrix. The sharp ordinate remainder bound is an explicit `hR` premise.

## 2. Stronger convergent horizontal energy

Write each actual nontrivial zero as rho=beta+i gamma and retain its positive
analytic multiplicity m. Define

\[
w_4(\rho)=\frac{m(\beta-1/2)^2}{(1+\gamma^2)^2},\qquad
w_2(\rho)=\frac{m(\beta-1/2)^2}{1+\gamma^2},\qquad E_j=\sum_\rho w_j(\rho).
\]

`ActualZeroSecondEnergy.lean` proves convergence of E2 using the existing
unconditional reciprocal-square zero sum. Both signs of gamma are retained.
It proves

\[
0\le E_4\le E_2\le\frac5{16}\sum_\rho
\frac{m}{1+|\gamma-i(\beta-1/2)|^2},\qquad E_2=0\iff RH,
\]
\[
\boxed{\sum_\rho\gamma^2 w_4(\rho)=E_2-E_4.}
\]

Every individual zero satisfies the quantitative bound

\[
m(\beta-1/2)^2\le E_2(1+\gamma^2).
\]

This improves the previous fourth-energy height factor while leaving energy
vanishing genuinely open. The second-moment identity is formalized as a sum
identity; a claim of formally verified differentiability of the kernel is not
made here.

## 3. An infinite beta-sensitive positive-definite kernel with full tails

Define

\[
K(u)=\sum_\rho w_4(\rho)e^{iu\gamma},\qquad
K_S(u)=\sum_{\rho\in S}w_4(\rho)e^{iu\gamma}.
\]

The generic module `SummableOrdinateKernel.lean` proves absolute convergence,
positive definiteness, the exact finite-plus-tail equality, a uniform tail
bound and a moving finite-character tail theorem. The actual specialization
`ActualHorizontalEnergyKernel.lean` proves

\[
K(0)=E_4,\quad |K(u)|\le E_4,\quad K(0)=0\iff RH.
\]

If the finite set S contains all actual zeros with gamma^2<H^2, then

\[
\boxed{\sup_{u\in\mathbb R}|K(u)-K_S(u)|
\le\sum_{\rho\notin S}w_4(\rho)
\le\frac{E_2}{1+H^2}.}
\]

The formal theorem expresses the supremum statement as a bound for every
real u and records the exact geometric cutoff hypothesis. It does not hide
this hypothesis in the definition of an arbitrary finite set.

For any changing finite frequency/coefficient family,

\[
\left|\sum_i a_iK(u_i)-\sum_i a_iK_S(u_i)\right|
\le\left(\sum_i|a_i|\right)\frac{E_2}{1+H^2}.
\]

Consequently coefficient mass o(1+H^2) controls the entire omitted kernel tail
uniformly in frequency. No ordinate equidistribution or zero-density hypothesis
is needed for these results.

## 4. A combined endpoint with two substantive open obligations

Let finite zero sets S_n satisfy the geometric cutoff condition at H_n. Let
A_n=sum_i|a_(n,i)| and assume A_n/(1+H_n^2) tends to zero. Define the exact moments

\[
F_n=\sum_i a_{n,i}K(u_{n,i}),\qquad
Z_n=\sum_i a_{n,i}K_{S_n}(u_{n,i}).
\]

Lean proves RH from the following two additional obligations:

1. **Detection, Open:** for a fixed theta<1, `|E4-F_n| <= theta*E4` for every n.
2. **Arithmetic cancellation, Open:** `Z_n -> 0` for the same concrete family.

The proof is complete: the tail theorem gives F_n-Z_n -> 0; hence F_n -> 0;
passing to the limit in detection gives E4 <= theta E4; nonnegativity forces
E4=0; the existing actual-zero equivalence gives Mathlib's RH.

Declaration: `riemannHypothesis_of_detecting_height_tests`.

This is a **conditional research reduction**. The paper laws for unweighted
zero averages do not supply either obligation for these beta-sensitive
moments. Any purported final step must explicitly construct and prove a
provider for both, for the same family. Setting the constant test equal to 1
meets detection but merely turns cancellation into the original energy-zero
problem; this is not progress on the open arithmetic step.

## 5. Paper-level growing Mobius harmonic analysis

The companion proves, from Ford--Meng--Zaharescu Lemmas 1--2, a growing
Dirichlet-polynomial second-moment formula with its full prime-power term.
For Mobius coefficients that secondary term is positive. Weighted frequency
dispersion removes a spurious log-squared support loss from the principal
remainder. The full internal polynomial tails are controlled in empirical L2.

With cutoff Y(T)=floor(log^2 T), the joint empirical laws of ordinary and
Mobius Dirichlet polynomials converge in the space of analytic functions on
Re s>1/2 to reciprocal Haar-random Euler products. More strongly, for every
fixed compact K in that half-plane,

\[
\frac1{N(T)}\sum_{0<\gamma\le T}
\sup_{s\in K}|Z_T(s;\gamma)M_T(s;\gamma)-1|\longrightarrow0.
\]

This is a paper deduction with an independent mathematical audit, not a
fully Lean-verified analytic law or an established novelty claim. It controls
actual growing arithmetic observables and their own tails. It does not
identify them with actual shifted zeta or reciprocal zeta. The latter
approximation remains the precise analytic bottleneck.

## 6. Agenda status and next formal providers

| Agenda priority | Delivered | Remaining |
| --- | --- | --- |
| 1: beta and moving frequencies | Existing beta-preserving formulas retained; exact frequency dispersion and actual Gram identities | Formal sharp FMZ ordinate remainder provider |
| 2: growing observables and tails | Lean complete kernel tails; paper full growing polynomial L2 tails | Formal integral/log-growth estimates and random analytic-law transfer |
| 3: full zero-sequence analytic approximation | Paper polynomial laws and joint reciprocal compatibility | Approximation to actual shifted zeta/reciprocal zeta |
| 4: positive all-zero defect | Stronger summable E2, beta-sensitive kernel, explicit tail rate, exact RH reduction | Actual detecting/cancelling family, or BSY upper bound |
| 5: Bagchi self-recurrence | No premise imported | Actual-zeta recurrence remains Open |
| 6: unrestricted correlation/all-zero test | No unsupported transfer from ordinate statistics | Correlation extension and beta-sensitive endpoint remain Open |

The bibliography's unaudited references remain unaudited; none is admitted
into Lean by declaration as an axiom. External analytic claims needed by a
formal theorem remain visible arguments to that theorem. The first concrete
formalization target after this continuation is the sharp actual-ordinate
FMZ provider, followed by the specific growing Mobius coefficient bounds.

## Sources and verification boundary

- Ford, Meng and Zaharescu, *Simultaneous distribution of the fractional parts
  of Riemann zeta zeros*, Lemmas 1--2, https://arxiv.org/pdf/1511.06814.
  Supports the analytic inputs of the companion paper proofs.
- The supplied agenda motivates the division between unconditional structure,
  open arithmetic providers and RH-equivalent endpoints.
- Existing `ActualZeroHorizontalEnergy.lean`, `ActualZeroOrdinate.lean`,
  `GrowingPhaseCovarianceAssembly.lean` and their checked imports supply the
  actual zero definitions, multiplicities, reciprocal-square convergence,
  reflection structure and signed arithmetic matrix.

The publication checkpoint verifies the changed modules and affected local
reverse dependents on the user's Lean server. It does not convert the
companion's prose proofs or the conditional hypotheses into Lean theorems.
