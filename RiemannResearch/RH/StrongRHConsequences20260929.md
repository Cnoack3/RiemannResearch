# Strong RH consequences of the three imported bridges

The strongest completed logical implication is now the **full Weil
equivalence for the repository's actual smooth arithmetic form**. The earlier
work supplied only the RH-to-positivity direction. The converse is proved by
constructing an admissible negative test from any hypothetical off-line zero.
This is a formalization of a classical RH criterion, not a proof of RH or a
claim of mathematical novelty.

## 1. Exact negative witness and the full equivalence

Write
\[
\mathcal M f(s)=\int_{\mathbb R}f(x)e^{-(s-1/2)x}\,dx,
\qquad \rho^*=1-\overline\rho.
\]
Let \(\mathcal S_{\exp}\) be the existing `SmoothSuperexponentialDecay`
class: smooth complex tests whose every derivative decays faster than every
exponential. Let \(\mathcal W(f,g)\) denote the complete
`arithmeticWeilPairing`, including all prime powers, the polar terms and the
gamma contribution. Its established, absolutely convergent spectral formula is
\[
\mathcal W(f,g)=\sum_\rho m_\rho
  \overline{\mathcal M f(\rho^*)}\mathcal M g(\rho),
\]
over the actual nontrivial zeta zeros with their actual analytic multiplicities.

**Proved negative-witness theorem.** If \(\rho\) is an actual off-line
zero, there exists \(h\in\mathcal S_{\exp}\) such that
\[
\boxed{\mathcal W(h,h)=-2m_\rho<0.}
\]
There is no simplicity assumption and no assumed spectral-interpolation
provider. The test is constructed from already proved analytic operations.

Consequently,
\[
\boxed{\mathrm{RH}\iff
  \mathcal W(f,f)\ge0\text{ for every }f\in\mathcal S_{\exp}.}
\]
Equivalently every finite smooth Weil matrix has nonnegative quadratic form;
requiring this for every two-test family already suffices. Nonnegativity means
nonnegativity of the real part; Hermitian symmetry proves that each diagonal
and quadratic value is real.

### Proof construction

For each actual zero \(\rho\), the explicit compact smooth seed
`compactLaplaceSeed ρ` has transform exactly one at \(\rho\). Apply the
actual conductor-two `nymanFullReturn` to it. The resulting admissible test
has transform
\[
F(s)=\operatorname{conductorZeta}_2(s)\mathcal M u(s).
\]
It vanishes at every actual zeta zero and has finite analytic order at
\(\rho\). Finiteness follows from the established conductor function and
\(\mathcal M u(\rho)=1\); no assertion that the zero is simple is made.

Whenever \(F(z)=0\), the actual spatial integral
\[
(R_zf)(x)=e^{(z-1/2)x}\int_{-\infty}^x
 e^{-(z-1/2)t}f(t)\,dt
\]
stays in \(\mathcal S_{\exp}\) and satisfies
\(F(s)=(s-z)\mathcal M(R_zf)(s)\). Induction on the finite analytic order
removes all multiplicity at the selected zero and preserves every other
transform zero. Normalization produces an actual test \(g_\rho\) with
\[
\mathcal M g_\rho(\sigma)=
\begin{cases}1,&\sigma=\rho,\\0,&\sigma\ne\rho,\end{cases}
\quad\text{for every actual zero }\sigma.
\]
For an off-line zero, \(\rho^*\ne\rho\). Take
\(h=g_\rho-g_{\rho^*}\). Only the two reflected terms survive in the
spectral formula, each equal to \(-m_\rho\). Reflection invariance of the
actual multiplicity completes the proof. Thus the former null Nyman family
is used as a seed for detecting zeros, rather than mistaken for a positive
definite Gram matrix.

Principal checked declarations:

- `exists_transform_zero_removed_of_order`
- `exists_transform_zero_removed`
- `exists_smooth_single_actual_zero_test`
- `exists_smooth_negative_weil_of_off_line`
- `riemannHypothesis_iff_arithmeticWeilPairing_nonneg`
- `riemannHypothesis_iff_smoothWeilMatrix_two_nonneg`
- `riemannHypothesis_iff_smoothWeilMatrix_nonneg`

## 2. The arithmetic imports give an explicit zero obstruction

Let \(S_n\) be the actual finite `divisorReciprocalStatistic`, formed from
the signed common-period divisor values at their certified cutoffs. The
previous result gives
\[
S_n\longrightarrow-r(1),\qquad r=1-P_V1,
\]
with finite approximation error at most \(H_n/\sqrt{n+1}\). That error
controls truncation of the correction statistic; it is not an effective
rate of convergence to the limiting residual.

Set
\[
\alpha=1+\frac{\sqrt2}{2},\qquad t=1-\frac{\sqrt2}{2}.
\]
The new exact factorization is
\[
\boxed{r(1)=\alpha\|r-tD_2r\|^2,\qquad
S_n\longrightarrow-\alpha\|r-tD_2r\|^2.}
\]
Here \(D_2\) is the actual Hilbert dilation, with
\(\|D_2r\|^2=2\|r\|^2\). This follows by completing the square in the
established identity \(r(1)=2\|r\|^2-\langle r,D_2r\rangle\).

For an actual zero \(\rho=\beta+i\gamma\), \(\beta>1/2\), the Mellin
annihilator identity and dilation formula imply
\[
\boxed{r(1)\ge B(\rho):=
\alpha\frac{2\beta-1}{|\rho|^2}
  |1-t2^{1-\rho}|^2.}
\]
The dyadic multiplier satisfies
\[
\alpha|1-t2^{1-\rho}|^2\ge2-\sqrt2,
\]
so this bound dominates the universal obstruction
\[
r(1)\ge(2-\sqrt2)\frac{2\beta-1}{\beta^2+\gamma^2}>0.
\]
In particular an actual zero to the right of the line forces the finite
statistic eventually below minus half this universal positive margin.

**Conditional quantitative exclusion.** If a real budget \(A\) satisfies
\[
\exists^\infty n:\quad S_n>-A,
\]
then every such zero must satisfy \(B(\rho)\le A\). Thus a proved budget
excludes every point where \(B(\rho)>A\). The simpler uniform consequence
excludes \(\beta\ge1/2+\delta\), \(|\rho|\le R\), whenever
\(A\ge0\), \(\delta>0\), and
\[
AR^2<(2-\sqrt2)2\delta.
\]
The arithmetic budget is an explicit open hypothesis, not a conclusion of
the imported Abel identities or their truncation certificates.

## 3. What is established and what remains open

| Imported area | Strongest completed consequence here | Remaining RH-level obligation |
|---|---|---|
| Smooth Weil matrices | Actual negative witness from every off-line zero; full RH equivalence | Prove arithmetic nonnegativity for every supported smooth test |
| Signed Abel tails | Signed statistic limit is an exact negative dyadic norm square | Prove its cofinal lower bound approaching zero |
| Certified finite corrections | Explicit zero-dependent obstruction and quantitative zero exclusion | Supply the arithmetic lower budget; finite truncation accuracy alone does not do so |

The three imports do not supply an unconditional positivity estimate or RH.
What has been removed is a genuine missing implication: smooth arithmetic
Weil positivity now implies RH with all witness construction discharged.
The arithmetic side now gives explicit geometric constraints on a possible
off-line zero, including its dyadic phase.

We do not assert an unconditional Lean equivalence between RH and residual
vanishing: the reverse density direction in this repository still has its
explicit Baez-Duarte analytic-provider obligation. A single finite sign
observation about \(S_n\) is not a certified zero exclusion.

## Provenance and verification

The classical Weil-criterion background is discussed by J.-F. Burnol,
[The Explicit Formula and a Propagator, arXiv:math/9809119](https://arxiv.org/abs/math/9809119),
and M. Suzuki,
[The screw line of the Riemann zeta-function and its applications](https://arxiv.org/abs/2209.04658).
The actual formal proof uses the repository's imported explicit formula,
compact interpolation, Nyman full-return, analytic-order and integral
zero-removal theorems. No external paper is an axiom in the Lean proof.

Wolfram checked the elementary two-by-two eigenvalue/sign calculation and
positivity of the uniform zero margin. Lean supplies the proof verification.
Audited endpoints depend only on `propext`, `Classical.choice`, and
`Quot.sound`; theorem hypotheses remain exactly as stated above.
