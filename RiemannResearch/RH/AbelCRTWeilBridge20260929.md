# Exact Abel–CRT–Weil bridges, 2026-09-29

Continuation requested from 4208a0054cbe5b1ee54b5b8d19eefd70e58331ac.
The working source is its direct successor 9122d5e05058475a3fc9fbbac983c19fbb4a20ec;
the weighted-divisor and quadratic-zero results already present there are reused.

## Result and remaining gap

This development gives (1) an exact CRT expression for the actual Abel row and
each kernel difference, (2) a finite expansion in actual integer zeta values
with a uniform geometric Hilbert-energy remainder, and (3) actual finite Weil
forms and mixed Weil entries using exactly the same correction primitive.
It does not prove cancellation of that primitive or RH. No novelty claim is made.

The important unconditional estimate is uniform in the growing coefficient
dimension: the finite zeta/CRT approximation has error at most
2^(-M) times the norm of the fixed derivative test times a single bounded
correction-vector norm. No coefficient l1 norm is introduced.

## Notation and exact CRT row

At repository stage n, the conductor set is e=2,...,n+1. Write a_(n,e) for the
actual inverse-Gram correction coefficient, C_n for correctionSynthesis n,
H_n=Delta C_n, and h_d=Delta g_d, d=i+2. At positive physical sites,

\[
h_d(k)=\frac1d-\mathbf1_{d\mid k},\qquad
H_n(k)=q_n-\sum_{e\mid k}a_{n,e},\qquad
q_n=\sum_{e=2}^{n+1}\frac{a_{n,e}}e.
\]

All vectors are anchored at physical site zero. Put
w(k)=1/[k(k+1)], w(0)=0, and

\[
T(q)=\sum_{k\ge1,\ q\mid k}w(k)
=\operatorname{progressionWeight}(q,q).
\]

The positive representative q preserves the whole zero residue class without
inserting physical site zero. Simultaneous divisibility gives exactly

\[
\boxed{K(d,e)=\langle h_d,h_e\rangle
=\frac1{de}-\frac{T(e)}d-\frac{T(d)}e+T(\operatorname{lcm}(d,e)).}
\]

Therefore the actual signed row is

\[
\boxed{B_n(d)=
\left(\frac1d-T(d)\right)q_n
-\frac1d\sum_e a_{n,e}T(e)
+\sum_e a_{n,e}T(\operatorname{lcm}(d,e)).}
\]

Every term is retained, including the full lcm intersection. This is not an
independently perturbed Gram approximation.

Let P_n(k)=sum_(j<k) correctionCoefficient(n,j). The exact Abel expression is

\[
B_n(d)=P_n(n)K(d,n+2)
-\sum_{k<n}P_n(k+1)\{K(d,k+3)-K(d,k+2)\}.
\]

The first difference is explicitly

\[
\begin{aligned}
K(d,e+1)-K(d,e)
={}&(d^{-1}-T(d))((e+1)^{-1}-e^{-1})\\
&-\{T(e+1)-T(e)\}/d\\
&+T(\operatorname{lcm}(d,e+1))-T(\operatorname{lcm}(d,e)).
\end{aligned}
\]

The endpoint uses n+2, even though the finite coefficient support ends at n+1.
For K<=n the primitive itself also has the exact finite Mobius form

\[
P_n(K)=\sum_{j<K}\sum_{m\mid j+2}
\mu((j+2)/m)\,\Delta(1-P_{V_n}1)(m).
\]

All of these identities are formalized in RH/DerivativeCRT.lean, including
correctionAbel_explicit_crt, correctionPrimitive_eq_divisor_sum, and
correctionCRT_cofinal_iff_residual_zero.

## Actual zeta moments and a uniform complete remainder

For integer p>1 define the finite signed moments

\[
b_{n,p}=\sum_e a_{n,e}e^{-p},\qquad
\ell_{n,d,p}=\sum_e a_{n,e}\operatorname{lcm}(d,e)^{-p}.
\]

The inverse-power pairing of the actual derivative atoms is

\[
\sum_{k\ge1}\frac{h_d(k)h_e(k)}{k^p}
=\zeta(p)\left[
\frac1{de}-\frac1{de^p}-\frac1{ed^p}
+\frac1{\operatorname{lcm}(d,e)^p}\right].
\]

inversePowerSeries_eq_riemannZeta identifies the formal real series with
Mathlib's actual complex riemannZeta at each integer p>1.

Define the entirely finite arithmetic core

\[
\begin{aligned}
\mathcal T_{M,n,d}={}&\frac{q_n}{2d}\\
&+\sum_{j<M}(-1)^j\left[
\zeta(j+2)\left\{
\frac{q_n-b_{n,j+2}}d
-\frac{q_n}{d^{j+2}}+\ell_{n,d,j+2}
\right\}-\frac{q_n}d\right].
\end{aligned}
\]

The first physical site is exactly q_n/(2d), and every inverse-power tail
has its first-site subtraction q_n/d. Define the full signed remainder

\[
\mathcal R_{M,n,d}
=\sum_{k\ge2}\frac{h_d(k)H_n(k)}{k^{M+1}(k+1)}.
\]

Then for every finite M,n,d,

\[
\boxed{B_n(d)=\mathcal T_{M,n,d}+(-1)^M\mathcal R_{M,n,d},}
\qquad
\boxed{|\mathcal R_{M,n,d}|\le2^{-M}\|h_d\|\,\|H_n\|.}
\]

The proof constructs the actual Hilbert multiplier
f(k) -> 1_(k>=2) k^(-M) f(k), of norm at most 2^(-M).
It does not estimate the individual coefficients.
Strong convergence of H_n, already known unconditionally, supplies

\[
\exists C>0\ \forall n,\quad \|H_n\|\le C.
\]

Hence the displayed error bound is uniform in n, including growing dimensions.
The constant is existential, not claimed to be an effective numerical rate.

The full square identity is

\[
B_n(d)^2=\mathcal T_{M,n,d}^2+
2\mathcal T_{M,n,d}(-1)^M\mathcal R_{M,n,d}
+\{(-1)^M\mathcal R_{M,n,d}\}^2.
\]

For any Hilbert vector f, the diagonal version is also retained:

\[
\|f\|^2=\frac{f(1)^2}{2}
+\sum_{j<M}(-1)^j\sum_{k\ge2}\frac{f(k)^2}{k^{j+2}}
+(-1)^M\sum_{k\ge2}\frac{f(k)^2}{k^{M+1}(k+1)}.
\]

The last square remainder is nonnegative before its explicit alternating sign.
Neither this term nor the signed mixed term above is deleted.

Files: RH/GeometricDerivativeMoments.lean,
RH/DerivativeCRTPowerMoments.lean, RH/DerivativeZetaGeometricBridge.lean.

## A finite arithmetic equivalent of the cofinal Abel target

The uniform bound permits the diagonal choice M=n without exchanging a growing
sum with coordinatewise limits:

\[
B_n(d)-\mathcal T_{n,n,d}\longrightarrow0
\quad\text{for every fixed }d.
\]

Consequently the new checked theorem
correctionZetaCRT_cofinal_iff_residual_zero proves

\[
\boxed{\left[
\forall d\ge2\ \forall\varepsilon>0,\quad
|\mathcal T_{n,n,d}|<\varepsilon
\text{ for arbitrarily large }n
\right]\iff \mathrm{limitResidual}=0.}
\]

riemannHypothesis_of_cofinal_zetaCRT gives the conditional RH implication.
This is an explicit finite signed CRT/zeta estimate still requiring a provider.
Its equivalence is not a proof of the estimate.

One may instead fix an expansion order separately for each desired accuracy:
riemannHypothesis_of_cofinal_momentCore_budget requires cofinal smallness of
the complete signed core plus its displayed geometric error budget.
The expansion order is then fixed before choosing the cofinal set of stages.

Integer zeta values in this section are distinguished from zeta-zero sums in
the next section. Their connection is through the same finite coefficients and
primitive, with the signed transfer discrepancy explicitly retained.

## The same signed primitive in an actual Weil matrix

Put \(c_{n,j}=\texttt{correctionCoefficient}\ n\ j\),
\(C_n(k)=\sum_{j<k}c_{n,j}\), and
\[
\chi_s(j)=\exp\!\left(-(s-\tfrac12)\log(j+2)\right),
\qquad D_n(s)=\sum_{j<n}c_{n,j}\chi_s(j).
\]
The new complex Abel identity uses exactly the real primitive already present
in `DerivativeSignedCorrection`; it does not introduce different coefficients:
\[
\boxed{D_n(s)=C_n(n)\chi_s(n)
-\sum_{k<n}C_n(k+1)\bigl(\chi_s(k+1)-\chi_s(k)\bigr).}
\]
In particular, the endpoint is \(C_n(n)(n+2)^{1/2-s}\), even though the last
conductor appearing in the original finite sum is \(n+1\).

For an admissible smooth superexponentially decaying seed \(f\), set
\(f_j(x)=f(x-\log(j+2))\), and let \(W\) denote the complete arithmetic Weil
pairing. The transform translation law gives
\[
\sum_{j<n}c_{n,j}\widehat f_j(s)=D_n(s)\widehat f(s).
\]
Consequently the actual finite matrix, not a surrogate Gram matrix, satisfies
\[
\boxed{\sum_{j,k<n}c_{n,j}c_{n,k}W(f_j,f_k)
=\sum_{\rho}m_\rho\,
\overline{D_n(\rho^\star)\widehat f(\rho^\star)}
D_n(\rho)\widehat f(\rho),}
\qquad \rho^\star=1-\overline\rho.
\]
The sum ranges over actual nontrivial zeta zeros with their actual analytic
multiplicities. Every prime-power contribution, both poles, and the complete
gamma term remain in each arithmetic matrix entry. Finite sums are interchanged
only with proved summable zero series at a fixed \(n\).

Writing \(U_\rho=D_n(\rho^\star)\widehat f(\rho^\star)\) and
\(V_\rho=D_n(\rho)\widehat f(\rho)\), the checked real identity is
\[
\boxed{\Re Q_{n,f}=\sum_\rho\frac{m_\rho}{2}
\left(|U_\rho|^2+|V_\rho|^2-|U_\rho-V_\rho|^2\right).}
\]
The negative reflected-difference square is retained. The three terms remain
combined inside each summand; the proof does not split the infinite sum into
three separately unproved summable series. No positivity follows without an
additional argument controlling this complete expression.

## Actual mixed Weil entries recover the linear Abel samples

The repository's single-zero tests give a more direct connection to the signed
row than the quadratic identity alone. For every actual zero \(\rho\), choose
smooth admissible tests \(g_\rho,h_\rho\) whose transforms are respectively
one at \(\rho,\rho^\star\) and zero at the other actual zeros. The actual
explicit formula and translation law give, for every real \(t\),
\[
\boxed{W(h_\rho,\tau_tg_\rho)
=m_\rho\exp\!\left(-(\rho-\tfrac12)t\right).}
\]
This also holds on the critical line. Neither existence of an off-line zero
nor simplicity of any zero is assumed. Since \(m_\rho\ge1\), the following
normalized mixed arithmetic row is well-defined:
\[
\boxed{B_n(\rho):=\frac1{m_\rho}\sum_{j<n}c_{n,j}
W(h_\rho,\tau_{\log(j+2)}g_\rho)=D_n(\rho).}
\]
The seeds depend on \(\rho\) but do not need to change with \(n\).
Thus actual mixed Weil data recover the complete linear Abel expression at
each actual zero, with its original endpoint. These existence theorems do not
provide numerical formulas or quantitative norm bounds for the isolating seeds.

## An explicit signed CRT-to-Weil transfer target

Fix derivative row \(i\), and write
\(K_i(j)=\texttt{derivativeRowKernel}\ i\ j\). This is the physical kernel
identified by the exact CRT/divisibility formulas in the accompanying module.
At each finite stage choose finitely many actual zeros
\(\rho_1,\ldots,\rho_L\) and real weights \(a_\ell,b_\ell\), and set
\[
J(j)=\sum_{\ell=1}^L
\left[a_\ell\Re\chi_{\rho_\ell}(j)
+b_\ell\Im\chi_{\rho_\ell}(j)\right],\qquad E_i(j)=K_i(j)-J(j).
\]
This is a concrete approximation of the CRT kernel by the Mellin characters
realized by actual mixed Weil entries. Define
\[
Z_{n,i}=\sum_{\ell=1}^L
\left[a_\ell\Re B_n(\rho_\ell)+b_\ell\Im B_n(\rho_\ell)\right],
\]
and retain the entire signed arithmetic discrepancy
\[
\begin{aligned}
R_{n,i}
&=\sum_{j<n}c_{n,j}E_i(j)\\
&=C_n(n)E_i(n)
-\sum_{k<n}C_n(k+1)\bigl(E_i(k+1)-E_i(k)\bigr).
\end{aligned}
\]
Finite linearity and Abel summation give the full equality
\[
\boxed{\texttt{signedCorrectionRow}(n,i)=Z_{n,i}+R_{n,i}.}
\]
No coefficientwise absolute values occur. In squared form the complete
remainder accounting is
\[
\boxed{|\texttt{signedCorrectionRow}(n,i)|^2
=Z_{n,i}^2+2Z_{n,i}R_{n,i}+R_{n,i}^2.}
\]

The weakest scalar target supplied by this decomposition is cofinal smallness
of the full signed sum \(Z_{n,i}+R_{n,i}\), equivalently of the displayed square
with its signed cross term. This is an explicit arithmetic reformulation of the
open obligation, not a new provider of it.

A more practical sufficient provider has two independently checkable budgets:
for each fixed \(i\), every \(\varepsilon>0\), and every lower index \(N\), find
one \(n\ge N\) and finite sampling data as above for which
\[
\boxed{|Z_{n,i}|<\varepsilon/2,\qquad |R_{n,i}|<\varepsilon/2.}
\]
The first bound is on the complete signed combination of actual mixed Weil
rows; the second is on the complete coefficient-weighted CRT discrepancy,
including its endpoint and signed difference sum. Both must hold at the same
cofinal indices. Separate assertions that each holds frequently cannot be
intersected without further justification. The sample count, zeros, and weights
may vary with \(n\); the identities are finite and require no interchange of a
growing sum with coordinatewise limits.

Such a provider closes `correctionAbel_cofinal_iff_residual_zero` by the triangle
inequality applied only after the two complete signed quantities are formed.
It is stronger than allowing additional cancellation between \(Z_{n,i}\) and
\(R_{n,i}\). Neither budget has been established here. A small pointwise
error \(K_i(j)-J(j)\) is not enough: the coefficients and dimension move, so
the required estimate is specifically on their complete signed pairing.

Completed Nyman seeds cannot replace these non-null mixed tests: their full
Weil matrices vanish identically without RH, while the physical derivative
kernel does not. Likewise, positivity of an unrelated finite form does not
bound either budget. The remaining work is precisely this quantitative signed
transfer/cancellation estimate, not an unproved identification of the two Gram
matrices.



## Formal verification ledger and open obligations

All of the following are proved in Lean without RH or any project-local axiom:

- DerivativeCRT: derivativeRowKernel_crt, divisorMass_eq_progressionWeight,
  correctionPrimitive_eq_divisor_sum, correctionAbel_explicit_crt,
  correctionCRT_cofinal_iff_residual_zero.
- GeometricDerivativeMoments: inner_eq_head_moments_remainder,
  norm_sq_eq_head_moments_remainder, signedRemainder_bound,
  correction_derivative_uniform_norm_bound,
  signedCorrectionRow_momentCore_uniform_exists.
- DerivativeCRTPowerMoments: inversePowerSeries_eq_riemannZeta,
  derivativePowerKernel_crt, correctionPowerMoment_crt.
- DerivativeZetaGeometricBridge: signedCorrectionRow_eq_zetaCRT,
  signedCorrectionRow_zetaCRT_bound, signedCorrectionRow_zetaCRT_square,
  correctionZetaCRT_diagonal_error_tendsto_zero,
  correctionZetaCRT_cofinal_iff_residual_zero.
- DerivativeCorrectionWeilBridge: correctionWeilQuadratic_eq_abel_zero_sum,
  correctionWeilQuadratic_real_eq_signed_squares,
  exists_mixed_weil_mellin_character, exists_mixed_weil_correctionMellinAbel,
  signedCorrectionRow_eq_mellinProxy_add_discrepancy,
  mellinProxyDiscrepancy_eq_abel, signedCorrectionRow_sq_mellinProxy_exact,
  mellinProxy_cofinal_iff_residual_zero.

The finite proxy transfer and its complete square identity are formalized,
not merely paper deductions. Analysis/SignedAbel.lean contains the reusable
complexValue and sum_eq_complexValue extension.

**Conditional research reductions:** riemannHypothesis_of_cofinal_zetaCRT,
riemannHypothesis_of_cofinal_momentCore_budget, and
riemannHypothesis_of_joint_mellinProxy_budgets.
Their full domain-specific hypotheses remain explicit.

**Open:** Supply cofinal signed cancellation of the finite zeta/CRT cores,
or the complete mixed-Weil proxy plus signed CRT discrepancy.
**Open:** Construct nontrivial arithmetic sampling data with the two quantitative
budgets holding jointly at cofinal indices; the exact zero-isolating tests alone
supply no quantitative transfer bound.

No smallness of a growing signed sum is inferred from coordinatewise limits.
No completed-Nyman null matrix is identified with the derivative Gram matrix.
No RH proof or literature-priority claim is made.
