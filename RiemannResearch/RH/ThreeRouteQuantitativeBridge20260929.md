# Three routes: weighted correction convergence and a quantitative Weil bridge

Date: 29 September 2026. Source baseline: `4208a0054cbe5b1ee54b5b8d19eefd70e58331ac`.

This development establishes new connections in this project. It does not claim
priority in the mathematical literature or prove RH. The complete paper proofs
below are distinguished from the exact Lean declarations in the verification
ledger at the end. All zero sums count multiplicity and both ordinate signs.

## 1. Main quantitative overlap

Let H have norm squared `sum_{n>=1}|f(n)|^2/[n(n+1)]`, let
`g_d(n)=(n mod d)/d`, and put

\[
F_N=P_{\operatorname{span}(g_2,\ldots,g_N)}1,\qquad
Q_N=b_N^{\mathsf T}G_N^{-1}b_N=\|F_N\|^2,\qquad E_N=1-Q_N.
\]

Choose any fixed finite family of smooth compactly supported log-tests, with
centered Mellin transforms \(\Phi_1,\ldots,\Phi_k\). Use the actual Weil convention

\[
W_{ij}=\sum_\rho m_\rho
 \overline{\Phi_i(1-\bar\rho)}\Phi_j(\rho).
\]

The explicit formula identifies this with the complete arithmetic Weil matrix,
including prime, pole, and archimedean contributions. Set

\[
M^2=\sup_{0\le\sigma\le1,\ t\in\mathbb R}
 (1+t^2)^2\sum_j|\Phi'_j(\sigma+it)|^2<\infty,
\qquad H(q)=2(\sqrt q+q^{-1/2}-2).
\]

**Unconditional paper theorem.** For every N>=2,

\[
\boxed{\operatorname{tr}(W_-)\le M^2 H(Q_N)
=\frac{2M^2E_N^2}{\sqrt{Q_N}(1+\sqrt{Q_N})^2}.}
\]

Here \(W_-\) is the positive matrix formed from the absolute values of the
negative eigenvalues. The estimate controls their total mass, and hence also
the most negative eigenvalue. The constant explicitly depends on the chosen
test family; no assertion of a uniform bound across arbitrary rescalings is made.

Equivalently, any finite legal approximation A with \(\|1-A\|\le\varepsilon<1\)
gives this bound with \(Q_N\) replaced by \(1-\varepsilon^2\). The exact identity
behind that replacement is

\[
\|1-A\|^2=1-Q_N+\|A-F_N\|^2.
\]

As \(E\downarrow0\), \(H(1-E)=E^2/2+O(E^3)\). Thus the bound is quadratic in
residual energy and fourth order in residual norm. This asymptotic statement
does not assert that the actual sequence \(E_N\) tends to zero.

## 2. Proof, retaining the full spectral and projection remainders

Write \(\rho^\star=1-\bar\rho\). Define absolutely convergent matrices

\[
P_{ij}=\sum_\rho m_\rho\overline{\Phi_i(\rho)}\Phi_j(\rho),\quad
T_{ij}=\tfrac12\sum_\rho m_\rho
 \overline{\Phi_i(\rho)-\Phi_i(\rho^\star)}
 [\Phi_j(\rho)-\Phi_j(\rho^\star)].
\]

Reflection invariance gives the exact equality

\[
\boxed{W=P-T,\qquad P\succeq0,\quad T\succeq0.}
\]

For the negative spectral projection \(\Pi_-\) of W,
\(\operatorname{tr}(W_-)=-\operatorname{tr}(\Pi_-W)
\le\operatorname{tr}(\Pi_-T)\le\operatorname{tr}T\).

Put

\[
\Delta_\zeta=\tfrac12\sum_\rho m_\rho
 \frac{(2\Re\rho-1)^2}{|\rho|^2|1-\rho|^2}.
\]

The horizontal mean-value formula, followed by Cauchy--Schwarz, gives
\(\operatorname{tr}T\le M^2\Delta_\zeta\): on each horizontal segment,
the derivative vector norm is at most \(M/(1+(\Im\rho)^2)\), and
\(|\rho||1-\rho|\le1+(\Im\rho)^2\). This accounts for the factor 1/2
and both members of each reflected pair.

The established zero-sum identity yields the exact scalar discrepancy

\[
\Delta_\zeta=\sum_\rho\frac{m_\rho}{|\rho|^2}
 -(2+\gamma_E-\log(4\pi)).
\]

For each zero to the right of the line let
\(p_\rho=|1-\rho|^2/|\rho|^2\in(0,1)\). Then

\[
\Delta_\zeta=\sum_{\Re\rho>1/2}m_\rho f(p_\rho),
\qquad f(p)=p+p^{-1}-2=(1-p)^2/p.
\]

Burnol's Theorem 1.2 identifies the continuous Nyman--Beurling projection gain
\(q=\|P_{NB}1\|^2\) with \(\prod_{\Re\rho>1/2}p_\rho^{m_\rho}>0\).
The elementary identity

\[
\boxed{f(ab)=f(a)+f(b)+(1-a)(1-b)(1+(ab)^{-1})}
\]

retains every product interaction. Grouping conjugate zeros (there are no real
nontrivial zeta zeros) and applying it to upper-right zeros with multiplicity gives
\(\Delta_\zeta\le2f(\sqrt q)=H(q)\).

More precisely, enumerate those upper-right factors with repetitions and put
\(B_0=1\), \(B_k=\prod_{j<k}p_j\). Taking limits in the finite exact telescope gives

\[
\boxed{H(q)=\Delta_\zeta+
2\sum_{k\ge0}(1-B_k)(1-p_k)(1+B_{k+1}^{-1}).}
\]

For an empty or finite family, the corresponding empty or finite sum is used.
All terms of the additional sum are nonnegative; its convergence follows from
the exact partial identities and q>0.

The embedding \((Jf)(x)=f(\lfloor1/x\rfloor)\) is isometric into L2(0,1), and

\[
Jg_d(x)=\{1/(dx)\}-d^{-1}\{1/x\}\in NB.
\]

Therefore

\[
\boxed{q-Q_N=\|P_{NB}1-JF_N\|^2=:a_N\ge0.}
\]

This uses inclusion, not an equality between the discrete and continuous
closed spaces. Since H decreases on (0,1], the spectral bound follows. Even the
last comparison has the exact retained gap

\[
H(Q_N)-H(q)=
\frac{2a_N(1-\sqrt{qQ_N})}{\sqrt{qQ_N}(\sqrt q+\sqrt{Q_N})}.
\]

## 3. Full correction array and signed CRT rows

Write \(r=1-P_V1\), \(D=\|r\|^2\), and extend the actual finite correction vector
\(e_{N,d}=[G_N^{-1}(b_N+G_N\mu_N)]_d\) by zero for d>N. Its limit is

\[
e_{\infty,d}=\sum_{k\mid d}\mu(d/k)[r(k)-r(k-1)],\qquad d\ge2,
\]

with the anchored convention r(0)=0. For every s>3/2, set

\[
C_s=\zeta(s)\sqrt{\zeta(2s-2)+\zeta(2s-1)}.
\]

**Unconditional paper theorem.** The entire array converges in weighted l1:

\[
\boxed{\sum_{d\ge2}\frac{|e_{N,d}-e_{\infty,d}|}{d^s}
\le2C_s\sqrt{E_N-D}+\sum_{d>N}\frac{|\mu(d)|}{d^s}
\le2C_s\sqrt{E_N-D}+\frac{N^{1-s}}{s-1}\longrightarrow0.}
\]

Proof: for \((T_\mu x)(d)=\sum_{k\mid d}\mu(d/k)x(k)\), Tonelli and weighted
Cauchy--Schwarz give

\[
\sum_{d\ge1}d^{-s}|T_\mu x(d)|
\le\Big(\sum_{m\ge1}|\mu(m)|m^{-s}\Big)
 \sum_{k\ge1}|x(k)|k^{-s}\le C_s\|x\|_H.
\]

The exact pre-estimate identity is

\[
e_N-e_\infty=-T_\mu\Delta(F_N-P_V1)-\mu\,\mathbf1_{d>N},
\qquad \|F_N-P_V1\|^2=E_N-D.
\]

Use \(\|\Delta\|\le2\). This proof requires no prime number theorem. An alternative
bound retaining the complete signed derivative correction is
\(C_s\|\Delta R_N-\Delta(P_V1-F_N)\|\), where
\(R_N=1+\sum_{d=2}^N\mu(d)g_d\).
Neither convergence theorem says that the limiting correction is zero.

For the exact derivative Gram define

\[
A_q=\sum_{k\ge1}\frac1{qk(qk+1)},\quad
K(i,d)=\langle\Delta g_i,\Delta g_d\rangle,
\quad \alpha_i=1/i-A_i.
\]

Simultaneous divisibility gives the full CRT identity

\[
\boxed{K(i,d)=\frac{\alpha_i}{d}+T(i,d),\quad
T(i,d)=A_{\operatorname{lcm}(i,d)}-A_d/i.}
\]

It includes every cross term in
\((1/i-\mathbf1_{i\mid n})(1/d-\mathbf1_{d\mid n})\).
Because \(0\le A_{\operatorname{lcm}(i,d)}\le A_d\),

\[
|T(i,d)|\le A_d\le\zeta(2)/d^2\quad\text{uniformly for all }i,d\ge2.
\]

Thus, with \(C_N=\sum_{d=2}^Ne_{N,d}/d\),

\[
\sum_de_{N,d}K(i,d)=\alpha_i C_N+\sum_de_{N,d}T(i,d),
\]

and the second term converges to its complete absolutely convergent limit
uniformly in i, with error at most
\(\zeta(2)\sum_d|e_{N,d}-e_{\infty,d}|/d^2\).
The reciprocal charge \(C_N\to-r(1)\) is retained separately. This isolates
the slow reciprocal component without estimating an inverse-Gram operator norm.

## 4. Exact finite correction certificate

Let u_d be the finite-support coefficient dual with
\(\langle g_e,u_d\rangle=\mathbf1_{e=d}\), and let
\(U_{de}=\langle u_d,u_e\rangle\), \(q_{N,d}=(I-P_{V_N})u_d\).
For every real coefficient vector z,

\[
\boxed{\left\|t(1-F_N)+\sum_dz_dq_{N,d}\right\|^2
=t^2E_N-2t\,z^{\mathsf T}e_N
 +z^{\mathsf T}(U-G_N^{-1})z.}
\]

Consequently the full block matrix
\(\begin{pmatrix}E_N&-e_N^{\mathsf T}\\-e_N&U-G_N^{-1}\end{pmatrix}\)
is positive semidefinite, and

\[
\boxed{(z^{\mathsf T}e_N)^2\le E_N\,z^{\mathsf T}(U-G_N^{-1})z.}
\]

All signed off-diagonal terms remain in the quadratic form. This uses the
optimal residual, improving the corresponding bound with the potentially
large raw Möbius residual. It does not prove either factor tends to zero.

## 5. Exact spectral meaning of the limiting signed correction

See [CorrectionDirichletZeroBridge20260929.md](CorrectionDirichletZeroBridge20260929.md)
for the complete proof. Include the boundary coefficient \(e_{\infty,1}=r(1)\).
For Re(s)>3/2, absolute convergence and exact Abel summation give

\[
\boxed{\sum_{d\ge1}\frac{e_{\infty,d}}{d^s}
=\frac{A_r(s)}{\zeta(s)},\qquad
A_r(s)=\sum_{n\ge1}r(n)[n^{-s}-(n+1)^{-s}].}
\]

The numerator is holomorphic for Re(s)>1/2. Since
\(A_{g_d}(s)=\zeta(s)(d^{-1}-d^{-s})\), Hilbert convergence and local uniform
Mellin convergence show that \(A_{P_V1}\) vanishes with the full multiplicity
of every zeta zero in that half-plane. Thus \(A_r=1-A_{P_V1}\), and the
continued correction series has exactly the same principal part as
\(1/\zeta\) at every such zero. In particular, no unknown numerator can cancel
an off-line zero; at a simple zero the residue is exactly \(1/\zeta'(\rho)\).

This is a paper proof of the multiplicity closure target already identified
in `ResidualMellinZeroConditions.lean`, using the existing finite-energy Mellin
analyticity and local uniform convergence. The target has not yet been
discharged by a new Lean declaration. Holomorphy of the correction quotient
throughout Re(s)>1/2 would imply RH; it is not established here.

For completeness, the sparse CRT inverse also has a dimension-independent
signed-action certificate; see [CRTInverseActionCertificate20260929.md](CRTInverseActionCertificate20260929.md).
It retains the full positive sparse remainder and explicitly does not substitute
that derivative Gram for the legal primitive Gram.

## 6. Verification ledger and remaining obligations

The Lean additions cover exact contractive-product defect algebra, a bound
and summability theorem for the actual multiplicity-weighted right-zero
quadratic defect, the full optimal-residual correction covariance identity,
and finite weighted Möbius-convolution/Cauchy--Schwarz estimates. The
`WeightedDivisorCorrectionLimit` endpoint also proves the infinite s=2
weighted Möbius mass of `correctionSynthesis n + limitResidual` tends to zero,
with an explicit summable-series norm constant and no additional provider
hypothesis. This mass contains the full correction-array error together with
the reciprocal-charge error.

The checked declarations are:

- `ContractiveProductDefect.defect_mul_exact`, `defect_partialProduct_exact`,
  and `weighted_sum_defect_le_product`.
- `Burnol.quadraticZeroDefectTerm_exact`, `summable_quadraticZeroDefectTerm`,
  and `quadraticZeroDefect_le_certificate`.
- `GramMobiusCorrection.signed_correction_covariance_exact` and
  `signed_correction_sq_le_energy_dual_form`.
- `WeightedDivisorCorrection.finite_mobius_squareWeight_energy_bound`,
  `hilbert_divisor_summable_and_bound`, `correction_weightedMass_bound`, and
  `correction_weightedMass_tendsto_zero`.

The sharp conjugate-quartet constant, the complete analytic finite-Weil
transfer, the general s>3/2 weighted-array limit, and the principal-part
continuation are rigorous paper deductions here, not claimed as fully
kernel-verified endpoints. In particular, the existing Burnol projection
module explicitly requires the classical analytic projection identity as a
formal hypothesis. The new scalar certificate theorem keeps its lower bound
`q <= productSq` explicit. These are formalization obligations, not additional
unproved assumptions in the paper argument based on Burnol's theorem.

The mathematical RH-strength step remains open: establish vanishing of the
limiting signed correction (equivalently E_N->0), or positivity/removability
by an independent argument. None of the full covariance, reciprocal charge,
projection-gap, or product-interaction terms has been dropped to claim it.

## Sources

- J.-F. Burnol, *A note on Nyman's equivalent formulation of the Riemann
  Hypothesis*, Theorem 1.2 and equation (2.3),
  https://arxiv.org/abs/math/9910055. Supports the continuous projection product
  and Mellin transform of legal generators.
- J.-F. Burnol, *The explicit formula in simple terms*, page 3 and the Weil
  criterion discussion, https://arxiv.org/abs/math/9810169. Supports the exact
  scalar zero discrepancy and the established Weil framework.
- Current repository: `WeilSpectralPairing.lean`, `BurnolZeroProductConvergence.lean`,
  `BurnolProjectionConsequences.lean`, `DerivativeSignedCorrection.lean`,
  `ParetoInverseGramDual.lean`, `ResidueGramCorrectionPairing.lean`,
  `ParetoMellinFiniteEnergy.lean`, and `ResidualMellinZeroConditions.lean`.

The quantitative synthesis, weighted divisor estimate, and principal-part
assembly were developed for the user's exact-identity research request.
No claim that they are absent from all prior literature is made.
