# Squarefree prefix covariance and complete head leakage

Date: 1 November 2026. Source: the user's investigation of
[SquarefreePrefixAbelDispersion20261031.md](SquarefreePrefixAbelDispersion20261031.md).

**Conclusion.** Signed cross-prefix covariance and complete head leakage give
an unconditional block estimate of order \(M^2\varepsilon_N\), improving the
order obtained by summing separate evaluation bounds. They do not establish
the required \(M\) times polylogarithmic envelope. The missing arithmetic input
is an actual source-weighted compression-defect estimate of order
\(M^{-1}\) times a polylogarithm. The identities alone give no weaker RH criterion.

All objects use every squarefree conductor \(2\le d\le N+1\), including
composites, and the complete \(Q(m)=1/(\zeta(2)m^2)\) inner product.
No finite physical truncation defines a projection, Gram matrix, or residual.

## 1. Exact cross-prefix covariance

Write \(P=P_N\), \(r=r_N=(I-P)1\), \(\varepsilon=\|r\|_Q^2>0\), and
\(\chi_h=\mathbf1_{m\le h}\). Put

\[
u_h=\|\chi_h r\|_Q^2,\quad p_h=P\chi_h r,\quad
\ell_h=(I-P)(\chi_h r-(u_h/\varepsilon)r).
\]

Polarizing the existing exact source variance gives

\[
\boxed{\langle p_h,p_k\rangle_Q
=u_{\min(h,k)}-\frac{u_hu_k}{\varepsilon}
-\langle\ell_h,\ell_k\rangle_Q.}
\tag{1}
\]

Proof: the centered sources \(y_h=\chi_h r-(u_h/\varepsilon)r=p_h+\ell_h\)
have orthogonal projection and complementary parts. Also
\(\langle\chi_h r,\chi_k r\rangle_Q=u_{\min(h,k)}\).
Expand \(\langle y_h,y_k\rangle_Q\).
The Lean proof polarizes the previously checked source variance.

For any finite family of signed real coefficients \(c_h\), therefore,

\[
\left\|\sum_hc_hp_h\right\|_Q^2
=\sum_{h,k}c_hc_k\left[
u_{\min(h,k)}-\frac{u_hu_k}{\varepsilon}
-\langle\ell_h,\ell_k\rangle_Q\right].
\tag{2}
\]

The loss matrix is positive semidefinite; its off-diagonal entries can have
either sign. Taking absolute values or retaining only its diagonal changes (2).

Checked declarations: CenteredProjectionResponse.source_covariance_exact
and QSquarefreePrefixAbel.prefix_covariance_exact. The latter states \(h\le k\);
symmetry supplies the other ordering.
The checked compensated_le_exact_source_variance connects the existing
\(WJ-D=T^2\) identity to the existing exact source-variance estimate.

## 2. The complete compression defect

For any Hilbert vector \(z\), define

\[
p_{N,H}(z)=P_N\chi_Hz,\qquad
\Lambda_{N,H}(z)=(I-\chi_H)P_N\chi_Hz.
\]

The exact off-head energy and a retained-square refinement are

\[
\|\Lambda(z)\|_Q^2
=\|P_N\chi_Hz\|_Q^2-\|\chi_HP_N\chi_Hz\|_Q^2,
\tag{3}
\]
\[
\boxed{\|\Lambda(z)\|_Q^2+
\left\|\chi_HP_N\chi_Hz-\tfrac12\chi_Hz\right\|_Q^2
=\tfrac14\|\chi_Hz\|_Q^2.}
\tag{4}
\]

Proof: set \(a=\chi_Hz\), \(p=P_Na\). Then
\(\langle\chi_Hp,a\rangle_Q=\langle p,a\rangle_Q=\|p\|_Q^2\).
Expand the square and use the orthogonal head/tail decomposition of \(p\).
In particular \(\|\Lambda(z)\|^2\le\|\chi_Hz\|^2/4\), without an RH assumption.

In orthonormal physical head coordinates, let \(E=\chi_HP_N\chi_H\)
restricted to that head. Equation (3) is

\[
\|\Lambda(z)\|_Q^2=\langle a,(E-E^2)a\rangle,\qquad 0\preceq E\preceq I.
\tag{5}
\]

The relevant spectral quantity is the actual source-weighted
\(\lambda(1-\lambda)\). Bounding the inverse Gram does not by itself
give a decay rate for that quantity.

## 3. An unconditional compensated block inequality

Put \(Z=\zeta(2)\), \(\beta_n=1/(n+1)\), and

\[
\delta_B(N,H)=\|\Lambda_{N,H}(Br_N)\|_Q^2,\qquad
\delta_0(N,H)=\|\Lambda_{N,H}(r_N)\|_Q^2.
\]

For \(H\le M<n\le2M\), the actual response is exactly

\[
T_{N,H}(n)=\Lambda_{N,H}(Br_N)(n)-\beta_n\Lambda_{N,H}(r_N)(n).
\tag{6}
\]

This follows from \(T=(P_N\chi_H(B-\beta_n)r_N)(n)\).
The signed cross term is retained in

\[
\sum_nT(n)^2=\sum_n[
\Lambda_B(n)^2-2\beta_n\Lambda_B(n)\Lambda_0(n)
+\beta_n^2\Lambda_0(n)^2].
\tag{7}
\]

Use \((a-b)^2=2a^2+2b^2-(a+b)^2\), explicitly discarding its last square.
Since \(\beta_n\le1/(M+2)\) and \(1/Q(n)\le4ZM^2\), summing the complete
Q energy before taking evaluation bounds gives

\[
\boxed{\sum_{n=M+1}^{2M}(WJ-D)_{N,H,n}
\le8ZM^2\left[\delta_B(N,H)+\frac{\delta_0(N,H)}{(M+2)^2}\right].}
\tag{8}
\]

The existing equality \(WJ-D=T^2\) is reused, not reproved.

Equation (4), head contraction, and \(\|Bf\|\le\|f\|/2\) give
\(\delta_B\le\varepsilon_N/16\), \(\delta_0\le\varepsilon_N/4\), hence

\[
\boxed{\sum_{n=M+1}^{2M}(WJ-D)_{N,H,n}
\le8ZM^2\left[
\frac{\varepsilon_N}{16}+
\frac{\varepsilon_N}{4(M+2)^2}\right]
=O(M^2\varepsilon_N).}
\tag{9}
\]

Separate sitewise evaluation bounds give \(O(M^3\varepsilon_N)\) after
summation. Equation (9) saves one power relative to that geometric procedure.
It does not give \(O(M\,\mathrm{polylog}(M))\); no novelty claim is made
for the general projection inequalities.

For \(H\le M\), taking the minimum of (8) and the raw \(\sum WJ\) estimate
is always valid. The new estimate need not be numerically smaller.

Checked in QSquarefreeHeadLeakage.lean: leakage_energy_exact,
leakage_quarter_exact, response_eq_leakage, physical_block_sq_le,
compensated_block_le_leakage, and compensated_block_le_quadratic.

## 4. The full Schur and divisor representation

Use the actual screened head family from QSquarefreeSchurRepresentation.lean.
Write \(\psi\) for that family,
\(\mathcal S=(\langle\psi_i,\psi_j\rangle_Q)\), and
\(\mathsf T_H=(\langle\chi_H\psi_i,\chi_H\psi_j\rangle_Q)\).
For the head source \(\chi_Hz\), let \(q_z\) be its original anchored moments.
The existing complete normal-equation theorem gives
\(P_N\chi_Hz=\psi^T\mathcal S^{-1}q_z\). Subtracting head output energy yields

\[
\boxed{\|\Lambda_{N,H}(z)\|_Q^2
=q_z^T\mathcal S^{-1}(\mathcal S-\mathsf T_H)
\mathcal S^{-1}q_z.}
\tag{10}
\]

Here \(\mathcal S-\mathsf T_H\) is the complete tail Gram.
For \(z=Br_N\), \(q_z\) contains the actual signed residual, with high and
composite squarefree conductors retained through the coupled normal equations.

The literal synthesis and tail subtraction are formally bridged by
QSquarefreeHeadLeakageSchur.leakage_eq_schur_tail. Formula (10) is a paper
consequence of that synthesis and (3), not a separately named Lean declaration.

The proved \(\mathcal S\succeq\mathsf T_H\) and logarithmic inverse bound do
not make (10) small. The algebraic order constraint permits \(E=I/2\),
whose defect is \(I/4\). Additional arithmetic control of the actual source
alignment is necessary. This is a limitation of the matrix inequalities,
not a counterexample to the actual squarefree projections.

## 5. Numerical tests

All numbers here are exploratory float64 calculations using the complete-period
trigamma/digamma formulas. They are not interval-certified or Lean results.
See [reproduction code and recorded data](SquarefreePrefixCovarianceDiagnostics20261101.md).

At \(N=240,n=221,H=220\), all eight physical-range contributions remain negative.

| Quantity | Approximate value |
|---|---:|
| \(T=L_{240}(221)\) | -0.049197540742524 |
| \(W\) | 4.482143608149426 |
| \(J\) | 0.000675948130774 |
| \(WJ\) | 0.003029696593791 |
| \(D\) | 0.000609298578679 |
| \(T^2\) | 0.002420398015112 |
| \(D/(WJ)\) | 0.201108777667 |

Dispersion removes about 20.1% of raw Cauchy energy at this sample, without
opposite-sign physical-range cancellation. At prefix \(H=110\), the complete
Schur calculation gives -0.763612116697755, versus the direct full-Gram
prefix -0.763612116697750.

For the logarithmic common cutoff at \(N=240\):

| \(M\) | \(H\) | \(\sum T^2\) | \(\sum WJ\) | Right side of (8) |
|---:|---:|---:|---:|---:|
| 16 | 1 | 0.000018935 | 0.000018935 | 0.00186444 |
| 32 | 3 | 0.000058958 | 0.000071094 | 0.00324761 |
| 64 | 6 | 0.002497520 | 0.003585558 | 0.10840353 |
| 128 | 11 | 0.016018184 | 0.021988363 | 0.49499281 |

The last block includes sites 241–256 beyond stage 240; the canonical
projection is defined there. No finite row supplies a cofinal hypothesis.
The leakage bound is looser than measured raw Cauchy in these tests.
For \(H=1\), dispersion is exactly zero; computed values near \(-10^{-19}\)
are roundoff, not negative mathematical dispersion.

Across the runs, compression-defect discrepancies are below \(3\cdot10^{-20}\).
Computed loss covariance matrices have positive minimum eigenvalues in these
tests. These observations do not constitute rigorous error enclosures.

## 6. The precise Open arithmetic estimate

For \(M=2^j\), \(H_M=\lfloor M/(6+\log M)\rfloor\), it would suffice to prove,
with one \(A\ge0\), \(m\in\mathbb N\),

\[
\boxed{\forall j,\ \exists^\mathrm{frequently}_{N\to\infty}:\quad
\delta_B(N,H_M)\le A(6+\log M)^{2m}/M.}
\tag{11}
\]

Since \(\delta_0\le\varepsilon_N/4\le1/4\), this supplies, for a larger
common constant \(C\),

\[
M\left[\delta_B(N,H_M)+\frac{\delta_0(N,H_M)}{(M+2)^2}\right]
\le C(6+\log M)^{2m}.
\tag{12}
\]

Equation (8) gives the existing block criterion with constant \(8ZC\).
The checked theorem
QSquarefreePrefixCriterion.riemannHypothesis_of_frequently_dyadic_head_leakage
formalizes (12) implies RH, by applying the existing dispersion consumer.

The budget (12) is an **Open arithmetic hypothesis**. Stage sets may depend
on the block. Choosing arbitrarily large \(N\) does not permit assuming
\(\varepsilon_N\to0\). The divisor normal equations and \(\varepsilon_N\le1\)
have not supplied (11). In Schur coordinates, (11) asks for precisely (10)
with the actual source \(z=Br_N\), or an estimate of the smaller actual
block response retaining its signed correlations.

## 7. Does this produce a genuinely stronger sufficient criterion?

No weaker arithmetic premise follows from the new identities alone.
The leakage provider counts all output beyond the cutoff and is stronger
than necessary for an individual finite block.

With some common polylogarithmic power and constant allowed, it describes
the same limiting regularity class as the existing dyadic condition.
Here is a paper proof; only the forward implication is newly formalized.

Let \(b_N=P_NBr_N\) and \(\tau_H=I-\chi_H\). Since
\(\Lambda(Br_N)=\tau_Hb_N-\tau_HP_N\tau_HBr_N\), contraction gives

\[
\left|\sqrt{\delta_B(N,H)}-\|\tau_Hb_N\|_Q\right|
\le\|\tau_HBr_N\|_Q\le\|\tau_Hr_N\|_Q/(H+2).
\tag{13}
\]

For fixed \(H\), strong convergence of projections and residuals passes this
to the limit, without giving a moving-head rate. The existing cofinal
short-head block bound plus complete-tail localization gives
\(\sum_{M<n\le2M}b_\infty(n)^2=O(M(6+\log M)^{2a})\).
Dyadic summation gives
\(\|\tau_Hb_\infty\|_Q^2=O((6+\log H)^{2a}/H)\).
Indeed the block at scale \(2^k\) contributes
\(O(2^{-k}(6+k)^{2a})\), and its dyadic tail has the same order.

Using (13) and \(H_M\asymp M/(6+\log M)\), therefore,
\(\delta_B(\infty,H_M)=O((6+\log M)^{2a+1}/M)\).
Increase the logarithmic power to an even integer and enlarge the constant.
Fixed-head convergence then supplies (12) at arbitrarily large stages;
finitely many small blocks are absorbed by the same enlarged constant.
Conversely, (12), (8), and localization give the old limiting block bound.

Thus no logically weaker polylogarithmic RH condition has been proved.
The useful output is the exact source-weighted defect, signed covariance,
and an unconditional quantitative block inequality. Its required arithmetic
rate remains Open.

## 8. Formal verification scope

- Covariance candidate: job_NMwUvtMTd-dnSNFdOb526rLGEg3wI3II,
  verified=true, exit code 0, server-reported 5.800 seconds.
- Leakage/block candidate: job_PW6oFEDIjy2LBP4CDx2bnCiT4ueDqaiK,
  verified=true, exit code 0, server-reported 6.012 seconds.
- Quadratic bound, Schur bridge, and conditional consumer candidate:
  job_KkMgDPdvd_r4aGGoyt7jn0cHhGbSW9MO,
  verified=true, exit code 0, server-reported 46.246 seconds.
- Saved-module import and eight principal axiom audits: job_hbNKi_KRy9KLJFHOAJQtzy7Tq-RLaKmg,
  verified=true, exit code 0, server-reported 21.792 seconds.

Each inspected principal theorem uses only propext, Classical.choice, and
Quot.sound. This does not discharge the conditional theorem's hypothesis.
Formula (10) and the converse comparison in section 7 are paper arguments;
the numerical data remain exploratory. The final checkpoint receipt separately
identifies aggregate project validation and the exact published commit.
