# Five actual legal orthonormal directions in complete Q

Research continuation, 21 October 2026.
Source: the user's request to extend the actual squarefree residue Gram–Schmidt
basis beyond the constant and parity directions. These are independent
derivations from complete-Q identities already in the project.

## Result and scope

Let \(Z=\zeta(2)\), \(Q(n)=1/(Zn^2)\) on positive integers,
\(g_d(n)=(n\bmod d)/d\), and \(F_p(n)=\lfloor\log_p n\rfloor\).
Write C for PrimePowerTarget.closureWithConstants.

The new finite orthonormal family is
\[
  1,\quad \eta_2=(3-8g_2)/\sqrt3,\quad \psi_3,\quad\psi_5,\quad\psi_6.
\]
Every vector belongs to C. Each new direction uses actual legal squarefree
atoms; no valuation coordinate is substituted for a legal atom.

The complete projection reduces both target errors, but the remaining energy
is strictly positive at this finite stage. Neither target membership in C nor
Parseval saturation for the exhaustive legal family has been proved.

## Exact construction and nondegeneracy

Set
\[
P_2f=\langle f,1\rangle1+\langle f,\eta_2\rangle\eta_2,\quad
u_3=g_3-P_2g_3,\quad s_3=\|u_3\|,\quad\psi_3=u_3/s_3,
\]
\[
P_3f=P_2f+\langle f,\psi_3\rangle\psi_3,\quad
u_5=g_5-P_3g_5,\quad s_5=\|u_5\|,\quad\psi_5=u_5/s_5,
\]
\[
P_4f=P_3f+\langle f,\psi_5\rangle\psi_5,\quad
u_6=g_6-P_4g_6,\quad s_6=\|u_6\|,\quad\psi_6=u_6/s_6.
\]
Finally \(P_5f=P_4f+\langle f,\psi_6\rangle\psi_6\).
Lean uses conductor labels: approximation3, approximation5, and approximation6
are respectively \(P_3,P_4,P_5\).

Nonzero innovations are proved by finite-coordinate functionals:

| Atom | Functional annihilating predecessors | Value on atom |
|---|---|---:|
| g3 | f(1)-f(3) | 1/3 |
| g5 | f(1)-f(7) | -1/5 |
| g6 | f(5)+f(3)-f(1)-f(7) | 1 |

These are exact proofs, not numerical rank checks. Weighted Cauchy–Schwarz also
gives the ordinary mathematical bounds
\[
s_3^2\ge\frac1{90Z},\qquad
s_5^2\ge\frac1{1250Z},\qquad
s_6^2\ge\frac1{84Z}.
\]
The explicit constants in these three inequalities are not formalized in the
new modules; the nonzero innovations are.

## Closed conductor-three identities

Put \(a=\langle g_3,1\rangle_Q\). Full weighted even-index reindexing gives
\[
\langle g_3,1_{\{2\mid n\}}\rangle_Q=\frac{8/9-a}{4},\qquad
b:=\langle g_3,\eta_2\rangle_Q=\frac{8/9-2a}{\sqrt3}.
\]
The pointwise identities
\[
g_3(2n)=1_{\{3\nmid n\}}-g_3(n),\qquad
g_3(n)^2=g_3(n)-\frac29\,1_{\{3\nmid n\}}
\]
and \(Q(3\mid n)=1/9\) yield
\[
\|g_3\|_Q^2=a-\frac{16}{81},\qquad
s_3^2=a-\frac{16}{81}-a^2-b^2,\qquad
\psi_3=\frac{g_3-a1-b\eta_2}{s_3}.
\]
These identities, including the complete infinite sums, are formalized.

## Exact complete-Q target coefficients

Define the complete moments
\[
\mu_p=\sum_{n\ge1}\frac{F_p(n)}{Zn^2},\quad
E_p=\sum_{n\ge1}\frac{F_p(n)^2}{Zn^2},\quad
T_{p,d}=\sum_{n\ge1}\frac{F_p(n)g_d(n)}{Zn^2}.
\]
Then
\[
\beta_p=\frac{3\mu_p-8T_{p,2}}{\sqrt3},\qquad
\alpha_{p,3}=\frac{T_{p,3}-a\mu_p-b\beta_p}{s_3},
\]
\[
\alpha_{p,5}=
\frac{T_{p,5}-\langle g_5,1\rangle\mu_p
-\langle g_5,\eta_2\rangle\beta_p
-\langle g_5,\psi_3\rangle\alpha_{p,3}}{s_5},
\]
\[
\alpha_{p,6}=
\frac{T_{p,6}-\langle g_6,1\rangle\mu_p
-\langle g_6,\eta_2\rangle\beta_p
-\langle g_6,\psi_3\rangle\alpha_{p,3}
-\langle g_6,\psi_5\rangle\alpha_{p,5}}{s_6}.
\]
The Lean theorems identify these expressions with the actual target inner
products for every integer p>1, including p=2,3.
The theorem residueMoment_head_tail proves an exact finite-head PLUS
infinite-tail split; a coefficient is never defined using only a finite head.

For sequential indexing write
\(v_0=1,v_1=\eta_2,v_2=\psi_3,v_3=\psi_5,v_4=\psi_6\).
For every actual QHilbert vector f,
\[
\|f\|_Q^2=\sum_{j=0}^{4}|\langle f,v_j\rangle_Q|^2+\|f-P_5f\|_Q^2,
\]
\[
\left\|f-\sum_{j=0}^{4}c_jv_j\right\|_Q^2
=\|f-P_5f\|_Q^2+\sum_{j=0}^{4}(c_j-\langle f,v_j\rangle_Q)^2.
\]
Thus the projection is optimal in this five-dimensional legal space, and its
residual gives an upper bound on squared distance to C.

## Full-tail evaluation and numerical evidence

The following are numerical evaluations, not Lean-certified decimal bounds:

| Added direction | F2 coefficient | F3 coefficient | F2 residual squared | F3 residual squared |
|---|---:|---:|---:|---:|
| eta2 | 1/sqrt(3) | 0.143396036656 | 1.154364569890 | 0.519414647983 |
| psi3 | -0.238589738486 | -0.278780722119 | 1.097439506579 | 0.441695956957 |
| psi5 | 0.220852355840 | 0.150925866281 | 1.048663743499 | 0.418917339845 |
| psi6 | 0.490482963356 | 0.339123803758 | 0.808090206157 | 0.303912385570 |

The normalizers are \(s_3\approx0.161135305005468\),
\(s_5\approx0.144519028440044\), \(s_6\approx0.154654372010380\).
The target means and energies are
\[
(\mu_2,E_2)\approx(0.723156446310197,\ 2.010653149063368),\qquad
(\mu_3,E_3)\approx(0.345778012862354,\ 0.659539505490265).
\]

Here is the exact arithmetic evaluation scheme.
Let \(S(x)=\sum_{m\ge0}(m+x)^{-2}\), and for \(1\le r\le d\) let
\(n_r(A)=r+d\lceil(A-r)/d\rceil\). For A>=1 this is the first positive integer
at least A in the indicated residue class. Then
\[
H_d(A)=\frac1{Zd^2}\sum_{r=1}^d g_d(r)S(n_r(A)/d),\qquad
T_{p,d}=\sum_{k\ge1}H_d(p^k),
\]
\[
\mu_p=\frac1Z\sum_{k\ge1}S(p^k),\qquad
E_p=\frac1Z\sum_{k\ge1}(2k-1)S(p^k).
\]
For L=lcm(d,e), the complete Gram entry is
\[
G_{de}=\frac1{ZL^2}\sum_{r=1}^L g_d(r)g_e(r)S(r/L).
\]
These ordinary mathematical regroupings follow from nonnegative summation and
the threshold expansion of Fp. The AP/block formulation is not separately
formalized; the Lean moments are complete, summable integer series.

For K>=0 the omitted positive logarithmic layers obey
\[
0\le T_{p,d}-\sum_{k=1}^K H_d(p^k)
\le\frac{d-1}{d}\frac{p^{-K}}{Z(p-1)(1-p^{-K-1})}.
\]
For the mean omit (d-1)/d. The energy remainder is at most
\[
\frac{p^{-K}}{Z(1-p^{-K-1})}
\left(\frac{2K+1}{p-1}+\frac2{(p-1)^2}\right).
\]
These follow from \(S(A)\le1/(A-1)\) for A>1. The analytic truncation bounds
are ordinary proofs, not newly Lean-certified interval estimates.

Numerical evaluation used 75-digit Decimal arithmetic, 220
logarithmic layers, and Euler–Maclaurin evaluation of S. An independent
80-layer SciPy calculation agrees at the displayed precision. Roundoff is not
formally enclosed; the decimal table is not a proof of a numerical inequality.

## Finite obstruction and remaining saturation

Every current approximant is 30-periodic on positive coordinates. In particular
P5f(1)=P5f(31). Since F2(1)=F3(1)=0, F2(31)=4 and F3(31)=3, both target residuals
are nonzero. This finite-stage nonvanishing is formalized. The ordinary
two-coordinate bound is
\[
\|F_p-P\|_Q^2\ge\frac{F_p(31)^2}{962Z}
\quad\text{for every 30-periodic }P.
\]
Its explicit constant is not among the new Lean declarations.

Let \((v_j)_{j\ge0}\) be a complete orthonormal basis of C extending the
verified five-vector frame. One may continue Gram–Schmidt through an
exhaustive enumeration of the remaining squarefree residue atoms.
Construction and completeness of that infinite continuation are not formalized here.

The precise **open saturation condition** is
\[
F_p\in C
\iff
\sum_{j\ge5}|\langle F_p,v_j\rangle_Q|^2=R_p,
\]
where
\[
R_p=E_p-\mu_p^2-\beta_p^2
-\alpha_{p,3}^2-\alpha_{p,5}^2-\alpha_{p,6}^2
=\|F_p-P_5F_p\|_Q^2.
\]
The equality with the actual norm square and positivity at p=2,3 are formalized.
Numerically \(R_2\approx0.808090206157231\) and
\(R_3\approx0.303912385569614\). The further coefficient sums have not been
shown to equal these quantities.

This is separate from ambient Meixner/prime-valuation completeness. An ambient
basis vector need not lie in C, and ambient projections cannot replace legal
projections. Finite orthonormality, error improvement, and positivity at fixed
period imply neither target closure membership nor RH.

## Formal source and verification boundary

* QResidueThreeMoments.lean: exact complete-Q conductor-three moments.
* QSquarefreeLegalBasis.lean: three nonzero innovations, five-vector
  orthonormality, legal membership, exact finite energy and least-squares gap,
  and endpoint certificates for the two nonzero finite target residuals.
* QPrimePowerLegalCoefficients.lean: complete mean/energy/residue series,
  exact head-plus-tail split, target coefficients, the closed conductor-three
  normalization, and strictly positive remaining energy.

There are no RH hypotheses or assumed target-closure providers in these new
results. Saved-source verification job job_L0A8zXI-yGK3OZZK5PsHOt9_tFGO-XkE
succeeded with exit code 0 and verified=true. All three new modules were built
or reused from the successful targeted build; eight inspected declarations
depend only on propext, Classical.choice and Quot.sound.
The server reported 17.130 seconds for this verification job. Workspace-opening
round-trip time and polling delay were not separately instrumented and are not
being identified with Lean compilation time.
Final acceptance and publication are separately gated by the checkpoint;
its job and exact commit are reported in the accompanying response.
The checkpoint does not certify the numerical evaluations or the informal
AP-series and explicit coordinate-bound derivations.

## Next research steps

1. Extend through g7,g10,g11,g13,g14,g15 and then an exhaustive squarefree
   list, retaining every signed coefficient correction and residual square.
2. Formalize AP/threshold regrouping and interval evaluation to turn numerical
   comparisons into certified finite bounds.
3. Seek an upper bound on the exhaustive residual tending to zero, or a
   checkable cofinal energy budget. Finite nondegeneracy and Bessel bounds alone
   do not supply this.
4. Completed in QSquarefreeCompleteBasis.lean (22 October 2026): the exhaustive
   legal Gram–Schmidt Hilbert basis, norm-convergent legal projection series,
   exact full residual and signed-error identities, and saturation equivalence.
   Saturation for F2 and F3 remains open; see FpOrthonormalBasisResearch20261020.md.
