# GROW-001: signed residual certificates for the actual canonical lift

13 November 2026. Source: continuation of the user's proof-triage target.
This is an independently derived formalization, without a novelty claim.

**Status:** the finite response certificate is formalized; the uniform eventual
canonical growth provider remains **Open**. No RH conclusion is claimed.

## Actual system and an arbitrary predictor

Let U be synthesis of the repository's joined old/screened-new family.
Let A be its actual nonsymmetric difference-test collocation operator,
and beta its prescribed source from h_M - F_L. These are constructed in
QCRTScreenedCoordinates.lean; their invertibility is already proved.
No physical Gram inverse is substituted for A inverse.

For any proposed coefficient vector z, put

    v = U z,   rho = beta - A z,
    T = U A^{-1},   w_i = T e_i,
    epsilon = sum_i |rho_i| ||w_i||_Q.

Every quantity here uses the old canonical vector, the new target, the
predictor, and the actual finite collocation system. It does not require
the unknown F_M as an input. All norms and inner products include the
complete infinite physical Q tail.

The new application theorems prove

    F_M - (F_L + v) = T rho,
    ||F_M - (F_L + v)||_Q <= epsilon,
    ||T rho||_Q^2 <= (sum_i rho_i^2)(sum_i ||w_i||_Q^2).

The last formula explains exactly which inverse-response cost must accompany
PAPER-001's raw squared-source estimate. Neither its decay nor boundedness
uniformly along admissions has been proved.

## Exact signed energy and a certified upper bound

With e = T rho, the full equality is

    E_M - E_L =
      2<F_L,v>_Q + ||v||_Q^2
      + 2<F_L+v,e>_Q + ||e||_Q^2.

The signed predictor term remains exact. For z=(x,y), Lean identifies it as

    2 c^T G x + x^T G x + y^T H y.

The error terms alone are bounded to obtain

    E_M - E_L <=
      2<F_L,v>_Q + ||v||_Q^2
      + 2 ||F_L+v||_Q epsilon + epsilon^2.

Thus a concrete upper bound on the right-hand side by alpha E_L certifies
E_M <= (1+alpha) E_L for the **actual** canonical vectors. The theorem
canonical_growth_of_residual_certificate is a **conditional research
reduction**: its finite certificate inequality is an explicit hypothesis,
not an established provider.

## Exact old-block elimination

Choose x0 = A00^{-1} beta0 and z0=(x0,0). The checked residual is exactly

    rho(z0) = (0, sigma),
    sigma = beta1 - A10 A00^{-1} beta0.

Consequently its radius reduces to

    epsilon(z0) =
      sum_new j |sigma_j| || U A^{-1} e_(new j) ||_Q.

These full inverse columns contain both the new Schur response and the
compensating old refit. This is not the physical inverse H^{-1}, and A01
and A10 are not identified by transpose.

## Zero cases and row normalization

No division by residual energy, projected-test capacity, or E_L occurs.
Zero radius implies an exact predicted update. Zero Schur source also
gives the exact old-only predictor, including an empty new block.

For positive row scales a_i, multiplying rho_i by a_i and the matching
response column by a_i^{-1} leaves epsilon unchanged. This identity is
proved in FiniteCollocationCertificate.radius_rescaling. Raw conductor
factors therefore cannot create a response gain by coordinate normalization.

## Unconditional upper bound in the physical period

For a period \(P\ge2\) write
\[
 W_{P,r}=\sum_{k\ge0}(r+kP)^{-2},\qquad
 C_P=\frac{W_{P,P-1}}{W_{P,P-1}-W_{P,P}} .
\]
If \(f\) is \(P\)-periodic and vanishes at multiples of \(P\), its complete
physical energy and anchored shift defect satisfy
\[
 \|f\|_Q^2\le C_P\,\bigl(\|f\|_Q^2-\|Sf\|_Q^2\bigr).
\]
Indeed, writing \(Z=\zeta(2)\), the two sides before multiplication by
\(C_P\) are respectively \(Z^{-1}\sum_{r<P}W_{P,r}|f(r)|^2\) and
\(Z^{-1}\sum_{r<P}(W_{P,r}-W_{P,r+1})|f(r)|^2\), with \(r\ge1\).
Cauchy–Schwarz and \((n+1)^{-2}\le[n(n+2)]^{-1}\) imply
\(W_{P,r+1}^2\le W_{P,r}W_{P,r+2}\). Thus \(W_{P,r+1}/W_{P,r}\)
increases with \(r\), and the largest weight ratio occurs at \(r=P-1\).
The periodic indicator of that residue attains equality, so this is the
optimal constant for this class of physical sequences.

Since \(P^2W_{P,P}=\zeta(2)\) and
\(P^2W_{P,P-1}=\sum_{j\ge1}(j-1/P)^{-2}\), expansion in \(1/P\) gives
\[
 C_P \le 1+\frac{\zeta(2)P}{2\zeta(3)},\qquad
 C_P=\frac{\zeta(2)}{2\zeta(3)}P+O(1).
\]
For the inequality retain the first two nonnegative terms in
\((1-1/(Pj))^{-2}\). For the asymptotic the further terms in
\(P^2(W_{P,P-1}-W_{P,P})\) total \(O(P^{-2})\), uniformly for \(P\ge2\).

Each trial atom \(g_d\), \(d\mid P\), is periodic and vanishes at multiples
of \(P\). Applying the comparison to the canonical lift \(F_P\) and using
`canonical_difference_energy` yields the unconditional estimate
\[
 E_P\le C_P\bigl[1-P^{-2}-\|\mathcal D F_P-h_P\|_Q^2\bigr].
\]
The same argument applies to \(\Delta F=F_M-F_L\) for \(L\mid M\). With
\(b=h_M-T_M F_L\), \(r_L=F_L-h_L\), and \(T_M\) the orthogonal
projection onto the finer gcd-cell space, put
\[
 B=\|b\|_Q^2=L^{-2}-M^{-2}+\|T_Mr_L\|_Q^2,\qquad
 J=B-\|\mathcal D\Delta F-b\|_Q^2.
\]
The matched difference-energy identity gives
\(J=\|\Delta F\|_Q^2-\|S\Delta F\|_Q^2\). Consequently
\[
 \|\Delta F\|_Q^2\le C_M J\le C_M B,\qquad
 E_M-E_L\le 2\sqrt{E_L C_M B}+C_M B .
\]
These are paper consequences of the checked finite identities. They give a
cofinal upper bound in the physical period, which can grow exponentially
with the arithmetic cutoff on the LCM tower. The smaller signed bound
needed for the RH criterion remains open.
[Canonical shift defect](QCRTFiniteCollocation.lean)
· [Nested source and energy identities](QCRTNestedCutoffs.lean)

At prime periods \(p\) the period exponent one is necessary for any
all-period bound. The exact prime-lift formula also gives
\[
 E_p=\zeta(2)\bigl(\log(2\pi)-\gamma\bigr)
       \frac{p}{(\log p+1)^2}\bigl(1+O(1/p)\bigr),
\]
where \(\gamma\) is Euler's constant. In fact \(g_p(n)=\{n/p\}\) spans
the trial space and \(F_p=(1-p^{-2})g_p/\mathbb E_Qg_p\).
Writing \(Z=\zeta(2)\) as above,
\[
 pZ\mathbb E_Q g_p=H_{p-1}+\int_1^\infty \{t\}t^{-2}dt+O(1/p)
       =\log p+1+O(1/p),\qquad
 pZ\|g_p\|_Q^2=\int_0^\infty\{t\}^2t^{-2}dt+O(1/p).
\]
Both mesh errors follow from bounded variation. On \([1,\infty)\) the
variation on each \([m,m+1)\), together with its jump, is \(O(m^{-2})\).
The first integral equals \(1-\gamma\) by summation over unit intervals.
The second through \(K+1\) equals
\(2K+2-H_{K+1}-2K\log(K+1)+2\log(K!)\); Stirling's formula gives
\(\log(2\pi)-\gamma\). The stated asymptotic follows by taking the ratio.
In particular a uniform bound \(E_P=O(P^{1-\epsilon})\) over all periods
fails for every \(\epsilon>0\). The cofinal LCM sequence has different
arithmetic and is consistent with a subpolynomial cutoff bound.
[Exact prime canonical lift](QCRTPrimeCutoffGrowth.lean)

For a nested pair and any predictor \(w=F_L+\Phi z\in V_M\), the error
\(e=F_M-w\) satisfies the same difference identity with the orthogonal
projection \(b\) of \(h_M-w\) onto \(\mathcal D V_M\). Indeed collocation
gives \(\langle e,\mathcal D e\rangle_Q=\langle b,\mathcal D e\rangle_Q\).
Expanding the square yields
\[
 \|\mathcal D e-b\|_Q^2+
    \|e\|_Q^2-\|Se\|_Q^2=\|b\|_Q^2 .
\]
Consequently the signed residual-column interval can use the smaller of
the inverse-column radius and \(\sqrt{C_M}\|b\|_Q\). This second radius
requires only the positive physical Gram matrix of the test vectors.
In the raw divisor basis, for \(d,e>1\) dividing \(M\), it is exactly
\[
 J_{de}=\langle \mathcal Dg_d,\mathcal Dg_e\rangle_Q
 =\frac1{de}-\frac1{de^2}-\frac1{d^2e}+\frac1{[d,e]^2}.
\]
The tests are independent by strict accretivity on the finite trial
space. For \(\rho_d=\langle h_M-w,\mathcal Dg_d\rangle_Q\), the squared
projection norm is \(\rho^\mathsf{T}J^{-1}\rho\). One can instead use
the elementary upper bound \(\|b\|_Q\le\|h_M-w\|_Q\).

The test Gram inverse can also be evaluated analytically. For \(g\mid M\)
let \(p_g=g^{-2}\prod_{\ell\mid M/g,\ \ell\ {\rm prime}}(1-\ell^{-2})\)
be the \(Q\)-mass of the gcd cell and \(u_g=\varphi(M/g)/M\) its
ordinary uniform-period mass. On the finite cell space,
\(\mathcal D V_M=\{f:\sum_g u_g f(g)=0\}\), since every basis difference
\(1/d-1_{d\mid n}\) has uniform mean zero and these tests have codimension
one. Extend the raw residual by \(\rho_1=0\), and set
\(\xi_g=\sum_{k\mid M/g}\mu(k)\rho_{gk}\). For the cell profile of \(b\),
the test equations give
\(\sum_{g:\,d\mid g}p_g b(g)=s/d-\rho_d\), where \(s=\sum_g p_g b(g)\).
Divisor Möbius inversion gives \(p_g b(g)=s u_g-\xi_g\).
Eliminating \(s\) by \(\sum_g u_g b(g)=0\) yields
\[
 \|b\|_Q^2=\sum_{g\mid M}\frac{\xi_g^2}{p_g}
  -\frac{\bigl(\sum_{g\mid M}u_g\xi_g/p_g\bigr)^2}
         {\sum_{g\mid M}u_g^2/p_g},\qquad
 \sum_{g\mid M}u_g^2/p_g=
 \prod_{\ell^\nu\parallel M}\left(1+\nu\frac{\ell-1}{\ell+1}\right).
\]
The product follows by writing \(k=M/g\) and factoring the divisor sum.
This gives a residual radius directly from signed divisor sums.

For every even \(M\), take \(w=F_2=1_{\rm odd}=2g_2\). Its squared norm
is \(3/4\), and \(\|h_M-w\|_Q^2=1/4-M^{-2}\). Thus the actual even-period
lifts satisfy the unconditional bound
\[
 E_M\le\left(\sqrt{3/4}+\sqrt{C_M(1/4-M^{-2})}\right)^2,\qquad
 \limsup_{M\to\infty,\ 2\mid M} E_M/M\le\frac{\zeta(2)}{8\zeta(3)}.
\]
More generally, on a divisor-exhausting nested tower, use any fixed
earlier trial vector \(v\). Since \(\|h_M-1\|_Q=M^{-1}\), dividing the
norm bound by \(\sqrt M\) and taking the infimum over all such \(v\)
bounds \(\limsup E_M/M\) by \(\zeta(2)/(2\zeta(3))\) times the squared
distance of \(1\) to the closed union of trial spaces.

## Remaining arithmetic provider

**Open:** construct predictors and certified complete-tail estimates for
the actual LCM prime-power admissions such that

    2<F_L,v>_Q + ||v||_Q^2
      + 2||F_L+v||_Q epsilon + epsilon^2 <= (C/p^k) E_L

eventually with **one fixed C**. A separate finite constant at each stage
does not establish GROW-001. The original signed response estimate itself
also remains open: the error certificate is a sufficient route, and may
be stronger because it bounds the unknown error correlation in absolute value.

Owning modules:
- Analysis/FiniteCollocationCertificate.lean: generic inverse-column
  response, exact signed residual identity, error bounds, zero case and
  positive row-rescaling identity.
- RH/QCRTCanonicalGrowthCertificate.lean: actual CRT instantiation,
  explicit signed old-refit energy, and exact old-only/Schur-source reduction.

## Verification

The owning application module and its generic certificate dependency passed
Bazel/BuildBuddy file check `job_IjsQM_7tpIN-VWcN_Z3ZACiJKXyuMxZI` (106.139 s):
[https://app.buildbuddy.io/invocation/b6c2da7b-0119-49b8-9ed6-12c2ceddc0d0](https://app.buildbuddy.io/invocation/b6c2da7b-0119-49b8-9ed6-12c2ceddc0d0).
Application source SHA-256: `d2fb6b6ec0b9396ec01659b8ca784b5b885209a5b9b4169b83386f5fda2233e8`.
All 30 declarations passed the strict transitive axiom whitelist in
`job_eb19EhAX5_qTVMu7RgtZMvTEeTyNla2l` (38.554 s):
[axiom audit](https://app.buildbuddy.io/invocation/bd60faf6-1b01-4c59-9db6-5ab038e159e8).
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted; this is
an allowed set, not a claim that every declaration uses all three.
The final full-project publication checkpoint is separately required.
