# Zero-ordinate screening and prime-coordinate Gram certificates

Research continuation, 21–22 October 2026.

This extends the checked density relaxation and inverse-Gram development at
commit 4605ae123e7606fe6ac1e0712dea799d2abc3a11. The new finite identities,
inequalities, prime-increment independence, and actual packet-coordinate
bridges do not assume RH or a zero-density estimate. Actual zero-ordinate
convergence still requires the existing sublinear horizontal-energy provider.

## 1. The laws and the actual Gram matrix

On positive integers,
\[
P(n)=\frac1{n(n+1)},\quad Q(n)=\frac1{\zeta(2)n^2},\quad
\frac{P(n)}{Q(n)}=\zeta(2)\frac n{n+1}.
\]
For integrated Ramanujan packets \(B_q\),
\[
\ell_q=\mathbb E_P B_q=\Lambda(q),\qquad
H_{qr}=\mathbb E_P(B_qB_r),\quad A=H^{-1},\quad
\kappa=\ell^TA\ell.
\]
The source metric is the actual finite inverse-Gram norm
\(\|e\|_A^2=e^TAe\). This is not a replacement by independent phases.
For squarefree conductors the exact signal is supported on primes:
\(\ell_p=\log p\). The sample space itself has not been conditioned to be squarefree.

## 2. A sharper zero contribution

Write \(\rho=\beta+i\gamma\), retaining analytic multiplicity \(m(\rho)\), and
\[
E(T)=\sum_{0<\gamma\le T}m(\rho)(\beta-1/2)^2.
\]
The exact signed relation remains
\[
S_T(u)-L_T(u)=
-\sum_{0<\gamma\le T}m(\rho)e^{iu\gamma}
  \{\cosh(u(\beta-1/2))-1\}.
\]
Reflection, finite cutoffs, and multiplicities are supplied by the existing
actual-zero development.

The previously proved sharp scalar strip inequality has now been propagated
through the actual finite sum:
\[
\|S_T(u)-L_T(u)\|
\le4\{\cosh(|u|/2)-1\}E(T).
\]
The coefficient is bounded above by the previous
\(u^2e^{|u|/2}\) coefficient. It is the optimal uniform quadratic envelope
on the closed strip \(|\beta-1/2|\le1/2\); this does not assert that actual zeros
attain its endpoints.

For the actual cosine estimator \(z_T(q)\) and centered Landau estimator
\(z_T^L(q)\), this gives, for \(q\ge1,T>0\),
\[
|z_T(q)-z_T^L(q)|
\le4\pi(\sqrt q-1)^2\frac{E(T)}T.
\]
The old conductor weight was
\(2\pi\sqrt q(\log q)^2e^{|\log q|/2}\).
The new weight removes its logarithmic-square growth for large q.
The actual full entrywise inverse-Gram budget decreases under this
pointwise improvement; this comparison is itself proved.

With \(v(q)=4\pi(\sqrt q-1)^2\),
\[
\|d_T\|_A^2\le
(E(T)/T)^2\sum_{q,r}|A_{qr}|v(q)v(r),
\qquad d_T=z_T-z_T^L.
\]
All mixed inverse entries are included.

A separate exponential-tail certificate now retains individual frequency
denominators. If the actual right tail satisfies
\(N_+(t,T)\le M e^{-a t}\) on \([0,1/2]\), and \(|\log q|<a\) for every
conductor in the finite family, define
\[
v_a(q)=\frac{4\pi\sqrt q(\log q)^2}{a^2-(\log q)^2}.
\]
Then
\[
\|d_T\|_A^2\le(M/T)^2\sum_{q,r}|A_{qr}|v_a(q)v_a(r).
\]
Unlike the earlier common-band certificate, this retains each denominator.
The tail assumption is explicit; the theorem does not prove its analytic provider.

Lean declarations:
- `ActualZeroCoshMass.coshMass_le_horizontalEnergy_sharp`
- `ActualZeroCoshMass.ordinate_landau_error_sharp`
- `ActualZeroCoshMass.sharp_coefficient_le_exponential`
- `RamanujanZeroSignal.horizontalSignalWeight_eq`
- `RamanujanZeroSignal.inverseGramWeightBudget_horizontal_le_exponential`
- `RamanujanZeroSignal.densityDefect_metric_sq_le_tailProfile_anisotropic`

The existing `horizontalSignalWeight` definition and its consumers now use
the sharper coefficient.

## 3. Remove radial bias before bounding the error

Define
\[
\Pi e=e-\frac{\ell^TAe}{\kappa}\ell,\qquad
K=A-\frac{(A\ell)(A\ell)^T}{\kappa}.
\]
For a nonzero signal, Lean proves the exact identities
\[
\|\Pi e\|_A^2=e^TKe,
\qquad
\|e-c\ell\|_A^2
=\|\Pi e\|_A^2+
\kappa\left(c-\frac{\ell^TAe}{\kappa}\right)^2.
\]
Consequently every chosen scalar c gives
\(\|\Pi e\|_A\le\|e-c\ell\|_A\).
The choice need not approximate zero. On squarefree conductors, its radial
correction changes only the prime coordinates.

Let \(e_L=z_T^L-\ell\) and \(d=z_T-z_T^L\). The full signed decomposition is
\[
\|\Pi z_T\|_A^2
=\|\Pi e_L\|_A^2+
  2\langle\Pi e_L,\Pi d\rangle_A+\|\Pi d\|_A^2.
\]
The interaction is retained before using the triangle inequality.

The normalized coefficients remain
\[
a_T=\frac{Az_T}{\ell^TAz_T},\qquad \ell^Ta_T=1.
\]
The new prime-only normalization theorem requires just a nonzero pairing;
it does not require a small relative error. For a unit target, the existing
complete target identity remains
\[
\|1-F_T\|_P^2=\kappa^{-1}-1+
\frac{\|\Pi z_T\|_A^2}{(\ell^TAz_T)^2}.
\]
Thus the sufficient certificate
\[
\|\Pi e_L\|_A+\|d-c\ell\|_A
\le\eta|\ell^TAz_T|
\]
gives error at most \(\kappa^{-1}-1+\eta^2\).
No radial-error smallness or density premise is part of this finite certificate.

A coordinate bound \(|d_q-c\ell_q|\le Rv_q\) additionally gives
\[
\|\Pi d\|_A^2\le R^2\sum_{q,r}|K_{qr}|v_qv_r.
\]
The signed quadratic form K is smaller than A. Their absolute-entry
majorants are not automatically ordered; no such claim is made.

Lean declarations:
- `FiniteGramSignalStability.inverseNorm_sub_smul_sq_eq_screened`
- `FiniteGramSignalStability.screenedInverseMatrix`
- `FiniteGramSignalStability.inverseNorm_screenedSource_sq_eq_screenedMatrix`
- `FiniteGramSignalStability.inverseNorm_screenedSource_sq_le_entrywise`
- `RamanujanZeroSignal.screened_signal_error_energy_exact`
- `RamanujanZeroSignal.sampled_target_error_le_of_split_screened`
- `RamanujanZeroSignal.densityDefect_screened_metric_sq_le`
- `RamanujanZeroSignal.coefficients_prime_signal_of_pairing`

## 4. Prime-factor independence: what is already unconditional

`PrimeValuationIndependence.lean` already proves, for distinct primes under
the actual Q law, independence of all prime valuation coordinates, their
geometric laws, and the finite Boolean divisibility law. This is not an
assumption about random integers in a finite interval.

In particular, \(Q(p\mid N)=p^{-2}\). Products of normalized centered
divisibility indicators form the actual orthonormal family
\[
\phi_S(N)=\prod_{p\in S}
\frac{1_{p\mid N}-p^{-2}}{\sqrt{p^{-2}(1-p^{-2})}}.
\]
`QFinitePrimeBasis.primeUnitVector_orthonormal` is the checked provider.

A new direct packet consumer proves
\[
\Delta B_p(N)=B_p(N)-B_p(N-1)=1-p1_{p\mid N}.
\]
For distinct primes these increments are mutually independent under Q:
`iIndepFun_primePacketIncrement`. This statement does not say that the
increments are centered or that integrated packets are independent.

## 5. Prime coordinates and the complete Pareto Gram form

For any actual Q Hilbert vector, the new exact norm-transfer identity is
\[
\|f\|_P^2=\zeta(2)\|f\|_Q^2-
\zeta(2)\mathbb E_Q\left[\frac{f(N)^2}{N+1}\right].
\]
The correction is a proved convergent positive series. It is not discarded.

For any finite sum \(f=\sum_S c_S\phi_S\), this yields the exact quadratic
formula followed by the uniform bounds
\[
\frac{\zeta(2)}2\sum_S c_S^2
\le\|f\|_P^2\le\zeta(2)\sum_S c_S^2.
\]
Equivalently the Gram matrix of these auxiliary prime modes satisfies
\(\zeta(2)I/2\preceq G_P\preceq\zeta(2)I\).
Its spectral condition number is at most 2.

For an actual packet synthesis \(f=\sum_q a_q B_q\), let
\(C_{Sq}=\langle B_q,\phi_S\rangle_Q\). With a finite set of prime modes,
the exact identity is
\[
\|f\|_P^2=
\zeta(2)\left(\|Ca\|_2^2+
  \left\|f-\sum_S(Ca)_S\phi_S\right\|_Q^2\right)
-\zeta(2)\mathbb E_Q\left[\frac{f(N)^2}{N+1}\right].
\]
The same identity is proved for the actual target error \(1-f\).
The observation-matrix consequence
\[
a^THa\ge\frac{\zeta(2)}2\|Ca\|_2^2
\]
is also verified.

This incorporates prime independence into the actual packet Gram problem.
To obtain quantitative inverse bounds from C one still needs information
about its rank and smallest singular values. Finite Boolean prime modes
only distinguish divisibility patterns; their projection remainder cannot
be set to zero for general packets. No prime mode is presumed to belong to
the legal squarefree packet span.

Owning modules:
- `RH/ZetaTwoParetoTransfer.lean`: convergent RN correction and exact norm.
- `RH/QPrimeParetoGram.lean`: exact prime-coordinate energy and two-sided bounds.
- `RH/PrimePacketIncrementIndependence.lean`: actual independent prime increments.
- `RH/RamanujanPrimeCoordinates.lean`: actual packet and target-error consumers.

## 6. Formalization boundary

| Assertion | Status after this continuation |
| --- | --- |
| Exact weighted mean and actual packet Gram | Already checked |
| Prime valuations independent under Q | Already checked, reused |
| Sharp finite zero correction and Gram budget | Newly checked |
| Screened matrix, optimal radial correction, signed mixed error | Newly checked |
| Independent actual prime-packet increments under Q | Newly checked |
| Prime-coordinate Pareto Gram and actual packet projection certificates | Newly checked |
| Classical analytic Selberg density provider for actual zeta zeros | Known mathematics; still not formalized here |
| Actual sublinear energy E(T)/T tending to zero | Conditional in the Lean convergence consumers until a provider is supplied |
| Alignment of actual density defect with Lambda | Not supplied by the radial-screening theorem |
| Squarefree packet capacity tending to one | Still an unresolved mathematical obligation in this program |
| Uniform conditioning of growing packet Gram matrices | Not established by auxiliary prime-coordinate conditioning |
| Independence of zeta-zero ordinate phases | Not asserted or used |

Sources: user-directed argument and existing checked repository declarations.
The original fixed-conductor zero-sum motivation is Ford–Zaharescu,
*On the distribution of imaginary parts of zeros of the Riemann zeta function*,
https://www.ford126.web.illinois.edu/wwwpapers/fz.pdf .
No claim of mathematical novelty or improved classical zero-density exponent is made.

## Verification

Targeted import-and-audit job `job_IftM-8dWigpEFiUvcWkCzVs6Hd9kEWrg`
succeeded with exit code 0 and verified=true. The server reported 15.057 seconds
for this targeted execution. It built the changed subject imports, including
the actual packet consumer and independent-increment module.

Ten central declarations were audited with `#print axioms`; every list contained
only `propext`, `Classical.choice`, and `Quot.sound`. The printed convergence
type still explicitly includes `SublinearHorizontalEnergy`; the printed actual
prime-valuation independence type contains only primality and injectivity
hypotheses. Axiom audits do not remove local hypotheses from theorem types.

The earlier coherent development check `job_ssFcPEOdqHKy99dpBA2Jlmsrh9sgz7Ag`
also succeeded, with reported execution 23.292 seconds. These targeted checks
are distinct from the final checkpoint's aggregate validation.

The workspace-opening request was not separately timed, so no precise opening
duration is claimed. Queue/polling latency is distinct from the server-reported
verification durations. Publication requires the containing commit's successful
server checkpoint, including its full exported-project validation.
