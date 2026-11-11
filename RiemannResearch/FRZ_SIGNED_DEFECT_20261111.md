# FRZ signed S₁ defect: investigation and proposed changes

Date: 2026-11-11
Inspected base: 6c4fe3312e24b00813bcc5c329cf28ba0fe14333
Status: approved for the repository checkpoint on 2026-11-11.

## Results and their status

1. **New checked finite-spectrum bounds.** The combined defect of a coefficient truncation is exactly the off-diagonal energy of its tail. A perturbation identity couples an approximation error only to the tail, not to the full reference polynomial. Twelve named declarations in two proposed Lean modules have passed a focused Bazel/BuildBuddy file check, including transitive imports.
2. **Unconditional mathematical deduction from classical theorems.** For the canonically normalized S₁ and the standard prime-power cosine polynomial P_X, the strongest estimate derived here is
   \[
   |D_X(T)|+\int_0^T|S_1(t)-P_X(t)|^2\,dt
   \ll_\vartheta \frac{T}{\log T},\qquad X=T^\vartheta,
   \quad 0<\vartheta<1/5.
   \]
   The proof aggregates horizontal modes, uses fifth moments at the actual zeros, and applies Selberg's density estimate with multiplicities. It retains gamma and endpoint corrections. This analytic assembly and the classical providers are **not newly kernel-checked** here.
3. **No new complete growing-support asymptotic.** The deduction improves the direct second-derivative/S₁ estimate. The complementary first-derivative/S estimate already allows a wider range. The finite cancellation identities alone do not improve that best range or establish Montgomery pair correlation.
4. **No claimed optimum in the literature.** The displayed bound is a deduction established from the sources inspected here, with its proof below. A sharper direct Selberg-type S₁ approximation may be obtainable, but it is not certified by substituting an RH-dependent mixed-moment theorem.

## 1. Definitions and the exact defect

Use the canonical normalization
\[
U(t)=\delta_1+\int_0^t S(u)\,du,\qquad
\delta_1=\frac1\pi\int_{1/2}^{\infty}\log|\zeta(\sigma)|\,d\sigma.
\]
Here \(\theta(t)\) is the continuous Riemann–Siegel theta function, \(\theta(0)=0\),
\[
N(t)=\sum_{0<\gamma\le t}m_\rho,\quad
S(t)=N(t)-1-\theta(t)/\pi,\quad \mu(t)=\theta'(t)/\pi.
\]
Every distinct analytic zero is weighted by its analytic multiplicity \(m_\rho\); different zeros with the same ordinate are still counted. The upper endpoint is included. At zero heights this right-continuous S differs from the usual averaged convention only on a null set. Endpoint terms must nevertheless use the chosen convention consistently.

For a finite spectrum, put
\[
P(t)=\sum_i c_i e^{i\omega_i t},\qquad E_P=\sum_i|c_i|^2,
\]
\[
e_U=\int_0^T|U|^2-CT,\quad e_P=\int_0^T|P|^2-TE_P,\quad
r_i=\int_0^T U(t)e^{-i\omega_i t}\,dt-Tc_i.
\]
The repository's exact identity is
\[
D=e_U+e_P-2\Re\sum_i\overline{c_i}r_i,\qquad
R_P:=\int_0^T|U-P|^2=T(C-E_P)+D.
\]
Consequently \(D\ge -T(C-E_P)\). A signed upper bound suffices for an upper residual bound; separate absolute estimates are stronger requirements.

An arbitrary additive constant in U is not harmless. The classical mean-square constant C below applies to the canonical normalization. The exact Lean identities allow any normalization and do not silently identify it with the canonical one.

## 2. Exact cancellation for finite reference polynomials

Let
\[
Q(t)=\sum_i a_i e^{i\omega_i t},\quad
P(t)=\sum_i c_i e^{i\omega_i t},\quad H=Q-P.
\]
Write
\[
K_T(v)=\int_0^T e^{ivt}\,dt,\qquad
\operatorname{OD}_T(h)=
\sum_{i\ne j}\overline{h_i}h_j K_T(\omega_j-\omega_i).
\]
The kernel retains both endpoints: \(K_T(0)=T\) and
\(K_T(v)=(e^{ivT}-1)/(iv)\) for \(v\ne0\).

The checked general identity is
\[
D(Q,c;T,C)=
T\left(\sum_i|a_i-c_i|^2-C+\sum_i|c_i|^2\right)
+\Re\operatorname{OD}_T(a-c).
\]
If \(c_i=a_i\) on a selected set and \(c_i=0\) elsewhere, and \(C=\sum|a_i|^2\), then
\[
\boxed{D(Q,P)=\Re\operatorname{OD}_T(a-c).}
\]
Thus all head-head terms and head-tail terms cancel exactly between the three defects. For any valid local separation weights
\(0<\delta_i\le|\omega_i-\omega_j|\) for \(j\ne i\),
\[
\boxed{|D(Q,P)|\le26\sum_i\frac{|a_i-c_i|^2}{\delta_i}.}
\]
One can restrict the index set to the active tail before choosing the gaps.

This is a genuine improvement over separately bounding full energy and correlations. Increasing the head coefficients while keeping the tail fixed leaves the combined defect unchanged, whereas separate error bounds can grow.

There is no general nonpositivity principle. For the two-mode tail
\(H=e^{iut}+e^{ivt}\), its defect is
\(2\sin((v-u)T)/(v-u)\), which has either sign. Prime support and positivity of coefficient energies do not remove this phenomenon.

### Perturbation toward the actual primitive

Put \(R=U-Q\). The checked comparison identity is
\[
\boxed{D(U,P;C)=D(Q,P;C)+\|R\|_2^2+2\Re\langle R,H\rangle.}
\]
If \(\|R\|_2^2\le B\) and \(\|H\|_2^2\le K\), then
\[
D(U,P;C)\le D(Q,P;C)+B+2\sqrt{BK}.
\]
The mixed term involves the unretained tail. Applying Cauchy–Schwarz before the exact cancellation would instead expose the much larger norm of Q or P.

For canonical nested prime-power cutoffs \(X<Y\), let
\(\tau_X=C-E_X\), \(H=P_Y-P_X\), and \(R_Y=U-P_Y\). Then
\[
D_X=-T\tau_Y+\Re\operatorname{OD}_T(H)
+\|R_Y\|_2^2+2\Re\langle R_Y,H\rangle.
\]
All four terms are retained. A finite-polynomial calculation does not supply the missing bound on the actual \(R_Y\).

## 3. Actual-zero integration, with gamma and endpoints

For \(\ell>0\), define
\[
Z_\ell(T)=\sum_{0<\gamma\le T}m_\rho e^{i\ell\gamma},\quad
I_\ell(T)=\int_0^T U(t)e^{i\ell t}\,dt,
\]
\[
G_\ell(T)=\int_0^T\mu(t)e^{i\ell t}\,dt,\quad
B_\ell(T)=[S(t)e^{i\ell t}-i\ell U(t)e^{i\ell t}]_0^T.
\]
The proposed actual-zero module checks
\[
\boxed{\ell^2I_\ell=G_\ell+B_\ell-Z_\ell.}
\]
Its Lean statement also retains the zero sum at height 0, rather than suppressing it by notation. This follows directly from the existing multiplicity-aware twice-integrated identity.

For a general finite test polynomial F,
\[
\sum_{0<\gamma\le T}m_\rho F(\gamma)
=\int_0^T\mu F+[SF-UF']_0^T+\int_0^T PF''
+\underbrace{\int_0^T(U-P)F''}_{\mathcal E_{P,F}}.
\]
The second new actual-zero theorem gives, without asymptotic providers,
\[
|\mathcal E_{P,F}|^2
\le \{T(C-E_P)+D\}(T+26/\delta)J_4(F).
\]
This is an unconditional inequality containing the actual defect; it is not itself a small-defect estimate.

## 4. Unconditional actual S₁ estimates: pointwise fallback and aggregate improvement

Let
\[
a_n=\frac{\Lambda(n)}{\pi\sqrt n(\log n)^2},\quad
P_X(t)=\sum_{2\le n\le X}a_n\cos(t\log n),
\]
\[
C=\frac1{2\pi^2}\sum_{n\ge2}\frac{\Lambda(n)^2}{n(\log n)^4},
\quad E_X=\frac12\sum_{n\le X}a_n^2,\quad \tau_X=C-E_X.
\]
Only prime powers contribute. Replacing this polynomial by a sum over primes alone leaves a fixed positive energy contribution from omitted higher prime powers.

The external inputs are:

- Selberg's canonical second moment: \(e_U=O(T/\log T)\). Chirre–Quesada-Herrera, equation (1.5) and its normalization footnote, records this unconditional result. Their sharper mixed-moment Lemma 8 explicitly assumes RH.
- Ford–Zaharescu, Lemma 1, gives a uniform Landau formula; Lemma 2 and equation (3.8) give the unconditional horizontal-to-ordinate error. At prime powers n, with \(L=\log T\) and \(\log n\le L/(100\log L)\), these imply
  \[
  Z_{\log n}(T)=-\frac{T\Lambda(n)}{2\pi\sqrt n}
  +O\!\left(\frac{T(\log n)^2}{L}
       +\sqrt n\log^2(2nT)+\frac{L}{\sqrt n\log n}\right).
  \]
- The classical \(S(T),U(T)=O(\log T)\) endpoint bounds and smooth gamma estimates give
  \(|G_\ell|\ll L/\ell\), \(|B_\ell|\ll L(1+\ell)\). The exact gamma integral is retained before this estimate.
- Chebyshev's bound \(\psi(x)\ll x\), partial summation, and the already proved weighted mean-value inequality control the finite polynomial and coefficient sums.

Combining these inputs with the exact mode identity yields, uniformly in this n-range,
\[
\left|I_{\log n}(T)-\frac{T a_n}{2}\right|
\ll \frac{T}{L}+
\frac{\sqrt n\log^2(2nT)}{(\log n)^2}+\frac{L}{\log n}.
\]
This is a deduction here from the cited inputs, not the RH-dependent mixed-moment formula.

For \(3\le X\le\exp(L/(100\log L))\), partial summation gives
\[
\sum_{n\le X}a_n\ll\frac{\sqrt X}{(\log X)^2},\quad
\sum_{n\le X}\frac{a_n}{\log n}\ll\frac{\sqrt X}{(\log X)^3},
\]
\[
\tau_X\ll(\log X)^{-2},\quad
|e_{P_X}|\ll X/(\log X)^3.
\]
For the last bound, the signed frequencies \(\pm\log n\) admit local gaps
\(1/(2n)\). Also \(\Lambda(n)^2\le\Lambda(n)\log n\).

It follows, with absolute implied constants for sufficiently large T, that
\[
\boxed{
|D_X(T)|\ll
\frac{T}{L}\left(1+\frac{\sqrt X}{(\log X)^2}\right)
+\frac{X\log^2(2XT)}{(\log X)^4}
+\frac{X}{(\log X)^3}
+\frac{L\sqrt X}{(\log X)^3}.}
\]
In particular, \(D_X=O_X(T/L)\) at each fixed X. Taking \(X=L^2\) gives
\[
|D_X(T)|\ll T/(\log L)^2,\qquad
R_X=T\tau_X+D_X\ll T/(\log L)^2.
\]

This fallback uses absolute bounds after recording the exact signed identity. It does **not** establish additional cancellation for actual S₁. It shows precisely what is already available from classical unconditional inputs before asking for a stronger spectral estimate.

### A stronger polynomial-cutoff bound by aggregating the horizontal modes

The pointwise-mode fallback above is not the strongest bound obtained in this investigation. The following argument sums over the modes before applying a moment inequality. It uses only unconditional classical inputs and elementary finite Dirichlet-polynomial estimates. It is a mathematical deduction; the analytic assembly is not kernel-checked.

**Claim.** For each fixed \(0<\vartheta<1/5\), with \(X=T^\vartheta\),
\[
\boxed{|D_X(T)|\ll_\vartheta T/\log T,\qquad
\int_0^T|U-P_X|^2\ll_\vartheta T/\log T.}
\]
All prime powers in \(P_X\) and all analytic zero multiplicities are retained.

Here is a derivation with the required uniformities exposed. Put \(L=\log T\),
\[
\eta_\rho=|\beta-1/2|,\qquad
V_{X,u}(t)=\sum_{n\le X}a_n\cosh(u\log n)\cos(t\log n),
\quad 0\le u\le1/2.
\]
For any fixed integer \(q\ge2\) and \(X^q\le T\), we first establish the actual-zero sampling bound
\[
\tag{S_q}
\sum_{0<\gamma\le T}m_\rho |V_{X,u}(\gamma)|^q
\ll_q TL X^{qu}.
\]
This step needs no hypothesis about the real parts of the zeros.

To verify it, write \(V_{X,u}=\Re A_{X,u}\), where
\(A_{X,u}(t)=\sum_{n\le X}a_n\cosh(u\log n)n^{it}\).
Let \(d_q\) be the ordered q-fold divisor function. Cauchy–Schwarz on each product fiber and the elementary inequality \(d_q(nm)\le d_q(n)d_q(m)\) give
\[
\sum_k\left|\sum_{n_1\cdots n_q=k}c_{n_1}\cdots c_{n_q}\right|^2
\le\left(\sum_n d_q(n)|c_n|^2\right)^q.
\]
For \(n=p^k\), \(d_q(n)=\binom{k+q-1}{q-1}\). Consequently,
\[
\sum_{n\le X}d_q(n)a_n^2\cosh^2(u\log n)\ll_q X^{2u},
\]
\[
\sum_{n\le X}d_q(n)a_n^2(\log n)^2\cosh^2(u\log n)
\ll_q X^{2u}\log\log(3X).
\]
The prime contributions are bounded respectively by the convergent sum \(\sum_p1/(p\log^2p)\) and by \(\sum_{p\le X}1/p\ll\log\log(3X)\); the higher-power contributions converge. The ordinary mean-value inequality, applied to the q-th powers (whose product frequencies are logs of distinct integers at most \(X^q\)), now gives
\[
\int_0^T|A_{X,u}|^{2q}\ll_q TX^{2qu},\qquad
\int_0^T|A'_{X,u}|^{2q}
\ll_q TX^{2qu}\{\log\log(3X)\}^{q}.
\]
The separation used here is \(1/X^q\); the finite mean-value factor is \(T+26X^q\), so no uniformity in the cutoff has been hidden.

Apply the exact once-integrated counting identity to \(F=|V_{X,u}|^q\):
\[
\sum_{0<\gamma\le T}m_\rho F(\gamma)
=\int_0^T\mu(t)F(t)\,dt+[S(t)F(t)]_0^T-\int_0^T S(t)F'(t)\,dt.
\]
Gamma and both endpoints occur explicitly. The preceding polynomial moments imply
\[
\int_0^T F\ll_q TX^{qu},\qquad
\int_0^T |F'|^2\ll_q TX^{2qu}\log\log(3X).
\]
Use \(|\mu(t)|\ll\log(2+t)\), \(S(T)=O(L)\), and Selberg's unconditional \(\int_0^T S^2\ll T\log L\). The three terms are respectively bounded by
\[
O_q(TLX^{qu}),\quad O_q(LX^{q/2+qu}),\quad
O_q\!\left(TX^{qu}\sqrt{\log L\,\log\log(3X)}\right).
\]
The endpoint bound follows from \(\sum_{n\le X}a_n\ll\sqrt X\), and \(X^{q/2}\le\sqrt T\). These estimates prove \((S_q)\), uniformly in \(0\le u\le1/2\). The right-continuous convention is used throughout; an initial finite interval can equivalently be retained in the endpoint budget.

Next, Selberg's uniform density estimate as stated in Ford–Zaharescu Lemma 2, together with reflection symmetry, gives
\[
\#\{\rho:0<\gamma\le T,\ \eta_\rho>v\}
\ll TL e^{-Lv/4},\qquad 0\le v\le1/2,
\]
where the count includes multiplicities. For \(p=q/(q-1)\), layer-cake integration yields
\[
\tag{D_p}
\sum_{0<\gamma\le T}m_\rho(\eta_\rho-u)_+^p
\ll_p T L^{1-p}e^{-Lu/4}.
\]
Indeed, integrate \(p(v-u)^{p-1}\) against the displayed tail count over \(u\le v\le1/2\), and extend the positive exponential integral to infinity.

Let \(H_n=Z_{\log n}-n^{-1/2}\sum m_\rho n^\rho\), as in the exact signed decomposition below. The identity
\[
\frac{\cosh(\eta\ell)-1}{\ell^2}
=\int_0^{1/2}(\eta-u)_+\cosh(u\ell)\,du
\quad(0\le\eta\le1/2)
\]
and reflection symmetry give the **signed, aggregated** formula
\[
\tag{H}
2\sum_{n\le X}\frac{a_n}{(\log n)^2}\Re H_n
=-2\int_0^{1/2}\sum_{0<\gamma\le T}
m_\rho(\eta_\rho-u)_+ V_{X,u}(\gamma)\,du.
\]
Only now apply weighted Hölder, combining \((S_q)\) and \((D_p)\). The absolute value of the inner sum is at most
\[
O_q\!\left(T\exp\{-(1/(4p)-\vartheta)Lu\}\right).
\]
For \(\vartheta<1/(4p)\), its u-integral is \(O_{q,\vartheta}(T/L)\).
Taking \(q=5\), \(p=5/4\) simultaneously permits \(X^5\le T\) and \(\vartheta<1/5\). The simpler q=2 argument already gives the same order for \(\vartheta<1/8\).

Finally combine (H) with the exact defect decomposition below, Selberg's \(e_U=O(T/L)\), and the prime-power Landau, gamma, endpoint and polynomial bounds. Those latter terms are \(o(T/L^2)\) for this fixed power cutoff. Since \(\tau_X=O_\vartheta(L^{-2})\), both claims follow.

This improves the pointwise-mode fallback by controlling the aggregate horizontal contribution with its spectral moments. It **does not** prove cancellation between that aggregate and \(e_U\): they are still bounded separately at order \(T/L\). Obtaining the further factor \(1/L\) remains the precise signed cancellation problem below. The argument is not claimed to be new in the literature or optimal among all direct Selberg-type approximation theorems.


### The signed target that would improve it

For prime powers n set
\[
W_n=n^{-1/2}\sum_{0<\gamma\le T}m_\rho n^\rho,\quad
H_n=Z_{\log n}-W_n,\quad
A_n=W_n+\frac{T\Lambda(n)}{2\pi\sqrt n}.
\]
Reflection symmetry, with multiplicities, gives the exact expression
\[
H_n=\sum_{0<\gamma\le T}m_\rho e^{i\gamma\log n}
\{1-\cosh((\beta-\tfrac12)\log n)\}.
\]
Thus the actual signed defect is
\[
\boxed{
D_X=e_U+e_{P_X}
+2\sum_{n\le X}\frac{a_n}{(\log n)^2}
\Re(H_n+A_n-G_{\log n}-B_{\log n}).}
\]
A concrete stronger target is the **coupled**, one-sided estimate
\[
e_U+2\sum_{n\le X}\frac{a_n}{(\log n)^2}\Re H_n
\ll T/L^2,\qquad X=T^\vartheta
\]
for a fixed small positive \(\vartheta\). The remaining displayed terms are
\(o(T/L^2)\) for fixed \(0<\vartheta<1\) using the uniform prime-power Landau bound and the endpoint estimates. This would give \(D_X\ll T/L^2\) and \(R_X\ll T/L^2\).

This target has not been proved here. It involves the energy defect and the signed horizontal-mode sum jointly. A bound on \(\sum m_\rho(\beta-1/2)^2\) alone discards the required signs. A correctly normalized direct mean-square approximation theorem with this uniform cutoff would be another way to supply the provider; that theorem has not been extracted and verified in this investigation.

## 5. J₂/J₄, multiplicative energy, and the range comparison

For the test \(A(t)=\sum_{n\in S}u_n n^{it}\), aggregate ratios first:
\[
F(t)=|A(t)|^2-E=\sum_{q\ne1}b_q q^{it},\quad
E=\sum|u_n|^2,\quad J_j=\sum_{q\ne1}|b_q|^2|\log q|^j.
\]
Let \(\Delta=\log(\max S/\min S)\), and \(M\ge\max S\).
The existing arithmetic results give
\[
J_4\le\Delta^2J_2\le\tfrac12\Delta^4E^2
\]
on prime support. For \(\Omega(n)\le d\), replace the prime constant by
\(\binom{2d}{d}-1\) in the bound
\(J_4\le\Delta^4(\binom{2d}{d}-1)E^2\).
For unrestricted support use the actual product energy:
\(J_4\le\Delta^4(\mathcal M-E^2)\), where
\(\mathcal M=\sum_k|\sum_{nm=k}u_nu_m|^2\).

The rational gap is at least \(1/M^2\). With \(N(T)\asymp TL\),
\[
\frac{|\mathcal E_{P,F}|}{N(T)E}
\ll \frac{\Delta^2}{L}\sqrt{\frac{R_X}{T}}\,
\sqrt{1+M^2/T}
\]
on prime support. Local gaps give a stronger, coefficient-sensitive version.

For comparison, when the gap factor stays bounded:

| Input | Sufficient width for the corresponding normalized remainder to vanish |
|---|---|
| Raw \(U\) second moment \(R=O(T)\) | \(\Delta=o(\sqrt L)\) |
| Pointwise-mode fallback \(R_X=O(T/(\log L)^2)\) | \(\Delta=o(\sqrt{L\log L})\) |
| Aggregate fifth-moment bound \(R_X=O(T/L)\) | \(\Delta=o(L^{3/4})\) |
| Classical first-derivative method \(\int S^2\ll T\log L\), \(J_2\le\Delta^2E^2/2\) | \(\Delta=o(L/\sqrt{\log L})\) |
| Desired \(R_X=O(T/L^2)\) | \(\Delta=o(L)\) |

The first-derivative row retains its own exact boundary/correction terms. These are remainder comparisons, not assertions that those explicit terms vanish. Neither the fallback nor the stronger aggregate bound beats the existing J₂ range. The new deduction improves the direct S₁ route only.

For \(M=T^\alpha\), \(\Delta\asymp L\), even \(R_X=O(T/L^2)\) gives only an \(O(1)\) relative bound when the gap factor is bounded. A norm-only route would require
\[
R_X=o\!\left(\frac{TL^2}{\Delta^4(1+M^2/T)}\right).
\]
Alternatively, prove cancellation in the actual test pairing:
\[
-\sum_{q\ne1}b_q(\log q)^2
\int_0^T(U-P_X)(t)q^{it}\,dt=o(N(T)E).
\]
This is the exact spectral estimate needed for this corrected FRZ remainder. It must be combined with the retained polynomial bias, gamma and boundary terms, and the separate transfer to Montgomery's statistic. For support beyond the classical pair-correlation range, the corresponding signed shifted von Mangoldt correlations remain an additional arithmetic obligation. J₂/J₄ energy bounds alone do not establish them.

## 6. Numerical experiments

The supplied Python script uses the closed finite-interval kernel, not time-grid quadrature, for every finite-polynomial test. These are floating-point experiments, not kernel certificates.

Take \(Q=P_{97}\) and \(P=P_7\), including all prime powers. The total C in this finite experiment is exactly the coefficient energy of Q.

| T | Combined D | Sum of separate absolute defects |
|---:|---:|---:|
| 10 | 0.0593287397 | 0.1831132890 |
| 50 | 0.0098395311 | 0.7771347731 |
| 100 | -0.0141426970 | 0.1640100696 |
| 1000 | -0.0108829961 | 0.1840751768 |

Every run agrees with the tail-only identity. Scaling the retained head by 1, 10 and 100 leaves D at 0.0098395311 (T=50), while the separate absolute totals grow from 0.7771 to 78.8236 and 7902.2337. The MV26 tail budget is 1.2916880, versus 6.9567947 for the full reference energy with the same gaps. The sign changes rule out a generic nonpositive-defect rule.

Equal weights on \(\{2,3\}\), with E=1, give
\(J_4/(\Delta^4E^2)=0.5000000000000001\), displaying the sharp 1/2 constant to floating-point precision. A four-prime example gives 0.1924082. On \(\{2,3,4,6,9\}\), with coefficients \((1,i,-1,1/2,0.3i)\), aggregated ratio energy and product energy both equal 20.4406.

The general divisor-moment inequality is checked numerically for q=2 and q=5 on the mixed support. A separate **synthetic** reflected collection, with multiplicities 2, 1 and 3, tests the aggregated horizontal identity: the direct and layer-integral values both equal 0.0537289382, and the integrated fifth-moment Hölder bound is 0.0707219270. These points are not asserted to be zeta zeros and do not test the classical density theorem.

A separate diagnostic at T=100 reconstructs U from 29 numerical zeros, the continuous gamma phase, and the numerical canonical constant \(\delta_1\approx0.8173527686\). For X=7, it gives residual energy 0.3488980; halving the quadrature step changes this by about \(7.2\cdot10^{-6}\).
The reported numerical \(D_{\rm cutoff}=-0.1426648\) uses a total-energy sum cut at 100000: it is not a certified value of the infinite-C defect. Algebraically
\(D=D_{\rm cutoff}-T(C-C_{\rm cutoff})\).
The raw JSON retains this label and the quadrature checks. No asymptotic claim is inferred from these low-height data.

Reproduce with NumPy, SciPy, SymPy and mpmath:
\[
\texttt{python frz\_signed\_defect\_experiments.py --output experiments.json}.
\]

## 7. Proposed repository files and verification

- Analysis/SpectralSignedTail.lean: ten theorems, finite tail cancellation and perturbation bounds.
- Analysis/ActualSignedResidualPairing.lean: two theorems, exact single-mode extraction and actual-zero defect consumer.
- RiemannResearch.lean: two exports.
- FRZ_FORMALIZATION_20261110.md: an additive update to Section 8 Third.
- FRZ_SIGNED_DEFECT_20261111.md: this investigation and its open obligations.

The companion review bundle includes frz_signed_defect_experiments.py and experiments.json for reproducibility. They are separate from the five-file repository patch.

Focused acceptance: job job_TImID_uegbH6BQIwuk14Lb4YPoTuFplo, backend Bazel/BuildBuddy, target //RiemannResearch/Analysis:ActualSignedResidualPairing, exit code 0, verified=true. It includes SpectralSignedTail and transitive imports. Reported server verification duration: 35.064 seconds; this is not a measurement of pure kernel time. [BuildBuddy evidence](https://app.buildbuddy.io/invocation/0cf0f5d2-8a5c-45d8-8890-e1799ea1120c).

The focused result above predates publication. The publication checkpoint separately audits and builds the complete project, including the root export target; its terminal record supplies the final validation status and commit. The classical energy, normalization, density, Landau and endpoint providers, and the aggregate fifth-moment analytic assembly, remain mathematical inputs and deductions outside the new kernel-checked declarations. An additional editor axiom-check request returned no printed axiom output and was inconclusive; it is not counted as verification evidence.

## Sources

- [Chirre and Quesada-Herrera, The second moment of S_n(t) on the Riemann hypothesis, arXiv:2006.08503v2](https://arxiv.org/pdf/2006.08503): canonical normalization, (1.5), normalization footnote; Lemma 8 is explicitly conditional on RH.
- [Ford and Zaharescu, On the distribution of imaginary parts of zeros of the Riemann zeta function](https://arxiv.org/pdf/math/0405459): Lemmas 1–2 and (3.8).
- [Brent, Platt and Trudgian, Accurate estimation of sums over zeros of the Riemann zeta-function](https://arxiv.org/pdf/2009.13791): exact counting convention, gamma term and logarithmic endpoint bounds, especially §2 and (10).
- Montgomery and Vaughan, “Hilbert's inequality,” J. London Math. Soc. (2) 8 (1974), 73–82: separation inequality underlying the existing checked constant 26.
- [Baseline FRZ formalization](https://github.com/Cnoack3/RiemannResearch/blob/6c4fe3312e24b00813bcc5c329cf28ba0fe14333/RiemannResearch/FRZ_FORMALIZATION_20261110.md): exact residual and arithmetic consumers.

The new finite arguments, the pointwise fallback, and the aggregate fifth-moment deduction above are mathematical deductions made in this investigation. No claim of mathematical novelty or literature-optimality is made.
