# Attempt to prove the actual E4 vanishes

Continuation of the supplied ordinate-harmonic Markdown, 10 October 2026.

**Outcome:** no unconditional proof of E4 = 0 was obtained. The actual assertion
remains Open. The work below gives a kernel-checked obstruction to the proposed
ordinate-only routes, an exact arithmetic target, and a paper proof retaining
the complete growing-degree Gaussian tail. None assumes the requested
conclusion and then presents it as an unconditional theorem.

## 1. Use the same actual energy throughout

The repository quantity is
\[
E_4=\sum_{\rho\ {\rm nontrivial}}m_\rho
\frac{\delta_\rho^2}{(1+\gamma_\rho^2)^2},
\qquad \delta_\rho=\Re\rho-\tfrac12,\quad\gamma_\rho=\Im\rho.
\]
It indexes all actual zeros, both ordinate signs and horizontal partners,
with analytic multiplicities. The already published module
`Analysis/ActualZeroHorizontalEnergy.lean` proves unconditional summability,
nonnegativity, and
\[
E_4=0\iff {\rm RiemannHypothesis}.
\]
Its declaration is `horizontalFourthEnergy_eq_zero_iff_RH`. That equivalence
is a reduction; it does not provide a proof of its left side.

In the paper calculations below, \(E_+=\sum_{\gamma_\rho>0}
m_\rho\delta_\rho^2/(1+\gamma_\rho^2)^2\).
Classical absence of real nontrivial zeros and conjugation give \(E_4=2E_+\).
This all-zero/upper-zero identification has not been added as a Lean provider
in this attempt. An unregularized upper-zero sum with denominator \(\gamma^4\)
is a different quantity and is not renamed E4 here.

## 2. Verified finite quartet obstruction

The new module `Analysis/FiniteQuartetOrdinateBlindness.lean` uses lists to
retain multiplicity. Compare
\[
\mathcal Q_d=
\{\tfrac12+d+i g,\tfrac12-d+i g,
  \tfrac12+d-i g,\tfrac12-d-i g\},
\qquad \mathcal Q_0.
\]
The comparison at \(d=0\) repeats each of the two line atoms twice. It does not
assume simplicity.

Lean proves all of the following:

| Declaration | Exact result |
|---|---|
| `quartet_ordinates` | The complete signed ordinate lists agree. |
| `ordinateObservable_quartet` | Every real function of ordinate has the same multiplicity-weighted sum. |
| `energy_quartet` | The finite horizontal energy is exactly \(4d^2/(1+g^2)^2\). |
| `energy_quartet_pos` | It is strictly positive for every \(d\ne0\). |
| `quartet_in_strip` | All four atoms lie in the open strip when \(|d|<1/2\). |
| `energyTail_quartet_zero` | The exact tail above \(T\) is zero whenever \(0\le g\le T\). |
| `same_ordinates_positive_energy_zero_tail` | Identical ordinate data and an exactly zero tail coexist with a positive core. |
| `concrete_quartet` | At \(d=1/4,g=T=15\), the open-strip energy is \(1/204304>0\), with zero tail. |
| `heatMoment_determinant_neg` | The squared-node Gaussian pair has a negative size-two Hankel determinant whenever \(dg\ne0\). |
| `heatMoment_negative_witness` | It has a real finite quadratic direction of strictly negative energy. |

These are artificial spectral configurations, not alleged actual zeros of
\(\zeta\). A common background may be added to both. Every ordinate statistic
remains equal, and their horizontal energies still differ by the displayed
positive amount. Leading counting asymptotics and the quoted density upper bounds tolerate
a finite perturbation.

The full arithmetic explicit formula does distinguish them. Their heat trace
contributions are
\[
R_d(a)=4e^{-a(g^2-d^2)}\cos(2agd),\qquad R_0(a)=4e^{-ag^2},
\]
and, exactly to leading Taylor order,
\[
R_d(a)-R_0(a)=4d^2a+
2(d^4-6d^2g^2)a^2+O(a^3).
\]
A fixed prime/archimedean right side cannot remain unchanged. Thus the theorem
rules out deriving zero energy from ordinate data alone; it does not rule out
a proof using the complete prime-side identity.

Wolfram independently returned
\[
R_dR_d''-(R_d')^2
=-64d^2g^2e^{-2a(g^2-d^2)}
\]
and the Taylor coefficients above. The real derivative identity and Taylor
expansion are computer-algebra checks, not separately formalized calculus.
Lean verifies the corresponding squared-node Gaussian moment determinant and
negative witness. A full infinite background still needs tail control.

## 3. The exact remaining arithmetic target

The following infinite identities are audited paper calculations, not new
kernel-checked analytic bridge declarations. They use the classical centered
Hadamard expansion and the classical fact that actual nontrivial ordinates
satisfy \(\gamma^2\ge1\). The latter height input is explicit in the existing
Lean finite-cutoff bounds and has not been discharged by a new actual-zeta
provider here.

For \(x>1/2\), set
\[
B(x)=\sum_{\gamma_\rho>0}\frac{2xm_\rho}{x^2+\gamma_\rho^2},
\qquad
D(x)=B(x)-\frac{\xi'}{\xi}(\tfrac12+x).
\]
Reflecting horizontal partners before summing gives the exact identity
\[
D(x)=\sum_{\gamma_\rho>0}m_\rho
\frac{2x\delta_\rho^2(3\gamma_\rho^2+\delta_\rho^2-x^2)}
{(x^2+\gamma_\rho^2)
 ((x-\delta_\rho)^2+\gamma_\rho^2)
 ((x+\delta_\rho)^2+\gamma_\rho^2)}.
\]
For \(x=3/2\), the previous verified pointwise constants give
\[
\tfrac15E_+\le D(3/2)\le9E_+,
\quad\text{hence}\quad
\tfrac1{10}E_4\le D(3/2)\le\tfrac92E_4.
\]

Let \(S(t)=\arg\zeta(1/2+it)/\pi\), with the argument continued from
\(\arg\zeta(2)=0\) along \(2\to2+it\to1/2+it\). The principal argument is
not an interchangeable definition. Averaged limiting values at zero heights
do not change any integral. Put
\[
I(x)=\int_0^\infty\frac{tS(t)}{(t^2+x^2)^2}\,dt.
\]
The exact zero count \(N(t)=1+\theta(t)/\pi+S(t)\) and Stieltjes integration
by parts give
\[
B(x)=4x\int_0^\infty\frac{tN(t)}{(t^2+x^2)^2}\,dt
=\frac2x+\frac12\psi(\tfrac14+\tfrac x2)
-\frac12\log\pi+4xI(x).
\]
The absolutely convergent prime-power expansion gives
\[
\frac{\xi'}{\xi}(\tfrac12+x)
=\frac{2x}{x^2-1/4}
+\frac12\psi(\tfrac14+\tfrac x2)-\frac12\log\pi
-\sum_{n\ge2}\frac{\Lambda(n)}{n^{1/2+x}}.
\]
Subtracting cancels the complete archimedean expression, leaving
\[
D(x)=4xI(x)+\sum_{n\ge2}\frac{\Lambda(n)}{n^{1/2+x}}
-\frac1{2x(x^2-1/4)}.
\]
In particular,
\[
\boxed{D(3/2)=
6\int_0^\infty\frac{tS(t)}{(t^2+9/4)^2}\,dt
+\sum_{n\ge2}\frac{\Lambda(n)}{n^2}-\frac16.}
\]
The proposed proof of E4 = 0 therefore needs the independent bound
\[
\boxed{
6\int_0^\infty\frac{tS(t)}{(t^2+9/4)^2}\,dt
\le \frac16-\sum_{n\ge2}\frac{\Lambda(n)}{n^2}.}
\tag{Open}
\]
The positive displacement identity already proves the reverse inequality.
No checked argument supplies the displayed direction.

This is a member of the generalized Volchkov family, not an asserted new
criterion. Sekatskii–Beltraminelli–Merlini, Section 2.2 equations (7)–(10),
retain the off-line correction explicitly. Removing that correction assumes
the cancellation one is trying to prove:
<https://arxiv.org/pdf/0904.1277>.
The original Volchkov journal page is
<https://umj.imath.kiev.ua/index.php/umj/article/view/5435>.

### Exact digamma step and boundary audit

For \(a>0,r=n+a,p_x(t)=x/[\pi(x^2+t^2)]\), the combined real digamma term is
\[
\frac1{n+1}-\frac r{r^2+t^2/4}
=\left(\frac1{n+1}-\frac1r\right)
+\frac{t^2}{4r(r^2+t^2/4)}.
\]
Its second term is nonnegative, and
\[
\int_{\mathbb R}p_x(t)\frac{4r}{t^2+4r^2}\,dt
=\frac1{r+x/2}.
\]
Consequently the integral of its absolute value is at most
\[
\left|\frac1{n+1}-\frac1r\right|
+\frac1r-\frac1{r+x/2}=O_{a,x}((n+1)^{-2}).
\]
Absolute Fubini therefore gives the exact Poisson identity
\[
\int_{\mathbb R}p_x(t)\Re\psi(a+it/2)\,dt=\psi(a+x/2).
\]
Constants and rational terms remain combined before summing; no divergent
series is split. Evenness gives the half-line identity used above.

At the lower endpoint, \(\theta(0)=0,S(0+)=-1,N(0+)=0\). At infinity,
\(N(t),\theta(t)=O(t\log t)\), whereas \(S(t)=O(\log(t+2))\).
Both integration-by-parts boundary ratios tend to zero. All weighted
integrals converge absolutely. The \(2/x\) constant and rational pole term
have both been retained.

## 4. Density controls the tail, not the total energy

Ford–Zaharescu, Lemma 2, states the uniform Selberg bound
\[
N(\sigma,T)\ll T^{1-(\sigma-1/2)/4}\log T
\quad(1/2\le\sigma\le1),
\]
with multiplicity. Source:
<https://www.ford126.web.illinois.edu/wwwpapers/fz.pdf>.

Horizontal reflection and layer cake imply, for sufficiently large \(T\),
\(B_+(T)=\sum_{0<\gamma_\rho\le T}m_\rho\delta_\rho^2\le CT/\log T\).
Keeping the endpoint, the complete signed tail is
\[
E_4(|\gamma|>T)
=-\frac{2B_+(T)}{(1+T^2)^2}
+8\int_T^\infty\frac{tB_+(t)}{(1+t^2)^3}\,dt.
\]
Only then may one estimate
\[
0\le E_4(|\gamma|>T)\le \frac{8C}{3T^3\log T}.
\]
This tends to zero. The core is still present. The verified quartet has an
exactly zero tail and a strictly positive core, demonstrating this distinction
without reliance on a limiting approximation.

## 5. Complete Gaussian interpolation route: paper status

A constructive converse detects an off-line node at any fixed Gaussian width.
It does not prove the actual Gaussian form is positive.

Let the rotated nodes be \(z=\gamma-i\delta\), including both signs and
multiplicities. Assume local finiteness, positive integer multiplicities \(m_z\ge1\),
weighted conjugation invariance \(m_{\bar z}=m_z\),
\(|\Im z|\le1/2\), and total weighted count \(O(T\log(T+2))\) for
\(|\Re z|\le T\). Fix \(a>0\) and a nonreal node \(z_0\).
Its weight \(v_0=m_0e^{-az_0^2}\) is nonzero. Choose
\(\zeta_0\in\{1,i,1+i,1-i\}\) so that
\(2\Re(v_0\zeta_0^2)=-\eta<0\).

For the finite set of distinct nodes \(K_T\), set
\[
P_T(X)=\prod_{z\in K_T\setminus\{z_0,\bar z_0\}}(X-z),
\qquad M(T)=\deg P_T.
\]
Conjugation gives real coefficients. Write
\(\zeta_0/P_T(z_0)=c_T+i d_T\) and put
\[
p_T(X)=\left(\frac{d_T}{\Im z_0}X+
c_T-\frac{d_T\Re z_0}{\Im z_0}\right)P_T(X).
\]
It takes the target conjugate values and kills every other cutoff node,
including any negative-ordinate companions outside the target pair. The finite energy is exactly
\(-\eta\). Multiplicities stay in the weights; repeated roots do not require
Hermite interpolation.

For sufficiently large \(T\), \(|P_T(z_0)|\ge r_*>0\) uniformly. The finitely
many distinct roots with \(|z|<|z_0|+1\) contribute a fixed nonzero product;
all further distances are at least one. This is not a high-root gap estimate.

For \(|\Re z|>T\ge1\),
\[
|p_T(z)|\le C(z_0,r_*)\,3^{M(T)}|z|^{M(T)+1}.
\]
The full omitted energy is bounded by
\[
C_aC(z_0,r_*)^2\,9^{M(T)}
\sum_{|\Re z|>T}m_z e^{-a(\Re z)^2}|z|^{2M(T)+2}.
\]
It is essential to retain this sum. Put \(D(T)=M(T)+1=O(T\log(T+2))\).
When \(T^2\ge2D(T)/a\), logarithmic differentiation shows
\[
(t^2+1/4)^{D(T)}e^{-at^2}
\le (T^2+1/4)^{D(T)}e^{-aT^2}
e^{-a(t^2-T^2)/2}\quad(t\ge T).
\]
For unit windows starting at \(T+k\), the total count bound gives
\[
N(T+k+1)\le C(T+1)(k+1)^2\log(T+3).
\]
For \(T\ge2\), the Gaussian ratio is at most \(e^{-2ak}\).
Summing \((k+1)^2e^{-2ak}\) gives the additional factor
\(O_a((T+1)\log(T+3))\). Thus the log of the tail bound is
\[
-aT^2+O(T\log^2(T+2))\longrightarrow-\infty.
\]
A sharper actual unit-window count gives \(O_a(\log(T+3))\), but is unnecessary.
Choose \(T\) making the full tail smaller than \(\eta/2\); the infinite
quadratic form is strictly negative. Conversely, real support gives an exact
sum of positive Gaussian weights times real squares.

Hence all-order Gaussian Hankel positivity detects real support on paper.
The cutoff degree grows with \(T\); keeping it fixed would invalidate the
interpolation argument. This full interpolation/tail theorem has not been
formalized here. Proving its arithmetic positivity remains Open.

## 6. Current primary literature and verification scope

Suzuki's September 2026 revision proves continuity of the lowest localized
Weil eigenvalue and small-interval positivity; it explicitly allows a zero
crossing if RH fails. The global ground-state limit remains conjectural:
<https://arxiv.org/html/2606.09096v3>, introduction Theorems 1.3–1.4.

The August 2026 contour-Hankel paper explicitly leaves independent arithmetic
positivity unresolved:
<https://arxiv.org/html/2608.11520>, Corollary 3.7 and Remark 3.8.
These sources support the boundary of the approach; they do not discharge
the required cancellation.

The new finite module has eleven public theorem declarations. The exact
infinite arithmetic identities and Gaussian interpolation theorem above are
paper work. E4 = 0, the actual infinite Lean bridges, and independent global
positivity remain Open. The source bundle passed server job
`job_hE8Tg0r-DAL-F8TpPC6upyPoYvnB3JXb`: exit code 0, `verified=true`.
Printed foundations for the combined quartet theorem, Gaussian negative
witness, and existing actual E4/RH equivalence contain only `propext`,
`Classical.choice`, and `Quot.sound`; no new-source warnings were emitted.
The final server checkpoint validates the changed
module and local reverse dependents; it is not an incremental full-repository
rebuild. Its terminal result and published commit are reported with delivery.
