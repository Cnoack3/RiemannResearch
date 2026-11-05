# Leakage and Chebyshev continuation: Lean catalog

Prepared for Christian Noack, 5 November 2026.

## Status

This continuation formalizes the two selected paper claims and strengthens the
scaled-leakage hypothesis. All RH implications below are **conditional research
reductions**. No arithmetic provider for their leakage or averaging hypotheses
has been proved. RH remains unproved.

The source is based on commit 400ebec57611f863f42d8624628a2c8b8902f905.
All ten modules are exported by RiemannResearch.lean. Final integration and
publication require the server checkpoint; candidate checks alone are insufficient.

## Definitions

Let \(Z=\zeta(2)\), \(Q(n)=1/(Zn^2)\), V the actual closed squarefree residue
span, \(\Pi\) its Q-orthogonal projection, and \(d=f_Q-f_P\).
Physical indices are positive. Set
\[
g_m(n)=(n\bmod m)/m,\quad
\epsilon_m=\operatorname{dist}_Q(dg_m,V),\quad
E_m=m(I-\Pi)(dg_m).
\]
The actual pointwise product is encoded in QHilbert after proving its square
summability. The declaration leakage_eq_distance identifies its projection
residual norm with the infimum distance to V. Thus \(\|E_m\|_Q=m\epsilon_m\).

Write
\[
\Lambda_n(h)=h(n^2)-h(n^2-1)-h(n)+h(n-1),\qquad
T_n(d)=\Lambda_n(k\mapsto kd(k)).
\]
The exact identity \(\Lambda_n(E_m)=T_n(d)\), for \(m>n^2\), is formalized.

## Conditional research reductions

Every premise in this table remains **Open** for the actual arithmetic objects.

| Declaration | Sufficient premise |
|---|---|
| QSquarefreeApproximateTests.riemannHypothesis_of_normalized_weighted_tests | \(T_n(d)/n^2\to0\) |
| QSquarefreeMultiplierLeakage.riemannHypothesis_of_scaled_leakage_sequence | \(m_j\to\infty,\ m_j\epsilon_{m_j}\to0\) |
| QSquarefreeMultiplierLeakage.riemannHypothesis_of_scaledError_weak_cluster | The sequence \(E_m\) has a weak cluster point in QHilbert |
| QSquarefreeMultiplierLeakage.riemannHypothesis_of_frequently_bounded_scaled_leakage | One finite C has \(m\epsilon_m\le C\) for arbitrarily large m |
| QSquarefreeMultiplierLeakage.riemannHypothesis_of_scaled_leakage_liminf_finite | \(\liminf_m m\epsilon_m<+\infty\), formalized in ENNReal |
| QSquarefreeMultiplierLeakage.riemannHypothesis_of_scaled_leakage_liminf_zero | The original extended nonnegative liminf is zero |
| QMeanSquareDisplacement.riemannHypothesis_of_bounded_mean_square | \(S_N(d)\le CN\) for all N |
| QMeanSquareDisplacement.riemannHypothesis_of_geometric_head_means | \(S_{B^j}(u_j)\le CB^j,\ B^j\|d-u_j\|^2\le D\), integer B≥2 |
| QMeanSquareDisplacement.riemannHypothesis_of_covered_head_means | \(S_{H_j}(u_j)\le CH_j,\ H_j\|d-u_j\|^2\le D\), and each N≥1 has \(N\le H_j\le KN\) for some j |
| QSquarefreeChebyshev.riemannHypothesis_of_resolvent_mean_square | \(S_{9^j}(s_j)\le C9^j\) for the existing centered resolvent |
| QSquarefreeChebyshev.riemannHypothesis_of_accelerated_mean_square | \(S_{33^j}(u_j)\le C33^j\) for the actual accelerated sequence |
| QSquarefreeChebyshev.riemannHypothesis_of_accelerated_exact_head_mean_square | \(S_{a_j^2}(u_j)\le Ca_j^2,\ a_j=T_j(3)\) |

Here \(S_N(f)=\sum_{1\le n\le N}|f(n)|^2\). The last three mean inequalities
require one finite-head bound per iteration, without a uniform physical bound
on the entire infinite sequence.

### Bounded scaled leakage

A bound holding frequently yields a weak cluster point of \(E_m\) in a compact
Hilbert ball. The proof uses the existing Hilbert weak compactness theorem;
no separability assumption or weak sequential compactness assertion is needed.

For fixed n≥2, the continuous linear functional \(\Lambda_n\) is eventually
equal to \(T_n(d)\) on \(E_m\). A weak cluster point e therefore satisfies
\(\Lambda_n(e)=T_n(d)\). Every e in QHilbert satisfies e(n)/n→0. The new
sequence lemma yields
\[
\Lambda_n(e)/n^2\longrightarrow0.
\]
The normalized weighted-test theorem then proves RH, using the exact legal
square identity and the established physical sublinearity of d.

The checked contrapositive scaled_leakage_diverges_of_not_RH is
\[
\neg\mathrm{RH}\quad\Longrightarrow\quad m\epsilon_m\longrightarrow+\infty.
\]

ENNReal is used for liminf so that infinite divergence has its ordinary extended
nonnegative meaning. No real-liminf conditional-completeness premise is hidden.

## Unconditional Chebyshev identities

On QHilbert the symmetric contraction is
\[
C=4\Pi B\Pi-\Pi.
\]
It restricts to \(4A-I\) on V, and \(Cd=3d-4b\), with b the actual correction.
Define
\[
a_0=1,\quad a_1=3,\quad a_{j+2}=6a_{j+1}-a_j,
\]
\[
v_0=0,\quad v_1=4b,\quad
v_{j+2}=2Cv_{j+1}-v_j+8a_{j+1}b,\qquad u_j=v_j/a_j.
\]
The exact remainder and conserved energy are checked:
\[
a_j(d-u_j)=T_j(C)d,
\]
\[
a_j^2\|d-u_j\|^2+\|z_j\|^2-\|Cz_j\|^2=\|d\|^2,
\quad z_j=U_{j-1}(C)d,\quad U_{-1}=0.
\]
The difference of the last two norm squares is nonnegative, giving
\(\|d-u_j\|\le\|d\|/a_j\).

The scalar development proves positivity, integrality,
\(3a_j\le a_{j+1}\le6a_j\), and
\[
a_j=\frac{(3+2\sqrt2)^j+(3-2\sqrt2)^j}{2},\qquad
a_j^2\ge\frac{(17+12\sqrt2)^j}{4}.
\]
acceleratedHead is defined by a natural floor, and acceleratedHead_cast proves
that its real cast equals \(a_j^2\) exactly. acceleratedHead_cover supplies K=36
in the covered-head theorem. Thus the exact-head criterion has no rounding
assumption. The integer choice \(H_j=33^j\) satisfies \(H_j\le4a_j^2\).

The operator proof is elementary Hilbert energy algebra, with no unformalized
spectral theorem. Chebyshev semi-iteration is classical, not claimed as a new
numerical method. NIST DLMF 3.11.E7 is recorded as the recurrence reference.

## Exact prefix identity and complete tails

For \(D_n=D+Cn-\sum_{i<n}a_i\), weighted_prefix_identity proves
\[
\sum_{i<N}a_iw_i+D_Nw_N+
\sum_{i<N}D_{i+1}(w_i-w_{i+1})
=Dw_0+C\sum_{i<N}w_i.
\]
The boundary deficit and every summand are retained. Nonnegative deficits and
decreasing nonnegative weights give the estimate, followed by an infinite-sum
bound after every finite bound has been established.

The physical head-energy equality is
\[
S_N(f)=S_N(g)+2\sum_{n\le N}g(n)(f(n)-g(n))+S_N(f-g).
\]
The checked estimates are
\[
S_N(f-g)\le ZN^2\|f-g\|_Q^2,\qquad
S_N(f)\le2S_N(g)+2S_N(f-g).
\]
For \(S_N(f)\le CN\), the complete-tail theorem gives
\[
M\|\operatorname{tail}_M f\|_Q^2\le4C/Z.
\]
It uses the exact Pareto tail sum and the existing Q/P weight comparison.
The existing logarithmic displacement-tail consumer with exponent zero gives
RH. No finite cutoff replaces the complete tail.

## Logarithmic leakage and accelerated averaging

For the actual displacement write $E_m=m(I-\Pi)(dg_m)$ and $L_m=\|E_m\|_Q$.
`QSquarefreeLogLeakage` proves that failure of RH forces $L_m\ge c\sqrt{\log m}$ eventually for some $c>0$. Hence a zero lower limit of $L_m/\sqrt{\log m}$ suffices. The proof sums four-site tests over powers of a single base with a nonzero first difference. The same module gives a finite bound for all sampled sites with a common radical, and a criterion allowing a separate cofinal sequence of powers and conductors for each squarefree base. Each leakage premise for the actual displacement is **Open**.

`ChebyshevEnergy.geometric_head_budget_iff` identifies the sharp real base for the original denominator budget as $17+12\sqrt2$. `QRecenteredChebyshev` defines a different iteration using the existing four-site bound $983/2000$ for the compressed reciprocal. Its rational denominator is $a'_j=((119/20)^j+(20/119)^j)/2$. The signed remainder and conserved energy give $35^j\|d-u'_j\|^2\le4\|d\|^2$. On these heads a physical mean square bounded by any fixed power of the logarithm implies RH. The approximation bound is unconditional. The mean bound is **Open**.

`QMeanSquareDisplacement.annular_headEnergy_exact` retains the mixed term on each newly reached interval. For the original accelerated iterates only the energy on $(a_j^2,a_{j+1}^2]$ needs to be bounded by $C a_{j+1}^2$ at stage $j+1$. `QDisplacementPolylogHeadMeans` allows each dyadic block to have its own approximant with fixed polylogarithmic allowances in the block mean and in the scaled squared approximation error. `QChebyshevPolylogHeadMeans` applies the full-head version to the original resolvent at $9^j$ and to the original accelerated heads. For every fixed nonnegative integer $p$ one may use $H_j=a_j^2(j+1)^p$ and the premise $S_{H_j}(u_j)\le C H_j(j+1)^p$. These mean bounds are **Open**.

## Modules and verification evidence

| Module | Role |
|---|---|
| Analysis/ChebyshevEnergy | Exact Hilbert energy and approximation error |
| Analysis/ChebyshevScale | Closed form, integer heads, covering estimate |
| Analysis/PrefixWeightedEnergy | Exact finite identity and complete weighted sum |
| NumberTheory/ApproximateSquareTests | Sublinear sequences and local tests |
| RH/QSquarefreeApproximateTests | Normalized-test RH consumer |
| RH/QSquarefreeMultiplierLeakage | Products, distance, scaled finite tests |
| RH/QSquarefreeWeakLeakage | Weak cluster, finite liminf, divergence |
| RH/QMeanSquareDisplacement | Physical mean square and complete tails |
| RH/QSquarefreeChebyshev | Actual operator and accelerated iteration |
| RH/QSquarefreeChebyshevAveraging | Centered and accelerated RH consumers |

Successful candidate/module checks included:

- job_khgvUj9tv454O0igWZYtOxml8rmZpEGP: weak compactness reduction and Chebyshev identities.
- job_Fg2ljwJFxYWyjnYIZv7f2a89t6V4Yalo: finite extended liminf and geometric averaging.
- job_yI04Kw_k6w6aYZME-PxzV9GM-tSjAk2J: exact integer heads and their RH consumer.
- job_-_JygFkeFSXhzFqX9-Ze8ecs3av-We-v: exact prefix identity.

Printed consumer axiom reports contained only propext, Classical.choice, and
Quot.sound. These reports do not discharge local arithmetic hypotheses.
The final checkpoint also validates the aggregate project and all changed Lean
modules, including the final source organization and imports.
