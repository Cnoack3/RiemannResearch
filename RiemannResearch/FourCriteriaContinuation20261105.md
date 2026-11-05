# Four RH criteria: proof audit and stronger continuation

Prepared for Christian Noack. 4 November 2026 Pacific / 5 November 2026 UTC.

## Outcome and verification boundary

The four original implications are valid conditional routes. No one of their open
arithmetic premises was established for the actual infinite displacement, so this
work does not prove RH.

A coherent Lean submission passed with verified=true, exit code 0:
job_EcqnlnEtExDVciEky8fLHXRDrEw3c6ty. Server-reported verification time was
7.995 seconds; this excludes workspace opening, transport delays, and polling.
Two earlier candidates had ordinary elaboration errors, which were repaired.
The successful submission checked the following new actual-RH consumers:

- QSquarefreePrimeLocalTests.riemannHypothesis_of_two_selected_tests
- QSquarefreePrimeLocalTests.riemannHypothesis_of_weighted_local_tests
- QSquarefreePrimeLocalTests.riemannHypothesis_of_difference_tendsto_zero
- QSquarefreeFiniteDisplacement.riemannHypothesis_of_sitewise_frequent_polylog

Each printed axiom list was exactly propext, Classical.choice, Quot.sound.
Their substantive arithmetic hypotheses are still present in their types.
Final project publication additionally requires the serialized checkpoint;
the checkpoint response is the authoritative final integration/validation record.

The baseline workspace was opened at commit
6840ed95bacd5adda1b8865aaeacee09db70ba39.
The corresponding source modules added are NumberTheory/SquareDifferenceRigidity,
RH/QSquarefreePrimeLocalTests, and RH/QSquarefreeFinitePolylog.
NumberTheory/PrimeMultiplierRigidity receives the two-selected-test extension.

## Definitions and the common proof of the four implications

Let Z=zeta(2), Q(n)=1/(Z n²), P(n)=1/(n(n+1)), and
V=closure(span{g_m : m>=2 squarefree}) in H=L²(Q), with
g_m(n)=(n mod m)/m. All physical indices in the prose are positive.
Let Pi be Q-orthogonal projection onto V and put

\[
 f_Q=\Pi1,\quad f_P=P_V^P1,\quad r=1-f_Q,\quad d=f_Q-f_P,\quad
 r_P=r+d,\quad (Bf)(n)=f(n)/(n+1).
\]

The equivalent metrics obey
\[
 \langle f,h\rangle_P=Z\langle f,(I-B)h\rangle_Q.
\]
The P normal equation and Q orthogonality give
\[
 d=\Pi B(r+d),\qquad
 w=B(r+d)-d\in V^\perp.
\]
Keep the full faithful identity:
\[
 \langle1,w\rangle_Q
 =\langle r,Br\rangle_Q+\|d\|_P^2/Z.
\]
Both terms are nonnegative and B is faithful. Hence zero witness mean implies r=0.

For a bounded annihilator u, choose a prime M<p<=2M and a legal Möbius exact
head E_(p-1), with E_(p-1)(n)=1 for n<=p-1 and complete error energy o(M).
The exact signed identity and Cauchy--Schwarz give
\[
 \langle1,u\rangle_Q=\langle1-E_{p-1},T_Mu\rangle_Q,\quad
 |\langle1,u\rangle_Q|^2
 \le\|1-E_{p-1}\|_Q^2\|T_Mu\|_Q^2=o(1).
\]
Thus bounded annihilators have zero mean. Also B:H→c_0, since h(n)/n→0 for
every h∈H. Therefore d is bounded iff w is bounded; either forces r=0.

Bagchi's published squarefree criterion, Remark 8, identifies r=0 with RH
in ordinary mathematics. The project supplies the checked forward bridge
r=0→Mathlib.RiemannHypothesis. This work does not newly formalize the reverse bridge.

The original four forward implications are now immediate:

| Criterion | Exact reason it implies RH |
|---|---|
| C1: d extends continuously to the compact prime CRT product | Its restriction is bounded; the faithful witness argument applies. |
| C2: w=Kr is physically bounded | Orthogonality gives zero mean; the full energy identity forces r=0. |
| C3: centered resolvent approximants s_j have one common physical bound | The existing estimate ||d-s_j||≤3^(-j)||d|| gives coordinatewise convergence, which passes the common bound to d. |
| C4: finite displacements d_(J_k) have a common bound on heads H_k, with both sequences tending to infinity | Hilbert convergence d_J→d implies coordinatewise convergence; every fixed site eventually lies in the head. |

Under RH, d=w=s_j=0. For C4 choose H_k=k and increasing J_k with
||d_(J_k)||≤1/(sqrt(Z) k); this supplies head bound 1. These are conditional
equivalences, not four independent proofs of any open premise.

Relevant existing sources: QSquarefreeDisplacementRigidity,
QSquarefreeSchurOperator, QSquarefreeCRTRegularity,
QSquarefreeDisplacementResolvent, and QSquarefreeFiniteDisplacement.

## New Lean result: first differences tending to zero suffice

For every h∈V, the established legal relation is
\[
 \Delta h(n^2)=\Delta h(n)\qquad(n\ge2),\quad
 \Delta h(n)=h(n)-h(n-1).
\]
Fix n≥2 and iterate a_0=n, a_(j+1)=a_j². Then a_j→∞ and
Delta h(a_j)=Delta h(n). If Delta h(k)→0, its constant values on this
orbit must be zero. Thus h is constant on positive integers.

Applying this to the actual displacement proves
\[
 \boxed{\Delta d(n)\longrightarrow0\quad\Longrightarrow\quad\mathrm{RH}.}
\]
This implication is newly checked in Lean. It requires no bound on d itself.
The limit of the first differences remains OPEN.

## New Lean result: one weighted local test suffices

Define
\[
 \Lambda_n(h)=h(n^2)-h(n^2-1)-h(n)+h(n-1),\qquad
 T_n(h)=\Lambda_n(k\mapsto kh(k)).
\]
For h∈V, Lambda_n(h)=0 automatically. If T_n(h)=0 for every n≥2, expansion gives
\[
 h(n^2)=h(n)-(n^2-n)\Delta h(n).
\]
On the same squaring orbit, the exact invariant is
\[
 h(a_j)=h(n)-(a_j-n)\Delta h(n).
\]
Physical sublinearity h(a_j)/a_j→0 forces Delta h(n)=0. Therefore
\[
 \boxed{\forall n\ge2,\ T_n(d)=0\quad\Longrightarrow\quad\mathrm{RH}.}
\]
This implication and the abstract sequence theorem are newly checked in Lean.

For any conductor m>n², one has m Lambda_n(dg_m)=T_n(d). Thus one local test
with a sufficiently large conductor at each n suffices; primes may be used,
but primality is unnecessary for this identity. Full membership dg_m∈V is
stronger than the required single functional test.

The analytic weakening T_n(d)/n²→0 also suffices on paper: on a fixed
squaring orbit,
\[
 T_a(d)/a^2=d(a^2)/a^2-d(a)/a^2+(1-1/a)\Delta d(a),
\]
and sublinearity kills the first two terms. This approximate version has
not been newly Lean-checked here.

## New paper criterion: scaled multiplier leakage

Let epsilon_m=dist_Q(dg_m,V). Multiplication by g_m is bounded, so dg_m∈H.
The exact norm of Lambda_n is
\[
 c_n=\sqrt{Z\{n^4+(n^2-1)^2+n^2+(n-1)^2\}}.
\]
Since Lambda_n annihilates V, for m>n²,
\[
 |T_n(d)|=m|\Lambda_n(dg_m)|\le m c_n\epsilon_m.
\]
Consequently
\[
 \boxed{\liminf_{m\to\infty}m\,\operatorname{dist}_Q(dg_m,V)=0
 \quad\Longrightarrow\quad\mathrm{RH}.}
\]
A cofinal sequence of conductors, including primes, is enough. This uses
the newly checked one-test theorem, but this distance-to-functional assembly
is presently a paper proof.

Unscaled epsilon_m→0 holds automatically by dominated convergence and is
insufficient. If RH fails, some fixed n has T_n(d)≠0 and
m epsilon_m≥|T_n(d)|/c_n>0 for every m>n². The open issue is the rate.

## New Lean C4 weakening: different stages for different sites

Fix an integer m≥0 and C≥0. It suffices that, for every fixed physical n,
arbitrarily large stages J satisfy
\[
 |d_J(n)|\le C(6+\log n)^m.
\]
The stages may depend on n; neither one common subsequence nor one common
head schedule is required. Coordinatewise convergence passes the bound to d.
The existing QSquarefreeLogDisplacement polylog criterion then gives RH.
This new assembly is checked in Lean. The polylog rigidity theorem itself
already existed and is not claimed as a new result.

## New paper C3 weakening: one average per iteration

Let S_H(f)=sum_(1<=n<=H)|f(n)|². For every u∈H,
\[
 S_H(d)\le2S_H(u)+2Z H^2\|d-u\|_Q^2.                 \tag{1}
\]
This follows by retaining u and d-u in the pointwise square bound and
using n²≤H² inside the weighted error norm. Therefore the single budget
\[
 \boxed{\exists C\ \forall j,\quad S_{9^j}(s_j)\le C9^j} \tag{2}
\]
suffices: the established geometric error gives
S_(9^j)(d)≤2(C+Z||d||²)9^j. Adjacent heads have ratio 9, so monotonicity
extends this to S_M(d)=O(M) for every M. Dyadic summation then gives
M||T_Md||²=O(1), which implies RH.

One may instead require only
sum_(9^(j-1)<n<=9^j)|s_j(n)|²≤C9^j. Summing the corresponding geometric
blocks of d again gives S_M(d)=O(M). These average criteria remain paper
deductions here; their arithmetic budgets are OPEN.

## C4: finite projection gains control the error

Write E_(Q,J)=||1-f_(Q,J)||_Q² and E_(P,J)=||1-f_(P,J)||_P².
With gamma=1017/2000, the existing four-site bound on V gives
\[
 \|d-d_J\|_Q^2
 \le2(E_{Q,J}-E_{Q,\infty})
   +2(E_{P,J}-E_{P,\infty})/(Z\gamma).
\]
Choose H_k=2^k and cofinal stages J_k. A sufficient pair of finite-system
conditions is
\[
 S_{H_k}(d_{J_k})\le C_0H_k
\]
and, for every finite L≥J_k,
\[
 H_k\left[E_{Q,J_k}-E_{Q,L}
  +(E_{P,J_k}-E_{P,L})/(Z\gamma)\right]\le C_1.
\]
Pass L→∞ and apply (1). This controls future projection gains, without
assuming that either limiting residual energy is zero. Every individual
inequality involves finite projections, but the uniform quantification is OPEN.

## Chebyshev acceleration: exact recurrence, same arithmetic gap

Let A=Pi B Pi on V and b=Pi Br. Since spec(A)⊂[0,1/2], define
\[
 a_j=T_j(3),\ a_0=1,\ a_1=3,\ a_{j+1}=6a_j-a_{j-1},
\]
\[
 v_0=0,\ v_1=4b,\quad
 v_{j+1}=2(4A-I)v_j-v_{j-1}+8a_jb,\quad u_j=v_j/a_j.
\]
Using (I-A)d=b and the Chebyshev recurrence yields the exact remainder
\[
 d-u_j=T_j(4A-I)d/a_j,\qquad \|d-u_j\|\le\|d\|/a_j.
\]
Thus (2) holds as a sufficient criterion with u_j and heads a_j².
The first heads are 1,9,289,9801,332929,11309769; successive ratios are ≤36.
Wolfram returned exact zero for the scalar recurrence identity and confirmed
this table. The all-j operator proof uses the standard spectral theorem;
it is a paper deduction, not a new Lean spectral formalization.

This is standard Chebyshev semi-iteration, not a new numerical method.
Saad's author-hosted survey, section 10, gives the history and the
Golub--Varga 1961 references. Faster Hilbert convergence does not establish
the average budget on u_j.

## What the topology and operator arguments do not supply

Local boundedness of the physical trace in a neighborhood of every point of
the compact CRT product suffices by a finite subcover. A bounded oscillation
at one modulus also suffices; that reduction already exists in current source.

However, Hilbert limits of legal cylinder functions need not be CRT-continuous.
A concrete positive unbounded legal vector is
h=sum_(p prime) g_p/p. Indeed ||g_p||_Q²≤2/(Zp), so the series converges in H.
At n≡-1 mod product_(p<=P)p, its value is at least
sum_(p<=P)(1/p-1/p²), which diverges. This vector still has h(n)=o(n).

Mere measurable or Haar-essentially-bounded extension is vacuous: extend an
arbitrary physical sequence by zero outside the embedded integers. That
countable set is Borel and Haar-null. The relevant control must concern
actual physical values, not a Haar-almost-everywhere representative.

## Audit corrections and immediate targets

In the source paper's local test section, tau_(p,n)=+p Lambda_n(hg_p);
the prose has a minus sign. The subsequent zero tests and absolute estimates
are unaffected. The direct squarefree sequence citation is Bagchi Remark 8;
Remark 4 supplies the Hardy-space predecessor.

Priority arithmetic targets now are:

1. Prove Delta d(n)→0 using the actual projection equation.
2. Establish the scaled leakage liminf m dist(dg_m,V)=0.
3. Bound one geometric annular mean square for the actual resolvent orbit.
4. Improve the complete exact-head energy using quantitative published
   Mertens bounds, then match it with a genuinely controlled displacement tail.

The already known d(n)=o(n) does not supply any of these targets. No generic
positivity or conditional-expectation property of Pi has been assumed.

## References

- B. Bagchi, On Nyman, Beurling and Baez-Duarte's Hilbert space reformulation
  of the Riemann hypothesis, Proc. Indian Acad. Sci. Math. Sci. 116 (2006),
  137--146, Remark 8 and equivalent weights after Theorem 1.
  https://arxiv.org/pdf/math/0607733
- T. Tao, A remark on partial sums involving the Möbius function,
  Bull. Australian Math. Soc. 81 (2010), 343--349.
  https://arxiv.org/abs/0908.4323
- E. S. Lee and N. Leong, New explicit bounds for Mertens function and the
  reciprocal of the Riemann zeta function, arXiv:2208.06141v5 (2026),
  Theorem 1.1. This inspected version is a research preprint.
  https://arxiv.org/html/2208.06141v5
- Y. Saad, Iterative methods for linear systems of equations: A brief
  historical journey, section 10, author-hosted survey.
  https://www-users.cse.umn.edu/~saad/PDF/ys-2019-01.pdf

Source paper: Displacement_Schur_CRT_RH_2026-11-04.md.

## Stronger quantitative growth criterion (paper proof)

The current repository already proves logarithmic and stretched-tail results,
with the inspected stretched profile
\[
 \Psi(N)=((6+\log N)\log(6+\log N))^{1/11}.
\]
Using the stronger published-literature Vinogradov--Korobov Mertens estimate,
in the inspected modern Lee--Leong preprint, gives the larger profile
\[
 \Phi(N)=(\log N)^{3/5}(\log\log N)^{-1/5}.
\]
The existing exactHead_energy_of_uniform_mertens_log theorem provides a
natural formalization bridge, but the stronger analytic provider is not
formalized in this work. The complete paper derivation is saved in
[FourCriteriaQuantitative20261105.md](FourCriteriaQuantitative20261105.md).
It proves
\[
 \|1-E_N\|_Q^2=O(N e^{-c\Phi(N)})
\]
for some c>0 and consequently
\[
 \boxed{\log(2+|d(n)|)=o(\Phi(n))\Longrightarrow\mathrm{RH}.}
\]
For example, the still-open bound
|d(n)|=O(exp(sqrt(log n))) would suffice.
This improves the permitted growth relative to the inspected 1/11 profile,
but does not establish the needed bound for d.
