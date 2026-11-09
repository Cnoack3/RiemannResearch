# D5: CRT oscillation of the full projection displacement

Date: 2026-11-09.

Source: the user-provided *Full_Conductor_RH_Projection_Machinery.pdf*,
task D5 (printed p. 42), Section 10.1 (printed p. 27), the translation
identity in Sections 7 and 10.3, and the bounded-displacement criterion
in Section 6. The source poses the problem; the deductions below make
its quantifiers explicit.

## Scope and status

This development concerns the actual **full-conductor** displacement
\(d=f_Q-f_P\), with \(V=\overline{\operatorname{span}}\{g_q:q\ge2\}\),
\(g_q(n)=(n\bmod q)/q\), \(P(n)=1/[n(n+1)]\), and
\(Q(n)=1/[\zeta(2)n^2]\). All sequences are anchored at zero.

The new Lean results are structural theorems and **conditional research
reductions**. The global oscillation bound for the actual \(d\) is **Open**.
This work does not prove RH.

## 1. The periodicity quantifier

When every conductor in a finite dictionary divides \(L_j\), both metric
projections and their difference \(d_j\) are \(L_j\)-periodic.
For the dictionary \(\{2,\ldots,M_j\}\), take
\(L_j=\operatorname{lcm}(1,\ldots,M_j)\).

From \(L_j\mid L_{j+1}\), an \(L_j\)-periodic function is also
\(L_{j+1}\)-periodic. The reverse implication fails. Thus a later
projection is not automatically periodic at an earlier level.

The convergence \(d_j\to d\) in either physical Hilbert norm gives convergence
at every fixed integer. It does not show \(d(n+L_j)=d(n)\), because the
approximants at later stages do not satisfy that fixed-period identity.

## 2. A stronger D5 criterion

Define the extended-real oscillation
\[
 \Omega_L(d)=\sup_{\substack{n,m\ge1\\n\bmod L=m\bmod L}}|d(n)-d(m)| .
\]
For every fixed \(L\ge1\),
\[
 \Omega_L(d)<\infty \quad\Longleftrightarrow\quad r_Q=0,
 \qquad
 \Omega_L(d)<\infty\quad\Longrightarrow\quad \mathrm{RH}.
\]

Indeed, if the oscillation is bounded by \(C\), compare each \(n\ge1\)
with its representative in \(\{1,\ldots,L\}\):
\[
 |d(n)|\le C+\max_{1\le r\le L}|d(r)|.
\]
The established full-displacement witness argument gives \(r_Q=0\).
The reverse implication uses \(r_Q=0\Rightarrow d=0\).
The Lean proof uses a representative \(n\bmod L+L\) to avoid a separate
zero-residue case.

In particular, if RH fails, then \(\Omega_L(d)=+\infty\) for **every**
positive modulus \(L\). A modulus tending to zero would suffice, but
even finiteness at one modulus would suffice.

The formal implication to Mathlib RH uses the existing checked
full-closure-to-RH direction. It introduces no analytic converse provider.
The squarefree bounded-annihilator theorem is applied only to the *full*
witness, after the checked inclusion of the squarefree legal space in
the full space. It never substitutes the squarefree displacement for \(d\).

## 3. Exact signed carry formula

Write
\[
 b_q(f)=\sum_{a\mid q}\mu(q/a)\,[f(a)-f(a-1)].
\]
For any anchored physical function, every \(L,t,k\in\mathbb N\),
\[
 f(t+kL)-f(t)
 =f(kL)+
   \sum_{\substack{1\le q\le t+kL\\q\nmid L}}
       b_q(f)\,
       {\bf1}_{(kL\bmod q)+(t\bmod q)\ge q}.
\]
This is an exact finite identity, proved in Lean and specialized there
to the actual full displacement. If \(q\mid L\), the carry vanishes.
A surviving conductor may be a higher power of a small prime.
The endpoint \(d(kL)\) is retained and may cancel with the signed carry sum.

Consequently, D5's remaining obligation can be written concretely as:
find one \(L\ge1\) and one finite \(C\) such that, for every \(t\ge1,k\ge0\),
\[
 \left|d(kL)+
   \sum_{\substack{1\le q\le t+kL\\q\nmid L}}
       b_q(d)\,
       {\bf1}_{(kL\bmod q)+(t\bmod q)\ge q}
 \right|\le C.
\]
Every pair of congruent positive sites occurs in one of these orders.
A bound on the carry sum alone would omit the endpoint.

## 4. What the Hilbert limit actually gives

If \(g\) has equal values at \(n\) and \(m\), the checked estimate is
\[
 |f(n)-f(m)|
 \le \sqrt{\zeta(2)}(n+m)\,\|f-g\|_Q .
\]
For \(g=d_j\) and \(n\equiv m\pmod{L_j}\), put
\(\delta_j=\|d-d_j\|_Q\to0\). On a finite physical head,
\[
 \sup_{\substack{1\le n,m\le H\\n\equiv m\pmod{L_j}}}
 |d(n)-d(m)|\le2\sqrt{\zeta(2)}H\delta_j.
\]
The factor \(H\) prevents this estimate from controlling all sites.
For fixed \(H\), congruence modulo \(L_j>H\) also becomes vacuous except
for equal pairs.

By the nested-projection identities and metric comparison,
\[
 \delta_j\le
 \sqrt{\varepsilon_{Q,j}-\varepsilon_Q}
 +\sqrt{2/\zeta(2)}
  \sqrt{\varepsilon_{P,j}-\varepsilon_P}.
\]
This last displayed refinement is an informal deduction from the existing
projection identities, not a new separately formalized declaration here.

A uniform bound passes from finite stages to the limit only with fixed
quantifiers:
\[
 \exists L\ge1,\ C<\infty,\quad
 \forall\text{ sufficiently large }j,\quad \Omega_L(d_j)\le C.
\]
The new pointwise-limit theorem and its RH corollary formalize this.
The automatic identity \(\Omega_{L_j}(d_j)=0\) has a different quantifier order.

Uniform approximation to a fixed \(L\)-periodic function \(g\), with
\(\sup_n|f(n)-g(n)|\le\eta\), does imply
\(\Omega_L(f)\le2\eta\). This implication is also checked.

## 5. Explicit legal counterexample to the general limiting inference

The following is an **informal proof**, not a newly kernel-checked theorem
in this publication. It concerns an arbitrary legal sequence and isolates
the invalid inference; the normal equations of the actual \(d\) remain
additional structure.

Let
\[
 F_J(n)=\sum_{k=1}^J g_{2^k}(n).
\]
Each \(F_J\) is legal and \(2^J\)-periodic, and it is also
\(\operatorname{lcm}(1,\ldots,2^J)\)-periodic.
For \(q\ge2\), splitting at \(q\) gives
\[
 \|g_q\|_P^2
 =\sum_{n<q}\frac{n}{q^2(n+1)}
  +\sum_{n\ge q}\frac{g_q(n)^2}{n(n+1)}
 \le \frac{2}{q}.
\]
Thus the series of Hilbert norms is summable, and \(F_J\) converges in
both complete norms to a legal-closure vector \(F\), with
\[
 \|F-F_J\|_P\le(2+\sqrt2)2^{-J/2}.
\]

If \(n=\sum_i\epsilon_i2^i\) is its finite binary expansion, then
\[
 \sum_{k\ge1}\frac{n\bmod2^k}{2^k}
 =\sum_i\epsilon_i2^i\sum_{k>i}2^{-k}
 =\sum_i\epsilon_i=s_2(n).
\]
Hence \(F(n)\) is the binary digit sum and \(F(2^J-1)=J\).
It is unbounded, so its oscillation cannot be finite at any positive
modulus: finite residue-class oscillation would imply boundedness.

The genuine orthogonal projections of this same \(F\) onto the increasing
full spaces \(V_M\), in either metric, also converge to \(F\) and are
\(\operatorname{lcm}(1,\ldots,M)\)-periodic. Thus the general projection
convergence theorem does not remove the obstruction either.

This example has legal, periodic approximants and even an exponential
Hilbert convergence rate, but no uniform CRT modulus.
It demonstrates why periodicity and Hilbert convergence alone cannot
close the actual displacement problem.

## 6. Lean declaration map

| Module | Declaration | Result / hypothesis |
|---|---|---|
| Analysis/ResidueOscillation | Bound | Oscillation bound on all congruent positive pairs |
| Analysis/ResidueOscillation | exists_uniform_bound | One positive modulus with finite oscillation implies physical boundedness |
| Analysis/ResidueOscillation | bound_of_pointwise_limit | A common bound at a fixed modulus passes to a pointwise limit |
| Analysis/ResidueOscillation | bound_of_uniform_approximation | Supremum-norm approximation supplies a modulus |
| RH/QFullCRTDisplacement | residual_zero_of_physically_bounded | Full displacement boundedness forces zero full residual |
| RH/QFullCRTDisplacement | residual_zero_iff_finite_residue_oscillation | Exact zero-residual equivalence for each positive modulus |
| RH/QFullCRTDisplacement | riemannHypothesis_of_finite_residue_oscillation | Conditional research reduction; actual global bound Open |
| RH/QFullCRTDisplacement | unbounded_oscillation_of_not_riemannHypothesis | Under failure of RH, every positive modulus has unbounded oscillation |
| RH/QFullCRTDisplacement | full_carry_translation | Generic anchored identity, retaining all escaping conductors and the endpoint |
| RH/QFullCRTDisplacement | displacement_carry_translation | Exact identity for the actual full displacement |
| RH/QFullCRTDisplacement | pair_difference_le_norm_tail | Complete-Q norm controls physical pairs with factor \(n+m\) |
| RH/QFullCRTDisplacement | riemannHypothesis_of_stage_oscillation | Conditional finite-stage bound at one fixed modulus; the bound is Open |

No bound on the actual global oscillation has been supplied.


## 7. Verification and references

- Core candidate: Bazel/BuildBuddy job
  `job_d_WBiBAwNiHfBFPnVrzgbOrlaTsbta3v`,
  succeeded; server verification duration 103.654 seconds.
- Saved application and its transitive imports: Bazel/BuildBuddy job
  `job_QyHkeNVR5TYrr5zBTmkjz0YgtKP6ahxK`,
  succeeded; server verification duration 117.505 seconds.
  [BuildBuddy file-check evidence](https://app.buildbuddy.io/invocation/ca90b896-d75c-40d4-adbd-b232c516b7a9).
- Axiom inspection for
  `riemannHypothesis_of_finite_residue_oscillation`
  printed exactly `[propext, Classical.choice, Quot.sound]` in job
  `job_cSB7CxuQgL89PeYC873KbAM6woGFwAHf`.
  The temporary `#guard_msgs` wrapper failed because its expected message
  used different line wrapping and omitted a long-line linter warning.
  The printed axiom list is available in that job's log; this temporary
  wrapper is not part of the saved sources. Its failed status is not
  represented as a successful verification. The saved module passed
  separately as recorded above.
- Final publication requires a successful checkpoint of the complete
  project; the publication response is the authority for that scope.
  Workspace setup, transport, queue, and polling time are separate from
  the reported server verification durations.

The underlying discrete legal-closure RH criterion is stated as Theorem 1
of B. Bagchi, *On Nyman, Beurling and Baez-Duarte's Hilbert space
reformulation of the Riemann hypothesis* (2006):
https://arxiv.org/abs/math/0607733. Its role here is the existing
legal-closure-to-RH implication, not an oscillation estimate.
