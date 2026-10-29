# General squarefree-head energy certificates and shared-site Schur complements

29 October 2026. Continuation of
[SquarefreeHeadDimensionAndEnergy20261029.md](SquarefreeHeadDimensionAndEnergy20261029.md).
Source: the user's general-d argument and request for complete-energy formalization.
Development base: 1905e5be21ec20d217b0f7c32905f09bd8720f92.

## Scope

The requested general-d bounds concern complete energy from below. Their
hypotheses are radical compatibility and the prescribed head; they do not
assume a uniform energy bound, density, or RH. The stronger arbitrary-radical-
fibre formulation and the shared-site scalar completion are described below.
Kernel verification and publication status are recorded at the end.

## 1. Radical relation

Let d>=2 be squarefree. Since rad(d^2)=rad(d)=d, compatibility gives
F(d^2)-F(d^2-1)=F(d)-F(d-1).
A head equal to one through d-1 therefore gives exactly
\[
F(d)+F(d^2-1)-F(d^2)=1.
\]
Only the value at d-1 is used for this relation. The other prescribed head
values enter the energy calculation.

More generally, the same relation holds with d^2 replaced by any m with
rad(m)=d. For the three-site energy split, the Lean statement explicitly
assumes d+1<m, so d,m-1,m are distinct and lie beyond the head.
If m>d and rad(m)=d>=2, this separation follows arithmetically from d|m.

## 2. Exact weighted completion, including the whole complement

For positive A,B,C, put D=A+B+C. If x+y-z=t, then
\[
\frac{x^2}{A}+\frac{y^2}{B}+\frac{z^2}{C}
=\frac{t^2}{D}
+\frac{(x-At/D)^2}{A}
+\frac{(y-Bt/D)^2}{B}
+\frac{(z+Ct/D)^2}{C}.
\]
This is the primary identity. Weighted Cauchy--Schwarz is its consequence
after discarding the three nonnegative squares.

For reciprocal weights a(n), let
\[
J_{d,m}=\{1,\ldots,d-1\}\cup\{d,m-1,m\},\qquad
E_{\rm omit}=\sum_{\substack{n\ge1\\n\notin J_{d,m}}}\frac{F(n)^2}{a(n)}.
\]
The infinite series is split using summability, not by truncating its tail.
The complete identity is head energy + 1/D + three squares + E_omit.
The implementation also includes the anchored coordinate zero, whose
actual Q and Pareto weights vanish.
The omitted series is explicitly nonnegative.

For Q, a(n)=n^2 and the entire identity is divided by zeta(2). With
m=d^2,
\[
D=d^2+(d^2-1)^2+d^4=2d^4-d^2+1.
\]
Thus
\[
\|F\|_Q^2=
\frac{1}{\zeta(2)}
\left[
\sum_{n=1}^{d-1}\frac1{n^2}
+\frac1D
+\frac{(F(d)-d^2/D)^2}{d^2}
+\frac{(F(d^2-1)-(d^2-1)^2/D)^2}{(d^2-1)^2}
+\frac{(F(d^2)+d^4/D)^2}{d^4}
\right]+E_{Q,\rm omit}.
\]
All denominators used in square completion are proved positive.
Consequently
\[
\boxed{\|F\|_Q^2\ge
\frac{\sum_{n=1}^{d-1}n^{-2}+(2d^4-d^2+1)^{-1}}{\zeta(2)}.}
\]
The application covers compatible Q vectors, finite legal vectors, and
vectors in the closed legal span, using existing compatibility inclusions.

For Pareto, a(n)=n(n+1), and
\[
D=d(d+1)+(d^2-1)d^2+d^2(d^2+1)=2d^4+d^2+d.
\]
The same complete identity holds with these denominators, no zeta
normalization, and head mass (d-1)/d. In particular
\[
\boxed{\|F\|_P^2\ge\frac{d-1}{d}+\frac1{2d^4+d^2+d}.}
\]
The application uses the existing sequence-preserving toPareto map and its
inverse toQ. It does not identify the two Hilbert norms or their projections.

At d=5 the Q head is 205/144 and D=1226. For Pareto D=1280 and the full
lower bound is 4/5+1/1280=205/256. These are exact rational equalities.

## 3. A stronger single-row selection

For any m with rad(m)=d and d+1<m, the unnormalized Q correction is
\[
\frac1{d^2+(m-1)^2+m^2}
=\frac1{d^2+2m^2-2m+1},
\]
and the Pareto correction is
\[
\frac1{d(d+1)+2m^2}.
\]
For composite squarefree d, take m=dp where p is a prime divisor of d.
Then p<d, rad(dp)=d, and dp<d^2, so both corrections are strictly larger
than the requested d^2 corrections. At d=6,m=12 the denominators are
301 and 330, compared with 2557 and 2634 for m=36.

The arbitrary-m complete-energy identities are proved in the application
modules. The rule selecting the smallest prime divisor and its
strict improvement are mathematical consequences explained here; there is
no separate checked prime-selection declaration in this change.

## 4. Several constraints sharing F(d)

Choose a finite set T of distinct m>d with rad(m)=d. Since every such m is
a multiple of d>=2, the pairs {m-1,m} are disjoint, and none contains d.
They are also disjoint from the prescribed head.

For arbitrary positive physical weights w, write
\[
a=w_d^{-1},\quad b_m=w_{m-1}^{-1},\quad c_m=w_m^{-1},\quad
S=\sum_{m\in T}\frac1{b_m+c_m}.
\]
Let x=F(d), y_m=F(m-1), z_m=F(m), so x+y_m-z_m=1.
Then the exact selected energy is
\[
\begin{aligned}
\frac{x^2}{a}+\sum_{m\in T}
  \left(\frac{y_m^2}{b_m}+\frac{z_m^2}{c_m}\right)
={}&\frac{S}{1+aS}
+\left(\frac1a+S\right)
  \left(x-\frac{aS}{1+aS}\right)^2\\
&+\sum_{m\in T}\left[
 \frac{(y_m-b_m(1-x)/(b_m+c_m))^2}{b_m}
+\frac{(z_m+c_m(1-x)/(b_m+c_m))^2}{c_m}
\right].
\end{aligned}
\]
Add the head and the entire omitted-coordinate energy to obtain the
corresponding complete physical-energy identity.

This is a special Schur complement with
\[
G=\operatorname{diag}(b_m+c_m)+a\,\mathbf1\mathbf1^{\mathsf T},
\qquad \mathbf1^{\mathsf T}G^{-1}\mathbf1=\frac{S}{1+aS}.
\]
For completeness, put L_m=b_m+c_m and t_m=1/L_m. The inverse is explicitly
\[
G^{-1}=\operatorname{diag}(1/L_m)
-\frac{a}{1+aS}\,tt^{\mathsf T}.
\]
Multiplication verifies the formula using diag(L)t=1 and sum(t_m)=S.
For any right-hand side v, this also gives
\[
v^{\mathsf T}G^{-1}v
=\sum_m\frac{v_m^2}{L_m}
-\frac{a}{1+aS}\left(\sum_m\frac{v_m}{L_m}\right)^2.
\]
The constant-right-hand-side Lean identity is the v=1 case. The normal-
equation solution is u_m=1/[L_m(1+aS)], which directly verifies G u=1
and sum(u_m)=S/(1+aS).

Positive definiteness follows from
\[
u^{\mathsf T}Gu=\sum_m L_mu_m^2+a\left(\sum_m u_m\right)^2>0
\]
for every nonzero u. Thus no singular inverse or unproved rank assumption
is hidden in this paper-level matrix interpretation.

The existing checked building blocks are
`Analysis/FiniteSignedQuadratic.lean` (`schur_completion`,
`schur_completion_of_inverse`) and
`Analysis/FiniteGramMultipleConstraint.lean` (`sourceRows_gram`,
`sourceRows_independent_of_interpolants`, `coefficients_energy`,
`coefficients_completion`). The inverse-based theorem explicitly requires an
inverse certificate. The general squarefree weighted-window assembly in
Section 2 of the preceding memorandum is still paper-level. The new result
supplies an explicit special family and stronger concrete lower certificates;
it does not replace the abstract Schur theorem with a stronger theorem.

The scalar identity avoids introducing a matrix inverse into the Lean
development. It is the same finite constrained minimization. With one row,
S=1/(b+c) and S/(1+aS)=1/(a+b+c).

For a>=0 and 0<=S<T,
\[
\frac{T}{1+aT}-\frac{S}{1+aS}
=\frac{T-S}{(1+aT)(1+aS)}>0.
\]
Thus each additional disjoint radical-fibre row strictly improves this
lower certificate. Adding separately computed three-site lower bounds would
incorrectly count the F(d) energy more than once; the shared-site formula
accounts for it exactly.

The finite algebraic shared-family identity is included in the generic
module. The arithmetic disjointness-to-complete-physical-series assembly
for an arbitrary finite family, and the completely general weighted-window
matrix theorem, are not asserted as formalized here.


### Paper-level infinite Pareto fibre refinement

For a prime p, the later radical-p fibre is exactly m=p^k, k>=2.
For Pareto weights b_m+c_m=2m^2, and therefore
\[
S_\infty=\sum_{k=2}^{\infty}\frac1{2p^{2k}}
 =\frac1{2p^2(p^2-1)}.
\]
With a=p(p+1), the shared correction becomes
\[
\frac{S_\infty}{1+aS_\infty}=\frac1{2p^4-p^2+p}.
\]
Consequently the stronger complete-energy bound is
\[
\|F\|_P^2\ge \frac{p-1}{p}+\frac1{2p^4-p^2+p}.
\]
For p=5 this is 197/246, strictly exceeding 205/256.

For general squarefree d, finite-prime geometric products give
\[
S_\infty=\frac12\left[
  \prod_{p\mid d}\frac1{p^2-1}-\frac1{d^2}\right].
\]
Every site with radical d is divisible by d>=2, so its adjacent pair is
disjoint from all other such pairs and from the head and d itself.

The infinite identity also retains all remainders. Put x=F(d), t=1-x,
a=d(d+1), S=S_infty, and let Omega be the complete energy outside the head,
the site d, and all these pairs. Then
\[
\|F\|_P^2=\frac{d-1}{d}+\frac{S}{1+aS}
+\left(\frac1a+S\right)\left(x-\frac{aS}{1+aS}\right)^2
+\sum_{\substack{m>d\\\operatorname{rad}(m)=d}}R_m+\Omega,
\]
where
\[
R_m=
\frac{(F(m-1)-(m-1)t/(2m))^2}{m(m-1)}
+\frac{(F(m)+(m+1)t/(2m))^2}{m(m+1)}.
\]
The pair identity shows 0<=R_m<= the corresponding pair energy.
The disjoint pair-energy sum is bounded by the complete Hilbert energy,
so the remainder sum converges. Summing the pair identities is legitimate.
Equivalently, take finite fibre sets and pass to the limit in S/(1+aS).

This infinite-fibre application and the finite-prime Euler-product formula
remain paper-level in this change. Wolfram independently returned zero
for both scalar completion differences and confirmed the geometric sum and
197/246. This computation is not a substitute for Lean verification.
The relaxation minimizer need not satisfy the other radical constraints
or belong to the legal span.

## 5. Precise limitation for residual vanishing

The anchored sequence F(0)=0, F(n)=1 for n>=1 is itself radical-compatible
and has complete Q and Pareto energy one. Therefore every finite-window
relaxation of these compatibility equations with a constant head has
minimum at most one. Stronger lower certificates for that relaxation cannot
by themselves exclude this constant target.

Finite compatible interpolation does provide legal extensions, but the
remaining complete energy of those extensions is not controlled by a finite
window. The missing RH input remains a uniform upper bound on complete
legal exact-head energies along a cofinal sequence (a frequently bounded
cofinal subsequence suffices for the existing consumer), or a checked
equivalent residual-vanishing provider.

These lower-energy certificates neither supply that upper bound nor prove
that the residual is nonzero. No unconditional density or RH conclusion
is claimed.

## 6. Declaration and verification ledger

All 46 new theorems listed below compiled in their saved modules. Entries
marked "axiom-audited" were additionally inspected with `#print axioms`.
The 22 selected audits reported only `propext`, `Classical.choice`, and
`Quot.sound`; no extra domain-specific axiom or placeholder was used.
The hypotheses in their types remain explicit: squarefreeness, d>=2,
radical compatibility, and the prescribed head. For arbitrary m, separation
and rad(m)=d are also explicit. The scalar algebra uses the displayed
nonzero/positive-denominator hypotheses. Hilbert-space summability is proved
from the supplied vector, not assumed as a new research obligation.

| Server job | Scope | Result | Server-reported duration |
| --- | --- | --- | --- |
| `job_U9yHrs7GXbU43GEPeYN9-bJ_BYgo1XA2` | Import saved generic module; audit 9 central declarations | Passed, exit 0 | 27.788 s |
| `job_BkAkkHQ2r3AkBmvACyzYkXQ7qmZ5IpT8` | Build/import saved Q and Pareto application modules; audit 13 central declarations | Passed, exit 0 | 1631.145 s |

These durations include the server's imported-module build and audit work;
they are not isolated kernel timing measurements. The recorded queue delays
were approximately 0.001296 s and 0.000569 s respectively.
The long application job was polled at intervals of at least 60 seconds.
Workspace-opening request time was not independently recorded; initial
connection timeouts are not counted as proof-checking time.

The application tool returned a truncated tail of its large build/audit log,
together with terminal success, exit code 0, and `verified: true`.
Publication uses the separate source-audit and aggregate-project checkpoint
gate. The import audits above do not assert that unrelated repository
modules were freshly rebuilt; the checkpoint job and published commit are
reported in the accompanying delivery.

Earlier development submissions included bounded wall-time failures and
ordinary elaboration errors, all repaired before these successful checks.
The first proof-submission transport timeout was followed by an empty job
list, confirming that no job had been accepted. No duplicate job was
submitted while a prior verification was queued or running.

### Analysis/WeightedConstraintEnergy.lean (13 new theorems)

Namespace: `RiemannResearch.Analysis.WeightedConstraintEnergy`.

- `three_site_completion` — axiom-audited.
- `three_site_lower_bound` — axiom-audited.
- `sum_headThreeSites`
- `omittedEnergy_nonneg`
- `complete_head_three_split` — axiom-audited.
- `threeSiteRemainder_nonneg`
- `complete_head_three_completion` — axiom-audited.
- `complete_head_three_lower_bound` — axiom-audited.
- `pair_completion`
- `shared_site_completion` — axiom-audited.
- `shared_family_completion` — axiom-audited.
- `schur_correction_increment` — axiom-audited.
- `schur_correction_strict_mono` — axiom-audited.

### RH/QSquarefreeConstraintEnergy.lean (16 new theorems)

Namespace: `RiemannResearch.RH.QSquarefreeConstraintEnergy`.

- `radical_square_of_squarefree` — axiom-audited.
- `constrained_radical_fiber_relation`
- `constrained_square_relation` — axiom-audited.
- `qGeneralRemainder_nonneg`
- `qGeneralOmittedEnergy_nonneg`
- `raw_Q_term`
- `raw_Q_summable`
- `raw_Q_energy`
- `radical_fiber_energy_completion` — axiom-audited.
- `radical_fiber_energy_lower_bound`
- `qCertificateDenominator_square`
- `exact_head_square_energy_completion` — axiom-audited.
- `exact_head_square_energy_lower_bound` — axiom-audited.
- `legal_exact_head_square_energy_lower_bound` — axiom-audited.
- `closed_legal_exact_head_square_energy_lower_bound` — axiom-audited.
- `head_five_certificate_constants` — axiom-audited.

### RH/SquarefreeParetoConstraintEnergy.lean (17 new theorems)

Namespace: `RiemannResearch.RH.SquarefreeParetoConstraintEnergy`.

- `paretoDenominator_nonneg`
- `paretoDenominator_pos`
- `pGeneralRemainder_nonneg`
- `pGeneralOmittedEnergy_nonneg`
- `raw_P_term`
- `raw_P_summable`
- `raw_P_energy`
- `pareto_head_energy`
- `pareto_three_denominators`
- `radical_fiber_pareto_energy_completion` — axiom-audited.
- `radical_fiber_pareto_energy_lower_bound`
- `pCertificateDenominator_square`
- `exact_head_square_pareto_energy_completion` — axiom-audited.
- `exact_head_square_pareto_energy_lower_bound` — axiom-audited.
- `legal_exact_head_square_pareto_energy_lower_bound`
- `pareto_head_five_certificate_constant` — axiom-audited.
- `pareto_exact_head_square_energy_lower_bound` — axiom-audited.


## 7. Focused continuation

1. Connect the checked finite shared-family identity to disjoint physical
   radical-fibre pairs and a complete omitted-coordinate series for arbitrary
   finite families. Prove the physical Gram identity
   D W^{-1} D^T=diag(b_m+c_m)+a 11^T and verify the displayed normal-equation
   solution. The broader finite constraint structure is already available in
   `QSquarefreeHeadDimension`: `constraintRow_point_diagonal`,
   `constraintRow_point_above`, `constraintMap_surjective`,
   `constraintMap_rank`, and `legalHeads_eq_kernel`.
2. Formalize the general weighted-window Gram inverse/minimum theorem using
   the already proved triangular constraint independence.
3. Formalize the infinite Pareto fibre summation and finite-prime product,
   including the full nonnegative remainder identity.
4. Independently pursue a uniform upper bound for complete legal exact-head
   energies along a cofinal schedule. None of the lower certificates above
   supplies this missing RH provider.
