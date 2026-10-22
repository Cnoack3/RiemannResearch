# Squarefree LCM telescoping: feasible stages, signed budgets, and sublinear energy

Date: 2026-10-19 (UTC).

Source: the user's LCM/primorial block-squeeze proposal and request of October 19.
This continues commits 079319c2be6f140e8bc30d97f5e953d60463daf7 and
4650466d6a7d65d9bbd49f217b094b9e1063d9cd. The workspace base is
8e42d6ae8577129d4d52bdfe071e31f4b684938a, which already includes both.
The elementary prime-interval input is Bertrand's postulate, through the
existing `NumberTheory.exists_prime_upper_half`. The unconditional asymptotic
input is the repository's checked PNT-based reciprocal Mobius cancellation.
No mathematical novelty claim is made.

## Outcome and status

The natural squarefree LCM schedule is feasible and has nearby legal anchors.
The complete-Q constrained minima on this schedule satisfy the new unconditional
bound E_H=o(H). Their exact signed cumulative cost minus gain is therefore
o(H), with no physical tail omitted. Uniform boundedness remains Open.

The period-tail identity supplies exact bookkeeping, but enlarging the displayed
period of a fixed residual supplies no approximation gain. The gain requires
refitting the legal coefficients. Certified finite examples show substantial
positive costs between prime enlargements, so the energy is not monotone.

The following are new formalizations in this update:

| Module | Main declarations |
| --- | --- |
| QSquarefreeHeadSchedule | `exists_near_anchor`, `primorialSchedule`, `missing_prime_blocks_head`, `period_six_cannot_reach_head_five` |
| QSquarefreeBlockBalance | `head_cost_eq`, `evaluated_telescope`, `signed_weighted_bound`, `bounded_energy_iff_signed_budget` |
| QSquarefreeBlockBalance | Conditional consumers `rh_of_signed_budget`, `rh_of_weighted_defect_budget`, `rh_of_weighted_partial_sums`, `rh_of_cofinal_signed_budget` |
| QPeriodicBlockComparison | `crtReciprocalEnergy_refinement`, `periodicTailEnergy_refinement`, `periodicTailEnergy_add`, complete first-period/tail bounds |
| QSquarefreeAffineEnergy | `baseline_error_le`, `energy_le_canonical`, `energy_sublinear`, `signed_balance_sublinear` |

The conditional consumers have explicit unresolved arithmetic budgets in their
types. They are not unconditional RH results.

## 1. A precise feasible squarefree LCM schedule

Write Z=zeta(2), Q(n)=1/(Z n^2), g_d(n)=(n mod d)/d, and

    L_H = product of primes p <= max(3,H),
    D_H = {d>1 : d divides L_H},
    V_H = span {g_d : d in D_H}.

Equivalently, L_H is the radical of lcm(1,...,max(3,H)). Every divisor is
squarefree; every squarefree d<=H divides L_H. The periods form a divisibility
chain and the legal spaces exhaust the squarefree span. Keeping prime 3 at
startup handles H=2, where period 2 cannot interpolate its own zero site.

Define F_H as the actual complete-Q least-error element of V_H subject to
F_H(n)=1 for 1<=n<=H, and E_H=||1-F_H||_Q^2.

Nearby anchors exist without adding a prime above H. For H>=4 choose a prime
H/2<p<=H by Bertrand. It is odd, so r=2p is a squarefree divisor of L_H and
H<r<=2H. For H=1,2,3 choose r=2,3,6 respectively. Thus the factor-four
head-cost estimate applies at every squarefree boundary in this schedule.
This discharges the feasibility and nearby-anchor obligations, not an energy
budget. `Schedule` records only elementary finite feasibility data.

For a fixed primorial L=p_1...p_m, the next missing prime p_(m+1) cannot be
included in an exact head. The existing forced-coefficient identity would
require its coefficient to equal -mu(p_(m+1))=1, but its conductor is absent.
The new `missing_prime_blocks_head` makes this obstruction explicit; period 6
cannot reach head 5. Enlarge the period before imposing that prime site.
The anchors can be changed because the established optimizer and minimum are
anchor independent.

Head length and period length are different parameters. Every legal old-stage
function vanishes at L, by the existing `QResidueConditional.divisorStage_zero`.
Thus demanding an exact head through L is impossible. Using L as the endpoint
of a displayed energy block is valid and imposes no such interpolation.

## 2. Evaluated exact single-step comparison

For n>=2 first expand from L_(n-1) to L_n, holding the old exact head. Let

    A_n = F_(n-1),
    B_n = argmin in V_n, with exact head through n-1,
    G_n = ||A_n-B_n||_Q^2,
    delta_n = 1-B_n(n).

Let kappa_n be the actual complete-Q inverse-Gram evaluation capacity of the
old zero-head space in V_n. For squarefree n it is strictly positive. Set

    K_n = delta_n^2/kappa_n          if n is squarefree,
          0                         otherwise.

The exact identities, now assembled in `head_cost_eq` and `refit_period_gain`,
are

    E_(n-1) = ||1-B_n||_Q^2 + G_n,
    E_n     = ||1-B_n||_Q^2 + K_n,
    E_n + G_n = E_(n-1) + K_n.

No cost is charged at a nonsquarefree boundary. If c_(n,d) are the coefficients
of this actual B_n, the existing boundary inversion gives
delta_n=c_(n,n)+mu(n). These are neither arbitrary prescribed coefficients nor
the coefficients of the unconstrained projection.

Consequently

    E_N = E_1 + sum_(2<=n<=N) (K_n-G_n),
    E_N <= E_1 + sum_(2<=n<=N) (W_n-G_n),

where W_n=4 delta_n^2/[Z(n-1)] at squarefree n, and W_n=0 otherwise.
The first line is the exact balance. The second is a stronger sufficient
budget because it bounds each actual reciprocal capacity separately.
Lean indexes E_H by i=H-1 and the new boundary n by i=n-2.

For primorial blocks, take H_m=p_(m+1)-1 and L_m=p_1...p_m, m>=2. Refit at
the old head H_m into L_(m+1), then impose all new heads through H_(m+1).
There are no period changes inside this block. Thus

    E_(H_(m+1),L_(m+1)) - E_(H_m,L_m)
      = sum_(H_m<n<=H_(m+1), squarefree n)
          delta_(n,L_(m+1))^2/kappa_(n,L_(m+1)) - G_m,

with the actual fixed-period constrained refit defining every delta. The
nearby anchor construction still applies because all primes through H_m
belong to L_m. A bound only at a cofinal sequence of these endpoints is
sufficient; `rh_of_cofinal_signed_budget` proves that consumer without
assuming an energy bound at intermediate heads.

## 3. The unconditional cumulative estimate obtained here

The complete-Q conductor estimate from commit 4650466d is reused:

    ||g_d||_Q^2 <= 2/(Zd),  d>=2.

Let m_H=sum_(d<=H) mu(d)/d, and write the existing canonical exact head as

    X_H = -sum_(d<=H) mu(d) g_d + (H+1)m_H g_(H+1).

It is an ambient Q vector; this argument does not assert that H+1 is always
a squarefree legal conductor. Replace that anchor by an actual legal r with
H<r<=2H:

    Y_(H,r) = -sum_(d<=H) mu(d) g_d + r m_H g_r,
    Y_(H,r)-X_H = A-B,
    A=r m_H g_r,  B=(H+1)m_H g_(H+1).

The exact norm identity is

    ||A-B||_Q^2 = ||A||_Q^2 + ||B||_Q^2 - 2<A,B>_Q.

For the sublinear upper bound only, the signed term is bounded using
||A-B||^2<=2||A||^2+2||B||^2. The conductor estimate then yields

    ||A-B||_Q^2 <= (16/Z) H m_H^2,
    E_H <= ||1-Y_(H,r)||_Q^2
         <= 2||1-X_H||_Q^2 + (32/Z) H m_H^2.

The existing unconditional providers prove
||1-X_H||_Q^2/H -> 0 and m_H -> 0. Therefore

    E_H/H -> 0,
    [sum_(2<=n<=N)(K_n-G_n)]/N -> 0.

Both limits are now formalized for every `Schedule` satisfying the stated
nearby-anchor hypotheses, including `primorialSchedule`. No RH hypothesis is
used. This transfers the established sublinear canonical estimate to the
actual full divisor-stage constrained minima and their evaluated signed
balance. It does not establish O(1), O(H^epsilon) for every epsilon, or decay.

## 4. What the periodic tail contributes

For a bounded L-periodic residual R put

    J_L(R)=sum_(1<=a<=L) R(a)^2/a^2,
    S_L(R)=sum_(1<=a<=L) R(a)^2,
    c_Z=1-1/Z>0.

The complete energy is J_L(R)/Z+T_L(R), with

    c_Z S_L(R)/L^2 <= T_L(R) <= S_L(R)/L^2.

For L|K, keeping the SAME residual R, the new exact refinement theorem gives

    J_K(R)=J_L(R)+sum_(L<a<=K) R(a)^2/a^2,
    T_L(R)=T_K(R)+(1/Z)sum_(L<a<=K) R(a)^2/a^2.

The positive displayed-block increment exactly cancels the tail decrease.
Treating the latter as G_n would double count a gain that never occurred.

For different residuals R_old and R_new, both expressed on K, put
U=R_new-R_old. The new `periodicTailEnergy_add` retains

    T_K(R_new)=T_K(R_old)
      + 2 sum_a w_K(a+K) R_old(a) U(a) + T_K(U).

The signed mixed term has no general favorable sign. The complete-norm
version is the usual exact Hilbert expansion. The first-period/tail bounds
give a precise interval for the signed energy change:

    J_new/Z+c_Z S_new/K^2 - J_old/Z-S_old/L^2
      <= E_new-E_old = cost-gain
      <= J_new/Z+S_new/K^2 - J_old/Z-c_Z S_old/L^2.

Here J_old,S_old use period L and the OLD residual; J_new,S_new use period K
and the NEW residual. This supplies computable comparisons, not a uniform
bound on the two moving profiles.

Existing scaled carries show why tail decay needs proof. For an odd prime d,
let C_(d,2)=2g_(2d)-g_d and U_d=sqrt(d/2) C_(d,2). The already established
scaled-carry estimate gives ||U_d||_Q^2<=8/Z and weak convergence to zero.
Its values vanish below d. On one period 2d, exactly d values of C_(d,2) are
one and the rest are zero, so

    S_(2d)(U_d)/(2d)^2=1/8,
    T_(2d)(U_d)>=c_Z/8>0.

This is an ordinary proof using the existing carry results, not another
scaled-carry formalization. It disproves automatic periodic-tail decay from
bounded energy and growing zero heads for arbitrary periodic packets. It is
not a counterexample to the target-one affine optimizer construction.

## 5. Finite complete-tail certificates

`PrimorialBlockBalanceCertificates.md` contains the self-contained Python
program, using only integers and Fraction.
`PrimorialBlockBalanceCertificates.json` records all twelve heads and the
cost, gain, and signed-balance enclosures. Selected complete-Q minima are:

| H | L_H | Certified interval for E_H |
| ---: | ---: | --- |
| 1 | 6 | [0.055024959, 0.055025387] |
| 3 | 6 | [0.064251534, 0.064252051] |
| 5 | 30 | [0.026570451, 0.026570518] |
| 6 | 30 | [0.060631490, 0.060631632] |
| 7 | 210 | [0.022425784, 0.022425797] |
| 10 | 210 | [0.042502167, 0.042502187] |
| 11 | 2310 | [0.019629920, 0.019629924] |
| 12 | 2310 | [0.019629920, 0.019629924] |

These are enclosures for the ACTUAL minima, not just trial-function energies.
At head 5, the period gain lies in [0.038213777,0.038214358], and its new head
cost lies in [0.000532694,0.000532826]. Head 6 has zero period gain and cost
in [0.034060973,0.034061181]. Head 10 likewise has zero gain and cost in
[0.020076370,0.020076402]. Thus stepwise energy monotonicity is false for
this proposed natural schedule. The observed finite decreases at prime
enlargements do not prove their future dominance.

Certificate justification: for each residue a, enclose the raw progression
weight sum_(k>=0)1/(a+kL)^2. Compute 256 terms with outward integer rounding
at denominator 2^100. The remaining infinite series lies between
1/[L(a+256L)] and 1/[L(a+255L)], by the elementary decreasing-function
integral comparison. This is a complete-tail enclosure.

Write a_d=c_d/d. Exact heads force a_d=-mu(d)/d for d<=H and sum_d a_d=1.
Choose the smallest free anchor r>H, and parametrize all remaining coefficients
using the integer columns (n mod d)-(n mod r). The code minimizes each of the
lower and upper rational weighted quadratic forms exactly. Positive Gaussian
pivots and A*x=b are checked, as are the complete exact heads. The two minima
enclose Z*E_H by pointwise comparison of the weights. A separate outward
rational enclosure of Z, using 4096 terms and its entire integral tail,
produces the displayed normalized intervals.

The code also certifies the nearby-anchor inequality at every squarefree
tested step. If f_plus minimizes the upper-weight form and f_star is the
actual optimizer, the affine Pythagorean identity gives
||f_plus-f_star||_raw^2<=m_upper-m_lower. Consequently their values at n
differ by at most n*sqrt(m_upper-m_lower). A rational radius, checked by
squaring, supplies a lower bound for the actual |delta_n|. The code verifies
that the upper cost enclosure is below even this lower enclosure for the
factor-four RHS. The nonsquarefree zero costs are checked exactly.

These numerical certificates are exact rational host computations with the
mathematical justification above. They are not individually replayed by the
Lean kernel. The general finite identities and feasibility claims are Lean
formalizations; this distinction is intentional.

## 6. The precise remaining arithmetic inequality

Open, exact version: prove for an actual feasible schedule, possibly only at
cofinal endpoints N_j, that

    sum_(2<=n<=N_j, squarefree n) delta_n^2/kappa_n
      <= sum_(2<=n<=N_j) G_n + B

with one finite B independent of j. This is exactly a bounded-energy provider
for that family. The new o(N) result does not imply it.

Open, stronger sufficient version: replace delta_n^2/kappa_n by
4 delta_n^2/[Z(n-1)]. Absolute summability of these weighted moving defects
would suffice while ignoring all gains. A bound delta_n=O(n^-epsilon), or
O((log n)^(-1/2-epsilon)), would give that summability. Bounded defects only
give a logarithmic majorant; delta_n->0 alone is insufficient. Fixed-conductor
coefficient limits give no such bound on the MOVING n-th defect of B_n.

A useful sufficient block formulation is cost(block)<=gain(block)+epsilon_j
with summable positive epsilon_j. It retains cancellations between cumulative
positive costs and gains. An absolute budget is potentially much stronger.
No provider of either inequality is asserted in this update.

For a new-stage legal zero-head packet v, Hilbert projection gives the useful
ordinary bound G_n>=|<1-A_n,v>_Q|^2/||v||_Q^2, for v nonzero. Indeed the new
refit residual is orthogonal to the new zero-head space, and Cauchy--Schwarz
applies to B_n-A_n. The denominator can use the existing conductor and carry
estimates, but a sufficiently large correlation numerator remains an
arithmetic problem. This bound is not claimed as a new Lean declaration here.

The existing conditional-carry and Fourier identities preserve signed mixed
terms. The coefficient-mass obstruction and bounded scaled-carry examples
from commit 4650466d are reused, not reproved. They supply neither the
required moving-defect budget nor a lower bound on the selected refit gains.

## 7. Comparison with proving q_N -> 1 directly

For q_N=1-dist_Q(1,V_N)^2, squarefree constant closure and the established
Nyman--Beurling/Bagchi transfers identify q_N->1 with RH. A uniformly bounded
exact-head family is sufficient because the existing bounded-exact-head
averaging theorem produces legal approximants converging strongly to one.
This is the gain of the route: it asks for a bound on the constrained error,
then uses geometry to produce decay for averages.

It does not make the missing arithmetic estimate automatic. For the fixed
schedule L_H=primorial(max(3,H)), no converse from RH to its uniform affine
energy bound is proved here. RH guarantees approximation along the exhaustive
span, but not the conditioning of this prescribed head/period diagonal.
Allowing adaptive period enlargement gives more freedom; the present natural
schedule can be a stronger requirement. The exact signed budget is equivalent
to the bound for the selected family, not an independent estimate.

The route now has fully feasible stages, exact block accounting, certified
nonmonotone examples, and unconditional o(H) energy. Its next substantive
objective is O(1) signed balance at cofinal endpoints, or a different bound
that controls the weighted average errors directly. RH remains unproved.

## Verification boundary

The combined candidate declarations passed Lean-server snippet job
job_Y8MWzitwHh2LGByxRd7rsK2IjM10HTyl. Axiom checks on the anchor theorem,
evaluated telescope, sublinear-energy theorem, and cofinal conditional RH
consumer reported only propext, Classical.choice, and Quot.sound. Those checks
do not discharge the explicit signed-budget hypothesis of an RH consumer.

Publication requires the final push-enabled server checkpoint to validate
the separate modules and the required project dependents. Its terminal job,
validation scope, and published commit are reported in the accompanying
response. No hosted CI is used as a substitute.
