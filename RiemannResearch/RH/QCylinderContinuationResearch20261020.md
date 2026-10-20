# Squarefree cylinder rigidity, actual minimizer limits, and complete-Q obstructions

Research continuation for Christian Noack, 20 October 2026 UTC.

## Verification scope

The prior interrupted work has been recovered in the retained Lean workspace.
Development job `job_jv5l4vQ_48A9xkxYcf7sabcOi0P6DC7a` succeeded with exit code 0
and `verified=true`. It checked the repaired weight comparison, actual minimum
limit, actual minimizer convergence, and both modulus-three and modulus-six
conditional obstructions, together with imports of the four cylinder modules.
The six inspected key declarations depended only on `propext`,
`Classical.choice`, and `Quot.sound`.

Development job `job_HLMTuEUBLeqMRUVTMwH8eHfjvImhlgcP` also succeeded with
exit code 0 and `verified=true`. It built the repaired parity module as an
actual repository import and verified the complete signed-tail assembly.
The inspected signed-tail ratio declaration used only the same three ordinary
foundational axioms. Final publication is gated by the single server checkpoint,
which audits and validates the aggregate and changed modules before pushing.
The terminal checkpoint result, rather than these development snippets alone,
determines the published verification scope. No unconditional RH theorem is claimed.

## Scope and baseline

This continues `RH_CRT_Profinite_Research_Handoff_Verified_2100 (1).md`.
The isolated workspace started at main commit
`95abb42e14dfa55790046f80c91b234a2e87829c`, later than the handoff's
`3a38c26c294e285d951f9322c5a066e4a39a296f`. In particular,
`QRationalGcdTail.lean` already contains actual gcd-class signed-tail
means and variance identities. Those are reused, not claimed again.

The setting is unchanged: Q(n)=1/(zeta(2)n^2), n>=1;
g_d(n)=(n mod d)/d; H is the complete-Q closed span of all squarefree
g_d, including composite d. For squarefree L>0, V_L includes every
divisor atom d|L (d=1 is zero).

RH has not been proved. The new results described below do not establish
that the constant target belongs to H.

## 1. Cylinder rigidity

For every squarefree positive L, an L-periodic element F of H satisfies

    F = F(L) * 1 + v,   v in V_L.

In particular,

    H intersect Cyl_L subset V_L + R*1.

The coefficient of the extra constant direction is exactly the value on
the zero residue class, not a free unspecified scalar. Consequently:

* If F(L)=0, then F already belongs to the finite-dimensional V_L.
* If F(L) is nonzero, then membership F in H forces 1 in H.
* If 1 is not in H, then H intersect Cyl_L = V_L.
* If 1 is in H, then H intersect Cyl_L = V_L + R*1.

The last two displayed space equalities follow mathematically from the
representation and the obvious reverse inclusions. The formal declarations
record the exact vector representation and its zero/nonzero consequences.

### Proof architecture

1. At a positive physical site n, the backward jump of a legal atom is
   1/d - 1_{d|n}. Therefore jumps agree at any two sites having the same
   squarefree-divisor events. Point evaluation is continuous in complete
   Q-Hilbert space, so this relation survives closure. In particular,
   Delta F(n^k)=Delta F(n) for each k>0.
2. If gcd(n,L)=gcd(m,L)=g and L is squarefree, put q=L/g.
   Both n and m are coprime to q. Their q.totient powers are 1 modulo q
   and 0 modulo g. Since gcd(g,q)=1, CRT gives a common residue modulo L.
   Periodicity and power invariance then show that Delta F is constant on
   every gcd class, away from the artificial coordinate zero.
3. Finite divisor-incidence inversion writes any gcd-class jump as a sum
   of divisor indicators. Integrating retains an exact linear slope plus
   residue atoms. Periodicity makes the slope zero.
4. The repository's physical sequence has auxiliary value zero at index
   zero. The integration therefore uses f(n)=F(n+L), ensuring every jump
   used in the periodic argument is at a site >=2. This avoids incorrectly
   imposing periodicity at the artificial coordinate.

This proves research agenda item 6; it does not assume invariance of H under
conditional expectation.

## 2. Rational weight comparison and the exact remainder

Write w_L(a)=sum_{j>=0}Q(a+jL), 1<=a<=L, and

    u_L(a)=1/a^2 + 2/[L(2a+L)].

The midpoint comparison retains its exact positive defect. For
x=a+(j+1)L,

    2/[L(2x-L)] - 2/[L(2x+L)]
      = 1/x^2 + L^2/[x^2(4x^2-L^2)].

Finite sums telescope with both the terminal boundary value and the sum of
positive defects present. Passage to the summable inverse-square series gives

    zeta(2) w_L(a) <= u_L(a) <= (5/3) zeta(2) w_L(a).

For an L-periodic f, define the unnormalized rational objective E_L(f).
There is an exact nonnegative remainder

    E_L(f) = zeta(2) ||1-f||_Q^2 + Gap_L(f),
    Gap_L(f) = sum_{a=1}^L [u_L(a)-zeta(2)w_L(a)] (1-f(a))^2.

If |1-f(a)|<=B over the period, then

    0 <= Gap_L(f) <= 2B^2/L.

These estimates include the complete infinite Q tail. They are not
truncated-norm calculations and do not assume a bound on optimizer
coefficients. The periodic Q-Hilbert specialization uses the actual
physical sequence and qOne.

### Consequences, with formalization scope distinguished

The pointwise comparison immediately yields the ordinary finite-minimum
inequalities zeta(2)D_L <= min E_L <= (5/3)zeta(2)D_L for the same legal
dictionary. Thus their vanishing conditions are equivalent.

The fixed-competitor gap proves mathematically, along exhaustive divisibility
stages L_M, that min E_{L_M} tends to zeta(2)*delta^2, where
delta=dist_Q(1,H). For the upper limit, fix any finite legal competitor near
the limiting projection; it is admissible and periodic at every sufficiently
large stage and has a fixed finite sup bound B. For the lower limit, use
zeta(2)D_{L_M} <= min E_{L_M}. Then let the fixed competitor improve.

The rational minimizers also converge in Q to P_H1 by orthogonality:
||1-F_M||^2=delta^2+||F_M-P_H1||^2. The signed endpoint identity consequently
gives S_{L_M}->-zeta(2)delta^2. If delta>0, S_{L_M}/E_{L_M}->-1.

The attained-minimum limit and full-Q convergence of the actual rational
minimizers are now formalized in `QRationalMinimumLimit.lean` and
`QRationalMinimizerConvergence.lean`. The exact decomposition is

    min E_L = zeta(2) D_L
              + zeta(2) ||F_L-P_VL(1)||_Q^2 + Gap_L(F_L).

Both nonnegative excess terms tend to zero. No uniform coefficient bound is
assumed. The signed-tail assembly is verified in `QRationalSignedTailLimit.lean`:

    min E_L + S_L = 5 phi(L)/(3 L^2),
    S_L -> -zeta(2) delta^2,
    delta>0 implies S_L/min E_L -> -1.

Every finite rational minimum is strictly positive. The signed tail tends to
zero if and only if the constant belongs to H. The ratio theorem explicitly
assumes a positive limiting defect; it does not establish that hypothesis.
None of these limits assert that delta=0.

## 3. A conditional-expectation obstruction at modulus three

Let C_3 be actual Q-conditional expectation on residues modulo three and
u=C_3 g_2. Its input g_2 belongs to H unconditionally. Put

    A=Q(N=1 mod 3), B=Q(N=2 mod 3).

Complete progression refinement and the scaling Q(2n)=Q(n)/4 give

    A+B=8/9, 0<B<=1/4, A>B,
    u(1)=1/2-B/(8A), u(2)=1/2-A/(8B), u(3)=3/8.

Since u is 3-periodic, its four-site defect is exactly

    J=u(4)-u(3)-u(2)+u(1)
      =(A-B)(A+2B)/(8AB) >= 1/3 > 0.

Every element of H has zero such defect, by the squarefree jump witness.
Consequently u is outside H, independently of the truth of RH. The full
orthogonal decomposition retains the squared norm remainder, and gives

    ||u-F||_Q^2 >= J^2/[30 zeta(2)] >= 1/[270 zeta(2)]

for every F in H. In particular C_3 does not preserve H. This contrasts
mathematically with the already published parity preservation equivalence:
the modulus-three preservation statement is false, rather than merely an
unproved equivalent formulation of constant-target membership.

A 30-digit Wolfram evaluation of complete trigamma weights gives
A approximately .6819319002163039410, B approximately .2069569886725849478,
and J approximately .4610086331412099646. The exact witness lower bound
J^2/[30 zeta(2)] is approximately .00430673715366481778; the simpler proved
rational bound 1/[270 zeta(2)] is approximately .00225158185871861714.
These decimal evaluations are not interval certificates. The symbolic
identity and rational lower-bound inequality were checked separately.

### The actual primorial filtration: modulus-six obstruction

Modulus three is not itself a primorial stage. A separate exact rational
certificate addresses this distinction: for u=C_6 g_5, four-term fiber
prefixes and the proved midpoint tail majorant give

    u(1)<=214/1000, u(4)<=726/1000,
    u(2)>=404/1000, u(3)>=561/1000.

Hence its same four-site jump is <=-1/40, and its squared distance from H
is at least 1/[48000 zeta(2)]=1/[8000 pi^2]. The proof is now formalized in `QPrimorialSixConditionalObstruction.lean`.
The actual target is reconstructed in Q-Hilbert space from the complete
conditional fiber values. Exact finite head identities retain the infinite
mass and moment tails before bounding them; the final witness identity also
retains its entire orthogonal norm-square remainder. Thus conditioning fails
to preserve H even at the genuine primorial period six, independently of RH.

## 4. The actual optimizer and parity

Write h=P_H1 and D=||1-h||_Q^2. The actual orthogonal projection onto the
parity cylinder space C_2 is defined for every complete-Q vector, including
unbounded sequences. Since g_2 belongs to H, its residual has the exact image

    C_2(1-h)=4D 1_even,
    C_2 h=1-4D 1_even,
    ||h-C_2 h||_Q^2=D(1-4D).

The presence of g_3 makes D<1/4. Thus the limiting optimizer is physically
two-periodic if and only if 1 belongs to H. This is an established equivalence;
periodicity itself remains an unresolved hypothesis in its conditional RH
consumer. It cannot be inserted as a free property of the optimizer.

The exact legal trial g_2+g_3+g_6 has residual (0,0,0,0,-1,1) at residues
1,...,6. Its complete-Q error is w_6(5)+1/36, and w_6(5)<=1/25. Therefore

    D <= 61/900,
    (164/225)D <= ||h-C_2 h||_Q^2 <= D.

These statements are formalized in `QParityProjectionDefect.lean` and
`QSixAtomTrialBound.lean`. The trial estimate retains every infinite residue
tail. The lower comparison shows quantitatively that controlling the
optimizer's parity leakage is as strong as controlling its legal error.

## 5. Exact finite verification

Wolfram verified the finite cylinder reconstruction in exact rational
arithmetic for all 18 squarefree periods 2<=L<=30 and separately L=210.
The constraint matrix identifies cyclic jumps within gcd classes. For the
synthesis matrix B with columns 1 and every g_d for nontrivial d|L, the
checks verified C B=0, nullity(C)=rank(B)=tau(L), and explicit Mobius
reconstruction of every nullspace basis vector. There were no failures.

| L | Constraint rank | Nullity | Synthesis rank |
|---:|---:|---:|---:|
|2|0|2|2|
|6|2|4|4|
|30|22|8|8|
|210|194|16|16|

The reproducible finite scripts and their evaluation scope are retained in
`CRTExactChecks20261020.md`.

Wolfram also checked the midpoint rational identity and the elementary
5/3 comparison by exact symbolic algebra. These finite checks are separate
from general Lean proofs and establish no infinite exhaustion estimate.

## 6. Concrete prime-power sieve obstruction

The companion note `PrimePowerTargetsResearch20261020.md` studies the actual
finite synthesis with coefficients -1_{2|d} mu(d/2) over all divisors of the
primorial L_H. Its physical sequence is exactly

    A_H(n)=#{1<=m<=n:gcd(m,L_H)=2} - a_H n,
    a_H=product_{q prime, q<=H}(1-1/q).

For n<=H this is floor(log_2 n)-a_H n. Thus A_H converges at every physical
coordinate to floor(log_2 n). The complete-Q norm lower bound retains the
density correction and gives

    ||A_H||_Q^2 >= a_H^2 H/(2 zeta(2)) - floor(log_2 H)^2.

The elementary finite prime-product bounds already present in the repository
supply the growth mechanism. The newly verified `PrimeProductDyadicGrowth`
and `PrimeProductHeadGrowth` discharge the retained logarithmic error at every
cutoff. Consequently `primePowerTwoVector_norm_tendsto_atTop` proves
||A_H||_Q -> infinity, although each physical coordinate converges.
Development job `job_7_5OzFtPU28n2psmZJTofM8AE2_VyPz6` verified this result
and the pointwise limit with only ordinary foundational axioms. These approximants require a replacement with
controlled full norm; pointwise convergence alone does not give closure.
The companion note distinguishes the concrete formal declarations from its
broader ordinary arguments for other primes and averaged sieve families.

## 7. Remaining RH obligation

The decisive missing arithmetic estimate remains a uniform absorption

    S_L >= -theta E_L - epsilon_L,
    theta < 1 fixed, epsilon_L -> 0,

along exhaustive squarefree stages, or a sufficient divergent lower bound
on normalized combined prime-plus-carry gains. No such estimate is supplied
by cylinder rigidity, the weight comparison, or the finite checks.

The new rigidity theorem sharply restricts attempts using conditional
targets: a periodic target in H can acquire only the constant direction
beyond the finite divisor span. Finding a legal periodic target nonzero at
the zero residue would already settle the constant membership problem.

## Sources

* User-provided handoff, sections 6, 8 and 10, supplies the research targets
  and the midpoint-majorant argument, not a proof of arithmetic exhaustion.
* Bhaskar Bagchi, On Nyman, Beurling and Baez-Duarte's Hilbert space
  reformulation of the Riemann hypothesis, Theorem 1 and Remark 8,
  https://arxiv.org/abs/math/0607733, supplies the literature equivalence
  with squarefree closure. The existing project Mellin transfer supplies
  the formal implication from constant closure membership to RH.
* Existing project modules `SquarefreeRadicalDifference`, `QDivisorLegality`,
  `DivisorIncidence`, and `ArithmeticCumulativeBasic` supply the reused
  arithmetic and functional-analytic interfaces. No mathematical novelty
  claim is made merely because the formalization is new to this repository.

## Final development verification

Standalone-import job `job_04vz-YUURs6_1xaxISqRinrrHIJYGNqd` succeeded
with `verified=true` and exit code 0. It built the staged prime-power sieve,
full-cutoff head-growth, and primorial assembly modules independently, and
imported the staged signed-tail and quantitative parity modules. The inspected
pointwise, full-norm-divergence, parity-bound, and signed-tail-ratio declarations
depended only on `propext`, `Classical.choice`, and `Quot.sound`.
Publication is gated separately by the server source audit and incremental
aggregate/changed-module checkpoint; its terminal job and exact commit are
reported with the published result.
