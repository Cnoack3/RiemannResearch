# Period/head balance and a charge-changing prime repair

Research continuation dated 28 October 2026 (America/New_York).

**Status: RH is not proved.** The signed period/head identity, a restricted
dilation obstruction, and an explicit legal prime repair are Lean verified.
The uniform complete-Q energy estimate remains open. The conditional RH
declaration below retains that estimate as an explicit hypothesis.

## Source and setting

This continues the user-provided
[RH exact-head energy handoff](https://chatgpt.com/library?file_id=libfile_2c258d413d588191b526f2258f1d7514&account_id=personal),
especially Sections 9.A and 9.B, from repository baseline
`533ce3280ae4bdc9ab2de0bddf756e7b8efe3dba`.

Use the complete probability weight Q(n)=1/(zeta(2)n^2) for n>=1, with the
sequence anchored to zero at n=0. Write g_d(n)=(n mod d)/d and V_L for the
span of the g_d with d dividing L. The legal family is the real span of
squarefree residue atoms. All norms and inner products below use the
complete infinite Q sum.

The three new modules are exported by the root import. Existing finite-charge,
head-space projection, dilation, and exact-head RH criteria are reused.
The obstruction and repair are developments in this continuation; no claim
of priority over the mathematical literature is made.

## 1. Exact signed balance for actual primorial schedules

Module: [QCRTPeriodHeadBalance.lean](QCRTPeriodHeadBalance.lean).

Let M(j,H) be the minimum-norm vector in V_(primorial(j+2)) with head H,
as implemented by `minimumAt`. The stated exact-head interpretation
uses H<=j+1. Fix a monotone schedule sigma with n<=sigma(n), and put

- E_n = ||M(sigma(n),n+1)||^2;
- A_n = ||M(sigma(n),n+1)-M(sigma(n+1),n+1)||^2;
- B_n = ||M(sigma(n+1),n+2)-M(sigma(n+1),n+1)||^2.

Lean proves the full Pythagorean identities and hence

    E_(n+1) = E_n - A_n + B_n,
    E_N = E_0 + sum_(n<N) (B_n-A_n).

The bridge first enlarges the period while fixing the old head, then increases
the head at the new period. Both squared-distance terms are retained.

Main declarations:

- `minimumAt_completion`, `minimumAt_period_gain`, `minimumAt_head_cost`;
- `stageEnergy_step`, `stageEnergy_telescope`, `minimumAt_legal`;
- `budget_bound_iff`: a uniform signed cumulative budget is exactly
  equivalent to a uniform bound on this family's complete squared norms;
- `riemannHypothesis_of_balance_bound`: the conditional RH consumer.

The unresolved arithmetic input is to exhibit such a schedule and a finite C
satisfying, for every N,

    sum_(n<N) (B_n-A_n) <= C-E_0.

The last theorem discharges legality, exact heads, and the conversion from a
norm bound C to an error bound 2+2C. It does not discharge the displayed budget.
The budget identity alone does not make the RH-equivalent energy requirement
easier; useful progress must estimate the actual signed gains and costs.

## 2. New dilation factors conserve a finite obstruction

Module: [QFreshDilationObstruction.lean](QFreshDilationObstruction.lean).

For L>0, reuse the finite divisor charge

    C_L(f) = (1/L) sum_(e divides L) phi(L/e) (f(e)-f(e-1)).

The existing component-charge machinery supplies this formula. The new module
represents it by a finite Q Riesz vector R_L and thus a continuous linear
functional `cutFunctional L`.

The following are proved in Lean:

1. C_L vanishes on V_L.
2. If m>0 and m does not divide L, then C_L(D_m f)=0 for every f in QHilbert,
   where D_m f(n)=f(floor(n/m)).
3. C_L(1)=phi(L)/L>0.

For item 2, no e dividing L is a multiple of m. Thus floor(e/m) and
floor((e-1)/m) coincide in every term of the jump sum. This works for arbitrary
dilated Q vectors, rather than only old residue combinations.

Consequently, define

    S_L = closure(V_L + span {D_m f : m>0, m does not divide L, f in QHilbert}).

Every member of S_L has zero charge, so no member has exact head through L.
This includes arbitrary signed finite combinations and their norm limits.
For f in S_L the exact full-norm decomposition is

    ||1-f||^2 = (phi(L)/L)^2 / ||R_L||^2
      + ||1-f - ((phi(L)/L)/||R_L||^2) R_L||^2.

At L=6, let r_n be the coordinate Riesz vector and let
W=r_2+r_3-r_5+r_6. Then

    C_6(f) = (f(2)+f(3)-f(5)+f(6))/6,
    ||W||^2 = 74 zeta(2),
    ||1-f||^2 = 2/(37 zeta(2))
      + ||1-f - W/(37 zeta(2))||^2  for f in S_6.

The entire squared-norm remainder is present; the lower bound is not being
used as a substitute for the energy identity.

**Scope:** this obstructs correction schemes restricted to a fixed old
divisor space and dilations by factors not dividing its period. It does not
obstruct the full enlarged squarefree dictionary, prove the canonical
energies unbounded, or contradict RH.

The escape is also exact:

    C_L(g_d) = (1/d)(1 - indicator(d divides L)),
    C_L(g_d-(L/d)g_L) = 1/d  if d does not divide L.

Thus adding a compensated residue outside the old period changes the charge.
Any successful construction must permit directions of this kind or some
other means of escaping the restricted space.

## 3. Explicit prime repair with its signed energy

Module: [QCRTPrimeRepair.lean](QCRTPrimeRepair.lean).

Assume L>0, p is prime, p<L, p does not divide L, and f belongs to V_L with
f(n)=1 for 1<=n<p. The existing missing-prime theorem forces f(p)=2. Set

    u = D_p f,
    G = f-u,
    h = g_p-(L/p)g_L,
    w = u+h,
    t = <G,w>/||w||^2,
    F = G-tw.

Then G is exactly one through p, w is zero through p, and C_L(w)=1/p.
In particular w is nonzero, so the denominator in t is justified. Lean proves

    F(n)=1 for 1<=n<=p,
    F belongs to V_(pL).

If L is squarefree, pL is squarefree and F is a legal squarefree combination.
The optimized complete energy is exactly

    ||F||^2 = ||f||^2 - 2<f,u> + ||u||^2
      - <G,w>^2/||w||^2.

This is `primeRepair_energy`. The legality and exact-head results are
`primeRepair_legal` and `primeRepair_head`.
The energy identity needs only L,p>0 and p not dividing L; the head and
legality conclusions use the stronger hypotheses above.

A sufficient bound for one prime step is

    2<f,u> + <G,w>^2/||w||^2 >= ||u||^2-epsilon.

A summable total error would control a sequence of such prime steps. This is
not yet an all-head construction: intervening composite coordinates must also
be repaired, their costs must be charged, and the conditions p<L and
p not dividing L must be maintained wherever this particular repair is used.
No estimate controlling that complete iteration has been proved.

## 4. Concrete finite evidence, with verification levels separated

Take L=6, p=5, and f=g_2+g_3+g_6. This f has exact head 4. Wolfram evaluated
the complete periodic weights using their exact progression-sum expressions.
Approximate values were

    ||f||^2 = 1.08164426307774911,
    ||G||^2 = 0.93675401771336147,
    t = -0.29616298927493186,
    ||F||^2 = 0.92451481535311649.

These decimal values are exploratory numerical evidence, not Lean-certified
numerical bounds or a convergence argument.

The nearby rational choice t=-3/10 gives

    F_rat = g_2+g_3+g_5+(16/25)g_6
      -(7/10)(g_10+g_15+g_30).

Independent exact Python Fraction arithmetic verified its exact head 5 and
the complete-energy bound ||F_rat||^2 < 37/40. Both the weight normalization
and all progression tails were enclosed rationally. Its sixth coordinate is
-16/25, making the composite-head issue concrete.

Here is the reproduction code. The printed endpoints are floating displays
of exact rational enclosures; the strict 37/40 assertion uses exact rationals.

```python
from fractions import Fraction as F

L, K, M = 30, 64, 2048
c = {2: F(1), 3: F(1), 5: F(1), 6: F(16, 25),
     10: F(-7, 10), 15: F(-7, 10), 30: F(-7, 10)}
vals = [sum(a * F(n % d, d) for d, a in c.items())
        for n in range(1, L + 1)]
zlo = sum((F(1, n*n) for n in range(1, M + 1)), F(0))
zhi = zlo + F(1, M)
lo = hi = F(0)
for r, f in enumerate(vals, 1):
    w = sum((F(1, (r + k*L)**2) for k in range(K + 1)), F(0))
    lo += f*f * (w + F(1, L * (r + (K + 1)*L)))
    hi += f*f * (w + F(1, L * (r + K*L)))
lo /= zhi
hi /= zlo
assert vals[:5] == [1]*5
assert hi < F(37, 40)
print(float(lo), float(hi), vals[5])
# 0.9245158310668837 0.9247923093428888 -16/25
```

For each residue class r, the omitted positive progression tail lies between
1/[L(r+(K+1)L)] and 1/[L(r+KL)] by monotone integral comparison.
The zeta(2) tail after M is at most 1/M. This is a finite external arithmetic
certificate; no new Lean theorem asserting this particular numeric bound
was added.

## 5. Verification and continuation

The saved three modules were imported and built successfully by the Lean
server in job `job_5IxsZmEs9Sb-pfXiNruk21zF9ME0iMjH`.
The result was verified=true, exit_code=0. Reported server elapsed time was
17.113 seconds, including dependency/build work and source checking; this is
not a measurement of kernel time alone. Workspace-open time was not separately
instrumented. The queue polling guidance was 30 seconds, which must not be
confused with Lean execution time.

Ten main declarations were inspected with `#print axioms`:

- balance: `stageEnergy_telescope`, `riemannHypothesis_of_balance_bound`;
- obstruction: `cutFunctional_floorDilation`, `freshSpan_no_exact_head`,
  `freshSpan_error_exact`, `freshSpan_six_error_exact`,
  `cutFunctional_compensatedResidue`;
- repair: `primeRepair_head`, `primeRepair_legal`, `primeRepair_energy`.

Every audited declaration used only propext, Classical.choice, and Quot.sound.
No sorry, admit, or new axiom was introduced. Printed theorem types confirmed
that the RH consumer still takes hbudget as an explicit argument.

The final publication checkpoint is separate from this successful module and
axiom audit. Its terminal report supplies the repository-wide validation scope
and published commit; the commit containing this memo is the versioned record.

Retained continuation workspace:

- token: `ws_-jFTFCUGoGgI17Wb5IpdJKIum8SqVTio`;
- project root:
  `/home/cri_2025/lean-agent-workspaces/ws_-jFTFCUGoGgI17Wb5IpdJKIum8SqVTio/RiemannResearch`.

Follow any continuation workspace returned by the final checkpoint. Reuse the
retained token rather than creating an unrelated clone. Verification jobs must
remain serialized.

The next substantive objective is an arithmetic bound for the actual complete
signed cumulative budget, or a different explicit legal all-head family with
uniform complete energy. Further conditional wrappers and isolated finite
energy decreases will not close this obligation.
