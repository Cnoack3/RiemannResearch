# Squarefree closure dependencies and seventh-primorial checks

Continuation for Christian Noack, 20 October 2026 UTC (19 October locally).
Baseline: `75271daadaab4e33d7bf3c124be2713e3ac333a8` on RiemannResearch main.

The new work connects the actual rational optimizer coefficients, the exact
weighted energy of their signed-tail differences, and cofinal signed budgets
to the existing complete-Q closure criterion. It does not prove constant-target
membership or RH. The remaining arithmetic estimate is stated explicitly below.

## Verification

Targeted server job `job_YvilkfIZOAr6G2fp5uYHveRqsPeJe7sm` succeeded
with exit code 0 and `verified=true` (14.247 seconds). It imported all three
new modules, rebuilt their changed prerequisites as needed, and checked the
five principal declarations below. Every printed axiom list was exactly
`propext`, `Classical.choice`, and `Quot.sound`:

- `cofinal_absorption_iff_zero_limit`
- `cofinal_signed_absorption_iff_closure`
- `rationalMinimizer_qError_le_of_signed_budget`
- `rationalCoefficients_tendsto_moebius_iff`
- `rationalMinimum_tail_dirichlet`

The change adds 15 theorem declarations: four coefficient results, six
tail-difference/energy results, four signed-budget applications, and one
generic cofinal-limit lemma. The earlier failed development checks were
formalization and file-staging failures, resolved before this successful run.

Final publication requires the server checkpoint's source audit and validation
of the changed modules and their consumers. The final session receipt identifies
that checkpoint and its published commit. Wolfram checks are separate finite
algebraic evidence and are not Lean certificates or an infinite-limit proof.

## Setting

For n>=1, Q(n)=1/(zeta(2)n^2), and g_d(n)=(n mod d)/d.
Let H be the complete-Q closed span of all squarefree g_d, d>=2.
At squarefree L, the finite space V_L uses every nontrivial divisor of L,
including composites. Write P_L for the complete-Q projection of 1 onto V_L,
D_L=||1-P_L||_Q^2, and h=P_H1.

For 1<=a<=L set

    u_L(a)=1/a^2+2/[L(2a+L)].

Let F_L=sum_(d|L) c_(L,d)g_d be the actual selected rational-weight minimizer,
r_L=1-F_L, E_L=sum_a u_L(a)r_L(a)^2, and

    T_L(k)=sum_(a=k)^L u_L(a)r_L(a),
    S_L=sum_(2<=k<=L, gcd(k,L)=1) T_L(k),
    c_L=5/(3L^2), B_L=5phi(L)/(3L^2).

The conductor-one atom is zero. Its chosen coefficient and coefficients outside
the finite dictionary have no invariant meaning and are excluded from the
coefficient claims. The repository's `primorialPeriod n` is an exhaustive
prime-cutoff sequence, which can repeat a period; the finite Wolfram ledger
instead lists the first seven distinct primorials explicitly.

## 1. Actual rational coefficient stabilization

`RH/QRationalCoefficientLimit.lean` establishes four declarations:

- `qCoefficientCLM_qDivisorFit`: the existing continuous coefficient map
  extracts c_(L,m) from the full divisor synthesis when m|L and m>=2,
  and is zero when m is not in that dictionary.
- `rationalCoefficients_eventually_eq_coordinate`: each fixed squarefree
  m>=2 eventually belongs to every stage, so its selected coefficient is
  the intrinsic continuous coordinate of F_L.
- `rationalCoefficients_tendsto`: c_(L,m) tends unconditionally to
  lambda_m, the coefficient of h=P_H1, for each fixed legal conductor.
- `rationalCoefficients_tendsto_moebius_iff`: simultaneous convergence
  c_(L,m)->-mu(m), for every squarefree m>=2, is equivalent to 1 in H.

The proof uses the previously established norm convergence F_L->h and continuity
of coefficient extraction. It assumes neither a uniform coefficient bound nor
the identity lambda_m=-mu(m). Identifying these limits remains open.

## 2. Exact signed-tail difference energy

`RH/QRationalTailDirichlet.lean` proves the actual first-difference identity

    Delta_k=T_L(k)-T_L(k+1)=u_L(k)r_L(k).

The endpoint is retained: F_L(L)=0, r_L(L)=1, and u_L(L)=c_L. Consequently

    sum_(k=1)^(L-1) Delta_k^2/u_L(k)=E_L-c_L.

The finite normal equations also imply T_L(1)=E_L, so the complete equality is

    T_L(1)-c_L=sum_(k=1)^(L-1) Delta_k^2/u_L(k)=E_L-c_L.

Subtracting the common gcd-class mean c_L from every tail leaves all Delta_k
unchanged. Each individual increment has the unconditional bound

    Delta_k^2 <= u_L(k)(E_L-c_L),     1<=k<L.

This is an exact dependency for a possible within-class estimate. It does not
bound the full sum by a quantity tending to zero. The six declarations include
the positive-weight helper and a specialization to the chosen actual minimizer.

## 3. Complete-Q bounds and the exact cofinal obligation

`RH/QRationalSignedTailClosure.lean` first retains every term in the finite
identity, with Gap_L the existing nonnegative rational-weight comparison gap:

    zeta(2)D_L + zeta(2)||F_L-P_L||_Q^2 + Gap_L(F_L) + S_L = B_L.

If theta<1 and a particular finite stage satisfies

    S_L >= -theta E_L-epsilon,

then the full infinite-tail norm of the actual rational minimizer satisfies

    ||1-F_L||_Q^2 <= (B_L+epsilon)/[(1-theta)zeta(2)].

This controls the actual complete-Q error, not a truncated norm.
The module proves, for each fixed theta<1, the exact equivalence

    1 in H
      iff
    for every epsilon>0 and N, there exists n>=N with
      S_(L_n) >= -theta E_(L_n)-epsilon.

The generic cofinal-limit argument is added to
`Analysis/FiniteWeightedTailCharge.lean` as
`cofinal_absorption_iff_zero_limit`. It uses the actual existing limits
E_(L_n)->zeta(2)||1-h||_Q^2 and B_(L_n)->0 in the application.

The final consumer `closure_of_cofinal_signed_budget` accepts an explicit
error sequence epsilon_n->0 and cofinally valid absorption inequalities.
Those hypotheses would discharge the closure obligation. The new proof does
not provide that arithmetic sequence or those inequalities. In particular,
checking a fixed finite collection of stages cannot supply the cofinal input.

## 4. Wolfram checks: exactly seven distinct primorials

The requested cap was respected:

| Prime factors | Period | Legal atoms |
|---:|---:|---:|
| 1 | 2 | 1 |
| 2 | 6 | 3 |
| 3 | 30 | 7 |
| 4 | 210 | 15 |
| 5 | 2310 | 31 |
| 6 | 30030 | 63 |
| 7 | 510510 | 127 |

At every listed period, exact symbolic arithmetic checks both divisor-incidence
inverse identities, every gcd-class charge and divisibility moment, the class
cardinality total, and the centered quadratic identity. The rational midpoint
telescoping defect is also checked symbolically, including its sign.

The additional complete-period integer checks cover every residue 0,...,L:
543105 Mobius-synthesis cases and 543102 canonical CRT-carry cases, with no
failures. One canonical split is used per composite primorial; no claim is made
about exhaustive checks of every split or representative. These are not new
optimizer solves. No eighth or later primorial was evaluated.

Self-contained Wolfram source and the returned results are recorded in
`WolframSeventhPrimorialChecks20261020.md` beside this memorandum.

## 5. Remaining research obligation

Open: prove a cofinal signed lower bound with a fixed factor theta<1 and a
vanishing additive error for the actual rational minimizers. Equivalent
coefficient target: identify every lambda_m as -mu(m). The new exact
Dirichlet identity offers another expression for the energy that needs control;
it does not itself supply decay.

The previously proved gcd-class averages determine the class means. New
arithmetic control must address the fluctuations within those classes.

For the external criterion, Bagchi, *On Nyman, Beurling and Baez-Duarte's
Hilbert space reformulation of the Riemann hypothesis* (2006), Remark 8 and
the weight-comparison discussion, gives the squarefree closure equivalence
and its transfer between comparable inverse-square weights:
https://arxiv.org/pdf/math/0607733 . This source supplies no unconditional
exhaustion estimate. The new formal assembly reuses existing project providers;
it makes no mathematical novelty claim for coefficient continuity, finite
tail differencing, or the cofinal-limit argument.
