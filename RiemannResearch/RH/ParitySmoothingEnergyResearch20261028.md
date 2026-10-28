# Exact parity smoothing energy and initial response budgets

28 October 2026. Source: the user's requested continuation of
`InfiniteSquarefreeResponseResearch20261027.md` and its proposed odd-series
calculation. This note preserves complete infinite Q sums and distinguishes
Lean declarations from additional ordinary mathematical calculations.

## Exact odd series and parity energy

Put Z = zeta(2). For every M the complete finite partial-fraction identity is

    sum_(k<M) 1/[(2k+1)^2(2k+2)^2]
      = sum_(n=1)^(2M) 1/n^2 - 2(H_(2M)-H_M).

The paired difference H_(2M)-H_M tends to log 2. The Lean proof uses the
existing limit H_n-log n -> Euler's constant. Each paired summand
1/(2k+1)-1/(2k+2) is nonnegative. Consequently its ordered limit gives a
genuine unconditional HasSum; an unordered sum of the alternating harmonic
series is never asserted, and two divergent series are never subtracted.

The resulting complete infinite identity is

    sum_(k>=0) 1/[(2k+1)^2(2k+2)^2] = Z - 2 log 2.

In the actual QHilbert space, qOdd has physical values 1 on odd positive
integers and 0 elsewhere, including the zero anchor. The full weighted norm
identity, together with Bf(n)=f(n)/(n+1), gives

    ||B qOdd||_Q^2 = (Z - 2 log 2)/Z.

The canonical first projection identity gives qOdd=a_0 u_0 and a_0^2=3/4.
Thus the exact canonical innovation, with the repository's unchanged
normalization and natural indexing, satisfies

    h_0 := ||B u_0||_Q^2 = 4(Z - 2 log 2)/(3Z) > 0.

Applying the existing parity-exclusion theorem yields

    sum_N ||b_(N+1)-b_N||_Q^2
      <= C_1 := (Z-1)/4 - (Z-2 log 2)/(3Z).

The decimal C_1 = 0.108822154469455... is an illustrative numerical
evaluation; the Lean result is the exact expression, not a decimal interval.
The previous bound (Z-1)/4 is approximately 0.161233516712057.

Declarations:

- `Analysis/OddReciprocalSquare.lean`:
  `paired_reciprocal_sum`, `hasSum_paired_reciprocal`,
  `reciprocal_square_partial_fraction`,
  `hasSum_odd_reciprocal_square_of_hasSum`, `odd_reciprocal_square_tsum`.
- `RH/QParitySmoothingEnergy.lean`, namespace `QCanonicalInnovation`:
  `B_qOdd_norm_sq`, `targetCoefficient_zero_smul`,
  `targetCoefficient_zero_sq`, `B_direction_zero_norm_sq`,
  `B_direction_zero_norm_sq_pos`, `movingCorrection_variation_explicit_parity`,
  `explicit_parity_bound_lt_basic`.

## Exact accounting for further initial innovations

Set C=Z-1, e_j=||b_(j+1)-b_j||^2, h_j=||Bu_j||^2, E_K=||r_K||^2.
For every natural K define

    F_K = sum_(j<K) e_j + E_K (C-sum_(j<K) h_j).

The prefix is a finite set of canonical stage indices. Every Hilbert norm
and every remaining tail still includes all physical coordinates.
The exact prefix-tail identity is retained before the estimate:

    sum_j e_j = sum_(j<K) e_j + sum_(j>=K) e_j <= F_K.

There is an exact decrement identity

    F_K-F_(K+1)
      = (E_K h_K-e_K)
        + (E_K-E_(K+1)) (C-sum_(j<=K) h_j).

Both terms are nonnegative. Hence the computable-prefix bounds are
nonincreasing, with all earlier response costs retained. The energy split
also identifies E_K-E_(K+1)=a_K^2, but the new general decrement declaration
uses the residual-energy difference directly.

`RH/QSquarefreeResponsePrefixBudget.lean` supplies
`movingCorrection_variation_prefix_exact`,
`smoothing_prefix_complement_exact`, `movingCorrection_variation_prefix_le`,
`responsePrefixBudget_decrement_exact`, `responsePrefixBudget_succ_le`,
`responsePrefixBudget_succ_lt_of_error_lt`, and `responsePrefixBudget_one`.
The strict general theorem displays its two additional hypotheses explicitly.

For the actual conductor-three stage these hypotheses can be discharged:
the positive pairing of qEven with g_3 gives E_2<E_1=1/4. Both initial
directions vanish at physical site 6. Summing the nonnegative coordinate
Bessel deficits over every coordinate retains at least the site's diagonal
mass 1/(6+1)^2. Thus

    C-h_0-h_1 >= 1/49,
    F_1-F_2 >= (E_1-E_2)/49 > 0,
    sum_j e_j <= F_2 < F_1 = C_1.

The exact second cap is

    F_2 = ||b_2||^2 + E_2(C-h_0-h_1).

`RH/QInitialResponseImprovement.lean` contains
`error_two_lt_one`, `smoothing_prefix_two_complement_ge`,
`responsePrefixBudget_two_eq`, `responsePrefixBudget_one_sub_two_ge`,
`responsePrefixBudget_two_lt_one`, and
`movingCorrection_variation_lt_parity_budget`, and
`movingCorrection_variation_lt_explicit_parity`.

## Ordinary exact evaluation at conductor three

The formulas in this section are ordinary mathematical deductions. Their
special-function evaluations and numerical values have not been formalized
in Lean in this change. The strict improvement above has a separate proof
which does not use these evaluations.

Let L=L(2,chi_3)=sum_(k>=0)[1/(3k+1)^2-1/(3k+2)^2]. Put

    m=<1,g_3>=4/9-L/(6Z),
    G=||g_3||^2=20/81-L/(6Z),
    K=<qOdd,g_3>=1/3-5L/(24Z),
    t=4K/3,
    w=g_3-t qOdd,
    A=<1,w>=m-K=1/9+L/(24Z),
    H=||w||^2=G-4K^2/3 > 0.

Since w(2)=2/3, H is strictly positive. The canonical second direction is
u_1=w/sqrt(H), and E_2=1/4-A^2/H. Let p=pi/sqrt(3), l2=log 2, l3=log 3.
For r=1,...,6 the complete progression sums are

    S_r=sum_(k>=0) 1/(6k+r)^2,
    R_r=sum_(k>=0) [1/(6k+r)-1/(6k+r+1)].

| r | S_r | R_r |
|---|---|---|
| 1 | Z/3+5L/8 | p/6+l2/3 |
| 2 | Z/9+L/8 | p/12+l3/4-l2/3 |
| 3 | Z/12 | p/12-l3/4+l2/3 |
| 4 | Z/9-L/8 | p/6-l2/3 |
| 5 | Z/3-5L/8 | -p/4+l2/3+l3/4 |
| 6 | Z/36 | 1-p/4-l2/3-l3/4 |

The S values follow from splitting the mod-3 and parity square series.
The R values follow by integrating x^(r-1)/(1+x+...+x^5) on [0,1],
or equivalently evaluating rational digamma differences. These are paired
convergent series throughout.

Set T_r=S_r-R_r and U_r=S_r+S_(r+1)-2R_r, with S_7=S_1-1.
This boundary term is retained. The T and U sums are respectively
1/[n^2(n+1)] and 1/[n^2(n+1)^2] in progression r.
The physical residue vector of w is

    v=(1/3-t, 2/3, -t, 1/3, 2/3-t, 0).

All remaining quantities are explicit finite expressions in these complete
progression sums:

    D=(v_1 T_1+v_3 T_3+v_5 T_5)/Z = <Bw,qOdd>,
    J=(v_2 T_2+v_4 T_4+v_6 T_6)/Z = <B qEven,w>,
    K_B=sum_(r=1)^6 v_r^2 T_r/Z = <Bw,w>,
    h_1=sum_(r=1)^6 v_r^2 U_r/(ZH),
    e_1=(J-A K_B/H)^2/H + 4A^2 D^2/(3H^2).

In particular the non-parity response cost e_1 is retained. Illustratively,

    E_2 = 0.06868528248535...,
    h_1 = 0.08803258034406...,
    e_1 = 0.0000208950298603...,
    F_2 = 0.02387227406261....

These decimals are not Lean-certified intervals. Exact rational inequalities
also show e_1>0 without decimal evaluation. Indeed
L>=7390083/9486400 (four positive terms), Z<329/200 (the first 100 square
terms plus the integral tail), and hence 0<t<313/1000. The n=1 contribution
to ZD exceeds 61/6000. The only negative progression is n=6k+3, whose
absolute contribution is less than

    (313/1000)(1/36+1/729+1/972).

Their difference is 1051/1458000>0. Therefore D>0, A>0, and e_1>0.
Deleting all h_1 without paying e_1 would not be justified by parity's argument.
Conductor 4 is nonsquarefree, so its canonical innovation is zero and gives
no additional change (this observation is ordinary mathematics here).

Every fixed later prefix similarly reduces to finite periodic Gram data and
complete progression sums. Periodic linear dependence is decidable on one
period, and zero innovations remain at their original indices. Constants
need not reduce to Z and elementary logarithms alone.

## What this contributes toward RH

This is a quantitative sharpening and a reusable monotone hierarchy of
rigorous bounds. It supplies no new physical exponential-moment estimate.
Writing H_inf=sum_j h_j and E_inf=||limitingResidual||^2, the exact cap limit is

    lim_K F_K = sum_j e_j + E_inf(C-H_inf).

This is the declaration `responsePrefixBudget_tendsto`. It retains the
possibly positive limiting residual term; it does not force it to vanish.

The domain-specific obligation remains Open: some kappa>0 and a common finite
M such that for every finite physical set S there are arbitrarily late N with

    sum_(n in S) Q(n) exp(kappa*|b_N(n)|) <= M.

The existing `riemannHypothesis_of_frequently_exponential_finiteSum_bound`
consumes this additional hypothesis. Neither a smaller temporal square-
variation constant nor finitely many exact initial innovations provides it.
No residual vanishing or RH result is claimed.

## Verification record

The scalar identity passed isolated verification in
`job_VHDGI82qRfZIk0ovYvTeGjsXzO9j5Fo2` (verified=true, exit code 0;
server-reported duration 5.766 seconds).
Saved modules and five principal axiom checks passed in
`job_UDEd15jKaU7LNvWyZ4Fcmh1vVo8T1I4M` (verified=true, exit code 0;
server-reported duration 14.219 seconds, queue delay approximately 0.002 seconds).
Each audited declaration used only propext, Classical.choice, and Quot.sound.
No domain-specific premise occurs in the odd-series, parity-energy, explicit
variation, or unconditional prefix declarations.

The saved conductor-three module and three principal axiom checks passed in
`job_f4BpN4ybfHfvIENFrc4z34N_5VF7ssxn` (verified=true, exit code 0;
server-reported duration 14.096 seconds, queue delay approximately 0.001 seconds).
Its audited declarations likewise used only the three standard foundations.
In particular the strict improvement for the actual second stage has no
unresolved arithmetic hypothesis. The extra closed-form evaluations of its
mod-6 sums remain ordinary mathematics, as labeled above.

The successful workspace-opening request took 100.060 seconds round trip,
after two earlier connection timeouts. This is not kernel-checking time.
All verification submissions were serialized. Final publication remains
subject to the terminal server checkpoint; its result is reported separately.
