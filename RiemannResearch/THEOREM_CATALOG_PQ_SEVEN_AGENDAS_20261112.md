# Seven P/Q density agendas: results and remaining providers

Date: 2026-11-12 (user-facing date).
Source document: PQ_Density_Operators_and_RH_Agenda.pdf, all eight pages.
Repository base: 74442839223e0300ea19e304b199fa4f144e7a42.

No unconditional proof of the Riemann Hypothesis is claimed.
All norms and Gram entries below use the complete atomic measure, not a truncated sum.
Every conductor k >= 2 is included in V; prime-only and squarefree-only spaces must
not be substituted for V.

## Main advance and correction to the document

For H=L2(Q) and V=cl span{g_k:k>=2}, the new Lean theorem is

    1 in V  iff  V=H  iff  B(V) is contained in V
            iff  B g_k in V for every k>=2.

Consequently the distinction left unresolved on PDF pages 4 and 7 is now closed:
in this particular arithmetic space, density invariance is not stronger than
the constant target. This does not establish any one of these equivalent premises.

The proof uses the bounded floor dilation T_m f(n)=f(floor(n/m)), with f(0)=0.
The existing exact identity T_m g_k=g_(mk)-g_m/k preserves V.
If 1 is in V then T_m 1=1_{n>=m} is in V for every positive m.
Adjacent differences give every point vector. Their totality gives V=H.
The Lean implementation uses the equivalent annihilator-separation argument.

This is a formalization and strengthening of the supplied document, not a claim
of mathematical novelty. Bagchi's Theorems 1 and 7 establish the relevant
weighted-sequence criterion and dilation argument:
https://arxiv.org/abs/math/0607733

## Reverse inner products and the meaning of V

P_n=1/[n(n+1)], Q_n=1/[zeta(2)n^2].
B=dQ/dP=(I+D)/zeta(2), Df(n)=f(n)/n, Rf(n)=f(n)/(n+1).

For the same physical sequences,

    <f,g>_Q = (<f,g>_P + <f,Dg>_P)/zeta(2).

The PDF uses V for a closed subspace, not a third probability measure.
To express the formula entirely with arguments in V, equip V with the inherited
P inner product and let C_V=Pi_V^P D|V. Then for f,g in V,

    <f,g>_Q = (<f,g>_(V,P) + <f,C_V g>_(V,P))/zeta(2).

The second formula does not require D(V) to be contained in V.
Its Lean statement is more general: any P submodule with orthogonal projection
and a first argument in that submodule satisfies the compression identity.
Both identities are in RH/QDensityMetricInverse.lean:

- q_inner_pareto_add_D
- q_inner_pareto_compressed

The inverse relation remains <f,g>_P=zeta(2)(<f,g>_Q-<f,Rg>_Q).
Wolfram simplified both pointwise weight identities to zero.

## Agenda ledger

| Agenda | Added result | Arithmetic provider status |
|---|---|---|
| 1. Bounded legal lift | Full totality iff bounded lift of D1; full totality iff complete O(alpha) cost for any prescribed positive schedule alpha -> 0 | Open: a concrete bounded family |
| 2. Moving minimizers | Exact normalized signed balance, finite telescoping, RH from bounded signed partial sums | Open: bound the actual partial sums |
| 3. Actual residual | Dilation self-correlation, complete norm bound, adjacent coordinate identity, residual zero iff totality | Open: force the residual to vanish |
| 4. Leakage | Reciprocal leakage=zeta(2) density leakage; vanishing on V iff 1 in V | Open: arithmetic vanishing |
| 5. Parity image | Saturation at pi^2/64 iff the one vector E g_2 vanishes | Open: saturation and a propagation/direct-target argument |
| 6. CRT energy | Non-totality forces canonical norms to infinity on every cofinal divisor-exhausting tower | Open: a uniform bound for an explicit tower |
| 7. Converse audit | Unconditional target-totality equivalence; RH iff totality conditional on the explicit published Baez-Duarte approximation provider | Open in Lean: prove the analytic provider |

## 1. Bounded lift and complete regularization

QFullTargetTotality.closure_eq_top_iff_bounded_lift states

    V=H iff exists C and v_j in V,
      ||v_j||_Q <= C for all j and Dv_j -> D1.

QFullTargetTotality.closure_eq_top_iff_regularized_cost strengthens the conclusion
of the existing exact cost equivalence. For every fixed positive sequence
alpha_j -> 0,

    V=H iff exists C>=0 and finite legal v_j,
      ||D(v_j-1)||_Q^2 + alpha_j ||v_j||_Q^2 <= C alpha_j.

The source bound and the complete smoothed error must concern the same family.
No inversion of the compact operator D on an uncontrolled limit occurs.

## 2. Exact normalized signed budget

Let u=u_(H,alpha), v=u_(K,beta) be the existing complete inverse-Gram minimizers,
H<=K and alpha,beta>0. Put eta_(H,alpha)=J_alpha(u)/alpha. Then

    eta_(K,beta)-eta_(H,alpha)
      = (alpha-beta)/(alpha beta) ||D(u-1)||_Q^2
        - [||D(u-v)||_Q^2 + beta ||u-v||_Q^2]/beta.

The first term is the normalized parameter penalty, the second the full
enlargement gain. This uses the old minimizer u in the smoothed residual.
It is an equality even if beta>alpha; no monotonicity of regularization is assumed.

For a monotone cutoff sequence H_j and positive alpha_j, the partial sum of
these signed steps is exactly eta_n-eta_0. If alpha_j->0 and these signed partial
sums have a uniform upper bound, the actual minimizers have complete
O(alpha_j) cost, and the existing bounded-lift theorem gives RH.

Declarations in QReciprocalNormalizedBalance:

- signedStep
- normalized_balance
- normalized_telescoping
- riemannHypothesis_of_signed_budget

The last result is a conditional research reduction. Its hypothesis hbudget
is the unresolved arithmetic estimate. The theorem does not assume RH, and
does not prove hbudget. Cofinality of H_j is not required in its logical statement;
the asserted uniform cost itself is strong enough. Explicit cofinal schedules
remain the intended research application.

## 3. Residual correlations

Let r=1-Pi_V^Q 1. Then r is orthogonal to V and

    <T_m 1,r>_Q = <T_m r,r>_Q,
    |<T_m 1,r>_Q| <= ||r||_Q^2 / sqrt(m).

The second statement uses the existing sharp operator-energy estimate
||T_m f||_Q^2 <= ||f||_Q^2/m. No residual self-correlation is discarded.
For every positive physical index m,

    <(T_m-T_(m+1))r,r>_Q = Q_m r(m).

Lean writes the right side as the inner product with the normalized l2 point
vector lp.single 2 (m-1) (sqrt(qWeight (m-1))). This preserves the physical
index shift instead of identifying normalized and physical coordinates.

Declarations in QResidualDilationCorrelation:

- residual_dilation_identity
- residual_dilation_bound
- residual_coordinate_identity
- residual_zero_iff_totality

At m=1 the identity simply gives <1,r>=||r||^2. Decay with m does not force
this initial value to vanish. Cancellation or a genuinely stronger tail
estimate is still required.

## 4. Leakage and 5. parity

Define E f=Bf-Pi_V^Q Bf. For f in V,

    Df-Pi_V^Q Df=zeta(2) E f.

Thus E vanishes on V iff 1 is in V iff V=H. For u perpendicular to V,

    <u,Df>_Q=zeta(2)<u,E f>_Q.

For t=Dg_2=1_{n odd}/(2n), ||t||_Q^2=pi^2/64, and the existing complete
projection limit is

    beta_N^T G_N^(-1) beta_N -> pi^2/64 - ||t-Pi_V^Q t||_Q^2.

The new theorem identifies saturation with E g_2=0. This is a diagnostic,
not a proof of saturation or of propagation to all conductors.

Declarations in QDensityLeakage:

- leakage
- reciprocal_leakage
- leakage_eq_zero_iff
- leakage_vanishes_iff_one_mem
- orthogonal_pairing
- parity_leakage_eq_zero_iff
- parity_saturation_iff

Wolfram independently evaluated the odd reciprocal series as pi^2/64.
The Lean parity norm and remainder were already present and are reused.

## 6. CRT with complete Q energy

QCRTCanonicalEscape.canonical_norm_tendsto_atTop proves the following precise
escape alternative for the existing exact canonical CRT collocation sources.

Assume L_j>=2, L_j->infinity, and each positive integer d divides L_j eventually.
If V is proper, then

    ||canonical(L_j)||_Q -> infinity.

Proof: failure of escape yields a bounded cofinal subsequence. It still exhausts
all divisors. The existing QCRTBoundedCriterion.qOne_mem_of_bounded_canonical
then gives 1 in V, contradicting the new target-totality equivalence.

An LCM tower includes all prime powers and meets the exhaustion condition.
A primorial-only tower does not meet it. A positive bounded result has not
been supplied. Q is the original atomic measure, never Haar measure on a
profinite product, and no continuity of an arbitrary L2 representative is inferred.

## 7. Analytic converse: all assumptions visible

Bagchi's Theorem 1 gives the published equivalence RH iff 1 in V iff V=H in
the P-weighted sequence space. The P/Q weights are boundedly comparable.
This is exact published support for the intended converse, beyond an analogy
with a classical function space.

The repository already has Pareto.BaezDuarte.BaezDuarteMobiusApproximation:
an explicit proposition saying RH implies convergence of the complete global
L2 error for the prescribed finite Mobius approximants. It is a hypothesis,
not a proved analytic input.

QFullDensityConditionalConverse proves:

- squarefreeClosure_le_full, without any analytic hypothesis;
- riemannHypothesis_iff_one_mem hBD;
- riemannHypothesis_iff_totality hBD;
- riemannHypothesis_iff_density_invariant hBD.

Here hBD : Pareto.BaezDuarte.BaezDuarteMobiusApproximation is required in the
last three declarations. The chain passes through the existing centered
squarefree Pareto approximation, exact P/Q closure transfer, and inclusion
in the full-conductor closure. All translation steps are formal.
The analytic provider itself remains Open in Lean.

The published inputs are:
- Bagchi, On Nyman, Beurling and Baez-Duarte's Hilbert space reformulation of
  the Riemann hypothesis, https://arxiv.org/abs/math/0607733.
- Baez-Duarte, A strengthening of the Nyman-Beurling criterion for the Riemann
  hypothesis, https://arxiv.org/abs/math/0202141.
The existing provider module also cites the explicit approximation formulation
in https://arxiv.org/abs/math/0205003.

No RH equivalence in the repository should be presented with hBD suppressed.
The core target-totality theorem does not depend on hBD.

## Wolfram and the complete finite matrix experiment

For conductors k=2,...,H+1, let L=lcm(2,...,H+1), a_k(r)=(r mod k)/k, and

    w_s(r)=HurwitzZeta(s,r/L)/(zeta(2)L^s), 1<=r<=L.

Every positive integer belongs to exactly one such progression. Therefore

    G_ij = sum_r a_i(r)a_j(r) w_2(r),
    K_ij = sum_r a_i(r)a_j(r) w_4(r),
    h_i  = sum_r a_i(r) w_4(r),
    b_i  = sum_r a_i(r) w_2(r),
    d    = zeta(4)/zeta(2)=pi^2/15.

For the parity vector beta_i, use sum_r a_i(r) 1_(r odd) w_3(r)/2
(the selected L values are even). Wolfram evaluated these sums, inverted
K+alpha G, and checked the cost identity symbolically. These formulas include
all infinite progression tails.

At alpha=H^(-2), the actual finite-dimensional numerical minima were:

| H | L | Smoothed residual | Source energy | Complete cost | Cost/alpha |
|---|---|---|---|---|---|
| 2 | 6 | 0.0463620210674 | 0.475261785298 | 0.165177467392 | 0.660709869568 |
| 4 | 60 | 0.00704177682250 | 0.754095191801 | 0.0541727263101 | 0.866763620961 |
| 6 | 420 | 0.00222102994406 | 0.835090510107 | 0.0254179885581 | 0.915047588093 |

These are external floating-point computations, not certified interval bounds
and not Lean theorems. Three finite values establish no uniform bound.
The companion private site retains the full numerical matrices, an alpha
control, source/smoothed Gram views, coefficients, and both target remainders.

A reproducible Wolfram form for the matrix construction is:

    ks = Range[2,H+1]; L = LCM @@ ks;
    a[k_,r_] := Mod[r,k]/k;
    w[s_,r_] := HurwitzZeta[s,r/L]/(Zeta[2] L^s);
    G = Table[Sum[a[i,r] a[j,r] w[2,r],{r,1,L}],{i,ks},{j,ks}];
    K = Table[Sum[a[i,r] a[j,r] w[4,r],{r,1,L}],{i,ks},{j,ks}];
    h = Table[Sum[a[i,r] w[4,r],{r,1,L}],{i,ks}];
    c = LinearSolve[N[K+alpha G,40],N[h,40]];

## Verification and publication scope

Five core modules plus the metric extension passed the combined Bazel snippet:
job_F5LlHNj4CGq_e2CyyVl1S0HmDdIdWqwr, exit 0, verified=true,
server-reported verification duration 87.343 seconds.
https://app.buildbuddy.io/invocation/aec5ac25-9155-4e73-81c2-79ba23069aed

The additional conditional converse passed job_6P9jK_bZGFqXgcvso5z-i4QkMN3cbcK6,
exit 0, verified=true, server-reported verification duration 48.585 seconds.
https://app.buildbuddy.io/invocation/07260522-1834-4366-a7f9-e1291b9ee8cd
The required final checkpoint validates //:RiemannResearch with
--config=buildbuddy, audits the entire unpublished source delta, integrates
newer main if necessary, and publishes only verified integrated source.
The exact final checkpoint ID and commit are recorded in its returned result
and in the companion research site's proof-evidence panel.

The new code contains no proof placeholders, new axioms, or unsafe declarations.
Ordinary foundations in axiom reports do not discharge local hypotheses such
as hbudget or hBD. Those hypotheses remain explicit research obligations.

## Next concrete action

Study the exact signed sum in agenda 2 for actual full minimizers, retaining
the normalized residual penalty and full gain. A bounded upper budget is a
sufficient completed arithmetic input. Agenda 6 gives a parallel test:
a bounded cofinal subsequence of complete canonical CRT energies would suffice.
Neither bound follows from the finite computations above.
