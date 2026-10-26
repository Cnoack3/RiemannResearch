# Squarefree tail escape and weaker RH regularity criteria

26 October 2026. The baseline and the weaker criteria below passed targeted server import/axiom checks. The final repository checkpoint is the publication gate; its terminal result determines publication status. The finite-stage upper-bound hypotheses remain Open.

The arbitrary-stage uniform physical-head bound and RH remain unproved. The complete exact-head estimates transfer to the actual squarefree annihilator space. The continuation further weakens the sufficient hypothesis to a cofinal weighted head-energy budget or a critical stretched-tail condition.

## Implementation map

Paths are relative to `RiemannResearch/`.

| Module | Responsibility and principal declaration |
|---|---|
| `Analysis/LogTailWeights.lean` | `logWeight`, the monotone `polylogTailProfile`, and comparisons between the two weights. |
| `RH/QPolylogTailEnergy.lean` | Generic complete-Q physical-envelope estimate, `exists_log_scaled_tail_bound_of_polylog`. No squarefree or annihilator hypothesis. |
| `RH/QScaledTailPerturbation.lean` | Reuses the newer upstream eventual form of `QAnnihilatorTailEscape.weighted_tail_transfer_sub`; retains the existing signed tail identity. |
| `RH/QSquarefreeLogResidualTail.lean` | Squarefree logarithmic/stretched tail escape and the main `riemannHypothesis_of_polylog_moving_head_bound` criterion. |
| `RH/QSquarefreeReciprocalGap.lean` | Four-site spectral-deficit identity, parameter-two coercivity, and `movingCorrection_norm_le_squarefree`. |
| `RH/QParityReciprocalBounds.lean` | Exact centered multiplier identity, parity-moment estimates, and `movingCorrection_actual_parity_energy_bound`. |
| `Analysis/PointwiseEnergyDivergence.lean` | Generic fixed-prefix and cofinal-head Fatou bounds, added to the existing energy-convergence module. |
| `RH/QPolylogMovingHeadEnergy.lean` | Exact finite weighted head energy, the old pointwise-to-energy implication, and limit-energy control. |
| `RH/QSquarefreeMovingHeadEnergy.lean` | Cofinal weighted head-energy criterion, residual vanishing, and head-energy divergence for nonzero residual. |
| `Analysis/StretchedTailWeights.lean` | Scalar stretched weights, vanishing decay, and the exact half-exponent identity. |
| `RH/QStretchedTailEnergy.lean` | Negligibility of the unprojected reciprocal source at every positive stretched weight. |
| `RH/QSquarefreeStretchedTailCriterion.lean` | Critical cofinal tail criteria and unconditional stretched escape on the nonzero-residual branch. |

The first two namespaces are respectively `RiemannResearch.Analysis.LogTailWeights` and `RiemannResearch.RH.QPolylogTailEnergy`. The main criterion is in `RiemannResearch.RH.QSquarefreeLogResidualTail`; it is not in a separate `QSquarefreePolylogHead` module.

## Definitions and indexing

Use Q(n)=1/(zeta(2)n^2) for positive physical n, g_d(n)=(n mod d)/d, and V_N=span{g_d:2<=d<=N+1, d squarefree}. Thus the stage is masked and may be unchanged when N increases. Let V be the closure of their union, P_N and P_V the Q-orthogonal projections, r_N=1-P_N1, rho_N=||r_N||_Q^2, b_N=P_N B r_N, r=1-P_V1, b=P_V B r, and Bf(n)=f(n)/(n+1). All norms and pairings include the complete infinite Q sum.

## Stronger squarefree tail escape

For every integer k>=0 and every u in V-perp with nonzero mean,

    [N/(6+log N)^k] ||1_{n>N}u||_Q^2 -> +infinity.

This does not assume that u annihilates the full-conductor space. The proof uses a prime p with N<p<=2N and M=p-1. The explicit Mobius exact head at M uses only squarefree nonzero conductors because M+1 is prime. Its complete signed identity is

    <1-exactHead_M, 1_{n>N}u>_Q = <1,u>_Q.

For w_k(N)=N/(6+log N)^k, N<=M<=2N implies w_k(M)<=2w_k(N). The existing unconditional complete-error estimate ||1-exactHead_M||^2/w_k(M)->0 therefore gives the stated tail escape by Cauchy--Schwarz. No physical tail or reciprocal cross term is omitted.

The quantitative version retains the repository's stretched-exponential arithmetic provider: there are a>0 and C>=0 such that eventually in N, uniformly over all u in V-perp,

    <1,u>_Q^2 <= [16/zeta(2)+C N exp(-a Phi(6+log N))] ||1_{n>N}u||_Q^2,

where Phi(s)=(s log s)^(1/11). This inequality also holds for zero-mean u.

Apply this to the screened vector Br-b. It belongs to V-perp and has mean <r,Br>_Q, which is positive if r is nonzero. The complete identity

    ||tail(Br-b)||^2 = ||tail(Br)||^2+||tail(b)||^2-2<tail(Br),tail(b)>

and the established physical boundedness of Br imply

    r != 0 -> [N/(6+log N)^k] ||tail_N b||_Q^2 -> +infinity

for every integer k. Thus bounded logarithmically weighted correction tails on any cofinal sequence imply r=0 and then RH through the existing squarefree capacity bridge.

## Relaxed moving-head target

The useful arithmetic obligation can be weakened to finding some finite C>=0 and integer m>=0 such that

    for every N and every 1<=n<=N, |b_N(n)| <= C(6+log n)^m.

Fixed-coordinate convergence passes this bound to b. The generic provider in `QPolylogTailEnergy` then supplies a finite D such that

    [N/(6+log N)^(2m+2)] ||tail_N b||_Q^2 <= D for every N.

This contradicts the nonzero-residual branch. The implemented exponent is 2m+2; the argument does not require a sharp logarithmic tail estimate. The main declaration is `QSquarefreeLogResidualTail.riemannHypothesis_of_polylog_moving_head_bound`. Its m=0 specialization re-establishes the original constant-head criterion. This is a sufficient finite-stage criterion; no converse from RH to the finite-stage envelope is asserted.

The frequent-tail equivalences are equivalences with r=0. The RH assembly uses only the existing implication r=0 implies RH; this development does not assert or use RH implies squarefree residual vanishing.

The envelope itself remains OPEN. The improvement in the criterion does not constitute an unconditional regularity provider.

## Exact arithmetic spectral gap

Every legal squarefree vector and every actual residual satisfies

    f(4)-f(3)-f(2)+f(1)=0.

For normalized coordinates x_n=f(n)/(sqrt(zeta(2))n), this is x_1=2x_2+3x_3-4x_4. The exact finite identity

    19x^2+29y^2+35z^2-(2x+3y-4z)^2
      =(15x-6y+8z)^2/15+2(22y+19z)^2/55+53z^2/33

produces a full infinite spectral-deficit identity and hence

    <f,Bf>_Q <= (59/120)||f||_Q^2,
    <f,(I-2B)f>_Q >= (1/60)||f||_Q^2.

These hold on the entire kernel of the four-site functional, including the affine space 1-V. The ambient t=2 metric degenerates at physical site 1, but remains coercive on that kernel. Polarization also gives ||b_N||_Q <=(59/240)||r_N||_Q. This is a Hilbert bound, not a physical-head bound.

## Stronger actual-source parity estimate

The stage contains g_2 for every N>=1. Write e=1_even and o=1_odd. Then <r_N,o>=0, <r_N,e>=rho_N, ||e||^2=1/4, and ||o||^2=3/4. Removing the even mean and residualizing the first-coordinate evaluation vector against o gives

    r_N(1)^2 <= (zeta(2)-4/3) rho_N(1-4rho_N).

For normalized sequence coordinates y_j=f(j+1)/(sqrt(zeta(2))(j+1)) of any f, the exact centered multiplier identity is

    ||Bf-f/6||^2 = ||f||^2/36+y_0^2/12
      - sum_{j>=0} [1/(3(j+3))-1/(j+3)^2] y_{j+1}^2.

The full infinite remainder is nonnegative. Projection annihilates r_N, so this identity and the refined first-coordinate bound yield

    9 zeta(2)||b_N||^2
      <= (zeta(2)-1)rho_N-(3zeta(2)-4)rho_N^2.

This finite-stage inequality applies for N>=1; b_0=0 handles the initial stage. The same statement holds for the limiting correction. The elementary bounds 4/3<=zeta(2)<=2 and 0<=rho_N<=1/4 imply ||b_N||<=1/12. **The 1/12 corollary has not been formalized**; it is only an ordinary scalar consequence. Coordinate evaluation still costs sqrt(zeta(2))n, so none of these norm estimates supplies the required envelope.

## Additional ordinary result: arbitrary-partition quadratic variation

For every finite partition K=N_0<...<N_m=L,

    sum_j ||b_{N_j}-b_{N_{j-1}}||^2
      <= rho_K ||B(P_L-P_K)||_HS^2.

For a block W=P_1-P_0, z=W1, s=(I-P_1)1, the exact update is

    b_new-b_old=-P_0 Bz+W Bs,

and the two terms are orthogonal. The stronger block estimate retains both the diagonal block energy and the smaller off-diagonal channel. The full trace is

    ||B(P_V-P_K)||_HS^2
      =sum_{n>=1}||(P_V-P_K)e_n||^2/(n+1)^2 ->0.

Consequently the supremum over all finite partitions in the tail tends to zero. This strengthens adjacent square-summability. It is an ordinary proof, not a formalized Hilbert--Schmidt theorem in this development, and the handoff's generic countermodel also satisfies it.

## Remaining research agenda

1. Prove a finite weighted head-energy budget for the actual signed response a(n)^T G^dagger(h-Hc), at arbitrarily large stages. Start with H(N)=N, or prescribe a slower divergent cutoff. Preserve complete Q moments and signed cancellation.
2. Use the exact parity/source energy subtraction and four-site spectral deficit inside residualized evaluation estimates. A Hilbert norm estimate alone still leaves the factor n.
3. Investigate quantitative localization of the inverse response or the block trace. Any proposed rate must cover the first-entry value b_n(n) and every unchanged masked stage.
4. Do not assume full-conductor orthogonality, projection positivity, multiplier invariance, uniform Gram conditioning, or RH. The prime-anchor transfer already handles squarefree legality explicitly.


## Weaker criterion: a cofinal weighted head-energy budget

This section passed the targeted server import/axiom check listed below.

Fix an integer k≥0 and a prescribed function H:ℕ→ℕ with H(N)→∞. Define

    E_{k,H}(N)
      = Σ_{1≤n≤H(N)} |b_N(n)|² / [ζ(2)n(k+6+log n)^k].

The new sufficient hypothesis is only

    there is a finite C≥0 such that E_{k,H}(N)≤C
    for arbitrarily large stages N.

It does not require a pointwise bound, a bound at every stage, or a rate of growth for H. In particular H(N)=N gives a condition on the original physical moving heads. Slower explicit divergent schedules are also permitted.

The relevant declarations are

- `QPolylogTailEnergy.weightedEnergy_summable_of_frequently_moving_head_bound`;
- `QSquarefreeMovingHeadEnergy.residual_zero_of_frequently_moving_head_energy_bound`;
- `QSquarefreeMovingHeadEnergy.riemannHypothesis_of_frequently_moving_head_energy_bound`.

For every fixed finite head, coordinate convergence b_N(n)→b(n) passes its weighted energy to the limit. Nonnegativity compares that fixed head with the growing head. A frequent common budget therefore bounds every limiting finite prefix by C, and the elementary discrete Fatou argument gives

    Σ_{n≥1} |b(n)|² / [ζ(2)n(k+6+log n)^k] ≤ C.

The already established monotone-profile tail estimate then bounds

    [N/(6+log N)^k] ||tail_N b||²_Q ≤ (k+6)^k C.

The nonzero-residual logarithmic escape theorem rules this out when r≠0. Hence r=0, followed by the existing squarefree-closure implication to RH.

### Relationship to the pointwise polylogarithmic condition

The declaration `polylog_head_envelope_implies_uniform_head_budget` proves this implication before any limit is taken. If

    |b_N(n)|≤C₀(6+log n)^m for every 1≤n≤N,

choose k=2m+2. The corresponding weighted head energies with H(N)=N are bounded at every stage by the single finite constant

    D = (C₀²/ζ(2)) Σ_{n≥1} 1/[n(6+log n)²].

Thus the previous all-stage pointwise hypothesis supplies the new cofinal averaged-energy hypothesis. No pointwise bound has been silently retained in the converse direction.

As an ordinary comparison of regularity classes, the relaxation is strict. Put n_j=2^(2^j), j≥1, let h(n_j)=sqrt(n_j)/j, and set h(n)=0 at the other positive integers. Then

    Σ_{n≥1} h(n)²/[ζ(2)n] = (1/ζ(2))Σ_{j≥1}1/j² <∞,

yet h(n_j)/(6+log n_j)^m→∞ for every fixed m. Its finite truncations h_N=1_{n≤N}h converge in Q and have uniformly bounded k=0 weighted head energies while satisfying no common polylogarithmic pointwise envelope. These are illustrative sequences, **not** the actual residue-dictionary corrections. The example establishes strictness of the regularity classes, not a converse or counterexample concerning RH.

### Why an arbitrarily slow head does not make the condition automatic

If r≠0, logarithmic tail escape forces the limiting weighted energy above to be infinite for every fixed k. Given any C, some fixed finite prefix of b has energy greater than C+1. Coordinate convergence makes the same prefix of b_N exceed C at every sufficiently large stage. Every divergent H eventually contains this fixed prefix. Therefore

    r≠0 ⇒ E_{k,H}(N)→+∞

for **every** fixed k and **every** H(N)→∞, however slowly H grows. This conclusion is formalized in `moving_head_energy_tendsto_atTop_of_residual_ne_zero` and passed the same targeted check.

Choosing a slow head does not furnish a budget or evade the obstruction. A concrete remaining target is to prove the budget for H(N)=N, or for another explicit divergent schedule chosen in advance. The finite-stage energy bound remains an Open arithmetic provider; no unconditional residual-vanishing or RH conclusion is claimed.


## Stronger stretched-scale criteria and obstruction

The critical-tail criteria and stretched divergence below passed the targeted server check. The physical-envelope calculus is an ordinary proof only and is explicitly separated.

Write b=P_V B r, b_N=P_N B(1-P_N1), Bf(n)=f(n)/(n+1),
L(N)=6+log N, Phi(s)=(s log s)^(1/11), and

    D_a(N)=exp(-a Phi(L(N))),   W_a(N)=N D_a(N).

The prior squarefree stretched provider supplies fixed a>0 and C>=0 such that,
eventually in N and uniformly for every u in V-perp,

    <1,u>_Q^2 <= [16/zeta(2)+C W_a(N)] ||tail_N u||_Q^2.       (1)

The constants come from an unconditional complete exact-head estimate and
Bertrand's theorem. They do not depend on u.

## Critical tail criterion

For the fixed arithmetic exponent a in (1), either of the following along
one cofinal sequence N_j forces r=0 and therefore RH:

    W_a(N_j) ||tail_(N_j) r||_Q^2 -> 0;
    W_a(N_j) ||tail_(N_j) b||_Q^2 -> 0.                       (2)

The first follows directly from (1): the unweighted complete tail tends to
zero, so both terms on its right tend to zero. Since <1,r>=||r||^2, r=0.

For the correction version, put u=Br-b. Then u lies in V-perp and

    <1,u>_Q=<r,Br>_Q.

The established physical boundedness of Br gives N||tail_N Br||_Q^2<=K.
Since Phi(L(N))->infinity,

    W_a(N)||tail_N Br||_Q^2 <= K D_a(N) ->0.

The exact signed identity for the tail of Br-b is retained. Its consequence
||tail(Br-b)||^2<=2||tail Br||^2+2||tail b||^2 shows that (2) makes the
weighted tail of u tend to zero along the same sequence. Apply (1), then the
faithfulness of B, to conclude r=0.

Thus a **zero liminf at the critical stretched scale** is sufficient. No
bound on every N and no convergence rate for b_N->b is required. The Lean
declaration uses an explicit cofinal sequence instead of a liminf expression.

The same reasoning gives a quantitative positive threshold when r is nonzero.
For u in V-perp with nonzero mean and C>0,

    liminf_N W_a(N)||tail_N u||_Q^2 >= <1,u>_Q^2/C >0.

For b the corresponding lower threshold is <r,Br>_Q^2/C: the weighted
tail norm of Br tends to zero, so reverse triangle makes the weighted tail
norms of b and Br-b asymptotically agree. If C=0 in (1), the ordinary tail
limit already forces every squarefree annihilator's mean to vanish. The
liminf threshold is an ordinary consequence, not separately formalized.

There is also an unconditional divergent-tail version at half the provider
exponent. Since W_a(N)=D_(a/2)(N) W_(a/2)(N), (1) implies

    <1,u>_Q != 0 and u in V-perp
      => W_(a/2)(N)||tail_N u||_Q^2 -> +infinity.

Indeed, at any arbitrarily large N where this product were bounded by a
fixed B, the right side of (1) would be at most

    [16/zeta(2)]||tail_N u||_Q^2 + C B D_(a/2)(N) ->0,

a contradiction. The same divergence holds for b when r is nonzero,
because the weighted tail of Br tends to zero. The checked declarations `exists_stretched_annihilator_tail_escape` and
`exists_stretched_correction_tail_escape` formalize this argument, using
`arithmeticWeight_eq_half`. This improves the obstruction from every fixed logarithmic
scale to one stretched scale.

## Ordinary consequence, not formalized: a physical stretched envelope

The following substantially weaker replacement for a polynomial logarithmic
head envelope is sufficient:

    there exist finite A>=0 and C>=0 such that, for every N and 1<=n<=N,
    |b_N(n)| <= C exp(A(6+log n)^(1/11)).                    (3)

The number 1/11 is an exponent here, unrelated to the earlier unformalized
norm corollary ||b_N||<=1/12. The exponent 1/11 is allowed because the
arithmetic provider contains the additional factor (log L)^(1/11).

Fixed-coordinate convergence passes (3) to b. Put beta=1/11 and L=L(N).
Concavity gives, for n>N,

    L(n)^beta-L^beta <= beta L^(beta-1) log(n/N).

Set delta_N=2A beta L^(beta-1). Eventually 0<=delta_N<=1/2. Hence the
complete tail satisfies

    ||tail_N b||_Q^2
      <= C^2 exp(2A L^beta)/zeta(2)
           sum_(n>N) (n/N)^delta_N/n^2
      <= [2C^2/zeta(2)] exp(2A L^beta)/N.                  (4)

The last inequality uses the decreasing-power integral bound; no tail is
truncated. Multiplying by the actual critical weight in (1) gives

    W_a(N)||tail_N b||_Q^2
      <= [2C^2/zeta(2)]
           exp(L^(1/11)[2A-a(log L)^(1/11)]) ->0.

Thus (2) applies. A may be any fixed finite number: knowledge of the
arithmetic value a is not needed to formulate (3). This envelope eventually
dominates every fixed power of log n, while growing more slowly than n^epsilon
for every epsilon>0.

More generally, the same proof allows C exp(A L(n)^beta) for 0<beta<=1/11.
At the exact provider profile, C exp(c Phi(L(n))) is sufficient when
2c<a; that statement depends on the arithmetic constant and requires the
analogous slow-variation estimate for Phi.

## Cofinal physical heads

The hypothesis in (3) can hold only along stages q(j)->infinity and only
on heads 1<=n<=h(j), where h(j)->infinity. There is no required relationship
between their growth rates. Fixed n eventually lies in every such head,
and b_(q(j))(n)->b(n), so the same physical envelope follows. Alternatively,
a frequent bound at each fixed physical n suffices, with the same A and C.

These are sufficient criteria and, where proved through the tail dichotomy,
criteria for r=0. They are not asserted necessary for RH. The remaining
arithmetic task is still to supply any one of the proposed head, average,
or critical-tail upper bounds unconditionally.

## Provenance and verification

Source: the user-provided `RH_Uniform_Moving_Head_Bound_Research_Handoff_2026-10-26.md`, the existing exact-head/Mobius energy providers, and the actual squarefree projection modules. The prime-anchor transfer does not identify the full-conductor and squarefree annihilator spaces. No extra CRT construction was needed.

Bagchi's survey https://arxiv.org/abs/math/0607733 and Baez-Duarte's strengthened criterion https://arxiv.org/abs/math/0205003 provide external Hilbert-space/RH context only. They are not cited as providers of the new actual moving-head bounds. There is no novelty claim.

Wolfram was restricted to finite polynomial identities. In this continuation the scalar identity

    z/16 - [(z-1)rho-(3z-4)rho^2]
      = (1-4rho)[z-4(3z-4)rho]/16

returned zero remainder after exact expansion. It was not used as a substitute for an infinite argument or Lean verification.

### Terminal verification evidence

- The earlier pending job `job_MQT8z340mSYVofAoD3o4pJBJhVmX6JOk` ended **interrupted**, after 1259.410 seconds, while waiting for the workspace lock. Its owner exited; it was not a proof result.
- The retained-workspace reopen request in this continuation took about 58 seconds end-to-end. This is request latency, not kernel-checking time.
- `job_KGqO-qNa6btMmB_VzXekChLeexl1QiBy`: **success**, `verified: true`, exit code 0, server duration 22.026 seconds. It imported the saved logarithmic-tail, reciprocal-gap, and parity modules and printed the principal declarations' axioms.
- `job_Eauodx59Lau2EP91rilQOyrTLNt_sfUP`: **success**, `verified: true`, exit code 0, server duration 18.034 seconds. It imported the saved weighted-head and stretched-tail modules, including their updated dependencies, and audited the RH consumers, head-energy divergence, old-to-new hypothesis implication, and stretched correction-tail divergence.
- Each audited declaration reported only `[propext, Classical.choice, Quot.sound]`. No `sorry`, `admit`, project-local axiom, or unsafe declaration was added.
- The jobs started within 0.01 seconds of submission. The advertised polling interval was respected for the final result retrieval; any delay between completion and retrieval is polling latency, not proof-checking time. The server durations include dependency preparation/compilation and source checking; they are not isolated kernel timings.

The final checkpoint validates the aggregate project and changed modules, including affected dependencies, and integrates newer main only through the same verification gate. Read its terminal publication result for the final commit; an accepted checkpoint request alone is not publication.

The new upper bounds remain **conditional research reductions**. No unconditional provider of the uniform head bound, polylogarithmic envelope, cofinal energy budget, critical-tail vanishing, squarefree residual vanishing, or RH has been obtained. The physical stretched-envelope implication, sparse-spike regularity comparison, arbitrary-partition quadratic variation, and scalar 1/12 corollary are ordinary arguments rather than separately formalized declarations in this change.

### Integration record

The first checkpoint, `job_pS14uYRA4yRvy7WtRG98DavFQZAp7OfZ`, reached integration with newer main and stopped on conflicts in `QPolylogTailEnergy` and `QScaledTailPerturbation` after 128.732 server seconds. It preserved local commit `60e66e3245e5997edd8c5857effd969975e50577`; that commit was not published.

A separate integration checkout starts from main commit `686f2ace0bfa407c043472f5f10e65b10ab72b18`. It preserves the upstream sharp eventual polylog tail estimate, appends the complementary monotone weighted-energy estimates in the same owning module, and reuses the upstream more general eventual perturbation lemma. No upstream theorem was removed. The logarithmic correction-tail consumer was adapted to the newer eventual hypotheses. The original verified checkout remains intact. The integration-checkout creation request took approximately 65 seconds, distinct from subsequent verification time.

The integrated saved sources passed `job_aZCRuVsVXqNnCkwzKzfBddQ0UtJHDf_T`: success, verified true, exit code 0, server duration 26.214 seconds. The check imported both new criterion modules, the reciprocal gap, and parity module against the newer base. The audited polylog/head-energy/critical-tail/stretched-escape conclusions again used only propext, Classical.choice, and Quot.sound.


## Unconditional moving-head energy estimate

The unconditional conclusion of the subsequent paper argument is now recorded
as QSquarefreeMovingHeadEnergy.moving_head_energy_isLittleO_profile:

    for every k in Nat and H:Nat->Nat with H(N)->infinity,
    E_{k,H}(N) = o(H(N)/(k+6+log H(N))^k).

The companion declaration moving_head_energy_div_profile_tendsto_zero
states the normalized quotient limit explicitly. There is no RH, zero-residual,
bounded-head, or weighted-summability premise in either actual-correction theorem.

The reusable proof lives in Analysis/WeightedHeadEnergy.lean. Dominated
convergence first treats a fixed nonnegative summable energy. Normalized
monotone head weights are at most one, so an l1 perturbation costs at most
the complete l1 distance. The existing Q square-moment convergence theorem
supplies precisely this perturbation estimate for any norm-convergent Q
sequence. LogTailWeights proves that the profile diverges; the actual
squarefree conclusion uses movingCorrection_tendsto.

This unconditional growth estimate still permits divergence. It does not
supply the finite cofinal budget sufficient for RH.

The earlier publication checkpoint job_pLhFpBy4DwCF3-gqfgrdFGj8rfn1wSm3
ended failed after 3648.755 seconds, because its native remote cache upload
timed out after 3600 seconds. It did not publish a commit. The existing
workspace and the previously source-checked results were retained.

The complete new proof candidate passed job_UMQCqrIwt0AUx5Qc7jxC0JnDb3KVECp7:
verified true, exit code 0, 5.214 server seconds. Its actual little-o
conclusion used only propext, Classical.choice, and Quot.sound.
The saved modules passed job_X3Yxkckqcnku2indEHPeO_COLAfmLIp-: verified true,
exit code 0, 15.992 server seconds. The check imported the permanent actual
squarefree module with its new generic/scalar/Q dependencies, displayed the
little-o theorem type, and audited the generic l1 theorem, the Q theorem,
and both actual-correction conclusions. All four axiom reports contained
only propext, Classical.choice, and Quot.sound. Publication is determined
separately by the final checkpoint.
