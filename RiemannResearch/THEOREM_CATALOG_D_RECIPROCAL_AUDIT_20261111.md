# D-residue density: veracity audit, Lean strengthenings, and RH obligations

Source document: D_Residue_Density_PQ_Nyman_Beurling_2026-11-11.pdf (13 pages).
Inspected baseline: ff8bb2f43ab8784612535538a94e4f28c401d1fe, the exact commit named in the PDF.
This audit distinguishes mathematical arguments, checked Lean declarations, external analytic theorems, and open arithmetic providers.

## Verdict on the PDF

No mathematical contradiction was found in the stated results. The full-conductor, squarefree, and strict-conductor cases must remain separate. In particular, unconditional D-image density is compatible with the open RH question because D has no bounded inverse on its range. The PDF correctly identifies D1 as the target for lifting to 1.

| PDF result | Audit and formal coverage |
|---|---|
| 2.1–2.2: equivalent physical P/Q norms and corrected inner products | Sound. QParetoEquivalence and QReciprocalTargetLift supply the transfer. Orthogonal projections and means do not transfer by relabeling P and Q. |
| 2.3: B invertible; D injective with dense, nonclosed range | Sound diagonal-operator argument. The density and reciprocal multipliers must not be confused. The new comparison with shifted reciprocal R does not make either smoothing operator boundedly invertible. |
| 3.1: every unbounded D-conductor family approximates 1 | Sound; one_mem_reciprocalClosure_of_unbounded. This does not approximate the unsmoothed RH target. |
| 3.2–3.5: four-site and two-site obstructions | Sound exact arithmetic; agrees with the existing Lean functionals and independent Wolfram checks. |
| 4.1–4.4: full D-density, squarefree D1 membership, failure of D-invariance | Sound. Lean proves full density by the finite-sieve route. The absolutely convergent Möbius-series argument is a valid alternative paper proof; this audit does not claim a separate newly formalized infinite-series identity. |
| 4.5: omitting conductor 2 gives exactly f(1)=f(2) | Sound; strict_reciprocalClosure_eq_ker. The projection used in the paper is bounded but need not be orthogonal. |
| 5: RH iff 1 belongs to the full residue closure iff full density | Correct published theorem, Bagchi Theorem 1. The repository's sufficient direction ends in Mathlib RiemannHypothesis. The analytic reverse direction remains externally sourced in this audit. |
| 6.1–6.3: bounded/cofinal lifts and O(reg) costs imply RH | Sound conditional reductions. New finite-span cost iff and cost-divergence theorems sharpen their interpretation. |
| 6.2 head–tail estimate | Sound; now formalized with the exact energy split and a convergence theorem that needs no separate H_j -> infinity assumption. |
| 7: joint annihilator and K-block cancellation | Sound with the stated matched-subspace/prime-testing hypotheses. Squarefree D1 membership does not supply prime-to-squarefree orthogonality or eliminate the middle coupling term. |
| 8: published results | Bagchi/Báez-Duarte equivalence and Bettin–Conrey–Farmer's RH and derivative-moment assumptions checked against primary sources. Burnol's continuous lower bound transfers to the standard integer-dilation distance by inclusion of approximating spaces; its constant is not automatically the constant of the discrete regularized cost. |

## Strengthenings

Write Rf(n)=f(n)/(n+1), Df(n)=f(n)/n, and
J_a(v;x)=||D(v-x)||_Q^2+a||v||_Q^2.
All norms and tails below are complete, including infinitely many coordinates.

### Comparable smoothing norms

For every f,
    ||Rf||_Q^2 <= ||Df||_Q^2 <= 4 ||Rf||_Q^2.
The constants are the coordinate multiplier bounds 1 <= (n+1)/n <= 2.
This permits transfer of a useful existing Mellin-based criterion from R to D.

### Weaker sufficient cost condition

For a_j=(j+1)^(-4), finite legal U_j, it suffices that for every eta>0 there is a finite C_eta>=0 such that
    J_{a_j}(U_j;1) <= C_eta a_j^(1-eta)  for every j.
This is weaker than one uniform O(a_j) bound and permits subpower growth of the unsmoothed norms. The Lean proof uses the existing complete Mellin-tail criterion; weak compactness alone does not justify this weakening.
Open: supply these inequalities for an actual arithmetic family. No RH assumption is used by the conditional consumer.

### Exact finite-span cost equivalence

For a submodule S, target x, and any prescribed a_j>0 tending to zero:
    x in closure(S)
      iff
    exists C>=0 and v_j in S with J_{a_j}(v_j;x) <= C a_j for all j.
No separability hypothesis on S is required: the proof applies weak compactness inside the separable closed span of the countably many chosen approximants.
The forward proof chooses finite approximants with ||v_j-x|| <= min(1,sqrt(a_j)); the explicit sufficient constant is 1+(||x||+1)^2.
The reverse proof uses bounded injective lifting. This equivalence concerns closure membership; it is not a newly proved analytic RH converse.

If x is outside closure(S), then for every v_j in S:
    J_{a_j}(v_j;x)/a_j -> infinity.
No D-image convergence assumption is needed. In particular, failure of RH forces this divergence for every full legal sequence.

### Exact and estimated head–tail energies

For the physical head P_H and residual h, the exact identity is
    ||h||_w^2 = sum_{1<=n<=H} w(n)n^2 |Dh(n)|^2 + ||(I-P_H)h||_w^2.
Hence
    ||h||_w^2 <= H^2 ||Dh||_w^2 + ||(I-P_H)h||_w^2.
The implemented theorem is in Q's weighted l2 encoding. Existing P/Q transfer carries convergence and bounds to the same physical sequences in P.
For any heads H_j, convergence of both terms on the right to zero implies v_j -> x. There is no need separately to assume H_j -> infinity.
For legal v_j and x=1 this gives a checked conditional RH consumer. Both error terms remain explicit hypotheses.

### Quantitative finite sieve

For m>=1, S_{N,m} from PDF Proposition 4.2 is exactly T_m on every coordinate n<m(N+1), a sharper head than the original eventual-equality interface.
Moreover,
    ||S_{N,m}-T_m||_P^2 <= 1/[m^3(N+1)].
It follows by P/Q comparison that the Q squared error is at most 2/[zeta(2)m^3(N+1)].
The proof retains the exact signed Mobius sum, identifies it with a coprime count, and only then estimates its full tail.
These sieve vectors contain a constant component. They are not themselves a certificate of bounded finite legal unsmoothed preimages.

## Infinite CRT: exact role and versions

| Version | Formal evidence | What it supplies |
|---|---|---|
| Arbitrary overlapping positive moduli | ProfiniteGeneralizedCRT.exists_profiniteInt_iff_pairwise | Existence iff pairwise gcd compatibility. |
| Cofinal finite lcms | existsUnique_profiniteInt_iff_pairwise_of_lcm_cofinal | A unique profinite realization when finite lcms cover every positive modulus. |
| All-modulus inverse-limit topology | tendsto_iff_eventually_reduce_eq | Convergence iff eventual equality at each finite residue coordinate. |
| Product over all p-adic integers | ProfiniteCRT.profinitePadicEquiv and tendsto_iff_padicProjection | The equivalent prime-power model and coordinatewise p-adic convergence. |
| Categorical universal property | ProfiniteCRTUniversal.existsUnique_continuous_lift, compatibleLift_comp, padicFamilyLift_unique | Unique continuous compatible homomorphisms and naturality. |

Prime powers are retained. Prime-only residues are not cofinal in all positive moduli.
None of these CRT statements contains a bound on legal coefficients, a full P/Q energy bound, or a residual-tail estimate.
Existing FactorialCRTSeparation provides explicit escaping finite-level witnesses and the failed exchange of forall/exists quantifiers. Thus finite-level solvability must not be promoted to a bounded ordinary-integer or Hilbert-space lift.

## RH implication and equivalence ledger

| Condition or equivalence | Direction/status | Remaining obligation |
|---|---|---|
| 1 in full legal closure -> Mathlib RH | Existing Lean theorem | Prove membership. |
| RH iff 1 in full legal closure iff full residue density | Published Bagchi Theorem 1; analytic converse external here | Formal reverse direction is not claimed. |
| Full density of B g_k iff full density of g_k | Bounded invertible operator argument; externally RH-equivalent | No unconditional density provider. |
| Bounded D-lift of Dx iff x in a closed source S | Existing Lean iff | Bounded unsmoothed lifts. |
| Finite-span O(a_j) cost iff x in closure(S) | New Lean iff | Uniform complete-cost estimate. |
| Full legal near-linear costs for every eta>0 -> RH | New D specialization of existing Mellin result | One legal family with all exponent-loss estimates. |
| Complete head–tail errors -> 1 in legal closure -> RH | New Lean implication | Both quantitative head error and complete residual tail. |
| not RH -> normalized complete costs diverge | New Lean obstruction | Does not prove RH or its negation. |
| Full/squarefree D-image approximation to D1 | Unconditional Lean | Does not imply RH without a lift estimate. |
| K displacement zero iff exact K-block forcing cancellation | Existing Lean iff with explicit matched-subspace/prime assumptions | Actual signed cancellation, including the middle component. |


## New declaration map

All RH namespaces below have prefix RiemannResearch.RH; CRT declarations have prefix RiemannResearch.NumberTheory.GeneralizedCRT.

| Module | New declarations |
|---|---|
| RH/QReciprocalMetric.lean | shifted_norm_sq_le_D; D_norm_sq_le_four_shifted |
| RH/QReciprocalHeadTail.lean | norm_sq_eq_D_head_add_completeTail; head_norm_sq_le_D; complete_head_tail_bound; tendsto_of_variable_head_tail; riemannHypothesis_of_variable_D_head_tail |
| RH/QReciprocalCostEquivalence.lean | cost (definition); exists_cost_le_of_mem_closure; mem_closure_of_cost_bound; mem_closure_iff_regularized_cost; normalized_cost_tendsto_atTop_of_not_mem; normalized_cost_tendsto_atTop_of_not_RH; riemannHypothesis_of_near_linear_D_cost |
| RH/QReciprocalSieveRate.lean | factorialSieve_exact_head; tailSequence_le_inv; factorialSieve_pareto_error_sq_le; factorialSieve_q_error_sq_le |
| NumberTheory/ProfiniteGeneralizedCRT.lean | existsUnique_profiniteInt_iff_pairwise_of_lcm_cofinal; tendsto_iff_eventually_reduce_eq |
| NumberTheory/ProfiniteCRT.lean | tendsto_iff_padicProjection |

Total additions: 20 theorems and 1 definition; 3 new Lean modules and extensions to 3 existing modules. All new modules are exported from RiemannResearch.lean.

## Next proof obligations

1. Choose explicit finite legal vectors, including conductor 2, and retain the target D1. The full family avoids the known squarefree D-invariance obstruction.
2. Target either the near-linear complete-cost estimates above, or the two complete head–tail limits. The near-linear route is the stronger sufficient criterion now available.
3. Use finite CRT/prime-power systems to organize the signed coefficient and carry identities. Apply the inverse-limit interfaces only to their compatible residue data.
4. Bound full Gram quadratic forms, including signed cross terms and certified infinite tails. A finite-coordinate computation is not the required bound.
5. For the squarefree route, replace the sieve's constant component with actual finite legal D-images while tracking the unsmoothed cost; the two limits cannot be exchanged without an estimate.
6. Keep K cancellation separate unless a checked pairing bridge supplies all required squarefree tests and the middle-component coupling.
7. Specialize an RH consumer only after an unconditional arithmetic provider has been checked. RH remains open.

## External sources checked

- Bagchi, “On Nyman, Beurling and Baez-Duarte's Hilbert space reformulation of the Riemann hypothesis,” Theorem 1, https://arxiv.org/abs/math/0607733 .
- Báez-Duarte, “A strengthening of the Nyman–Beurling criterion for the Riemann hypothesis,” https://arxiv.org/abs/math/0202141 .
- Burnol, “A lower bound in an approximation problem involving the zeros of the Riemann zeta function,” Theorem 1.3, https://arxiv.org/abs/math/0103058 .
- Bettin, Conrey, Farmer, “An optimal choice of Dirichlet polynomials for the Nyman–Beurling criterion,” Theorem 1, https://arxiv.org/abs/1211.5191 . Its RH and derivative-moment assumptions are not unconditional providers.
- Wilkes, Profinite Groups, Sections 1.2 and 2.2, especially Theorem 2.2.1, https://www.dpmms.cam.ac.uk/~grw46/LectureNotes.pdf . Supports the inverse-limit/product CRT framework, not Hilbert density.

## Wolfram diagnostics

Exact values returned: LD(D^2 1)=5/12, LD(D^2 g_2)=1/3, LB(1)=-7/60.
Finite factorial-sieve identities were true for N=1..6, m=1..4, n=1..80.
Replacing N! by the product of primes <=N agreed in tests N=1..8, m=1..4, n=1..80.
The sharpened head identity agreed for n=1..m(N+1)-1, N=1..6, m=1..4.
These finite checks are diagnostics, not general proofs or RH evidence. A separate four-coordinate diagonal regularization check returned the expected normalized minimum limit ||x||^2=4; it is not a legal-family certificate.

## Verification evidence

The baseline matches the exact commit cited by the PDF:
ff8bb2f43ab8784612535538a94e4f28c401d1fe.

Saved-source scoped Bazel/BuildBuddy acceptance:
- Job: job_9GnedDEfG-WoWLfaiwv35IRfp2zHViIT.
- Status: succeeded; verified=true; exit code 0.
- Server-reported verification duration: 50.498 seconds.
- Log: https://app.buildbuddy.io/invocation/a3372164-e0a0-461b-8027-6921a0822448 .
- Scope: the new modules, their transitive dependencies, the existing PDF classification modules, and the cited CRT/joint-annihilator modules. This is not by itself a full-project acceptance.

An earlier scoped job reached its 240-second timeout after compiling its dependencies and before completing the final audit action. It was not counted as verification; the terminal timeout was established before the successful rerun.

Guarded axiom audit:
- Job: job_rXq_GKnoi_nUeLDeCl9FsPi0sj3__o8Q.
- Status: succeeded; verified=true; exit code 0; backend=bazel.
- Server-reported duration: 53.714 seconds.
- Log: https://app.buildbuddy.io/invocation/f120534e-08c1-4654-9053-2aa893dbab34 .
- Twenty-five principal declarations were checked with #guard_msgs against exactly propext, Classical.choice, and Quot.sound. The guard would reject an additional axiom.
- Audit code SHA-256: 9cc75eaaf471a540a218403a00cf9138b5d29c2134d5aef11242266d6e4c0e22.
- The check covers both the central existing PDF results and the new RH consumers, cost iff/divergence, sieve, head-tail identity, and CRT criteria. It checks dependencies as well as theorem types; local mathematical hypotheses remain visible in their types.


The final publication gate is the server checkpoint for the complete //:RiemannResearch target using Bazel --config=buildbuddy. Its exact job and published commit are reported with the delivery. A successful queued submission alone is not acceptance.
