# RH threshold paper: Lean continuation and coverage

This is a partial formalization of Christian Noack's revised September 7,
2026, 25-page *RH_Two_Seed_Threshold.pdf*. It is not a formalization of the
entire paper and is not a proof of RH.

## Source provenance

The three requested identities were retrieved at version 1, with modification
times September 7, 2026, around 21:16 UTC:

- PDF: `libfile_780734795aa881918aba3c2c3a0218aa`.
- TeX: `libfile_7d48c5eae9388191a161c5421684dedd`.
- Source bundle: `libfile_0edc0ba6355481919e748b5d9336d295`.

Both PDFs have 25 pages and identical extracted text. Their binary hashes
differ, but the standalone and bundled TeX are byte-identical, SHA-256
`4fdbf6f32baccc290a7b81cfae61811191f38f31ab1e12ed5a9987a0db2a74b8`.
The entire TeX, bibliography, README, and all three certificate programs were
read. The inventory below accounts for all 151 labels, all 34 theorem-like
environments, and the unlabelled mathematical obligations.

## Substantive progress

1. Exact all-integer dilation algebra and finite legal synthesis: composition,
   cocycle, power-seed telescoping, and invariance of the algebraic legal span
   under every positive integer dilation.
2. Exact infinite weighted mean, squared-norm, and mixed-product laws for
   arbitrary real weighted square-summable sequences, not just bounded ones.
   Nonzero values at the actual point zero have their boundary anomalies
   retained explicitly.
3. Actual infinite arithmetic progression weights, summability, complete
   finite-head/tail decomposition, and two-sided rational tail bounds.
4. Finite weighted conditional means, complete coarse/fine error splitting,
   exact pairwise variance, positive-weight nullspace, and optimal scalar
   partial correction with the signed mixed term retained.
5. General Hilbert-space exact coarse-lift witness and energy inequalities.
   These do not construct the paper's specific phase witness or prove its
   digit-based linear asymptotic bound.
6. An explicit legal period-36 witness with full weighted squared error
   strictly below `53/1000`, including the infinite tail.

The last result uses coefficients
`[556,117,18,6,7,2,367,50]/1000` on generators `(a,m)`
`[(2,1),(2,2),(2,3),(2,6),(2,9),(2,18),(3,1),(3,3)]`.
This is a new rational witness for the paper's upper bound, not a claim that
these rounded coefficients are the exact minimizer. Its proof uses two exact
head terms per residue and telescoping upper tails; all 36 positive residue
representatives, including 36 for the zero congruence class, remain present.

## Important unproved obligations

- The complete bundled weighted Hilbert-space and analytic adjoint construction.
- Strong Nyman--Beurling as a verified dependency, and its exact discrete bridge.
- Full finite-seed multiplicative-rank classification and joint dilation rigidity,
  including recovery of every discrete value from shrinking-cell estimates.
- Actual phase conditional operators, martingale spectrum, extremal vector,
  optimized phase floor, exact one-base criterion, Mellin continuation,
  removable values, and off-line-zero excess.
- Profinite topology, singularity versus Haar, nonclosability, and failure of
  strongly continuous profinite dilation parametrization.
- Full matrix rank/Schur specialization, finite coarse surjectivity, the
  period-36/coarse-6 determinant enclosure, and constrained squared error >21.
- Phase-constant certificates and the optimal unconstrained lower bound >0.051.
- Uniform two-seed repair and full-error convergence. No RH-equivalent
  estimate is assumed, supplied as a conclusion, or described as established.

All three original Python programs reproduced their assertions, but this is
external rational-program evidence only. Only the explicit upper witness has
been independently carried through to a full infinite-tail Lean proof here;
the other numerical claims remain explicit formalization gaps.

## Continuation priorities

1. Extend the exact-weight finite certificate infrastructure to the actual
   coarse-6 pairing matrix and certify its rank, then the constrained lower
   bound. The two-sided progression-tail theorem already supports all of the
   paper's prescribed arithmetic tail enclosures.
2. Package the weighted square-summable real sequences as the actual Hilbert
   space, with bounded dilation operators and their adjoints. Reuse the
   complete scalar sum identities; do not reintroduce boundedness assumptions.
3. Construct the phase law and forced profile, then the martingale hierarchy
   and extremal vector. Preserve the initial rank a-1 at level zero and the
   exceptional zero finite witness at a=2,L=0.
4. Formalize joint rigidity with its recovery estimate before claiming the
   threshold theorem. Isolate the strong NB dependency rather than making it
   a project-local axiom.
5. Develop coefficient-dependent full-error improvements using small dilations
   and exact mixed terms. Finite interpolation is not bounded synthesis;
   convergence of phase witnesses is not convergence of legal approximants.

## Workflow recovery

Coordinating workspace: `ws_NTw7MGlv-EVhLEAD5U9G4SwotOxq7e8k`.
Project root:
`/home/cri_2025/lean-agent-workspaces/ws_NTw7MGlv-EVhLEAD5U9G4SwotOxq7e8k/RiemannResearch`.
Opened from clean published base
`7ffd48bf380781fac08e3300cfe3e6c8192ee8b6`.
All verification submissions were serialized through the coordinator. Other
agents only developed proofs and inspected sources. No reset, forced push,
dependency update, or unrelated source change was performed.

## Current source-to-module mapping

The final acceptance and publication evidence follows this table. This table
supersedes the initial-status column in the historical source audit below;
items not explicitly discharged remain open.

| Module | Actual contribution and exact hypotheses | Paper coverage |
|---|---|---|
| `RH.ThresholdDilationAlgebra` | Pointwise real sequences, genuine residues, every positive integer dilation; actual algebraic seed span and power telescoping. Bounded raw test functions or explicit ordinary summability for the raw mean formula. | Algebraic part of Lemma 2.1 and rank-one power synthesis; positive-integer part of Proposition 10.1, not profinite topology. |
| `RH.ThresholdDilationEnergy` | Arbitrary real sequences with summable weighted squares. Proves output summability, expectation and mixed/norm identities. Anchor zero is explicit, with the nonzero-anchor correction proved separately. | Entire real sequence sum content of equation dilationnorm; does not yet bundle H or its adjoint operators. |
| `RH.ParetoProgressionTails` | Actual infinite sums with positive modulus; positive representative for lower bounds. Exact finite-head splitting and the certificate programs' two-sided tail prescription, via stronger telescoping bounds. | Quotient-weight and all Section 10 rational-tail infrastructure. |
| `RH.ParetoPeriodicRegrouping` | Actual positive normalized quotient weights and compatibility under refinement; bounded periodic sequences with exact means, norms, and mixed inner products. | Infinite-to-finite weighted CRT bridge and compatible finite measures. No profinite topological construction. |
| `LinearAlgebra.WeightedFiniteProjection` | Finite real weights. Nonzero mass for mean/error formulas, positive mass for scalar minimization, nonnegative weights for positivity, strictly positive weights for defect nullspace, positive correction energy for minimization. | Actual fiber content of Proposition 10.2; rank-one full-error repair. Not matrix rank M-N or the full multicolumn inverse theorem. |
| `Analysis.CoarseLiftObstruction` | Real inner-product space, symmetric linear map, fixed target and exact projected fit, genuine annihilating witness. Nonzero target pairing only when dividing by residual norm. | Exact signed witness identity and abstract energy bound in Theorem 10.9. The phase witness and digit-rate construction are still open. |
| `RH.ThresholdFiniteCertificate` | Exact rational residue-generator values and 36 finite outward upper bounds; no floating-point or native computation. | Finite arithmetic for an explicit upper witness, not the original optimized interval. |
| `RH.ThresholdInfiniteCertificate` | No unresolved analytic or RH hypothesis in `legalWitness36_full_error_lt`; separately proves actual legal-span membership, summability, periodicity, and all-tail regrouping. | Strict unconstrained upper bound <0.053 in Proposition 10.8. Other three inequalities there remain open. |
| `RH.ThresholdPeriod36Basis` | Exact evaluations of the eight stated functions; no assumptions on unknown weights. Linear independence and the four omitted-generator identities. | Algebraic basis components of Proposition 10.8. This does not prove independence after projection modulo 6. |

In particular, the new tail bounds apply to all three Section 10 numerical
expressions, but a valid tail bound alone does not certify determinant sign,
matrix inversion, or constrained optimal cost. Likewise, a finite scalar
correction formula is not the full multicolumn Schur construction.


## Verification before publication

Combined proof and 16-endpoint axiom audit: `job_OktJTJmjaHLu7nl2yKvttVB5phDyY6DP`, succeeded, verified=true, exit_code=0, 10.800 seconds. Code SHA-256 `bd5791ad35ccb4154341dc617cd619cd8714c43e5ce44b57effc9ca5efcfb9da`. Every audited endpoint reports only propext, Classical.choice and Quot.sound; no domain-specific axiom. All nine saved modules match the tested source, ignoring terminal newlines. Final checkpoint validates actual modules and reverse dependents before publication.

## Historical exhaustive source audit

The initial audit is retained for label-level continuity. The current mapping above records newly discharged components; initial Open statuses do not override that mapping.

# RH Two-Seed Threshold: complete source inventory and initial coverage audit

Source read in full: `sources/RH_Two_Seed_Threshold.tex`, 1798 lines, September 7, 2026 edition, including Section 10; all three certificate programs, their recorded output, and README. This is the initial read-only audit by the inventory agent, not a claim that any new result has passed Lean. The coordinating agent must attach subsequent checked providers and publication evidence. No verification job was submitted by this agent.

## Source identity and reproducibility

- Standalone TeX and bundled TeX are byte-identical: SHA-256 `4fdbf6f32baccc290a7b81cfae61811191f38f31ab1e12ed5a9987a0db2a74b8`.
- Both PDFs have 25 pages and identical `pdftotext` output. Their file hashes differ: standalone `7369a80b182bb164c8fb1e901b66b1ee846345bf28b130029e0933d90da3807a`; bundled `d031f5fe7f96914ba1377bab73b002f99cd55aef19ef5d3aca3afc3878522044`. This is not evidence of a mathematical source mismatch: extracted contents agree exactly.
- The source contains 151 labels, including 10 section labels, 1 table label, 28 statement/problem labels, and 112 equation labels. It has 34 theorem-like environments: 27 mathematical theorem/lemma/proposition/corollary environments, 2 remarks, and 5 research problems. Most definitions are in prose, not definition environments.
- The bibliography and acknowledgment explicitly say no Lean verification was performed for this paper. Claims of prior independent ordinary proof checks or successful Python certificates are not formal verification evidence.
- Required source identities supplied to the coordinator: PDF `libfile_780734795aa881918aba3c2c3a0218aa`, TeX `libfile_7d48c5eae9388191a161c5421684dedd`, bundle `libfile_0edc0ba6355481919e748b5d9336d295`. Version/status confirmation is the coordinator's retrieval record.

## Existing declarations actually inspected

Repository `AGENTS.md` was read in full. These are source-inspected reuse candidates, not a new build/axiom audit. Namespace abbreviations below: `P = RiemannResearch.RH.Pareto`, `LA = RiemannResearch.LinearAlgebra`.

| Existing source | Source-inspected declarations | Exact scope and missing bridge |
|---|---|---|
| `RH/ParetoResidueDuality.lean` | `P.residue`, `P.dilation`, `P.ramanujanPacket`, `P.residue_mul_floor`, `P.residue_difference`, `P.mobius_inversion`, `P.ramanujanPacket_divisor_sum` | Genuine natural-number residue, paper's scaled `T_m`, genuine Möbius function; exact pointwise arithmetic. Not Hilbert-space closure or density. |
| `RH/ParetoDilation.lean` | `P.positiveWeight`, `positiveWeight_difference`, `positiveWeight_interval`, `positiveWeight_block`, `dilation_block`, `dilation_product_block`, `dilation_block_all`, `dilation_partial_sum`, `dilation_tsum`, `positiveWeight_summable`, `positiveWeight_tsum`, `weighted_summable_of_bounded`, `paretoMean`, `paretoInner`, `paretoMean_dilation`, `paretoInner_dilation` | Actual weight `1/(k(k+1))`, weight zero at natural index zero; exact boundary block and full sum identities. `dilation_tsum` assumes summability of source and dilation. `paretoMean_dilation` and `paretoInner_dilation` discharge it for bounded sequences. They do NOT yet prove bounded operators on every element of weighted H. |
| `RH/ParetoPrimePackets.lean` | `P.moebius_prime_mul`, `prime_divisor_transform`, `sum_moebius_div`, `ramanujanPacket_mul_prime` | Exact finite divisor algebra; relevant to packet span and dimension, not the asserted span identity or independence by itself. |
| `Probability/ConditionalVarianceError.lean` | `ProbabilityTheory.integral_const_sub_sq_eq_bias_sq_add_variance`, `integral_const_sub_sq_total_variance`, `integral_const_sub_sq_condExp_pythagoras`, `integral_condVar_eq_integral_sq_residual`, `integral_condVar_nonneg` | Genuine probability-space integrals and conditional expectations with `MemLp X 2 μ`, sub-sigma-algebra and probability hypotheses. Must construct the paper's actual `(J,Y,K)` law and forced profile; generic total variance is not that construction. |
| `LinearAlgebra/FiniteWeightedEnergy.lean` | `LA.weighted_functional_sq_le`, `weighted_functional_energy_lower_bound`, `affine_normal_det_double_sum`, `affine_normal_det_nonnegative`, `affine_normal_det_positive`, `finite_weighted_square_completion` | Genuine finite weighted algebra. Useful for fiber variance and lower certificates but not matrix inverse/orthogonal-projection providers. |
| `LinearAlgebra/FiniteQuadraticError.lean` | `LA.quadratic_error_of_entrywise_bound` | Converts entrywise real matrix errors to coefficient-dependent quadratic bounds; not a smallest-eigenvalue certificate. |

Bounded declaration searches also found `P.paretoMean_residue_two` in `ParetoResidueMoments.lean`, plus many neighboring Pareto covariance and repair modules. Its type was not read in this audit, so no assertion about its hypotheses is made. Searches for `NymanBeurling`, `phase`, and `Schur` returned no declaration-name matches; this is not a proof of absence from Mathlib/repository. In particular, no verified provider of the strong Nyman–Beurling criterion has been located by this audit.

Status convention for all rows below: **Open** means no complete paper-specific provider was identified in this initial audit. **Partial** means the explicitly listed existing provider proves only a component. An ordinary proof supplied by the paper is not automatically a Lean proof. Later verified modules must be mapped at this granularity, without marking an entire row complete merely for a scalar consequence.

## Full statement inventory

| Number / label | Actual statement and indispensable hypotheses | Initial status |
|---|---|---|
| Theorem 1.1 `thm:mainthreshold` | Nonempty finite integer seeds ≥2. Independent pair: RH iff 1 in closure of all integer dilations iff that closure is H. Otherwise common integer base with gcd-one exponents, equality of algebraic dilation spans, unconditional positive distance. | Open: independence rigidity, finite-seed algebra, strong NB bridge. |
| Theorem 1.2 `thm:mainquant` | Every fixed integer a≥2: positive optimal phase lower floor d_a; actual distance equals floor iff RH; explicit finite annihilators with geometric asymptotic. | Open; assembled from Sections 5–8, not a proof of RH. |
| Lemma 2.1 `lem:dilation` | m,n≥1, every f∈H anchored at zero: composition, residue identity, exact expectation and norm scaling, preservation of V/W, cocycle, E R_a=log a. | Partial: arithmetic and bounded-sequence sums above. Full H operators, general residue expectation, invariant closures open. |
| Proposition 3.1 `prop:forced` | F∈closed single-seed M_a: B_aF=(E F)Y/μ_a; exact three-term error identity and positive beta_a lower bound. | Open actual conditional profile; generic variance identity available. |
| Lemma 4.1 `lem:rigidity` | Independent a,b≥2: joint adjoint fixed space is complex constants. | Open: local L² tail limit, irrational-period rigidity, recovery at EACH integer. |
| Theorem 5.1 `thm:spectrum` | Actual conditional partitions and B,Q: S=sum π_j P_j=sum a^-ell Δ_ell; norm formula; all eigenspaces/multiplicities, compact/injective, 0 in spectrum. | Open. Initial eigenspace dimension a−1, not always constants. |
| Lemma 5.2 `lem:fixedphase` | Closure range Q_a equals ker(T_a*−I), proved by weighted martingale approximation. | Open; need full fixed-space reverse inclusion. |
| Proposition 6.1 `prop:constant` | C_a=a(1+s) for every integer a≥2, with actual summable δ_k. | Open infinite variance block evaluation. |
| Theorem 6.2 `thm:pythagoras` | Construct actual r_a∈H with explicit cells, mean μ, norm² C, B r=Y and adjoint-fixed; z*=1−μr/C annihilates M_a; exact error identities for every real F∈M_a. | Open construction. Generic square completion is only a component. |
| Remark 6.3 (unlabelled) | Do not apply bounded S^-1 to Y; Q_a t_L converges even if formal S^-1Y is not in phase L². | Required domain restriction, not optional. |
| Proposition 6.4 `prop:phaseopt` | Projection of 1 onto closed phase-annihilator space is z*; supremum ratio d_a; finite witness mean=norm²=d_a,L increasing to d_a. | Open; zero witness for a=2,L=0 must be excluded from ratio. |
| Theorem 6.5 `thm:RHsharp` | Under RH, M_a perp=N_a; distance and projection, exact attained mean-one variance. Unconditionally only lower bound. | Open and conditional on genuine RH/strong NB bridge. |
| Lemma 7.1 `lem:recurrence` | ψ and bounded φ as defined; pointwise-finite r recurrence, H cocycle; integral representation φ increasing from 2log2−1>1/4 to 1/2. | Open actual log/integral identities; pointwise ψ is not an H vector. |
| Theorem 7.2 `thm:distanceiff` | Mellin r factorization Re s>1/2, removable μ at s=1; fixed-a RH iff r∈W iff r∈M_a iff distance²=d_a. | Open complex analysis, bounded Mellin functional and external zero facts. |
| Corollary 7.3 `cor:excesszero` | Hypothetical zeta zero ρ with 1/2<σ<1 forces explicit strictly positive excess. | Open: requires actual Mellin nonvanishing, not assumed conclusion. |
| Remark 7.4 (unlabelled) | Norm-convergent legal-dilation Φ, Neumann inverse preserving W and commuting with all dilations; alternate zero obstruction. | Open operator construction; does not synthesize r. |
| Lemma 8.1 `lem:delta` | δ_k positive summand upper/lower bounds for k≥1; universal tail for N≥1 (implicit in expression N^-3). | Open analytic series/remainder. |
| Proposition 8.2 `prop:cert-rate` | L≥0: 0<C−C_L≤(a+1)/(12a^L), exact tail decomposition, O_a(a^-3L) and d asymptotic. | Open full tail/asymptotic, not numerical witness convergence. |
| Theorem 9.1 `thm:nogap` | Independent a,b: normalized real or complex g_j⊥1 exactly a-adjoint-fixed, b defect→0; no coercivity even after finitely many fixed bounded pairings. | Open eigenvector, diverging norms, Diophantine approximation, weak convergence. |
| Proposition 10.1 `prop:profinite` | m≥1: continuous state quotient q_m, exact pushforward with δ_0 boundary; bounded value-zero-core composition. For m≥2, raw composition on ALL locally constant functions is not closable. | Open profinite/measure bridge, boundary essential. |
| Proposition 10.2 `prop:crt-defect` | Positive quotient weights, N|M: weighted projection identities, PSD defect rank M−N, exact fiber variance and error. | Partial generic finite algebra; actual quotient provider and rank open. |
| Proposition 10.3 `prop:anchored` | N|M anchored projections compatible; as integer N→∞ strong convergence, explicit finite-head error; every m≥1 preserved through modulus mN with exact commutator and bound. | Open projections and strong-limit bridge. |
| Theorem 10.4 `thm:crt-interpolation` | Every a≥2,N≥1: projecting span of T_m R_a with N|m is onto E_N. For all sufficiently large L, m=NjL, 1≤j≤N are basis; lift norm ≤K_N,a L^(N−1/2)||y||, explicit finite period. | Open analytic moment/Vandermonde asymptotic and controlled finite inverse. No uniform-in-N claim. |
| Proposition 10.5 `prop:crt-six` | Six specified legal generators of period |36 have independent projections modulo6; Π_6 V_36=E_6; determinant in (−0.000062,−0.000061). | Open Lean certificate, actual infinite weights/tails required. |
| Theorem 10.6 `thm:crt-repair` | Independent legal columns, positive weights, coarse K full row rank: unique minimum-norm exact lift and Schur inverse cost; fine energy nonnegative. | Open full matrix provider; generic scalar completion insufficient. |
| Corollary 10.7 `cor:crt-partial` | Under preceding full rank: optimum coarse y*=S Ω_N1; error 1−bᵀSb and exact seed-three gain. Prose extends direct coefficient formulas to deficient rank. | Open; keep rank conditions distinct for arbitrary-profile inverse versus partial optimization. |
| Proposition 10.8 `prop:crt-cost-example` | Entire V_36 with eight-column basis: exact coarse mean-one min norm² between22 and23; unconstrained error² between.051 and.053; constrained error²>21. | Open Lean interval inversion, basis spanning and actual tail bridge. |
| Theorem 10.9 `thm:crt-linear` | F∈M_a, Π_NF=1: annihilator cost. For N=a^L,L≥1, explicit residual bound and linear norm² lower bound; base2 A=116/9,B=41/9. | Open actual r digit expansion and tail sums; scalar consequence alone partial. |
| Theorem 10.10 `thm:crt-RH` | Any N_j→∞: uniformly bounded exact finite legal lift energies iff RH. RH gives infimum1 each N; non-RH gives Λ_N→∞. Nondecreasing under divisibility. | Open and RH-equivalent, NOT proved boundedness. Requires weak compactness and exact finite right inverse. |
| Problem 11.1 `prob:extremal` | Explicit finite legal approximation of r_a with nontrivial N,a-dependent coefficient estimate. | Open research. |
| Problem 11.2 (unlabelled) | Certified finite E_a,N upper bounds exclude zeros on specified compact right-half-strip regions via nondegenerate penalty. | Open bounded research; fixed certificate cannot exclude unlimited height/all σ>1/2. |
| Problem 11.3 (unlabelled) | Describe arithmetic defects N_a perp minus M_a in martingale coordinates; transfer relaxed decompositions to legal finite synthesis controlling full error and dilation sizes. | Open research; relaxed-space density alone is not legal density. |
| Problem 11.4 (unlabelled) | Certified finite cross-phase singular values and troublesome near-common martingale levels; coefficient-dependent suppression. | Open bounded/asymptotic research. |
| Problem 11.5 (unlabelled) | Explicit optimizer/coefficient estimate forcing mᵀG^-1m→1. | Open RH-equivalent research. |

## Every labelled equation: definition or proof obligation

Rows group only related equations; every equation label is retained explicitly. All are Open except the partial reuse specified above. Labels for the ten sections are `sec:background`, `sec:phase`, `sec:threshold`, `sec:compression`, `sec:optimal`, `sec:distanceiff`, `sec:constants`, `sec:nogap`, `sec:crt`, `sec:research`; these organize the source, not claims.

### Sections 1–4

- `eq:H`: define actual weighted H and expectation, summable probability mass; require complete Hilbert realization, not raw `tsum` alone.
- `eq:definitions`: R_a, zero-extension D_m and scaled T_m, all m≥1.
- `eq:NB`: strong NB equivalence; externally published but no Lean dependency identified.
- `eq:packets`: genuine Möbius packets J_q,q>1; existing `ramanujanPacket`.
- `eq:packetcriterion`: restricted-to-either-prime packet completeness iff RH, with every other prime factor unrestricted.
- `eq:universal`: δ_k,s,d_a definitions, plus convergence and positivity before use.
- `eq:mainquant`: d_a lower floor for actual distance.
- `eq:cert-rate-intro`: exact asymptotic constant for d_a−d_a,L.
- `eq:dilation`: T_mT_n=T_mn and T_mR_n=R_mn−R_m; second has existing pointwise provider.
- `eq:dilationnorm`: exact expectation/norm scaling on all H; bounded-source partial providers exist.
- `eq:cocycle`: (T_a−I)R_n=T_nR_a−R_a; finite algebra component.
- `eq:fullNB`: 1∈W iff W=H via all tail indicators and finite-support density, then RH bridge.
- `eq:packetmodule`: exact algebraic prime-seed span = packets divisible by p, via Möbius inversion.
- `eq:phase-law`: actual independent geometric J and inverse-square phase Y laws.
- `eq:B`: actual conditional phase B, contraction; convergent series interpretation.
- `eq:forced`: B F=(EF)Y/μ for ALL closed M_a.
- `eq:firstvariance`: exact bias + forced phase variance + conditional variance, no terms omitted.
- `eq:beta`: strict unconditional positive single-seed floor.
- `eq:rigidity`: joint adjoint fixed space exactly constants for independent pair.
- `eq:tailscaling`: qU(qn)=U(n), n≥1, q=a,b.
- `eq:localdefect`: compact-interval L² defect bounded by C a^-j times actual weighted tail energy.
- `eq:recovery-rate`: same rate for u_j−u, indispensable for shrinking-cell recovery U(n)=c/n. Local L² convergence alone does NOT establish discrete values.

### Sections 5–6

- `eq:Q`: adjoint compression value on each j,k cell, including j=0 with a−1 cells.
- `eq:S`: strong/operator series equality, martingale diagonal form, weighted norm identity; require convergence topology.
- `eq:phaseannihilator`: Y-orthogonal phase compressions annihilate M_a.
- `eq:fixedphase`: full closed range/fixed-space equality.
- `eq:Clevels`: positive finite and infinite weighted martingale energies C_a,L,C_a.
- `eq:Cuniversal`: evaluate C=a(1+s).
- `eq:Cvariance`: summation-by-parts variance identity with vanishing boundary tail.
- `eq:cell`: exact weighted cell mass and logarithmic conditional mean.
- `eq:vj`: variance block formula in δ_k.
- `eq:r-properties`: actual extremal mean, norm, conditional image, fixed equation.
- `eq:r-explicit`: pointwise discrete formula from stabilized finite levels.
- `eq:zstar`: optimal witness definition.
- `eq:exact-decomp`: exact three-term error for real F∈M_a, m=EF.
- `eq:excess`: exact error =d_a+distance to scaled r_a, not an inequality with dropped cross terms.
- `eq:riesz`: actual pairing identity <Qb,r>=<b,Y>.
- `eq:bL`: finite phase witness with C_a,L>0.
- `eq:phaseopt`: supremum ratio over nonzero Y-orthogonal b equals d_a.
- `eq:finitebounds`: finite compressed witness mean=norm²=d_a,L increasing to d_a; zero initial dyadic witness handled separately.
- `eq:sharp`: under RH exact distance/projection; domain hypothesis must remain visible.
- `eq:meanone`: RH-conditional exact infimum and actual attainment, unconditional lower bound only.
- `eq:arithmeticexcess`: exact unconditional separation of geometric floor and remaining legal synthesis distance.

### Sections 7–9

- `eq:rexplicit2`: ψ/floored finite sum formula for r; ψ itself is unbounded and not H.
- `eq:rcocycle`: actual H equality using bounded φ and pointwise cancellation of unbounded ψ.
- `eq:phi`: integral identity, strict >1/4 initial value, monotonicity and limit1/2.
- `eq:Adirichlet`: A(s), with positive increments summing to1/2−φ(1); absolute convergence on Re s≥0.
- `eq:Azero`: actual nonvanishing lower bound 4log2−5/2>0 on that closed half-plane.
- `eq:Mellin`: continuous linear functional on H for Re s>1/2 with norm bound (2Re s−1)^-1/2.
- `eq:residuemellin`: Mellin residue transform, analytic continuation into Re s>0, exceptional s=1 explicitly removable (value log n).
- `eq:rmellin`: Mellin r factorization; s=1 removable value μ_a. Literal substitution into a totalized `riemannZeta 1` expression is NOT the removable-value proof.
- `eq:singleiff`: RH iff r∈W iff r∈M_a iff exact positive distance floor attained.
- `eq:rzeta`: off-line zero evaluation nonzero: numerator nonzero in open critical strip, denominator nonzero in Re s>0, A nonzero.
- `eq:zeroexcess`, `eq:zeroexcesssimple`: exact functional-derived lower bound, then explicit positive weaker lower bound. Require 1/2<σ<1, ζ(ρ)=0, actual r transform.
- `eq:delta-bounds`: explicit δ sandwich; prove positive artanh coefficient expansion and bounds.
- `eq:Stail`: s tail enclosure N≥1; actual series and integral comparison, not assumed numerical endpoints.
- `eq:Ctail`: strict positive C−C_L and geometric upper bound.
- `eq:asymptotic`: O_a(a^-3L) and asymptotic-equivalence constants.
- `eq:exactCtail`: exact two-block infinite δ decomposition, retaining both pieces.
- `eq:logcertificate`: finite positive artanh sum plus rational remainder for 0<z<1,M≥1.
- `eq:Snumeric`: strict s interval (0.0803270395119,0.0803270395185); all tails included.
- `tab:bounds`: strict d_2 interval(.110541537245,.110541537251), d_3(.162094729186,.162094729192), d_5(.250721569938,.250721569943); beta column is approximate only.
- `eq:vt`: actual complex sequence v_t∈H, t real nonzero.
- `eq:vteigen`: E v_t=1 and T_m* v_t=m^-it v_t for every m≥1; norm divergence and weakly normalized limit needed separately.

### Section 10

- `eq:profinite-identities`: quotient composition, residue cocycle, and pushforward ν/m+(1−1/m)δ_0, including boundary atom.
- `eq:boundary-repair`: zero-extension D_m u equals raw pullback minus u(0) initial block for periodic representatives.
- `eq:crt-weights`: actual positive infinite residue weights Ω_N with mass1 and compatibility.
- `eq:crt-weight-integral`: integral and tail w_r<ω_N(r)≤w_r+ζ(2)/N², representatives1..N, N denotes zero.
- `eq:crt-zero-weight`: ζ(2)/N²−ω_N(0) between0 andζ(3)/N³.
- `eq:crt-dependence`: coprime a,b→∞ covariance of residue1 indicators tends1/4 with O(a^-2+b^-2); correlation→1, not independence.
- `eq:conditional-matrix`: A=Ω_N^-1 JᵀΩ_M when N|M.
- `eq:crt-defect-matrix`: actual PSD matrix Ω_M−Ω_MJΩ_N^-1JᵀΩ_M.
- `eq:crt-exact-error`: full error decomposes into coarse error and exact defect quadratic form.
- `eq:crt-fiber-variance`: defect equals full signed double-sum fiber square expression; denominator2ω_N(r).
- `eq:crt-finite-norm`: actual infinite H error of period|N legal F equals finite weighted error.
- `eq:anchored-head`: exact head projection residual and ζ(2)K(K+1)/N² relative norm bound, N>K.
- `eq:anchored-commutator`: all integer dilations into anchored modulus mN and exact commutator identity.
- `eq:anchored-commutator-bound`: m^-1/2 times actual unresolved head error.
- `eq:crt-rank-one`: raw pullback weighted Gram anomaly (1−1/m)e_0e_0ᵀ, no removal except on zero-coordinate subspace.
- `eq:finite-legal-space`: V_N generated by seeds2,3 at periods dividing N; conductor condition only, no smoothness restriction on m.
- `eq:crt-dimension`: packet span, dimension (((u+1)(v+1))−1)τ(b) when N=2^u3^v b,(b,6)=1; prove independent jumps/Fourier orders or equivalent exact algebra.
- `eq:crt-explicit-defect`: g=T_2R_2 period4|12 has Π_6g(0)=2ω_12(6)/ω_6(0)>0, hence projected g not V_6.
- `eq:legality-defect`: weighted orthogonal-complement matrix of coarse legal projection; independent columns, empty-space projection zero.
- `eq:crt-surjectivity`: every finite coarse profile attainable by single seed and dilations divisible by N.
- `eq:crt-lift-upper`: norm growth K_N,a L^(N−1/2), enough large L; no uniform N bound.
- `eq:crt-moment`: actual weighted pairing integral G_r(m), N|m, c_r and strictly positive ell_a.
- `eq:crt-positive-moments`: η_0=log a; η_j=j! ζ(j+1)(1−a^-j)>0 for j≥1.
- `eq:crt-vandermonde`: exact positive leading determinant gamma_N,a L^-P with relative O(L^-1), P=N(N−1)/2.
- `eq:crt-delayed-cost`: N≥2, only dilations m≥N and Π_N F=1 force norm²≥ω_N(1)²/(ω_N(1)−1/2)≥N²/(4ζ(2))=3N²/(2π²), EVEN for two seeds.
- `eq:crt-six-generators`: ordered pairs(3,3),(2,3),(3,1),(2,2),(2,1),(2,9).
- `eq:crt-det-certificate`: strict determinant interval(−62/10^6,−61/10^6).
- `eq:crt-repair-matrices`: G=BᵀΩ_MB, K=AB, H=G−KᵀΩ_NK PSD for independent legal B.
- `eq:crt-repair-pythagoras`: coefficient norm²=coarse norm²+ALL fine energy.
- `eq:crt-minimum-repair`: full-row-rank K, S=KG^-1Kᵀ, c*=G^-1KᵀS^-1 y, unique minimum yᵀS^-1y.
- `eq:crt-fine-cost`: yᵀ(S^-1−Ω_N)y≥0.
- `eq:crt-second-seed`: independent new columns modulo old; residual positive Gram S and residual coarse Z; old coarse rank full for inverse lift gain.
- `eq:crt-information-gain`: exact S_23=S_2+ZS^-1Zᵀ.
- `eq:crt-exact-gain`: full inverse-update formula for exact lift gain, positive; Z=0 yields no coarse-target benefit.
- `eq:crt-partial-optimum`: y*=S b and error1−bᵀSb,b=Ω_N1.
- `eq:crt-partial-gain`: exact partial error gain bᵀZS^-1Zᵀb; no discarded mixed terms.
- `eq:crt-certified-cost`: actual min constrained norm² in(22,23) and unconstrained distance² in(.051,.053) at6|36.
- `eq:crt-annihilator-cost`: norm²≥1+d_a²/||(I−Π_N)z*||² for every actual single-seed exact lift; denominator must be proved nonzero.
- `eq:crt-digit-bound`: actual r residual≤A_a/N+B_a/N² along N=a^L,L≥1; explicit A and B polynomials.
- `eq:crt-linear-cost`: actual lower bound1+(d/θ)²N/(A+B/N), θ=μ/C.
- `eq:crt-witness-equality`: exact signed pairing <F−1,(I−Π_N)z*>=−d_a.
- `eq:crt-digit-expansion`: digit sum minus centered digit depth plus bounded epsilon, derived from actual φ; preserve all terms.
- `eq:crt-lift-energy`: infimum over finite legal combinations from both seeds with Π_N F=1; nonempty by interpolation; not necessarily attained.

### Section 11

- `eq:finiteexcess`: fixed-a finite-seed excess equals(μ/C)² dist(r,M_a,N)²≥0; decreasing to0 iff RH. Changing base requires normalization.
- `eq:nintersection`: unconditional phase-relaxed N_a∩N_b={0} and closure(N_a perp+N_b perp)=H; does not show closure(M_a+M_b)=H.
- `eq:crossphase`: actual weighted compressed cross pairing; bounded truncation error≤||b||∞||c||∞/(K+1).
- `eq:fullgram`: independent finite basis: exact error minimum1−mᵀG^-1m.
- `eq:meangram`: m≠0: exact mean-one minimum variance1/(mᵀG^-1m)−1; eigenvalue lower bound required for certified inversion.

## Additional unlabelled obligations that must not disappear

1. Weighted H isometry with step functions x↦f(floor(1/x)) on(0,1), centered fractional-part identity, and conversion from strong criterion on(0,∞) using vanishing A/x tail.
2. V and M_A definitions, closure topology, arbitrary all-integer dilation invariance, finite-support density via differences of tail indicators.
3. Primitive rational ray of finite seed prime exponent vectors, gcd reduction, polynomial S_e Bezout identity over Q, and application of a polynomial in T_c without analytic convergence assumptions.
4. Phase probabilities, moments E Y=μ and E Y²=a; finite digit identity forcing profile with final floor zero and limiting remainder controlled.
5. Nested phase sigma-algebras generating measurable sets and strong P_j→I; P_-1=0, Δ_0=P_0 of dimension a−1.
6. Explicit adjoint formula a/w_n times weighted block; fixed martingale P_j h_(j+1)=h_j and full-H approximation by compressed h_L.
7. r construction by Cauchy sequence Q t_L; stabilization of coordinates, not arbitrary representatives; hyperplane correction denominator a−1>0 proving closed phase annihilator equality under RH.
8. Mellin scaling on D_m, boundedness and holomorphy; zero-free line Re s=1 and zeta functional equation as actual dependencies. Zero multiplicity is not separately used in this paper's RH converse: one nonzero evaluation at any hypothetical zero suffices. Do not manufacture multiplicity conclusions.
9. Norm-convergent Φ and Neumann inverse; absolute coefficient positivity/sum supplies bound. Formal S^-1Y remains outside the permissible phase-domain assertion.
10. Linear witness z_a(k) and approximate a=2 lower bound .0873430760; finite d_2,3>.09749. Approximate beta table values and linear witness value are not enclosed by the programs as separate assertions.
11. No-gap eigenvectors: entry bound for H membership, norm divergence over |t|≤k≤2|t|, simultaneous rational approximation, normalization after subtracting constants, weak convergence, real extraction.
12. ν on profinite integers: atomic, full support, Haar singular, isometric weighted-H realization. Raw local-constant pullback not closable using u_N=1_(N Zhat), ||u_N||²≤ζ(2)/N² but raw images→nonzero boundary indicator. Domain distinction mandatory.
13. No strongly continuous profinite D-parameter extension: m_j=1+j!→1 profinitely but operator norms→0 while D_1=I. This does not contradict continuity of each q_m as a state map.
14. Haar-vs-weighted example: distinct prime sequence, normalized residue averages. CRT Haar independence gives error²=(1/J²)sum(p+1)/(3(p−1))≤1/J, while dominated convergence gives the SAME functions→0 in H. Preserve distinctness and all bounds0≤F_J≤2.
15. Positive quotient weights and actual probability mass; inverse diagonal legal. Anchored versus unanchored projection zero-coordinate cost≤tail from N and strong convergence through all N, not merely a tower.
16. Raw pullback operator norm²=1/m+(1−1/m)/ω_N(0), growing quadratically for fixed m≥2; anomaly vanishes exactly on anchored subspace.
17. Finite V_N union along cofinal divisibility tower recovers M_2,3; Ramanujan packet jumps−c_q and disjoint Fourier orders justify independence.
18. Exact interpolation proof: generating series, nonnegative interchange, positive kernel bounded at0 and exponentially decaying; Taylor derivative bounds and determinant leading sign; N=1 edge case; effective b_n recurrence (N≥2) and normalized error<1/2 threshold.
19. All six periods divide36; eight-column V_36 basis spanning, via dimension or exact seed relation T_2R_3=T_3R_2+R_3−R_2. Full-rank six projection is NOT alone proof the eight columns span the entire V_36.
20. Weighted matrix minimum exact lift vs partial fit distinction; 0<Σ≤I, tᵀΣ^-1t vs1−tᵀΣt, preserving all small eigenvalue contributions.
21. Digit epsilon bound0<epsilon≤1/2+a/6 from 0<1/2−φ(n)≤1/(6n), digit concatenation, nonzero-residue and zero-residue terms separately, two full geometric moment sums through order3. A_2=116/9,B_2=41/9.
22. General single-seed lift energy divergence along arbitrary N→∞, stronger explicit linear rate only along base powers.
23. Exact finite right inverse under RH gives infimum Λ_N=1, no attainment claim. Bounded sequence of exact finite lifts gives weak limit1 via strong Π_N; closed legal subspace weakly closed. Divisibility monotonicity not ordinary numeric monotonicity.
24. Full weighted Gram and cross-phase entry tails≤B_iB_j/(K+1), PLUS spectral/inverse stability. Error control at entry level alone does not certify optimization.

## All three certificate programs: exact scope and required Lean bridge

### `certify_phase_constant.py`

- Standard-library exact `Fraction` arithmetic; log(1+1/k) uses z=1/(2k+1), 52 positive artanh terms, rational remainder, outward grid10^-50.
- Builds log/δ enclosures for k=1..4095. Universal sum uses N=1024 with the actual `eq:Stail` lower and upper remainder.
- Strictly asserts s interval and the three d_a table intervals a=2,3,5. Obtains log a by telescoping sum of log(1+1/k), k<a.
- Finite levels a=2,L=1..7 and a=3,L=1..6, with exact finite C formula from δ blocks; specifically asserts d_2,3>.09749. Recorded values, e.g. d_2,3≈.0974997604339954, agree with manuscript.
- Required Lean chain: artanh remainder theorem → real log enclosure → summand δ interval → exact finite integer/rational computation → real universal tail → positive denominator/inverse propagation → actual phase-floor/witness bridge.
- Caveat: program says “all numerical enclosures”; approximate beta column and approximate linear-witness figure are not separately asserted. They are displayed approximations, not extra rigorous intervals.

### `certify_weighted_crt_rank.py`

- N=6,M=36, TERMS=64, SCALE=10^18; ordered six generators exactly those in `eq:crt-six-generators`.
- Actual weight representative r=1..36, r36 for zero; head terms floored individually, at most64 grid units added upstairs.
- At t=r+36*64, real omitted tail bounded below1/[36(t+1)] and above1/[t(t+1)]+1/(36t); then outward rational rounding.
- Builds nonnegative pairing entries from actual residue values `s%(a*m)-s%m`. Determinant interval expands all720 permutations with correct signs; strict enclosure(−62/10^6,−61/10^6).
- Required Lean chain: actual infinite arithmetic-progression weights → rigorous tail interval → interval determinant soundness/exact computed endpoint inequalities → det nonzero → projected six independent → surjectivity of actual weighted Π_6 restricted V_36. Rational determinant success alone is not the last three steps.

### `certify_weighted_crt_cost.py`

- N=6,M=36, TERMS=4096,SCALE=10^24; eight generators (2,1),(2,2),(2,3),(2,6),(2,9),(2,18),(3,1),(3,3).
- Same actual arithmetic-progression tail prescription, tighter head. Every interval addition, multiplication, subtraction, and division is integer outward rounded. Division checks denominator excludes zero.
- Gaussian/Gauss–Jordan elimination tracks intervals and requires each pivot's lower endpoint positive. For exact symmetric matrices this proves positive-definite Gram and coarse Schur matrices, provided operation soundness and identity with exact elimination are formalized.
- G=BᵀΩ_36B, R=JᵀΩ_36B, b=Ω_6 1. Cost=bᵀ(RG^-1Rᵀ)^-1b; v=column mean, error=1−vᵀG^-1v.
- Recorded outward intervals: cost[22.178187471,22.581931562], error[.051941468,.051943020]; exact assertions give22<cost<23 and.051<error<.053.
- Required Lean chain: actual weight tail bounds → sound interval algebra/elimination with positive pivots → real inverse identity/positive definiteness → eight-column basis and entire legal space → exact constrained/unconstrained minimum identities. Π_6F=1 implies mean1, so constrained error²=norm²−1>21. None of these infinite/optimization steps may be replaced by a finite rational surrogate matrix.

## Mathematical audit findings and continuation priority

No definite mathematical counterexample was found in this read-only audit. This is not an expert validation of every analytic proof. The paper's delicate points are real obligations, particularly discrete recovery, removable Mellin values, and the value-zero profinite boundary. The source's ordinary proofs consistently distinguish geometric witness convergence from arithmetic approximation convergence.

The strongest missing assertion remains a uniform-in-coarse-level bound on full two-seed repair cost, or full legal approximation error tending to zero. The paper explicitly identifies this with RH. General Schur formulas, finite surjectivity, fixed finite errors, and dense phase-relaxed sums do not supply it.

Prioritize reusable actual arithmetic weight/tail and finite certificate bridges; then full weighted-H and conditional phase operators; then actual extremal construction, rigidity with recovery, Mellin criterion, and profinite representations. The root should record precise checked modules/declarations against this ledger and preserve unfinished analytic, spectral, certificate, and RH-equivalent targets as Open. A final checkpoint must include dependency/axiom audit and actual published commit; this inventory does not provide either.

## Coordinator-reported implementation candidates (not audited here)

At handoff the coordinator reported these new modules as forthcoming. Their exact types, verification results, dependency audit, and publication commit must be filled from the coordinating record, not inferred from the module names:

| Candidate module | Intended paper coverage | Limits that remain |
|---|---|---|
| `RH/ThresholdDilationAlgebra` | Pointwise algebra for Section2 and related seed identities | Does not by itself construct H, phase operators, rigidity or RH equivalence. |
| `RH/ParetoProgressionTails` | Actual residue-progression weighted tails in Section10 | Must inspect exact statement to determine which certificate tail prescription it supplies. |
| `RH/ThresholdFiniteCertificate` and `RH/ThresholdInfiniteCertificate` | Coordinator reports an explicit legal witness with full error<.053, using rigorous J=2 tail | This is a valid upper-bound witness if checked, but it does not verify the original4096-term interval inversion, optimum lower bound>.051, constrained cost22–23 or six-column determinant. Preserve those distinct obligations. |
| `LinearAlgebra/WeightedFiniteProjection` | Coordinator reports19 finite projection theorems for exact weighted errors/defects | Generic finite formulas need actual quotient-weight, rank and Hilbert projection specialization; not all of Proposition10.2 automatically. |
| `Analysis/CoarseLiftObstruction` | Coordinator reports5 generic Hilbert obstruction identities | Not the actual extremal r_a residual bound, explicit digit constants, linear single-seed growth, or two-seed boundedness/RH criterion until providers are specialized. |

The coordinator explicitly confirmed that neither the threshold/RH equivalences nor the analytic phase results have been proved in this run at this checkpoint of the inventory. Do not mark those complete based on the above support modules.
