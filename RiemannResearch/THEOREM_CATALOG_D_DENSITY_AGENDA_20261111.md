# Section 9 agenda: complete costs, signed sieves, and actual block forcing

Source: D_Residue_Density_PQ_Nyman_Beurling_2026-11-11.pdf, Section 9, priorities 1–7.
Implementation baseline: 2d94869a4c420b6596ef068f7403a2e94dfb0f74.
This continuation adds seven focused Lean modules, 50 public theorems, and nine public definitions.
The arithmetic complete-cost provider and RH remain OPEN.

P/Q notation and the exact closure/invariance audit: [density operator catalog](THEOREM_CATALOG_PQ_DENSITY_OPERATORS_20261112.md).

## Status of the seven priorities

| Priority | Proved or improved here | What remains open |
|---|---|---|
| 9.1 Target and conductors | All costs use D(v−1). The actual inverse-Gram family uses conductors 2 through H+1. Its legality and containment of the canonical exact-head competitor are proved. The physical P/Q D operators commute with the identification. | No claim of bounded inversion of D. Squarefree D1 membership remains the previous unconditional image result. |
| 9.2 Complete regularized tradeoff | Exact complete G_D+αG normal equations, positive definiteness, unique minimizer, signed quadratic identity, exact improvement formula, inverse-Gram minimum value, and a finite-coordinate certificate with both infinite tails. The optimizer inherits the previous unconditional canonical complete-cost bounds. | A fixed-C cofinal J≤Cα, or the weaker all-exponent near-linear bound, for the actual optimizer. Finite evidence does not prove these. |
| 9.3 Signed Möbius blocks | The complete quadratic form applies to any finite coefficient family, including damped and logarithmic coefficients. Actual factorial-sieve pairings retain their Möbius signs and have a quantitative error. Existing damped diagonal/off-diagonal identities remain applicable. | Uniform signed off-diagonal estimates and joint cutoff control for damped/logarithmic families; no new asymptotic logarithmic-mollifier theorem is claimed. |
| 9.4 Cofinal provider | Closure iff existence of cofinal O(α) costs; explicit RH consumers for cofinal costs, cofinally bounded canonical energies, and cofinal inverse-Gram values. If RH fails, the actual canonical energies tend to infinity. | The arithmetic boundedness hypothesis for one concrete family. The criterion is a reduction until that hypothesis is proved. |
| 9.5 Prime-to-squarefree gap | Exact finite sieve pairing, disappearance of prime contributions, quantitative Q-mean certificate, and an iff between vanishing of the actual K-block and signed sieve cancellation including the actual middle coupling. | Prove the remaining composite sum cancels that coupling. Neither term is assumed zero. |
| 9.6 P/Q audit metrics | Exact complete-cost correction identity and J_P≤ζ(2)J_Q≤2J_P. Existence of a cofinal O(α) bound is invariant under the physical identification. | This does not identify orthogonal projections or means; the existing B correction remains necessary. |
| 9.7 RH endpoint | New consumers conclude Mathlib RiemannHypothesis with all arithmetic assumptions explicit. Every new public theorem is included in the guarded axiom audit. | RH is not proved. The full-project checkpoint is the final integration gate. |

## Complete finite-dimensional minimization

Let g_d(n)=(n mod d)/d, Df(n)=f(n)/n, and
J_α(v;x)=‖D(v−x)‖²_Q+α‖v‖²_Q.
For an injective finite legal conductor list d_i>1, set a_i=g_(d_i) and

G_ij=⟨a_i,a_j⟩_Q,
(G_D)_ij=⟨Da_i,Da_j⟩_Q,
b_i=⟨Da_i,Dx⟩_Q,
A_α=G_D+αG.

These are complete infinite-coordinate Hilbert inner products, not truncated matrices.
For α>0, A_α is positive definite and the unique minimizer in span{a_i} is

c*=A_α^(-1)b,   v*=Σ_i c*_i a_i.

The exact identities are

J_α(Σ_i c_i a_i;x)=‖Dx‖²−2cᵀb+cᵀA_αc,

J_α(v;x)=J_α(v*;x)+‖D(v−v*)‖²+α‖v−v*‖²,

J_α(v*;x)=‖Dx‖²−bᵀA_α^(-1)b.

Thus signs and all cross terms survive. The matrix inverse formula is mathematically explicit;
the Lean definition is noncomputable over real complete Gram entries. It is not a claimed
floating-point certified inversion routine.

Module: RH/QReciprocalFiniteCost.lean.
Principal declarations: gram_posDef, minimizer_normal, cost_quadratic,
cost_completion, minimum_value, minimizer_le, minimizer_unique,
residue_minimizer_legal, residue_gram_posDef.

## Actual full-conductor family and inherited bounds

RH/QReciprocalFullMinimizer.lean defines fullMinimizer H α using g_2,...,g_(H+1)
and fullValue H α using the exact inverse-Gram scalar above. In particular,

0≤fullValue(H,α)=J_α(fullMinimizer(H,α);1)
                 ≤J_α(exactHead(H);1).

The canonical competitor is the previously verified finite legal vector

v_H=−Σ_(1≤d≤H) μ(d)g_d+(H+1)m_Hg_(H+1),
m_H=Σ_(1≤d≤H) μ(d)/d.

For H≥1 and E_H=‖canonicalMobiusHilbert H‖²_P,

fullValue(H,H^(-2)) ≤ (4/ζ(2))H^(-2)E_H ≤ 16/(ζ(2)H).

For every positive c below the existing certified classical contour endpoint, there is C≥0
such that for all H≥1,

fullValue(H,H^(-2))
 ≤12/(ζ(2)H²)+(C/H)exp(−c√log H).

These are unconditional inherited upper bounds. The optimizer is never worse than the
canonical competitor; a stronger asymptotic exponent is NOT established here.
The bound just displayed is still insufficient for the RH consumers below.

## Certified infinite tails

Let T_H omit the first H encoded Hilbert coordinates, so the physical retained coordinates
are n=1,...,H. Define

headCost(α,v,H)=Σ_(k<H) ( |D(v−1)(k)|²+α|v(k)|² )

in the weighted l² encoding. This is exactly the physical sum

Σ_(1≤n≤H) Q(n) [ |(v(n)−1)/n|²+α|v(n)|² ].

No tail is hidden in this definition. The exact identity is

J_α(v;1)=headCost(α,v,H)+‖T_H D(v−1)‖²+α‖T_H v‖².

For α≥0, |v(n)|≤A at every positive physical coordinate, and A≥0, put
κ_H=(1+1/(H+1))/ζ(2). Then

headCost(α,v,H) ≤ J_α(v;1)
 ≤ headCost(α,v,H)+κ_H[(A+1)²/(H+1)³+αA²/(H+1)].

For any finite residue combination v=Σ_i c_i g_(d_i), A=Σ_i |c_i| is valid.
The complete bound is therefore usable without assuming any cancellation in the tail.
It preserves the exact signs in the finite head. For large coefficients the allowance
can be large; its validity does not guarantee a useful uniform asymptotic estimate.

Module: RH/QReciprocalCostCertificates.lean.
Declarations: cost_eq_head_add_tails, headCost_le, reciprocal_tail_sq_le,
cost_certificate, finite_residue_sequence_bound, finite_residue_cost_certificate.

## Cofinal criteria and RH implication ledger

All α_j below are positive and tend to zero.

| Formal statement | Exact logical status |
|---|---|
| x∈closure(S) iff ∃C≥0, F_j∈S, ∀N ∃j≥N, J_(α_j)(F_j;x)≤Cα_j | Lean iff, for arbitrary submodules S. The family is existential. |
| The displayed cofinal cost condition for finite full legal F_j and x=1 implies RH | Lean implication. |
| ∃C≥0, ∀N ∃H≥N, H>0 and E_H≤C implies RH | Lean implication for the actual canonical family. |
| ¬RH implies E_H→∞ | Lean contrapositive consequence. This is not a converse characterizing RH by boundedness of this family. |
| ∃C≥0, ∀N ∃H≥N, fullValue(H,α_H)≤Cα_H implies RH | Lean implication for the specified actual finite inverse-Gram family. |
| For H_j=(j+1)² and α_j=(j+1)^(-4), ∀η>0 ∃C_η≥0 ∀j, fullValue(H_j,α_j)≤C_η α_j^(1−η) implies RH | Lean implication using the existing Mellin-based near-linear consumer. |
| A cofinal O(α) complete-cost bound exists in Q iff it exists in P for the same family | Lean metric iff, with constant factors. |
| Q-mean of h∈K vanishes iff its actual signed sieve pairings tend to zero | Lean iff under the explicit joint-annihilator/prime hypotheses. |
| Actual K-block k=0 iff the signed sieve pairings minus the actual middle coupling tend to zero | Lean iff under matched-subspace and projection hypotheses. It is not asserted as an RH iff. |
| RH iff 1 is in the full residue closure | Published Bagchi/Báez-Duarte equivalence. The new Lean work uses the already checked sufficient direction; no newly formalized analytic converse is claimed. |

Modules: RH/QReciprocalCofinalCost.lean, RH/QReciprocalFullMinimizer.lean.

## Actual signed sieve pairings and the middle component

Write K=jointAnnihilator(V,W) and suppose W contains every prime residue atom.
For h with Pareto mean zero, define the finite signed quantity

M_N(h)=−Σ_(d divides N!) μ(d)⟨h,Dg_d⟩_P.

This equals the pairing with the actual factorial sieve S_(N,1), including its constant
component before the mean-zero cancellation. The general certificate is

|⟨h,D1⟩_P−M_N(h)|²≤‖h‖²_P/(N+1).

For h∈K the theorem specializes to

|ζ(2)⟨1,h⟩_Q−M_N(h)|²≤‖h‖²_P/(N+1).

Here h in the Q pairing means its same-physical-sequence Q realization.
The prime summands vanish. The implementation filters out d=1 and prime d;
nonsquarefree summands also vanish through their Möbius coefficients, but that additional
filter is not needed in the theorem. Composite squarefree contributions remain.

For the ACTUAL projected fit f=toPareto(Π_S^Q 1), set

k=Π_K^P f,
u=f−Π_(toPareto W)^P f−k.

Assume the explicit matched-subspace hypothesis toPareto(q)∈V iff q∈S and the
orthogonal-projection instances in the Lean theorem. The existing block equation gives

‖k‖²_P+⟨k,Dk⟩_P=⟨k,D1⟩_P−⟨k,Du⟩_P.

Consequently the new actual certificate is

|(‖k‖²_P+⟨k,Dk⟩_P)−(M_N(k)−⟨k,Du⟩_P)|²≤‖k‖²_P/(N+1),

and positivity of D proves

M_N(k)−⟨k,Du⟩_P →0  iff  k=0.

This is a useful exact scalar formulation of the remaining block cancellation.
It does not prove the cancellation: the sequence always converges to the nonnegative
block energy. There is no assumption that the middle component u vanishes.

Modules: RH/QSievePairingCertificates.lean, RH/QJointSieveForcing.lean.

## Exact P/Q correction

Under the same physical-sequence identification,

ζ(2)J_α^Q(v;x)
 =J_α^P(v;x)+metricCorrection(D(v−x))+α metricCorrection(v).

For α≥0 both corrections are nonnegative and are controlled by the Pareto norm terms.
Hence

J_α^P(v;x) ≤ ζ(2)J_α^Q(v;x) ≤ 2J_α^P(v;x).

A Q constant C transfers to the P constant ζ(2)C. A P constant C transfers to the Q
constant 2C/ζ(2). These comparisons include the source energy and the smoothing error.
They are not identities between P and Q projections.

Module: RH/QParetoCostTransfer.lean.

## CRT and published research: permissible uses

The previously checked infinite-CRT interfaces remain available:

- Arbitrary compatible moduli: ProfiniteGeneralizedCRT.exists_profiniteInt_iff_pairwise.
- Cofinal finite lcms: existsUnique_profiniteInt_iff_pairwise_of_lcm_cofinal.
- Inverse-limit convergence: tendsto_iff_eventually_reduce_eq.
- Prime-power product: ProfiniteCRT.profinitePadicEquiv and tendsto_iff_padicProjection.
- Categorical continuous lift: ProfiniteCRTUniversal.existsUnique_continuous_lift.

They organize residue compatibility and limits, not Hilbert coefficient bounds.
This continuation does not need another infinite-CRT theorem. Its signed factorial
identities and existing floor/carry formulas preserve the actual arithmetic.
No prime-only limit is treated as cofinal among all moduli, and no carry is discarded.

Published sources reviewed:

1. Bagchi, *On Nyman, Beurling and Baez-Duarte's Hilbert space reformulation of the
   Riemann hypothesis*, Theorem 1:
   https://arxiv.org/pdf/math/0607733 .
   This gives the discrete weighted-space equivalence and allows equivalent weights.
2. Báez-Duarte, *A strengthening of the Nyman–Beurling criterion for the Riemann hypothesis*,
   Theorems 1–2:
   https://www.bdim.eu/item?fmt=pdf&id=RLIN_2003_9_14_1_5_0 .
   The constructive damped approximation estimate assumes RH. It cannot supply the
   unconditional provider needed here.
3. Bettin–Conrey–Farmer, *An Optimal Choice of Dirichlet Polynomials for the Nyman–Beurling
   Criterion*, Theorem 1:
   https://aimath.org/~kaur/publications/80.pdf .
   The logarithmic coefficient design is a candidate for the finite quadratic form;
   the asymptotic theorem assumes RH and a reciprocal-zeta-derivative moment bound.
   Those hypotheses are not imported into any unconditional new theorem.

## Wolfram diagnostic: first conductor

For the normalization g_2(n)=(n mod 2)/2 and Q(n)=6/(π²n²), direct infinite-sum
evaluation returned

G=3/16,   G_D=π²/64,   b_D=π²/32,   ‖D1‖²_Q=π²/15.

Thus the one-conductor coefficient and minimum are

c_α=2π²/(12α+π²),

J_min(α)=(192απ²+π⁴)/(240(12α+π²)).

In particular the fixed-conductor minimum tends to π²/240, not zero, as α tends to zero.
This diagnostic corrected an initial normalization input for G; it uses the fractional
residue normalization, not the unnormalized indicator of odd integers.
These explicit π evaluations are external Wolfram checks, NOT additional Lean theorems.
The abstract inverse-Gram identity itself is proved in Lean.

## Verification

The combined development check succeeded:
job_jlfveO0WDIAKEF0_3Qj4kR8tpoFHsfIV, backend=bazel, verified=true, exit=0.
Log: https://app.buildbuddy.io/invocation/dc69faa3-f337-49c8-9b11-90c395559968 .
Code SHA-256: e956df6c6a443d2b47b3b30388376fbb4fe2f6bfcf9ed1f2d2792fe6e819af88.

Saved-module axiom audit checks all 50 new public theorem declarations.
It uses #guard_msgs (whitespace := lax) to require exactly
[propext, Classical.choice, Quot.sound]; only whitespace is normalized.
Local mathematical hypotheses remain explicit parameters, even when the axiom check passes.

Preliminary audit runs were rejected by message-format checks (line wrapping, then a
long-command-line style warning); their axiom messages showed the standard axioms.
Those runs are not counted as successful audits.

The final saved-module guarded audit succeeded:
- Job: job_2rbMjEb-VSIDmGUo3IOPH3p45CJkARu5.
- Backend: bazel; verified=true; exit code 0; duration 57.680 seconds.
- Log: https://app.buildbuddy.io/invocation/8daaf880-5aa8-4868-a5c0-1baebf922dac .
- Code SHA-256: e5c6ac01fd567ccbc16effd821afadb576e869702bd0d7e7acd3994f4a8838a4.
- All 50 public theorems passed exact standard-axiom guards. No sorry/admit/custom axiom
  occurs in the seven new source modules.

The final publication gate is the server checkpoint for the complete //:RiemannResearch
target using Bazel/BuildBuddy. Its terminal job result and exact published commit accompany
the delivery. Scoped acceptance alone is not full-project acceptance.

## Complete new public declaration map

All namespaces have prefix RiemannResearch.RH and the module's basename.

| Module | Theorems |
|---|---|
| RH/QReciprocalFiniteCost.lean | `gram_posDef`; `minimizer_mem`; `minimizer_normal`; `cost_completion`; `minimum_value`; `minimizer_le`; `minimizer_unique`; `minimizer_mem_submodule`; `residue_minimizer_legal`; `residue_gram_posDef`; `cost_quadratic` |
| RH/QParetoCostTransfer.lean | `toPareto_D`; `paretoCost_physical`; `cost_identity`; `paretoCost_le_scaled_cost`; `scaled_cost_le_twice_paretoCost`; `cofinal_cost_bound_iff` |
| RH/QReciprocalCostCertificates.lean | `cost_eq_head_add_tails`; `headCost_le`; `reciprocal_tail_sq_le`; `cost_certificate`; `finite_residue_sequence_bound`; `finite_residue_cost_certificate` |
| RH/QReciprocalCofinalCost.lean | `mem_closure_of_cofinal_cost`; `mem_closure_iff_cofinal_cost`; `riemannHypothesis_of_cofinal_cost`; `riemannHypothesis_of_cofinal_canonical_energy`; `canonical_energy_diverges_of_not_RH` |
| RH/QSievePairingCertificates.lean | `sieve_pairing_identity`; `pairing_error_sq`; `mobiusPairing_tendsto`; `reciprocal_pairing_zero_iff`; `joint_qMean_sieve_error_sq`; `joint_qMean_zero_iff`; `mobiusPairing_eq_nonprime` |
| RH/QJointSieveForcing.lean | `block_pairing_energy`; `block_sieve_certificate`; `block_sieve_cancellation_iff`; `actual_middle_sieve_cancellation_iff`; `actual_middle_sieve_certificate` |
| RH/QReciprocalFullMinimizer.lean | `fullMinimizer_legal`; `exactHead_mem`; `full_minimum_value`; `fullValue_nonneg`; `fullValue_le_exactHead`; `fullValue_source_bound`; `fullValue_explicit`; `fullValue_global_sqrt_log`; `riemannHypothesis_of_cofinal_fullValue`; `riemannHypothesis_of_near_linear_fullValue` |

## Next arithmetic obligation

For the explicit inverse-Gram family, prove either the cofinal fixed-C bound or the
all-exponent near-linear bound above using complete signed Gram estimates. The finite
head plus two-tail certificate supplies a rigorous interface for such estimates.
Alternatively, prove actual middle-coupling cancellation in the signed composite sieve
sum, then separately discharge the remaining hypotheses of the chosen RH chain.

No step is marked as an unconditional proof of RH, a bounded inverse to D, or a new
analytic RH converse.
