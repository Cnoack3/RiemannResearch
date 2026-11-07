# Full-conductor dilation and projection audit, November 2026

## Established finite and Hilbert identities

Module: `RiemannResearch/RH/QFloorDilationEnergy.lean`.
The following additions concern the actual inverse-square Q space and every
integer dilation m > 1, without a squarefree assumption.

- `qBlockWeight_lt`: each positive quotient block has mass strictly below Q(k)/m.
- `qBlockDefect_pos`: every positive block defect is strictly positive.
- `qBlockDefect_energy_summable`: the complete nonnegative energy defect is summable.
- `floorDilation_norm_sq_lt`: for nonzero f, ||T_m f||_Q^2 < ||f||_Q^2/m.
- `floorDilation_sharp_equality_iff`: equality in that bound iff f = 0.

These strengthen the existing weak upper estimate and exact defect identity.
They do not supply a uniform constant smaller than 1/m. They do not imply
that legal approximation error vanishes.

Source: user-requested full-conductor research audit; direct strict
inverse-square block comparison. No mathematical priority claim is made.
The initial coherent snippet passed server job
`job_mU_yRm8NjQrXSTs_Lxa0DDUDlUQRKfHl` (31.249 seconds);
these additions were published in commit 7ec9ee06cb5432a3e96597845f8780523ac2f433.
Their fresh verification is recorded below.

## Paper results, not new Lean certifications

The accompanying full-conductor manuscript develops exact P/Q Gram equations,
integrated Ramanujan changes of basis, full p-adic CRT, Q divisor Parseval, and
Mertens exact-head transfer for the full matched displacement.

In particular, the paper establishes:
RH iff liminf_m m dist_Q(d g_m,V)/(1+log m)^k < infinity, for each fixed k >= 0.
The argument uses localized residue pairing, the full exact-head correction,
and the actual full-family witness. Formalization of that proof is Open.

## Open obligations

- Formalize the remaining full-family product-distance asymptotic bridge (A5).
- Supply the named RH-to-natural-approximation provider wherever still explicit.
- Prove an actual quantitative regularity or tail bound for the full displacement.
- Do not substitute the squarefree displacement in these full-family statements.

## Full-conductor continuation: checked structure and conditional RH reduction

Source: the attached Full_Conductor_RH_Reproducibility_Supplement.zip and its
companion Full_Conductor_RH_Projection_Machinery.tex, 6 November 2026.
No mathematical priority claim is made.

The continuation adds 41 named theorems in five modules. The distinction
between proved implications and unproved bounds on the actual displacement
is essential.

### Full matched projections (agenda A1)

`RH/QFullDisplacement.lean` uses literally
`QFullResidueProjection.closure`, the closed span of every residue
`qResidue (i + 2)`. Its Pareto closure is the image of the same algebraic
dictionary under the sequence-preserving measure equivalence, followed by
closure. The two projections are not identified.

With r_Q = 1 - f_Q, r_P = 1 - f_P, d = f_Q - f_P, and
B h(n) = h(n)/(n+1), the module proves

- r_P = r_Q + d and d belongs to the full legal closure;
- w = B r_P - d is orthogonal to that full closure;
- zeta(2) <1,w>_Q = zeta(2) <r_Q,B r_Q>_Q + ||d||_P^2;
- zero witness mean forces r_Q = 0;
- d = Pi_Q(B r_P) = Pi_Q(B r_Q) + Pi_Q(B d).

The exact positive energy terms are retained.

### Reversed metric expansion and the remaining projected residual

Source: the user's simultaneous D/R expansion argument, 6 November 2026.
Here the source name B still denotes the reciprocal multiplier R(n)=1/(n+1);
it does not denote the invertible metric operator A* A.

The new module RH/QReciprocalMetric.lean constructs Df(n)=f(n)/n as a bounded
linear operator, retaining the anchored coordinate at zero. It proves

- D - B D = B;
- <Df,g>_P = zeta(2) <Bf,g>_Q;
- <f,g>_Q = (<f,g>_P + <Df,g>_P)/zeta(2).

For the actual full-conductor displacement, RH/QFullDisplacement.lean adds

- displacement_swapped_normal_equation:
  <D r_Q,v>_P = <d,v>_P for every v in the full legal closure;
- displacement_p_energy:
  ||d||_P^2 = zeta(2) <d,B r_Q>_Q;
- displacement_eq_zero_iff_projected_residual_eq_zero:
  d=0 iff Pi_Q(B r_Q)=0.

These are exact identities and an equivalence. They do not prove that d or
the projected reciprocal residual vanishes. Combining the two metric
expansions retains the positive displacement energy; setting the cross term
to zero would add the unresolved hypothesis.

The coherent source candidate passed job job_IFOy2iaN-CHmzokn9q6rEs7aaR2fadxc:
verified=true, exit code 0, server-reported 7.148 seconds. Its two principal
axiom reports contain only propext, Classical.choice, and Quot.sound.
This isolated check is distinct from the final project checkpoint.
The initial candidate had a rewrite-direction error and an incomplete
positivity tactic; both were repaired before this successful check.

Open: establish Pi_Q(B r_Q)=0 using additional arithmetic information, or
supply a bounded full-legal family v_j with B v_j -> B 1. Infinite CRT
coordinate approximation alone does not supply that Hilbert norm bound.

### Reciprocal invariance is an RH-strength hypothesis

Source: the user's positive-square-root/invariant-subspace question,
6 November 2026. The operator called R in the discussion is still named
QShiftedReciprocal.B in the source.

- displacement_eq_zero_iff_reciprocal_mem proves d=0 iff B d belongs to V.
- riemannHypothesis_of_reciprocal_displacement_mem concludes RH from that
  target-specific membership.
- riemannHypothesis_of_reciprocal_invariant concludes RH from B(V) subset V.

The proof retains the exact energy:
||d||_P^2 = zeta(2) <B d,r_Q>_Q.
If B d is legal, residual orthogonality makes this energy zero.

These are conditional research reductions. The membership and invariance
hypotheses remain Open; positivity and existence of a positive square root
do not establish them. No RH-to-density converse is newly formalized here.

The coherent candidate passed job job_RHEXto2B-em3eZmXeaMr7iN5n_yzkbUK:
verified=true, exit code 0, server-reported 33.074 seconds. The audited
declarations use only propext, Classical.choice, and Quot.sound.
This is an isolated source check, distinct from the final project checkpoint.

### Reciprocal compactness argument: checked limits and the missing defect bound

Source: the user's approximation/compactness argument, 6 November 2026.
New module RH/QFullReciprocalLimits.lean uses the actual full-conductor
displacement and the reciprocal operator QShiftedReciprocal.B.

- G_M -> d implies B G_M -> B d; B qOne is nonzero.
- B commutes with an orthogonal projection iff the subspace is B-invariant.
- Commutation at d is equivalent to d=0.
- d=0 iff B G_M - Pi_Q(B G_M) -> 0 for any G_M -> d.
- ||d||_P^2 <= zeta(2) ||r_Q||_Q
  (||B G_M - Pi_Q(B G_M)||_Q + ||G_M-d||_Q/2).
- Every reciprocal orbit converges to zero at rate 2^(-k), including an
  explicitly exhibited nonzero vector with nonzero first image.
- Full projection commutation, or the extra zero-defect limit, implies RH.

The new source does not prove the reciprocal operator compact in Lean.
Its compactness is an elementary paper result via finite-rank truncations,
and would not make its strong limit zero. The missing estimate concerns
the distance of B G_M back to V, not merely the norm or convergence of B G_M.

The coherent extended candidate passed job
job_M1rbJ2q8K8x_LwEBY_BvOQD5FZCxtxjV: verified=true, exit code 0,
22.802 seconds. All four audited declarations use only propext,
Classical.choice, and Quot.sound. This is an isolated source check;
publication uses a separate final project checkpoint. An earlier
triangle-inequality API error was repaired before this successful check.

### Isometric transport of distances, projections, and the RH defect

Source: the user's question comparing dist_Q(R G,V) with dist_P(G,A V),
6 November 2026. The cross-space isometry A is physical multiplication by
sqrt((n+1)/(zeta(2)*n)); it is not the sequence-preserving toPareto map.

RH/QParetoIsometricTransport.lean proves the physical formulas for A and
its inverse, then specializes Mathlib's isometry-distance and projection API:

- dist_Q(R G,V) = dist_P(A R G,A V);
- dist_P(G,A V) = dist_Q(A inverse G,V), with G the same physical sequence;
- Pi_(A V)^P = A Pi_V^Q A inverse;
- the transported projection defects have exactly the same norm.

RH/QFullIsometricTransport.lean retains the actual all-conductor closure.
The Q target 1 transports to A(1), not to the physical constant target 1.
For G_M -> d it proves d=0 iff the P projection defect of A R G_M from A(V)
tends to zero, and derives the conditional RH implication.

Open: prove this transported defect tends to zero for actual legal
approximants. The isometry does not identify A(V) with the original physical
V, does not identify the two original projections, and does not establish RH.

The coherent candidate passed job job_swWmStRRX9ZKVjzjs6UprHl9D1vWaCcX:
verified=true, exit code 0, 11.252 seconds. Four audited declarations
(the physical A formula, reciprocal distance transport, projection conjugacy,
and conditional RH implication) use only propext, Classical.choice,
and Quot.sound. The final project checkpoint separately validates the
persisted module split and imports.

### Exact errors and localized integer tests (agenda A2–A3)

`RH/QMobiusFloorError.lean` gives the actual Q defect's complete signed
floor expansion, including physical site zero, and its exact finite
Mertens hyperbola identity on and beyond the head. It reuses the proved
finite arithmetic identities rather than assuming a new Mertens provider.
The conductor-(N+1) correction is retained with its original sign.
The exact head and its full legal membership are already in
`QMobiusExactHead.exactHead_exact` and
`QMobiusExactHead.exactHead_mem_legalSpan`.

`RH/QFullLocalResiduePairing.lean` proves complete HasSum pairings against
every full annihilator and specializes the localized signed-charge estimate.
Its residue probe is any integer m > Y. Neither primality nor squarefreeness
of N+1 is required. The head cutoffs Y <= X and both complete absolute
charge tails remain explicit. The cheaper sign can be chosen independently.

### Cofinal harmonic criterion for the actual full displacement (agenda A4)

`RH/QFullCofinalHarmonic.lean` defines

H(X) = min_{sigma = +/-1} sum_{1 <= n <= X} max(sigma*d(n),0)/n.

It proves the following exact residual equivalence:

r_Q = 0 iff there exist B,C >= 0 with
H(X) <= C * (log X)^B at arbitrarily large integer X.

`riemannHypothesis_of_cofinal_harmonic_polylog` concludes Mathlib's
RiemannHypothesis from that explicitly stated harmonic budget.
There is no bounded-gap restriction. The sign may change at each cutoff.
No RH-to-natural-approximation converse provider is an input.

The proof uses the already checked generic charge theorem for an arbitrary
squarefree annihilator, after proving inclusion of the smaller dictionary
in the full one. A full annihilator annihilates the smaller dictionary.
The displacement and both projections remain the full-family objects;
they are never replaced by the squarefree displacement.

The module also proves r_Q = 0 iff d = 0, and, if r_Q is nonzero,
H(X)/(log X)^B tends to infinity for every fixed real B >= 0.
These are conditional reductions, not a proof of the actual harmonic budget.

### Optimal lower and upper floor-dilation constants

`RH/QFloorDilationSharpBounds.lean` defines

c_m = sum_{0 <= r < m} 1/(m+r)^2.

For every positive integer m and every f in the actual ambient Q Hilbert
space it proves

c_m ||f||_Q^2 <= ||T_m f||_Q^2 <= ||f||_Q^2/m.

`floorDilation_lower_bound_iff` characterizes every global lower energy
constant: a real c works for all f iff c <= c_m. The minimum ratio is
attained by the physical unit spike at site one.
`floorDilation_opNorm_eq_sharp` proves ||T_m|| = sqrt(1/m).
Unit spikes escaping to infinity give sharpness of the upper constant.
Together with the supplied strict theorem, the operator norm is unattained
by any nonzero f for m > 1. Injectivity is also proved.

These are ambient operator statements. They do not assert that the unit
spikes are legal, or that a legal projection error vanishes.

### Verification and computational evidence

- The supplied five declarations and the new full witness were freshly
  audited in job `job_4beldPE69GAVf4GimzRA6-uvxPQczirN`:
  verified=true, exit code 0, server-reported elapsed 193.156 seconds.
- The sharp bounds, local full pairing, and full cofinal RH implication
  passed job `job_S-BrAmRfbx_w1fB-tweiQaYohWQAP_iu`:
  verified=true, exit code 0, server-reported elapsed 473.615 seconds.
- The final added-source import and axiom audit is recorded in
  `job_u31l_NtZe4_VHb8pgEunXAGo1nQXB15u`: verified=true, exit code 0, server-reported elapsed 373.221 seconds.
- Axiom reports for the audited principal declarations contain only
  propext, Classical.choice, and Quot.sound. The harmonic bound in the
  theorem type remains an explicit substantive hypothesis.
- The archive's 22,214-byte QFloorDilationEnergy.lean matches the repository
  byte-for-byte; SHA-256:
  dfb5eec77fb528c976e71da3743d9b175885c35752a99e0e7c1503791360a82a.
- All nine archived numerical rows were reproduced exactly with the
  supplied NumPy/SciPy script. Maximum absolute discrepancy: zero.
  They remain double-precision diagnostics, not interval or Lean certificates.
- Wolfram independently evaluated the new lower constants for m=2,...,6;
  for example c_2=13/36. These computations support the formulas but do not
  replace the kernel proofs of the general statements.
- An initial 180-second import audit timed out; subsequent successful jobs
  supersede it. Temporary tactic and import errors were repaired.
  Request/transport time and the 60-second polling intervals are not kernel
  execution measurements. Workspace-opening latency was not separately
  measured. Final publication still requires the mandatory changed-source
  and aggregate-project checkpoint.

### What remains open

This does not complete the manuscript's sixty-task research agenda.

- A5: the full polylogarithmic product-distance asymptotic bridge is not
  newly formalized here. The exact local residue estimate and cofinal
  full-family harmonic criterion are now available as its checked inputs.
- A6 / J2 / J4 / J6: no bound on the actual full displacement's product
  distance, cheaper harmonic sign, or complete legal approximation error
  is established. Such a bound would finish an RH route.
- The manuscript's raw Ramanujan density proof, integration-space
  construction, and categorical full p-adic CRT isomorphism are not newly
  certified by this continuation.
- The analytic RH-to-natural-approximation provider remains open where
  existing iff packages take it explicitly. Nothing here silently
  discharges that provider.
- The L^(8/7) approximation input for the eighth-moment route is not supplied.
- Reproduction of a floating-point Gram solve is not an outward-rounded
  complete-Gram certificate.

For further work on A5, its paper argument can be simplified before
formalization: bound the cross term
m <B r_P, d g_m>_Q uniformly by ||r_P||_Q ||d||_Q, since
(n mod m)/(n+1) <= 1. For the finite-liminf polylogarithmic criterion this
uniform bound suffices; its convergence to zero is unnecessary.
The remaining steps are the actual full product-distance pairing and a
finite weighted Cauchy bound converting it to H(m-1), followed by A4.
This simplification is a paper observation, not a newly checked theorem.

More explicitly, put eta_m = dist_Q(d g_m,V) and
h_{m-1} = sum_{1 <= n < m} 1/n. For m >= 2 the paper calculation gives

4 H(m-1)^2 <= zeta(2) h_{m-1}
  (||r_P||_Q ||d||_Q + m ||w||_Q eta_m).

The nonnegative complete residue energy is bounded above by the bracket
using the exact witness pairing; its head bounds H by weighted finite
Cauchy-Schwarz. A cofinal bound m eta_m = O((log m)^k) would therefore
supply H(m-1) = O((log m)^((k+1)/2)) and feed the checked A4 theorem.
The finite estimate and this product-distance assembly are not yet
kernel-certified.

## Crossed distances and square-root correction: November 6 continuation

Source: Isometric_Transport_Lean_Handoff_2026-11-06.md, Section 5 and
priorities 1--5. Detailed statements and remaining obligations:
RH/CrossedDistanceContinuation20261106.md.

### Established identities and quantitative estimates

Three new modules: Analysis/OrthogonalDistanceBound,
RH/QParetoSquareRootEnergy, and RH/QFullCrossedDistances.

Let T=A^{-1}I, q(f)=<f,Tf>_Q, a(g)=dist_P(Ag,V_P),
b(g)=dist_P(Ig,A V_Q), and Delta(g)=||r_P||_P a(g)+||r_Q||_Q b(g).
Every displacement declaration uses the actual full-conductor residuals.

- signedTest_eq: F(g)=<Ir_P,Ag>_P-<r_Q,Tg>_Q=<d,Tg>_Q.
- inverseEnergy_lower/upper: sqrt(Z/2)||f||_Q^2 <= q(f) <= sqrt(Z)||f||_Q^2.
- two_distance_bound: sqrt(Z/2)||d||_Q^2 <= Delta(d).
- two_distance_trial_bound: the handoff's full linear approximation penalty.
- inverseEnergy_polarization: q(d)+q(g)=2F(g)+q(d-g), retaining all terms.
- quadratic_two_distance_bound:
  sqrt(Z/2)||d||_Q^2+q(g) <= 2 Delta(g)+sqrt(Z)||d-g||_Q^2.
- displacement_eq_zero_iff_crossed_membership:
  d=0 iff both Ad in V_P and Id in A V_Q.
- inversePhysical_square: T^2=Z(1-R).
- displacement_eq_zero_iff_second_inverse_mem: d=0 iff T^2d in V_Q.
- rootDefect=J=1-T/sqrt(Z), with its exact coordinate multiplier.
- rootDefect_norm_le_of_head_zero:
  ||Jf||_Q <= ||f||_Q/(2N+3) when the first N positive coordinates vanish.
- two_distance_head_certificate: explicit legal-correction certificates
  for a shared J-transformed head target, retaining the infinite remainder.

### Conditional research reductions

For G_M -> d, the combined budget and signed-test zero limits are each
equivalent to d=0. The RH implications conclude Mathlib RiemannHypothesis
from the corresponding explicit provider.

- Open: vanishing of both actual crossed distances, or their combined budget.
- Open: signed-test cancellation F(G_M)->0.
- Open: second-inverse membership T^2d in the full legal closure.
- Open: actual legal corrections with vanishing complete J-target errors.

No global invariance, first-inverse-to-second-inverse shortcut, or RH
conclusion without these providers is asserted.

The assembled modules and seven principal axiom reports passed
job_Odin6V3Y3pnftimYSpdTePhqM2miJeiF (verified=true, exit 0,
server-reported 20.679 seconds). Reports contain only propext,
Classical.choice, and Quot.sound. Publication additionally uses the
mandatory aggregate and changed-module checkpoint.

## Compact square-root corrections and explicit Gram fits: November 6 continuation

Source: CrossedDistanceLeanHandoff20261106.md. Detailed account and remaining
providers: RH/CompactCrossedCorrectionResearch20261106.md.

### Established

- QParetoSquareRootEnergy: exact rationalization of the J coefficient;
  rootDefect_norm_le_of_head_zero and both head certificates are strengthened
  from denominator N+2 to 2N+3, retaining every infinite tail term.
- QFullCrossedDistances: for legal g, a(g)=dist_P(A Jg,V_P) and
  b(g)=sqrt(Z) dist_Q(Jg,V_Q), with no identification of A(V_Q) with V_P.
- QParetoSquareRootCompactness: finite-rank J_N, operator error <=1/(2N+3),
  IsCompactOperator J, and bounded coordinatewise/weak convergence giving
  strong convergence JG_M -> Jf. The limit is not asserted to vanish.
- QFullCorrectionCertificates: both full inverse-Gram corrections,
  exact Schur values and completion identities, finite target pairings,
  and explicit matchedApprox N defined by two finite solves with target 1.
  matchedApprox_tendsto proves convergence to the actual full displacement.
- matched_head_certificate instantiates the complete strengthened certificate
  with those approximants and both optimal finite corrections.
- optimized_correction_budget_tendsto gives the actual crossed-budget limit
  for fixed legal targets; it does not give a zero-limit provider.

### Conditional research reductions

- QFullCompactCrossedDistances: legal norm-bounded approximants with coordinate
  limit d suffice for the budget-decay iff and RH implication.
  Open: vanishing of their complete crossed budget.
- QFullCrossedDistances: weak convergence determines the signed-test limit;
  an independently justified nonpositive limit implies d=0 and RH.
  Open: the arithmetic signed nonpositive-limit provider.
- Open: cofinal full correction-error decay, and T(Td) membership in V_Q.
  Compactness and finite-head matching do not discharge either condition.

Assembled-module verification and nine axiom audits succeeded in
job_M5yiY2OyEf3aD5ELvT--00J40dERKUWb (verified=true, exit 0,
server-reported 24.999 seconds). Only propext, Classical.choice, and
Quot.sound occur in those reports. Final publication additionally requires
and uses the source-audited aggregate checkpoint.

## Weak-star finite-head compactness and reciprocal residual-tail costs

Source: the user's weak-star compactness request, November 6, 2026.
Detailed proofs, exact hypotheses, and the remaining arithmetic tasks are in
RH/WeakStarReciprocalHeadResearch20261106.md.

### Established

- Analysis/BoundedWeakInterpolation transports Banach--Alaoglu through Riesz:
  a bounded sequence in a complete separable subspace has an ambient weak
  subsequence with limit in the same subspace and norm ball. Bounded finite
  feasibility of countably many linear tests is equivalent to simultaneous
  bounded feasibility. A continuous-linear-image coordinate version is included.
- QFullResidueProjection now explicitly exposes completeness and separability
  of the actual all-conductor legal closure.
- QFullHeadObstruction.mem_closure_iff_bounded_exact_heads: x belongs to the
  full closure iff all its finite heads admit finite legal interpolants with
  one uniform complete Q-norm bound. The reverse uses weak-star compactness.
- exists_finite_head_norm_obstruction supplies a finite dual witness for any
  proposed norm bound when x is outside the closure. Every increasing-head
  legal interpolation family then has norm tending to infinity.
- QFullReciprocalHeadTail.reciprocal_head_energy_identity: for a legal F_N
  matching the first N coordinates of R d,
  ||I d||_P^2 = Z <R d-F_N,r_Q-H_N r_Q>_Q, retaining both complete factors.
- residual_tail_norm_tendsto_zero is unconditional.
- reciprocal_head_norm_lower: if d is nonzero, tau_N=||r_Q-H_N r_Q|| is
  positive whenever such a repair exists, and
  ||F_N|| >= ||I d||_P^2/(Z tau_N) - ||R d||.

### Conditional research reductions

- displacement_eq_zero_iff_bounded_reciprocal_heads: d=0 iff all finite heads
  of R d admit uniformly bounded finite legal repairs. The consequent RH
  theorem leaves that norm bound explicit and Open.
- reciprocal_head_norm_tendsto_atTop: nonzero actual full displacement forces
  every such family of repair norms to tend to infinity.
- riemannHypothesis_of_repair_norm_tail_product permits unbounded repairs:
  ||F_N|| tau_N -> 0 suffices. The complete-error product criterion also suffices.
  Open: either product-decay estimate for the actual reciprocal-head repairs.
- QFullWeakHeadCorrections: uniformly bounded finite-head corrections h_N,k_N
  satisfying H_N T h_N=H_N Jd and H_N k_N=H_N Jd force d=0 and RH.
  Open: both uniform full-norm bounds. No identification of A(V_Q) with V_P
  or global reciprocal invariance is assumed.

The combined candidate containing all 28 new theorem declarations passed
job_G9PUjB9eFP-jR0EXaLsITvbe2D9crKOJ (verified=true, exit 0, 9.201 seconds).

The persisted modules and nine axiom audits passed
job_CN-XP_8VlGeCnueN-51fITbhAeY-q23n (verified=true, exit 0, 154.211 seconds).
Only propext, Classical.choice, and Quot.sound occur in those reports.
Publication additionally uses the mandatory source-audited aggregate and
changed-module checkpoint. RH and every actual norm/product provider remain Open.
