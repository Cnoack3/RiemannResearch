# Consecutive zeta ordinates: exact identities and conditional distribution laws

This development records the consecutive-pair deductions discussed on
2026-10-11. It keeps the finite signed identities primary and makes every
unproved analytic provider visible in the theorem types. No RH or simplicity
assumption, project-local axiom, placeholder proof, or novelty claim is added.

## Which consecutive pairs?

Chronological consecutive ordinates of actual zeta zeros, counted with
analytic multiplicity, are different from consecutive fractional parts after
sorting on a circle. Ordinary equidistribution alone does not give a
two-dimensional product distribution or a limiting nearest-neighbor gap law.
The diagonal-Haar result uses chronological order and vanishing average
displacement. The Marklof gap-window mechanism is formalized separately.

The `chronologicalList` construction in `ActualConsecutiveOrdinates` sorts
the existing actual zero copies below height T. Its length is exactly `Ncount 0 T`; all copies remain,
and arbitrary sums agree with the original actual-zero sums. The resulting
`cutoffOrdinate T j` is monotone and is padded with T once j reaches the count.
Thus its final gap is truncated at T. The exact endpoint-replacement identity
isolates the correction to any supplied next ordinate B; the Fourier correction
has norm at most 2. No theorem identifies an arbitrary B with the next zero.

The strict-order criterion is also retained: distinct ordinate copies in the
cutoff are equivalent to all zeros in that cutoff being critical-line and
simple, using the pre-existing actual-zero symmetry theorem. Strict ordering
is therefore not built into the construction.

## Exact phase transport

Write p_u(t) = exp(i u t), Δ_j = γ_{j+1} − γ_j, q = a+b, and
R_1(t) = exp(i t) − 1 − i t. For any c with b = cq, Lean proves

    Σ_{j<J} p_a(γ_j) p_b(γ_{j+1})
      = Σ_{j<J} p_q(γ_j)
        + c (p_q(γ_J) − p_q(γ_0))
        + Σ_{j<J} p_q(γ_j) (R_1(bΔ_j) − c R_1(qΔ_j)).

The final signed sum is bounded by
2 (b² + |c| q²) Σ Δ_j². For q ≠ 0 take c = b/q. This retains the
endpoint term before making an estimate. It applies to arbitrary finite
sequences, including the concrete multiplicity-preserving zeta cutoffs.

`ActualZeroOrdinate.cutoffPairSum_transport_eq` specializes this identity
to those cutoffs, and `cutoffOrdinate_phase_sum` identifies the diagonal sum
with the actual ordinate sum used by the existing FMZ development.

## Resonance and higher moments

For a = −b the pair mean is the gap characteristic function. Lean retains

    Σ_{j<J} exp(i b Δ_j)
      = J + i b (γ_J − γ_0) − (b²/2) Σ Δ_j²
        + Σ R_2(bΔ_j),

where R_2(t) = R_1(t) + t²/2 and |R_2(t)| ≤ 3 |t|³ globally. Defining
R_3(t) = R_2(t) + i t³/6 gives |R_3(t)| ≤ 4 |t|⁴ and the exact real identity

    Σ_{j<J} (1 − cos(b Δ_j)) = (b²/2) Σ Δ_j² − Σ Re R_3(bΔ_j).

No bounded-gap hypothesis is used for these Taylor estimates. The constants
are convenient global bounds, not claimed optimal.

`ConsecutivePhaseAsymptotics` accepts triangular rows γ(T,j), counts J(T),
and any rate r(T). It proves nonresonant transfer of a supplied one-point
main term if E₂/J = O(r) and 1/J = O(r). At resonance it retains the
exact drift i b (γ_J−γ_0)/J, and the square-retaining version bounds only
the remaining cubic moment. Zeta rates such as log(T)⁻² require actual
providers of the relevant moment and count estimates. The drift has not
been silently replaced by an asymptotic expression.

## Continuous and gap-weighted laws

`ContinuousPairCoalescence` proves that continuous pair tests on any compact
metric space are insensitive in mean to a displacement whose average
distance tends to zero.

`OrdinateDiagonalHaar.continuous_pair_diagonal_haar` combines this with scalar
Fourier cancellation for a monotone infinite sequence γ. It covers a moving
lag ℓ_n when

    ℓ_n (γ_{n+1+ℓ_n} − γ_0)/(n+1) → 0.

For every nonzero α and every continuous F on the circle squared, the mean
of F(αγ_j, αγ_{j+ℓ_n}) tends to the integral of F(x,x). This is diagonal
Haar, not product Haar. The theorem is an abstract sequence theorem: the
finite actual-zero sorting construction is not a proved global enumeration.

The weighted module proves a different law from

    height_n → infinity,
    (γ_{n+1}−γ_0)/height_n → 1,
    Σ_{j≤n} Δ_j² / height_n → 0.

Nonnegative weights Δ_j/height_n then give Haar convergence of every continuous
starting-phase test. This part does not assume ordinary Fourier cancellation.
After adding ordinary Fourier cancellation, the centered normalized next gap
has zero limiting correlation with every continuous phase test. A continuous
selection function with nonzero Haar integral has selected normalized-gap mean
tending to one. These are precise test-function conclusions; a joint weak
limit, a measure disintegration theorem, or full gap/phase independence is not
asserted.

## Marklof stop-loss and empty-window mechanism

`ZeroOrdinateStopLoss` proves exact finite and marked identities using

    max(g−L,0) = g − min(g,L).

It includes monotonicity, nonnegativity, tail bounds, the complete centered
marked defect, and its zero-threshold first-moment reduction.
`ZeroOrdinateGapWindows` proves that starting positions of a window of length
L inside a gap (a,b) have Lebesgue length max((b−a)−L,0). The union over
finitely many disjoint gaps gives exactly the stop-loss sum, with all scaling
factors retained. Strict endpoints avoid overlap and have no length cost.

`ActualConsecutiveGapWindows` applies this geometric identity to the sorted
actual-zeta gaps, including the final truncated interval to T. These are
finite linear-gap identities. Circular wraparound and sorting modulo one are
separate constructions.

Factorization of the positive-threshold marked stop-loss transform is still
an open research target in this development. Its L=0 consequence and first
moment independence do not establish it.

## Actual-zeta analytic obligation ledger

| Result | Checked deterministic content | Domain-specific obligations |
| --- | --- | --- |
| Actual chronological cutoff sums | Sorting, multiplicities, moments, boundaries, signed phase transport | None |
| Actual gap-window geometry | Disjoint chronological intervals and exact scaled stop-loss length | None |
| Actual rational consecutive mode divided by T | Transfers the existing actual rational FMZ mode | **Open:** provider of `UniformSelbergDensity (1/4)`; **Open:** provider of `VanishingCutoffGapEnergy` |
| Continuous diagonal Haar and controlled lags | Abstract full continuous-test transfer | **Open:** complete actual global-sequence or triangular-row specialization and its scalar cancellation provider |
| Zeta log-scale pair expansion | Generic `IsBigO` transport with exact drift and signed moments | **Open:** actual Fujii moment/rate providers and required one-point rate |
| Gap-weighted Haar and selected mean | Abstract dense-test, weighted Fourier, and mean theorems | **Open:** actual enumeration/row assembly and gap-energy provider |
| Positive-threshold marked factorization | Exact finite defect and L=0 reduction | **Open:** substantive factorization/independence theorem |

The results with unresolved domain-specific premises are **conditional
research reductions**. Selberg density and the required Fujii gap-moment
estimates are classical unconditional mathematics on paper; their Lean
providers are not included here. A transitive axiom report does not discharge
these local hypotheses. Nothing here proves RH or a universal gap distribution.

## Provenance and verification

The supplied source is Jens Marklof, *Distribution modulo one and Ratner's
theorem*, in *Equidistribution in Number Theory, An Introduction*, Springer
(2007), especially Section 2.1, pp. 220–222. It supports the gap-window and
stop-loss interpretation. The phase identities are the user-discussed
consecutive-ordinate argument formalized here, with no claim of literature
novelty. The existing Ford–Zaharescu/FMZ modules support the one-point
arithmetic input; A. Ivić, arXiv:1610.01317, equation (1.2), records the
classical Fujii gap moments used as motivation.

All modules are exported through `RiemannResearch.lean`. Final acceptance is
the server checkpoint's audit and affected-module/aggregate validation of
the exact published source. Development checks alone do not certify the
whole repository. The checkpoint identifier and commit are reported with
delivery.

The combined twelve-module development check passed in server job
`job_riR-u3ilrtgsrpgpCL1SnuXKEBcBWNTR`. Six selected transitive axiom
reports contain only `propext`, `Classical.choice`, and `Quot.sound`.
This does not discharge the analytic premises listed above.
