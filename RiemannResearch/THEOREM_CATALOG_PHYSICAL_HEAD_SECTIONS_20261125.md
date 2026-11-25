# Physical head sections of the Pareto mean

Let `fiber N` be the legal mean-one vectors that equal one at physical sites 1 through N. Write κ(N) for the norm of its orthogonal minimizer and ∂ for the centered mean snake boundary. The physical cutoff N and the conductor-window cutoff B serve different roles.

## Finite splittings and the limit

- [PhysicalHeadMixedInterpolation.lean](RH/PhysicalHeadMixedInterpolation.lean) proves fresh-prime packet reversal on a head, exact finite mixed interpolation, and approximation in a mixed translate preserving a prescribed head.
- [PhysicalHeadSnakeSections.lean](RH/PhysicalHeadSnakeSections.lean) identifies the stage kernel, constructs a splitting of every stage row, and identifies the intersection of the stages with the legal constants. The limiting mean is surjective exactly when ∂ vanishes.
- For every mean-one legal lift v with unit head through N, `head_tail_boundary_pairing` identifies its residual pairing with the physical tail of the centered defect as ‖∂‖². Any finite uniform norm bound for such lifts over all N forces ∂ = 0.

## Complete section costs

- [PhysicalHeadFiniteMinimum.lean](RH/PhysicalHeadFiniteMinimum.lean) realizes every physical head in the mixed conductor window B = 2(N+1)² using floor-matrix columns. The infimum of finite-window section norms in any fixed legal mean-one translate equals κ(N).
- [PhysicalHeadSectionGrowth.lean](RH/PhysicalHeadSectionGrowth.lean) proves that RH gives κ(N) = 1 for every N. A right zero ρ with real part σ forces κ(N)² ≥ 1 + (2σ−1)(N+1)^(2σ−1)/|ρ|².
- [PhysicalHeadSectionLog.lean](RH/PhysicalHeadSectionLog.lean) proves `parity_cofinalLogSections_iff_rh`. For the normalized parity seed g = J₂/log 2, RH is equivalent to existence of cutoffs Nⱼ → ∞ and finite mixed corrections mⱼ with g+mⱼ in the unit-head fiber and log‖g+mⱼ‖/log(Nⱼ+1) → 0.

**Open.** Construct such a cofinal family with subpolynomial complete Pareto norm unconditionally. The finite interpolation theorem controls the head and the conductor window. The growth criterion concerns the norm on the entire positive axis.

## Algebras of the physical-head sections

- [PhysicalHeadStageAlgebra.lean](RH/PhysicalHeadStageAlgebra.lean) equips the actual stage with a scoped commutative real algebra. The least-norm patch is its unit, the original Pareto mean is its augmentation, and the kernel ideal has square zero. The augmentation and mixed coordinate identify the algebra with the trivial square-zero extension.
- [PhysicalHeadStageAlgebraComparison.lean](RH/PhysicalHeadStageAlgebraComparison.lean) proves the signed product defect for ordinary inclusion and constructs the injective unital comparison that transports the unit. All ordinary adjacent stage inclusions preserve multiplication if and only if RH holds.
- [PhysicalHeadAlgebraSnake.lean](RH/PhysicalHeadAlgebraSnake.lean) computes the Mathlib snake map on the underlying additive rows. Its value at one is the quotient class of the product defect at the upper unit. Its squared quotient norm is κ(K)² − κ(N)².
- [PhysicalHeadPacketSquare.lean](RH/PhysicalHeadPacketSquare.lean) gives a finite mixed witness in each positive stage. Its physical pointwise square has positive Pareto mean and zero head, so it lies outside the stage.

**Open.** Prove ordinary multiplicativity at every adjacent physical-head stage. Transporting the section gives a unital embedding at every stage unconditionally.

## The infinite physical-head snake

- [PhysicalHeadProductSnake.lean](RH/PhysicalHeadProductSnake.lean) constructs the Mathlib connecting map for the product of the additive stage rows. With the differential given by the next entry minus the current entry, `productSnake_one` gives the class of the adjacent displacements. `stageCokernelEquiv` computes the legal-stage cokernel by quotienting the mixed cokernel by the span of this one class.
- [PhysicalHeadInfiniteBoundary.lean](RH/PhysicalHeadInfiniteBoundary.lean) proves that this class vanishes exactly under RH and exactly when the adjacent squared quotient norms are summable. Its finite squared norms telescope. They are sublinear in the cutoff and diverge when the class is nonzero.
- [PhysicalHeadLayerIsometry.lean](RH/PhysicalHeadLayerIsometry.lean) normalizes the successive physical directions to a Hilbert basis. Its coefficient isometry identifies the mixed space with scalar ℓ², and the stage kernels with the corresponding coordinate tails. `headLayer_hasSum` gives Parseval in the full Pareto norm.
- [PhysicalHeadSequenceCokernel.lean](RH/PhysicalHeadSequenceCokernel.lean) identifies the product cokernel with unrestricted physical sequences modulo the sequences of actual mixed vectors. The original centered quotient embeds into this cokernel and its boundary maps to the product boundary.
- [PhysicalHeadBoundaryCoordinates.lean](RH/PhysicalHeadBoundaryCoordinates.lean) identifies the same cokernel with unrestricted sequences modulo ℓ². `layerCokernel_boundary` sends the connecting class at one to the signed layer coefficients. `constant_layers_survive` shows that putting one unit in each layer gives a nonzero class even in the legal-stage cokernel. The arithmetic carry has vanishing Cesàro mean square, whereas the all-ones sequence has mean square one. `parity_capture_iff_summable_signedCarry` identifies the parity-capture endpoint with square summability.

**Open.** Prove square summability of this particular signed carry sequence. Equivalently, bound the partial sums of its squared coefficients uniformly over all physical cutoffs.

## Computing mixed parity capture

[MixedParityDigammaParseval.lean](RH/MixedParityDigammaParseval.lean) gives the signed scalar recursion `digammaRow`. Every row uses rational digamma nodes and earlier mixed conductors. `parity_projection_norm` computes the unnormalized Pareto norm of the mixed projection of J₂ as the square root of a convergent series. `physical_head_coefficient` gives the orthogonal change of coordinates to the physical-head basis. `first_digamma_term` and `second_digamma_term` give the initial contributions in conductor order.

**Open.** Identify the value of the convergent energy series with log 2 − (log 2)². Convergence of the capture series holds unconditionally.
