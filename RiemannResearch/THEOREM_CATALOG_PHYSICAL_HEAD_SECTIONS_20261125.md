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
