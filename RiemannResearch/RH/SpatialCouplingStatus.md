# Spatial arithmetic DPP coupling: formalization boundary

Base: 462dc26, including 7a6456b. Source: Russell Lyons,
*Determinantal probability measures*, https://arxiv.org/abs/math/0204325,
Theorems 6.2 and 7.1 for projection-law stochastic domination, and the
discussion of Strassen coupling. These references support the mathematical
route, not a claim that their proofs have been formalized here.

## What the new code establishes

- Compact probability-measure limits assemble all finitely satisfiable clopen
  probability constraints. The witnesses need not be projectively consistent.
- A finite square witness retains every determinantal row correlation and has
  zero probability of any adjacent-time disappearance.
- Such witnesses for every finite square imply a single probability measure
  carrying every arithmetic DPP stage.
- Taking each path's running union changes nothing almost surely and makes
  inclusion hold pointwise for every path.
- Conversely, restricting an actual coupling gives the finite square witnesses.
  This makes the residual transport obligation exact.
- Every supplied full coupling has, at every site k,
  P(k never enters) = 1 - limitingKernel k k.
  Thus summability of (k+1) times these probabilities is precisely the existing
  weightedLimitingHole summability hypothesis.

## What remains open in Lean

SpatialWindowFeasible is a proposition whose provider is NOT proved here.
The unconditional full spatial coupling is therefore NOT completed.

The missing finite result is supported monotone transport for the genuine
projection DPP laws. Kernel positive-semidefinite order and coordinatewise
vacancy monotonicity alone do not provide a joint determinantal coupling.
Finite rank does not make the original arithmetic site set finite.
Restricting a projection to a finite site window gives a positive contraction,
usually not a projection.

One concrete route: for nested orthonormal column matrices U and [U,v],
compare the squared minors indexed by r- and (r+1)-subsets. A signed
inclusion matrix implementing wedge-by-v gives the weighted Hall inequalities
for every family of subsets. A finite supported transport theorem then
constructs adjacent couplings; finite gluing supplies each window witness.
The compactness theorem above discharges the passage from these witnesses
to countably many times and sites. The signed-minor/Hall and finite-transport
proofs are still required; they are not axioms or hidden instances.

## Exactly what this adds toward RH

With K_infinity the fixed arithmetic limiting kernel,

  sum_k (k+1) P(k never enters) < infinity  ==>  RH.

No choice of coupling can improve these one-site probabilities: they depend
only on K_infinity. Coupling supplies a common pathwise interpretation and
access to joint trajectory events, not a new vacancy estimate.

If zeta(s)=0 with 1/2 < Re(s) < 1, the established all-site obstruction gives

  (k+1) P(k never enters) >= c(s)/(k+2),

where c(s) = (2 Re(s)-1) Re(s)^2 / |s|^2 > 0.
Hence the weighted sum diverges. The formal implication retains exactly
this arithmetic boundary.

No weighted summability, zero vacancy, density, or RH proof is asserted.
An unweighted almost-sure finiteness statement about holes would not by
itself imply the weighted expectation bound. Likewise the identification of
a monotone union with its limiting DPP does not assert that the union is all
sites. An RH-to-residue-density converse is not assumed.
