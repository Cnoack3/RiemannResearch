# Pareto–CRT chat formalization

This development formalizes the mathematical research recorded in
[RH_CRT_Packet_Research_2026-09-09.md](RH_CRT_Packet_Research_2026-09-09.md).
It extends the existing RiemannResearch Lean 4/mathlib project. It does not
prove the Riemann Hypothesis or assume the desired global energy bound.

Principal Lean sources: [concrete recursion](OptimizedPacketRecursion.lean),
[full CRT minimum](ParetoExactHeadCRT.lean),
[arithmetic cancellation](RoughProfileCancellation.lean), and
[finite-seed Mellin obstruction](FiniteSeedMellinObstruction.lean).

## Main target and exact logical boundary

The actual weighted Hilbert space has squared norm
\(\sum_{k\ge1} f(k)^2/[k(k+1)]\), with a zero anchor at coordinate zero.
The finite legal space uses every positive integer dilation of the two
residue seeds \(r_2,r_3\). The target is the constant one on positive coordinates.

`OptimizedPacketRecursion.lean` constructs a concrete finite legal sequence
`optimizedPacketIterate`. Its legality, mean one, exact initial coordinates,
and full signed energy telescope are proved. `OptimizedPacketUniformBound`
is the remaining proposition that its full squared norms are uniformly bounded.
It has no asserted proof. The associated membership theorem assumes exactly
that bound and obtains membership of one in the actual closed legal space.

The earlier `Analysis.BoundedInterpolation` and `ThresholdBoundedInterpolation`
modules supply the projection/Pythagoras argument. Bounded exact interpolation
gives closure membership; bounded minimum interpolation energies give strong
convergence. Pythagoras does not provide the bound. The new
`ThresholdInterpolationCompleteness` also shows that target membership and
integer-dilation invariance force the legal closure to equal the entire space.

The classical RH criterion remains a separate formalization bridge. An
informal implication through the full-residue criterion is recorded in the
research note; no unproved criterion is silently installed as a Lean axiom.

## Exact constructions and calculations

| Research content | Lean modules | Mathematical scope |
|---|---|---|
| Infinite CRT tail weights, head mass, mixed defect, inverse Gram matrix, attained Schur minimum | `ParetoExactHeadCRT` | Actual infinite progression weights; positive definiteness and inverse construction from independent columns; empty control families are included. |
| Nearby-dilation Gram decomposition and logarithmic limits | `NearbyDilationGram`, `Analysis.PeriodicHarmonicMean`, `NearbyDilationAsymptotic` | Complete tail retained in the exact formula; bounded harmonic remainder; fixed periodic seeds. |
| Residue jump covariance and harmonic identity | `ResidueJumpCovariance`, `ResidueNearbyAsymptotic`, `OptimizedResidueHarmonic` | Exact common-period covariance `gcd(a,b)-1` and exact harmonic cutoff formula. |
| Improved seeds and local optimality | `OptimizedResiduePackets`, `OptimizedResidueIdentities`, `SmoothResidueJumpOptimality` | Concrete phi/theta, exact square completions, and the sharp one-half coefficient in the stated fixed-seed class. |
| Actual Hilbert packet vectors and dyadic substitution | `OptimizedResidueHilbert`, `OptimizedResidueSubstitution` | Finite legal constructions, head support, means, nonzero correction direction, exact remainder norm and closure equality. |
| Full Gram and transfer asymptotics | `OptimizedResidueAsymptotic`, `OptimizedCorrectionNormAsymptotic`, `OptimizedTransferAsymptotic` | Actual infinite norms and mixed inner products; the transfer energy divided by log tends to one-half. |
| Schur repair and concrete recursion | `LinearAlgebra.OrthogonalSchurRepair`, `ParetoPacketCoordinates`, `OptimizedPacketRecursion` | Attained one-direction minimum and exact updates, with all mixed terms and signs present. |
| Complete coordinates and sharp transfer | `ParetoHaarCoordinates`, `LinearAlgebra.SchurTransferSharpBound`, `ParetoSchurTransfer` | Complete Hilbert-basis isometry, arithmetic coordinates, causal orbit identity, and sharp constant on the permitted future subspace. |
| Earlier process analogy | `ParetoTailMartingale` | Actual physical values, means, covariance `min(N,M)`, and exact head-energy obstruction. See the qualification below. |
| Forced charges and component cancellation | `ExactHeadCharges`, `ComponentHeadEnergy`, `RoughComponentHead`, `RoughComponentExhaustion` | Divisor reconstruction, automatic exhaustion of actual finite legal components, and the four-floor profile; every ordered cross term retained. |
| Fixed original-generator prefix obstruction | `FixedPrefixIncidence`, `SmoothHeadBoundaryFlux`, `SmoothPrefixFlow`, `SmoothPrefixDivergence` | Exact incidence and boundary flux, exponential energy lower bounds, and failure of uniform boundedness for this fixed-prefix construction. |
| Diagonal asymptotics | `RoughProfileBounds`, `RoughDiagonalLimit`, `NumberTheory.SquarefreeEulerSeries`, `RoughDiagonalEvaluation` | Exact floor defects, summable domination, Cesaro limit, full rough-core series, and its exact value `6/(5*pi^2)`. |
| Mandatory arithmetic mixed cancellation | `RoughProfileCancellation` | The actual signed rough profiles sum to one on every finite head; their full ordered mixed energy is exactly `N/(N+1)-D_N`, and its quotient by `N` tends to `-6/(5*pi^2)`. |
| Mellin functional and quantitative obstruction | `ParetoMellinFunctional`, `ParetoMellinDilation`, `ParetoMellinHeadObstruction` | Actual infinite integral, continuity, dilation law, target value, and exact-head tail-energy lower bounds. |
| Arithmetic Mellin identity | `ParetoResidueMellinArithmetic`, `ParetoMellinHolomorphic`, `ParetoResidueMellinContinuation`, `ArithmeticMellinIdentity` | Partial summation, actual holomorphy and continuation, then the finite legal combination identity. |
| Finite-seed obstruction | `Analysis.AnalyticZeroPersistence`, `Analysis.FiniteExponentialZeros`, `ArithmeticMellinSymbolZeros`, `FiniteSeedMellinObstruction` | Compact phase recurrence and zero persistence yield a nonreal arithmetic-symbol zero; the Mellin functional separates one from a single finite legal seed's dilation closure. |

Names in the table denote `RiemannResearch.RH` modules unless another subject
directory is indicated. The module sources state every hypothesis explicitly.

In particular, the arithmetic cancellation calculation retains the exact
identities before passing to limits:
\[
M_N=\frac{N}{N+1}-D_N,\qquad
\frac{D_N}{N}\longrightarrow\frac{6}{5\pi^2},\qquad
\frac{M_N}{N}\longrightarrow-\frac{6}{5\pi^2}.
\]
Here `M_N` includes every ordered pair of distinct components with the
original Pareto weights. It is not an unweighted CRT replacement.

## Wiener analogy and zero countability

The discrete process has some covariance identities shared with Brownian
motion. These identities do not establish Gaussian increments or independent
increments. `ParetoTailMartingale` does not claim a bundled stochastic-process
martingale instance. It proves the stronger relevant deterministic identity
\(\|F\|^2=N+\|F-Y_N\|^2\) for mean-zero exact-head vectors, which rules out
uniform boundedness within that class. The minimum interpolants and the
mean-one packet recursion are separate constructions.

Zeta-zero countability is already proved in `CountableZetaDetector`, notably
`RiemannResearch.RH.zeta_strip_zeros_countable`. Countability alone provides
neither the required uniform bound nor RH. The new zero-persistence proof uses
the inverse maximum-modulus principle; it does not misattribute countability
to Hurwitz's theorem.

## Scope of completion

The global uniform-bound claim remains open. Local packet optimality and the
logarithmic transfer limit do not prove that bound. The research note's decimal
experiments are preserved as experiments, without invented Lean certificates.
The diagonal limit's exact Euler-product evaluation is proved. Automatic
finite component exhaustion also supplies the geometric closure condition.

All included proof sources must pass the project checkpoint before publication.
The public sources contain no `sorry`, `admit`, project-local axiom, or unsafe
proof shortcut. The final checkpoint supplies the validation and publication
receipt. Development diagnostics and batch-composition scripts are not exports.
