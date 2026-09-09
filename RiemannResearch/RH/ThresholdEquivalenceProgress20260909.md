# Two-seed Nyman–Beurling equivalence: verification progress, 9 September 2026

## Result

The complete requested equivalence is **not yet formalized**. The actual
approximation-to-RH direction is now proved:

```lean
theorem riemannHypothesis_of_twoSeed_closure
    (hmem : hilbertOne ∈ hilbertLegalClosure {2, 3}) : RiemannHypothesis
```

Namespace: `RiemannResearch.RH.Pareto`. File:
`RiemannResearch/RH/ThresholdRiemannHypothesis.lean`.
The closure is in the genuine original weighted Hilbert norm, the seeds are
2 and 3, every positive integer dilation is allowed, and the conclusion is
Mathlib's actual `RiemannHypothesis`. No assumed NB/RH bridge is present.

## Proved forward argument

A hypothetical zeta zero s with Re(s)>1/2 and s≠1 annihilates every legal
generator by the actual Mellin/zeta formula. The actual continuous Mellin
functional then annihilates the whole closed legal subspace. It evaluates
the target at 1/s≠0. Thus target membership excludes these zeros. The actual
zeta reflection theorem and the verified strip formulation discharge the
remaining half of the critical strip and the boundary/trivial-zero details.

The same functional estimate proves the full infinite weighted lower bound
`(2*s.re-1)/‖s‖² ≤ ‖hilbertOne-f‖²` for every closed legal vector at such a zero.
This supplies `arithmeticZeroObstruction : ArithmeticZeroObstructionTarget`.

The Gibbs RH consumers were updated to remove their obsolete
`hbridge : ThresholdRiemannHypothesisBridgeTarget` argument. They remain
conditional only on the actual unproved legal invariance/repair construction.

## Converse components proved in this continuation

- `ThresholdHilbertCocycle.lean`: the full positive-seed legal space equals
  the finite residue span; the exact dilation cocycle extends to actual
  Hilbert closures; adjoint defects of seed annihilators annihilate the full
  residue space. Full residue density forces the corresponding adjoint fixed
  equations, with the density assumption explicitly present.
- `ThresholdJointAdjointTail.lean`: absolute weighted-tail summability,
  exact mU(mn)=U(n) and iterated scaling, finite block and coordinate identities,
  the full tail-energy decomposition and its limit zero, and the genuine
  finite-cell Cauchy–Schwarz estimate with that tail-energy budget retained.
- `ThresholdTwoSeedConverse.lean`: full residue density plus genuine joint
  adjoint rigidity imply full two-seed density and hence target membership.
  Both analytic inputs remain explicit assumptions.

## Remaining actual providers

1. Strong Nyman–Beurling/Báez-Duarte converse, connected to the genuine
   residue space:
   `RiemannHypothesis → hilbertLegalClosure {n : ℕ | 0 < n} = ⊤`.
   No provider was found in the current project or available declaration search.
   The existing `ParetoNymanNorm.lean` supplies finite norm identification,
   not the analytic RH-to-density theorem.
2. Two-seed joint adjoint rigidity:
   every h fixed by the actual adjoints for 2 and 3 is `c • hilbertOne`.
   The paper's proof still needs the local L² limit with quantitative tail
   recovery, irrational logarithmic periods, and shrinking-cell recovery.
   Plain local L² convergence does not recover every discrete coordinate.
   The necessary quantitative form retains
   `C * 2^(-j) * E_floor(A*2^j)`; the tail-energy factor may not be dropped.

These are missing formalizations. This continuation neither refutes the
paper's ordinary proof nor claims that its analytic inputs are proved in Lean.

## Verification receipt

Combined candidate and eight-endpoint axiom audit:
`job_DXrpu24wJRaJBGY75WkvcSEGILysKdRo`.
Terminal state **succeeded**, `verified=true`, `exit_code=0`, 4.056 seconds.
Code SHA-256:
`e523b51148023ba5dc73b787ee69d9f84b8ca2440ed7c8d6fb9774b956b5abb0`.

All eight audited endpoints report only `propext`, `Classical.choice`,
and `Quot.sound`. This audit does not erase substantive hypotheses in
the conditional converse declarations. The saved-source checkpoint validates
the actual modules and reverse dependents before publication; publication is
established by its terminal receipt, not by this inlined-candidate check.

Source: Christian Noack, `RH_Two_Seed_Threshold.tex`, September 8, 2026,
Sections 2 and 4, and the actual Mellin providers derived from
`RH_CRT_Packet_Research_2026-09-09.md`, Section 9.
