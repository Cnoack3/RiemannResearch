import RiemannResearch.RH.DyadicTentMellinCoefficients
import RiemannResearch.RH.DyadicFourierBoundaryEnergy
import RiemannResearch.RH.DampedMobiusCoefficients
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Concrete remaining Fourier and uniform arithmetic targets

Source: `FourierBridgeUniformSignedEnergy20260910.md`, September 10, 2026,
Sections 5–9. The phase, Fourier coefficients, normalization, arithmetic
coefficients, and Hilbert remainder below are the actual objects used in the
research project. Mathlib's `riemannZeta` supplies the complex zeta function.

The specification `DyadicSignedFourierBridge` has an unconditional provider
in `DyadicArithmeticFourierBridge`. The propositions
`DyadicUniformSignedFourierEnergyBound`, `ClassicalQuantitativeMertensBound`,
and `DyadicUniformSignedArithmeticDiscrepancyBound` remain unproved analytic
targets, not axioms or theorem providers. The theorems below establish
conditional equivalences and consequences; the downstream arithmetic bridge
discharges the Fourier premise, but no uniform energy bound or RH is asserted.

For the mathematical Mertens input, see E. S. Lee and N. Leong,
https://arxiv.org/abs/2208.06141v4 (statement and proof of quantitative
unconditional bounds for the Mertens function). This citation supports the
ordinary analytic input, not a claim that its proof is formalized here.
-/

namespace RiemannResearch.RH.Pareto

open scoped BigOperators
open RiemannResearch.Analysis
noncomputable section

/-- The zero mode is omitted before evaluating the zeta multiplier. -/
abbrev DyadicNonzeroFourierFrequency := {h : ℤ // h ≠ 0}

/-- The actual triadic phase on the dyadic logarithmic frequency lattice. -/
def dyadicTriadicFourierPhase (h : ℤ) : ℂ :=
  Complex.exp (Complex.I * (dyadicLogFrequency h : ℂ) * (Real.log 3 : ℂ))

/-- The exact signed zeta-ratio factor. The normalization is the project's
actual real Dirichlet-series normalization; it is not replaced by a free
parameter or by an independently postulated complex normalization. -/
def dyadicSignedZetaRatio (ε : ℝ) (h : DyadicNonzeroFourierFrequency) : ℂ :=
  (dyadicRegularizationNormalization ε : ℂ) *
      riemannZeta (1 - Complex.I * (dyadicLogFrequency h.1 : ℂ)) /
      riemannZeta (1 + (ε : ℂ) - Complex.I * (dyadicLogFrequency h.1 : ℂ)) - 1

/-- The full Fourier multiplier retains the exact Abel numerator. -/
def dyadicSignedFourierMultiplier (ε : ℝ)
    (h : DyadicNonzeroFourierFrequency) : ℂ :=
  dyadicSignedZetaRatio ε h *
    abelCancellationMultiplier (triadicDampingRatio ε) (dyadicTriadicFourierPhase h.1)

/-- The actual Mellin coefficient times the complete signed arithmetic
multiplier. The coordinate `i` corresponds to the paper's `ell = i + 1`. -/
def dyadicSignedFourierTerm (ε : ℝ) (i : ℕ)
    (h : DyadicNonzeroFourierFrequency) : ℂ :=
  dyadicTentMellinCoefficient i h.1 * dyadicSignedFourierMultiplier ε h

/-- Actual Fourier bridge specification: each scalar series must converge to the
already identified boundary coefficient of the actual arithmetic remainder.
`HasSum` explicitly excludes reliance on a default value of an unsummable
`tsum`. The proposition covers every positive damping and has the proved
provider `dyadicSignedFourierBridge_proved` in DyadicArithmeticFourierBridge. -/
def DyadicSignedFourierBridge : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ i : ℕ,
    HasSum (dyadicSignedFourierTerm ε i)
      (dyadicNormalizationBoundaryCoefficient ε i : ℂ)

/-- Unproved uniform bound for the complete signed Fourier energy. The same
constant bounds every finite set of boundary coordinates and every admissible
damping. Row convergence is included so this target cannot be discharged by
the default value of a divergent `tsum`. -/
def DyadicUniformSignedFourierEnergyBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
    (∀ i : ℕ, Summable (dyadicSignedFourierTerm ε i)) ∧
    (∀ s : Finset ℕ,
      (∑ i ∈ s, (1 / 4 : ℝ) * ‖∑' h, dyadicSignedFourierTerm ε i h‖ ^ 2) ≤ C)

/-- The requested actual quotient-remainder norm bound, as a concrete target. -/
def DyadicNormalizationRemainderUniformEnergyBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
    ‖dyadicNormalizationRemainder ε‖ ^ 2 ≤ C

/-- Under the actual Fourier bridge, the inner scalar Fourier sums give the
complete norm of the actual remainder, including all mixed terms. -/
theorem dyadicNormalizationRemainder_norm_sq_eq_actual_fourier
    (hbridge : DyadicSignedFourierBridge) {ε : ℝ} (hε : 0 < ε) :
    ‖dyadicNormalizationRemainder ε‖ ^ 2 =
      ∑' i : ℕ, (1 / 4 : ℝ) * ‖∑' h, dyadicSignedFourierTerm ε i h‖ ^ 2 := by
  exact dyadicNormalizationRemainder_norm_sq_eq_fourier_of_hasSum
    hε (dyadicSignedFourierTerm ε) (hbridge ε hε)

/-- Concrete uniform Fourier energy implies the actual uniform remainder
bound once the actual Fourier identification is supplied. -/
theorem dyadicNormalizationRemainderUniformEnergyBound_of_fourier
    (hbridge : DyadicSignedFourierBridge)
    (henergy : DyadicUniformSignedFourierEnergyBound) :
    DyadicNormalizationRemainderUniformEnergyBound := by
  rcases henergy with ⟨C, hC, henergy⟩
  refine ⟨C, hC, ?_⟩
  intro ε hε hhalf
  rw [dyadicNormalizationRemainder_norm_sq_eq_actual_fourier hbridge hε]
  have hs := dyadicNormalizationFourier_energy_summable_of_hasSum
    hε (dyadicSignedFourierTerm ε) (hbridge ε hε)
  exact le_of_tendsto hs.hasSum
    (Filter.Eventually.of_forall (henergy ε hε hhalf).2)

/-- Conversely, the actual norm bound controls every finite boundary set in
the exact Fourier representation. There is no frequency-diagonal substitute. -/
theorem dyadicUniformSignedFourierEnergyBound_of_remainder
    (hbridge : DyadicSignedFourierBridge)
    (henergy : DyadicNormalizationRemainderUniformEnergyBound) :
    DyadicUniformSignedFourierEnergyBound := by
  rcases henergy with ⟨C, hC, henergy⟩
  refine ⟨C, hC, ?_⟩
  intro ε hε hhalf
  refine ⟨fun i => (hbridge ε hε i).summable, ?_⟩
  intro s
  have hs := dyadicNormalizationFourier_energy_summable_of_hasSum
    hε (dyadicSignedFourierTerm ε) (hbridge ε hε)
  calc
    _ ≤ ∑' i : ℕ, (1 / 4 : ℝ) * ‖∑' h, dyadicSignedFourierTerm ε i h‖ ^ 2 :=
      hs.sum_le_tsum s (fun i _ => by positivity)
    _ = ‖dyadicNormalizationRemainder ε‖ ^ 2 :=
      (dyadicNormalizationRemainder_norm_sq_eq_actual_fourier hbridge hε).symm
    _ ≤ C := henergy ε hε hhalf

/-- With the exact scalar bridge, the proposed Fourier bound is equivalent
to the actual complete quotient-remainder bound. Neither is assumed proved. -/
theorem dyadicUniformSignedFourierEnergyBound_iff_remainder
    (hbridge : DyadicSignedFourierBridge) :
    DyadicUniformSignedFourierEnergyBound ↔
      DyadicNormalizationRemainderUniformEnergyBound :=
  ⟨dyadicNormalizationRemainderUniformEnergyBound_of_fourier hbridge,
    dyadicUniformSignedFourierEnergyBound_of_remainder hbridge⟩

/-- The two concrete analytic providers discharge the four actual norm
obligations in the existing regularization program. This theorem retains
both providers as hypotheses and does not claim they have been constructed. -/
theorem dyadicRegularized_norm_obligations_of_actual_fourier
    (hbridge : DyadicSignedFourierBridge)
    (henergy : DyadicUniformSignedFourierEnergyBound) :
    DyadicRegularizedSeriesSummable ∧ DyadicRegularizedNormBound ∧
      DyadicTailRegularizedSeriesSummable ∧ DyadicTailRegularizedNormBound := by
  rcases henergy with ⟨C, hC, henergy⟩
  apply dyadicRegularized_norm_obligations_of_fourier_energy
    dyadicSignedFourierTerm (fun ε hε _ i => hbridge ε hε i) C hC
  intro ε hε hhalf s
  exact (henergy ε hε hhalf).2 s

/-- The ordinary Mertens function on real cutoffs, with integer terms
`1 <= n <= x`. At every `x >= 1`, the atom at one is included. -/
def classicalMertensFunction (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (Nat.floor x), (ArithmeticFunction.moebius (n + 1) : ℝ)

/-- The classical unconditional quantitative Mertens estimate required by
the ordinary proof. This is a proposition definition, not its Lean proof. -/
def ClassicalQuantitativeMertensBound : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ x : ℝ, 1 ≤ x →
    |classicalMertensFunction x| ≤
      C * x * Real.exp (-c * Real.sqrt (Real.log (2 * x)))

/-- The exact continuous compensator residue. -/
def dyadicSignedArithmeticPoleResidue (ε : ℝ) : ℝ :=
  (1 - triadicDampingRatio ε) / Real.log 3

/-- The exact discrepancy for the actual signed coefficients. The measure
starts at one, inclusively, so the compensator is `kappa * (x - 1)`.
Replacing it by `kappa * x` changes the retained endpoint constant. -/
def dyadicSignedArithmeticDiscrepancy (ε x : ℝ) : ℝ :=
  (∑ n ∈ Finset.range (Nat.floor x),
    normalizedSignedCoefficient ε (dyadicRegularizationNormalization ε) (n + 1)) -
    dyadicSignedArithmeticPoleResidue ε * (x - 1)

/-- Uniform discrepancy needed for the compensated shell argument. The
implication from `ClassicalQuantitativeMertensBound` through weighted partial
summation and the hyperbola decomposition remains a formal proof obligation. -/
def DyadicUniformSignedArithmeticDiscrepancyBound : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
    ∀ x : ℝ, 1 ≤ x →
      |dyadicSignedArithmeticDiscrepancy ε x| ≤
        C * x * Real.exp (-c * Real.sqrt (Real.log (2 * x)))

end
end RiemannResearch.RH.Pareto
