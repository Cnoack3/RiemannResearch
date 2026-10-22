import RiemannResearch.RH.DyadicResidueFourierCocycle
import RiemannResearch.RH.DyadicRegularizationPhaseKernel

/-!
# The actual complete signed arithmetic Fourier bridge

Source: continuation of the user-provided
FourierResidueBridgeVerification20260911(1).md, September 11, 2026.
Exact successive-conductor cancellation is applied before absolute summation.
The actual projected Hilbert series, real normalization, zero mode and signed
comparison are retained. No estimate uniform in damping is asserted.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
noncomputable section

theorem dyadicRegularizedFamily_hasSum_phase_fourier
    {ε : ℝ} (hε : 0 < ε) (i : ℕ) :
    HasSum (fun h : ℤ => (dyadicRegularizationNormalization ε : ℂ) *
      (dyadicTentMellinCoefficient i h *
        ((∑' p : ℕ × ℕ, (dyadicRegularizationCoefficient ε p.1 p.2 : ℂ) *
          dyadicIntegerFourierPhase h ((p.1+1)*3^p.2)) *
          dyadicResidueFourierSymbol 3 h)))
      (dyadicBoundaryCoordinate (dyadicRegularizedFamily ε) i : ℂ) := by
  have hs := (dyadicBoundaryCoordinate_summable_residue_dilation_packet_hasSum_fourier
    i 3 (by norm_num) (fun p : ℕ × ℕ => (p.1+1)*3^p.2) (fun p => by positivity)
    (fun p : ℕ × ℕ => dyadicRegularizationCoefficient ε p.1 p.2)
    (dyadicRegularizationCoefficient_abs_summable hε)).mul_left
      (dyadicRegularizationNormalization ε : ℂ)
  have hv : (dyadicRegularizationNormalization ε : ℂ) *
      (∑' p : ℕ × ℕ, (dyadicRegularizationCoefficient ε p.1 p.2 : ℂ) *
        (dyadicBoundaryCoordinate (hilbertDilation ((p.1+1)*3^p.2) (by positivity)
          (hilbertResidue 3 (by norm_num))) i : ℂ)) =
      (dyadicBoundaryCoordinate (dyadicRegularizedFamily ε) i : ℂ) := by
    rw [dyadicRegularizedFamily, dyadicBoundaryCoordinate_smul,
      dyadicBoundaryCoordinate_tsum _ (dyadicRegularizedTerm_summable hε)]
    push_cast
    congr 1
    apply tsum_congr
    intro p
    rw [dyadicRegularizedTerm, dyadicBoundaryCoordinate_smul,
      dyadicBoundaryCoordinate_projection]
    push_cast
    rfl
  rwa [hv] at hs

end
end RiemannResearch.RH.Pareto

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
open RiemannResearch.Analysis
noncomputable section

/-- The actual arithmetic family has its exact nonzero zeta-ratio Fourier expansion,
with its normalized zero mode removed explicitly. -/
theorem dyadicRegularizedFamily_hasSum_arithmetic_fourier
    {ε : ℝ} (hε : 0 < ε) (i : ℕ) :
    HasSum (fun h : DyadicNonzeroFourierFrequency =>
      dyadicTentMellinCoefficient i h.1 *
        (((dyadicRegularizationNormalization ε : ℂ) *
            riemannZeta (1 - Complex.I * (dyadicLogFrequency h.1 : ℂ)) /
            riemannZeta (1 + (ε : ℂ) - Complex.I * (dyadicLogFrequency h.1 : ℂ))) *
          abelCancellationMultiplier (triadicDampingRatio ε)
            (dyadicTriadicFourierPhase h.1)))
      ((dyadicBoundaryCoordinate (dyadicRegularizedFamily ε) i : ℂ) -
        dyadicTentMellinCoefficient i 0) := by
  let f : ℤ → ℂ := fun h => (dyadicRegularizationNormalization ε : ℂ) *
    (dyadicTentMellinCoefficient i h *
      ((∑' p : ℕ × ℕ, (dyadicRegularizationCoefficient ε p.1 p.2 : ℂ) *
        dyadicIntegerFourierPhase h ((p.1+1)*3^p.2)) *
        dyadicResidueFourierSymbol 3 h))
  have hzero : f 0 = dyadicTentMellinCoefficient i 0 := by
    dsimp [f]
    simp only [dyadicIntegerFourierPhase_zero, mul_one,
      dyadicResidueFourierSymbol, ite_true, Nat.cast_ofNat]
    calc
      _ = dyadicTentMellinCoefficient i 0 *
          ((dyadicRegularizationNormalization ε : ℂ) *
            ((∑' p : ℕ × ℕ, (dyadicRegularizationCoefficient ε p.1 p.2 : ℂ)) *
              (Real.log 3 : ℂ))) := by ring
      _ = _ := by rw [dyadicRegularizationPhaseKernel_zero_normalization hε, mul_one]
  have hf : HasSum f (dyadicBoundaryCoordinate (dyadicRegularizedFamily ε) i : ℂ) :=
    dyadicRegularizedFamily_hasSum_phase_fourier hε i
  have hs := (({0} : Finset ℤ).hasSum_iff_compl).mp hf
  simp only [Finset.sum_singleton, hzero] at hs
  let e : DyadicNonzeroFourierFrequency ≃ {x : ℤ // x ∉ ({0} : Finset ℤ)} :=
    { toFun := fun h => ⟨h.1, by simpa only [Finset.mem_singleton] using h.2⟩
      invFun := fun h => ⟨h.1, by simpa only [Finset.mem_singleton] using h.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hs' := e.hasSum_iff.mpr hs
  convert hs' using 1 <;> try rfl
  funext h
  dsimp [Function.comp_def, e, f]
  rw [dyadicRegularizationPhaseKernel_tsum hε h.1]
  simp only [dyadicResidueFourierSymbol, if_neg h.2,
    dyadicIntegerFourierPhase_three, abelCancellationMultiplier]
  ring

/-- Unconditional provider of the full signed Fourier bridge at every positive damping. -/
theorem dyadicSignedFourierBridge_proved : DyadicSignedFourierBridge := by
  exact dyadicSignedFourierBridge_of_regularizedFamily_hasSum
    (fun ε hε i => dyadicRegularizedFamily_hasSum_arithmetic_fourier hε i)

/-- The actual complete signed energy is now identified without a bridge hypothesis.
The squared modulus still contains all frequency cross terms. -/
theorem dyadicNormalizationRemainder_norm_sq_eq_signed_fourier
    {ε : ℝ} (hε : 0 < ε) :
    ‖dyadicNormalizationRemainder ε‖ ^ 2 =
      ∑' i : ℕ, (1 / 4 : ℝ) * ‖∑' h, dyadicSignedFourierTerm ε i h‖ ^ 2 :=
  dyadicNormalizationRemainder_norm_sq_eq_actual_fourier
    dyadicSignedFourierBridge_proved hε

/-- With the arithmetic bridge discharged, the two open uniform energy targets
are unconditionally equivalent; neither target is asserted here. -/
theorem dyadicUniformSignedFourierEnergyBound_iff_actual_remainder :
    DyadicUniformSignedFourierEnergyBound ↔ DyadicNormalizationRemainderUniformEnergyBound :=
  dyadicUniformSignedFourierEnergyBound_iff_remainder dyadicSignedFourierBridge_proved

end
end RiemannResearch.RH.Pareto
