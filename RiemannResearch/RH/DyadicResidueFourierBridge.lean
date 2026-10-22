import RiemannResearch.RH.DyadicResidueFourierBounds
import RiemannResearch.RH.ParetoResidueMellinContinuation

/-!
# Unconditional fixed-conductor residue Fourier bridge

Source: continuation of the user-provided
FourierArithmeticContinuationVerification20260911(1).md, September 11, 2026.
The existing continuous Pareto Mellin functional transfers actual physical
step-prefix convergence to the zeta symbol. The logarithmic kernel bound
then justifies Fourier cutoff extraction. No RH, Mertens or signed-energy
hypothesis occurs in these providers.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
open Filter
noncomputable section

theorem dyadicIntegerFourierPhase_eq_cpow (h : ℤ) (n : ℕ) (hn : 0 < n) :
    dyadicIntegerFourierPhase h n =
      (n : ℂ) ^ (Complex.I * (dyadicLogFrequency h : ℂ)) := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hlog : Complex.log (n : ℂ) = (Real.log (n : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_natCast] using
      (Complex.ofReal_log (Nat.cast_nonneg n)).symm
  rw [dyadicIntegerFourierPhase, fourier_coe_apply,
    Complex.cpow_def_of_ne_zero hnC, hlog]
  unfold dyadicLogFrequency
  push_cast
  congr 1
  ring

theorem mul_paretoMellin_stepJumpPrefix (f : ThresholdHilbert) (K : ℕ)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    s * paretoMellin (hilbertStepJumpPrefix f K) s =
      ∑ j ∈ Finset.range K,
        (((hilbertSequence f (j+1) - hilbertSequence f j) / (j+1 : ℝ) : ℝ) : ℂ) *
          (j+1 : ℂ) ^ (1-s) := by
  have hs0 : s ≠ 0 := by intro hz; norm_num [hz] at hs
  change s * ((paretoMellinContinuous s hs)
    (∑ j ∈ Finset.range K,
      ((hilbertSequence f (j+1) - hilbertSequence f j) / (j+1 : ℝ)) •
        hilbertDilation (j+1) (by positivity) hilbertOne)) = _
  rw [map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_smul]
  change s * ((((hilbertSequence f (j+1) - hilbertSequence f j) /
      (j+1 : ℝ) : ℝ) : ℂ) *
      paretoMellin (hilbertDilation (j+1) (by positivity) hilbertOne) s) = _
  rw [paretoMellin_dilation, paretoMellin_one s hs]
  push_cast
  field_simp [hs0]

theorem dyadicResidueFourierKernel_eq_mellin (a : ℕ) (ha : 0 < a)
    (K : ℕ) (h : ℤ) :
    dyadicResidueFourierKernel a K h =
      (1 - Complex.I * (dyadicLogFrequency h : ℂ)) *
        paretoMellin (hilbertStepJumpPrefix (hilbertResidue a ha) K)
          (1 - Complex.I * (dyadicLogFrequency h : ℂ)) := by
  have hs : (1 / 2 : ℝ) <
      (1 - Complex.I * (dyadicLogFrequency h : ℂ)).re := by norm_num
  rw [mul_paretoMellin_stepJumpPrefix _ _ _ hs]
  unfold dyadicResidueFourierKernel
  apply Finset.sum_congr rfl
  intro j hj
  rw [hilbertResidue_sequence]
  simp only [residue, natResidue_cast_jump a _ ha]
  rw [dyadicIntegerFourierPhase_eq_cpow h (j+1) (by positivity)]
  push_cast
  congr 2
  ring

theorem hilbertResidue_eq_digitHilbert (a : ℕ) (ha : 0 < a) :
    hilbertResidue a ha = digitHilbert a 1 ha (by omega) := by
  apply hilbertSequence_injective
  rw [hilbertResidue_sequence, hilbertSequence_digitHilbert]
  funext k
  simp [residue, digitSequence]

theorem dyadicResidueFourierKernel_nonzero_tendsto
    (a : ℕ) (ha : 0 < a) (h : ℤ) (hh : h ≠ 0) :
    Tendsto (fun K => dyadicResidueFourierKernel a K h) atTop
      (nhds ((1 - dyadicIntegerFourierPhase h a) *
        riemannZeta (1 - Complex.I * (dyadicLogFrequency h : ℂ)))) := by
  let s : ℂ := 1 - Complex.I * (dyadicLogFrequency h : ℂ)
  have hs : (1 / 2 : ℝ) < s.re := by dsimp [s]; norm_num
  have hspos : 0 < s.re := by linarith
  have hs0 : s ≠ 0 := by intro hz; simp [hz] at hspos
  have hs1 : s ≠ 1 := by
    intro he
    have hf : Complex.I * (dyadicLogFrequency h : ℂ) = 0 := by
      dsimp [s] at he
      linear_combination -he
    have hf0 : (dyadicLogFrequency h : ℂ) = 0 :=
      (mul_eq_zero.mp hf).resolve_left Complex.I_ne_zero
    exact dyadicLogFrequency_ne_zero hh (Complex.ofReal_eq_zero.mp hf0)
  have ht := (paretoMellinContinuous s hs).continuous.continuousAt.tendsto.comp
    (hilbertResidue_stepJumpPrefix_tendsto a ha)
  have ht' := ht.const_mul s
  change Tendsto (fun K => s * paretoMellin
    (hilbertStepJumpPrefix (hilbertResidue a ha) K) s) atTop
      (nhds (s * paretoMellin (hilbertResidue a ha) s)) at ht'
  have hv : s * paretoMellin (hilbertResidue a ha) s =
      (1 - dyadicIntegerFourierPhase h a) * riemannZeta s := by
    rw [hilbertResidue_eq_digitHilbert, paretoMellin_residue_zeta a ha s hspos hs1,
      dyadicIntegerFourierPhase_eq_cpow h a ha]
    have he : 1-s = Complex.I * (dyadicLogFrequency h : ℂ) := by dsimp [s]; ring
    rw [he]
    field_simp [hs0]
  rw [hv] at ht'
  simpa only [dyadicResidueFourierKernel_eq_mellin a ha, s] using ht'

theorem dyadicResidueFourierKernel_tendsto_symbol (a : ℕ) (ha : 0 < a) (h : ℤ) :
    Tendsto (fun K => dyadicResidueFourierKernel a K h) atTop
      (nhds (dyadicResidueFourierSymbol a h)) := by
  by_cases hh : h = 0
  · subst h
    simpa [dyadicResidueFourierSymbol] using dyadicResidueFourierKernel_zero_tendsto a ha
  · simpa [dyadicResidueFourierSymbol, hh] using
      dyadicResidueFourierKernel_nonzero_tendsto a ha h hh

theorem dyadicResidueFourierSymbol_eq_mellin (a : ℕ) (ha : 0 < a) (h : ℤ) :
    dyadicResidueFourierSymbol a h =
      (1 - Complex.I * (dyadicLogFrequency h : ℂ)) *
        paretoMellin (hilbertResidue a ha)
          (1 - Complex.I * (dyadicLogFrequency h : ℂ)) := by
  have hs : (1 / 2 : ℝ) <
      (1 - Complex.I * (dyadicLogFrequency h : ℂ)).re := by norm_num
  have ht := ((paretoMellinContinuous _ hs).continuous.continuousAt.tendsto.comp
    (hilbertResidue_stepJumpPrefix_tendsto a ha)).const_mul
      (1 - Complex.I * (dyadicLogFrequency h : ℂ))
  change Tendsto (fun K => (1 - Complex.I * (dyadicLogFrequency h : ℂ)) *
      paretoMellin (hilbertStepJumpPrefix (hilbertResidue a ha) K)
        (1 - Complex.I * (dyadicLogFrequency h : ℂ))) atTop
      (nhds ((1 - Complex.I * (dyadicLogFrequency h : ℂ)) *
        paretoMellin (hilbertResidue a ha)
          (1 - Complex.I * (dyadicLogFrequency h : ℂ)))) at ht
  have ht' : Tendsto (fun K => dyadicResidueFourierKernel a K h) atTop
      (nhds ((1 - Complex.I * (dyadicLogFrequency h : ℂ)) *
        paretoMellin (hilbertResidue a ha)
          (1 - Complex.I * (dyadicLogFrequency h : ℂ)))) := by
    simpa only [dyadicResidueFourierKernel_eq_mellin a ha] using ht
  exact tendsto_nhds_unique (dyadicResidueFourierKernel_tendsto_symbol a ha h) ht'

theorem dyadicResidueFourierKernel_error_sq_le (a : ℕ) (ha : 0 < a)
    (K : ℕ) (h : ℤ) :
    ‖dyadicResidueFourierKernel a K h - dyadicResidueFourierSymbol a h‖ ^ 2 ≤
      ‖1 - Complex.I * (dyadicLogFrequency h : ℂ)‖ ^ 2 *
        (((a : ℝ)-1)^2 / (K+1 : ℝ)) := by
  let s : ℂ := 1 - Complex.I * (dyadicLogFrequency h : ℂ)
  have hs : (1 / 2 : ℝ) < s.re := by dsimp [s]; norm_num
  have hf := hilbertResidue_stepJumpPrefix_error_sq_le a ha K
  have hm := paretoMellin_norm_sq_le
    (hilbertStepJumpPrefix (hilbertResidue a ha) K - hilbertResidue a ha) s hs
  have hsre : s.re = 1 := by dsimp [s]; norm_num
  rw [hsre] at hm
  norm_num at hm
  rw [dyadicResidueFourierKernel_eq_mellin a ha, dyadicResidueFourierSymbol_eq_mellin a ha,
    ← mul_sub, norm_mul, mul_pow]
  have he : paretoMellin (hilbertStepJumpPrefix (hilbertResidue a ha) K) s -
      paretoMellin (hilbertResidue a ha) s =
      paretoMellin (hilbertStepJumpPrefix (hilbertResidue a ha) K - hilbertResidue a ha) s :=
    (map_sub (paretoMellinContinuous s hs) _ _).symm
  change ‖s‖ ^ 2 * ‖paretoMellin (hilbertStepJumpPrefix (hilbertResidue a ha) K) s -
      paretoMellin (hilbertResidue a ha) s‖ ^ 2 ≤ _
  rw [he]
  exact mul_le_mul_of_nonneg_left (hm.trans hf) (sq_nonneg ‖s‖)

end
end RiemannResearch.RH.Pareto

namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis
noncomputable section

/-- The actual fixed-conductor residue has its full, absolutely convergent
Fourier expansion. Neither analytic kernel input is a hypothesis here. -/
theorem dyadicBoundaryCoordinate_residue_hasSum_fourier
    (a : ℕ) (ha : 0 < a) (i : ℕ) :
    HasSum (fun h => dyadicTentMellinCoefficient i h * dyadicResidueFourierSymbol a h)
      (dyadicBoundaryCoordinate (hilbertResidue a ha) i : ℂ) := by
  obtain ⟨C, _, hC⟩ := dyadicResidueFourierKernel_logarithmic_majorant a ha
  exact dyadicBoundaryCoordinate_residue_hasSum_fourier_of_logarithmic_kernel
    a ha i C hC (dyadicResidueFourierKernel_nonzero_tendsto a ha)

/-- The entire residue symbol, including its removable zero mode, equals
the absolutely convergent modular Abel series. -/
theorem dyadicResidueFourierSymbol_eq_modular_series
    (a : ℕ) (ha : 0 < a) (h : ℤ) :
    dyadicResidueFourierSymbol a h =
      ∑' j : ℕ, (((j+1) % a : ℕ) : ℂ) *
        (dyadicHarmonicFourierWeight h (j+1) -
          dyadicHarmonicFourierWeight h (j+2)) := by
  exact tendsto_nhds_unique (dyadicResidueFourierKernel_tendsto_symbol a ha h)
    (dyadicResidueFourierKernel_tendsto_modular_series a ha h)

/-- This HasSum is over the Abel differences, not the conditionally
convergent original physical jump series. -/
theorem dyadicResidueFourierSymbol_hasSum_modular_abel
    (a : ℕ) (ha : 0 < a) (h : ℤ) :
    HasSum (fun j : ℕ => (((j+1) % a : ℕ) : ℂ) *
        (dyadicHarmonicFourierWeight h (j+1) -
          dyadicHarmonicFourierWeight h (j+2)))
      (dyadicResidueFourierSymbol a h) := by
  rw [dyadicResidueFourierSymbol_eq_modular_series a ha h]
  exact (summable_norm_dyadicResidue_abelTerm a ha h).of_norm.hasSum

end
end RiemannResearch.RH.Pareto
