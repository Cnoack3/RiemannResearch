import RiemannResearch.RH.DyadicResidueFourierKernel
import RiemannResearch.Analysis.HarmonicFourierVariation
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Uniform logarithmic bounds for actual signed residue Fourier kernels

Source: continuation of the user-provided
FourierArithmeticContinuationVerification20260911(1).md, September 11, 2026.
Exact signed modular Abel summation is used before all inequalities. The
conductor dependence is explicit and the physical terminal term is retained.
The Abel-difference series is absolutely summable at every frequency.
-/

open scoped BigOperators
noncomputable section

namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis

/-- Actual adjacent harmonic Fourier weights satisfy the summable Abel majorant. -/
theorem norm_dyadicHarmonicFourierWeight_sub_succ_le (h : ℤ) (n : ℕ) (hn : 0 < n) :
    ‖dyadicHarmonicFourierWeight h n - dyadicHarmonicFourierWeight h (n+1)‖ ≤
      (1 + |dyadicLogFrequency h|) / ((n : ℝ)*((n : ℝ)+1)) := by
  simpa only [dyadicHarmonicFourierWeight, dyadicIntegerFourierPhase_eq_exp,
    Nat.cast_add, Nat.cast_one, Complex.ofReal_natCast, Complex.ofReal_add,
    Complex.ofReal_one] using
    norm_exp_log_harmonic_sub_le (dyadicLogFrequency h) (n : ℝ) (by exact_mod_cast hn)

end RiemannResearch.RH.Pareto


namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis

/-- A harmless phase-size estimate supplies the harmonic part of the Abel split. -/
theorem norm_dyadicHarmonicFourierWeight_sub_succ_le_harmonic
    (h : ℤ) (n : ℕ) (hn : 0 < n) :
    ‖dyadicHarmonicFourierWeight h n - dyadicHarmonicFourierWeight h (n+1)‖ ≤
      2 / (n : ℝ) := by
  calc
    _ ≤ ‖dyadicHarmonicFourierWeight h n‖ +
        ‖dyadicHarmonicFourierWeight h (n+1)‖ := norm_sub_le _ _
    _ = 1 / (n : ℝ) + 1 / ((n+1 : ℕ) : ℝ) := by
      rw [norm_dyadicHarmonicFourierWeight, norm_dyadicHarmonicFourierWeight]
    _ ≤ 1 / (n : ℝ) + 1 / (n : ℝ) := by
      gcongr
      exact_mod_cast Nat.le_succ n
    _ = 2 / (n : ℝ) := by ring

/-- Explicit uniform cutoff bound at an arbitrary physical split index. -/
theorem norm_dyadicResidueFourierKernel_le_split (a : ℕ) (ha : 0 < a)
    (K N : ℕ) (h : ℤ) :
    ‖dyadicResidueFourierKernel a K h‖ ≤
      (a : ℝ) + 2*(a : ℝ) * (∑ j ∈ Finset.range N, 1 / ((j+1 : ℕ) : ℝ)) +
        ((a : ℝ)*(1+|dyadicLogFrequency h|)) / ((N+1 : ℕ) : ℝ) := by
  let u : ℕ → ℝ := fun j => ‖(((j+1) % a : ℕ) : ℂ) *
    (dyadicHarmonicFourierWeight h (j+1) - dyadicHarmonicFourierWeight h (j+2))‖
  have hm (j : ℕ) : ‖(((j+1) % a : ℕ) : ℂ)‖ ≤ (a : ℝ) := by
    rw [Complex.norm_natCast]
    exact_mod_cast (Nat.mod_lt (j+1) ha).le
  have hhead (j : ℕ) : u j ≤ 2*(a : ℝ) / ((j+1 : ℕ) : ℝ) := by
    dsimp [u]
    rw [norm_mul]
    calc
      _ ≤ (a : ℝ) * (2 / ((j+1 : ℕ) : ℝ)) := by
        apply mul_le_mul (hm j)
          (by simpa only [Nat.add_assoc] using
            norm_dyadicHarmonicFourierWeight_sub_succ_le_harmonic h (j+1) (by omega))
          (norm_nonneg _) (Nat.cast_nonneg _)
      _ = _ := by ring
  have htail (j : ℕ) : u j ≤ ((a : ℝ)*(1+|dyadicLogFrequency h|)) /
      (((j+1 : ℕ) : ℝ)*((j+2 : ℕ) : ℝ)) := by
    dsimp [u]
    rw [norm_mul]
    calc
      _ ≤ (a : ℝ) * ((1+|dyadicLogFrequency h|) /
          (((j+1 : ℕ) : ℝ)*((j+2 : ℕ) : ℝ))) := by
        apply mul_le_mul (hm j)
          (by simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, Nat.add_assoc,
            add_assoc, one_add_one_eq_two] using
            norm_dyadicHarmonicFourierWeight_sub_succ_le h (j+1) (by omega))
          (norm_nonneg _) (Nat.cast_nonneg _)
      _ = _ := by ring
  have hs := sum_range_harmonic_and_variation_le u (2*(a : ℝ))
    ((a : ℝ)*(1+|dyadicLogFrequency h|)) (by positivity) (by positivity) hhead htail N K
  have he : ‖((K % a : ℕ) : ℂ) * dyadicHarmonicFourierWeight h (K+1)‖ ≤ (a : ℝ) := by
    rw [norm_mul, Complex.norm_natCast, norm_dyadicHarmonicFourierWeight]
    have hmK : ((K % a : ℕ) : ℝ) ≤ (a : ℝ) := by
      exact_mod_cast (Nat.mod_lt K ha).le
    have hi : 1 / ((K+1 : ℕ) : ℝ) ≤ 1 := by
      apply (div_le_one (by positivity)).mpr
      exact_mod_cast (show 1 ≤ K+1 by omega)
    calc
      _ ≤ (a : ℝ) * 1 := mul_le_mul hmK hi (by positivity) (Nat.cast_nonneg _)
      _ = _ := mul_one _
  rw [dyadicResidueFourierKernel_eq_modular_abel a ha]
  calc
    _ ≤ ‖((K % a : ℕ) : ℂ) * dyadicHarmonicFourierWeight h (K+1)‖ +
        ‖∑ j ∈ Finset.range K, (((j+1) % a : ℕ) : ℂ) *
          (dyadicHarmonicFourierWeight h (j+1) - dyadicHarmonicFourierWeight h (j+2))‖ := norm_add_le _ _
    _ ≤ (a : ℝ) + ∑ j ∈ Finset.range K, u j :=
      add_le_add he (norm_sum_le _ _)
    _ ≤ _ := by linarith [hs]

/-- An unconditional logarithmic bound at each fixed conductor, uniform in the cutoff. -/
theorem norm_dyadicResidueFourierKernel_le_log_frequency
    (a : ℕ) (ha : 0 < a) (K : ℕ) (h : ℤ) :
    ‖dyadicResidueFourierKernel a K h‖ ≤
      4*(a : ℝ) + 2*(a : ℝ)*Real.log (1+|dyadicLogFrequency h|) := by
  let B : ℝ := 1+|dyadicLogFrequency h|
  let N : ℕ := ⌊B⌋₊
  have hB : 1 ≤ B := by dsimp [B]; linarith [abs_nonneg (dyadicLogFrequency h)]
  have hH : (∑ j ∈ Finset.range N, 1 / ((j+1 : ℕ) : ℝ)) ≤ 1+Real.log B := by
    have hh := harmonic_floor_le_one_add_log B hB
    simpa only [N, harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, Rat.cast_add, Rat.cast_one,
      Nat.cast_add, Nat.cast_one, one_div] using hh
  have htail : (a : ℝ)*B / ((N+1 : ℕ) : ℝ) ≤ (a : ℝ) := by
    apply (div_le_iff₀ (by positivity)).mpr
    have hbN : B ≤ ((N+1 : ℕ) : ℝ) := by
      simpa only [N, Nat.cast_add, Nat.cast_one] using (Nat.lt_floor_add_one B).le
    exact mul_le_mul_of_nonneg_left hbN (Nat.cast_nonneg _)
  have hs := norm_dyadicResidueFourierKernel_le_split a ha K N h
  have hmul := mul_le_mul_of_nonneg_left hH (show 0 ≤ 2*(a : ℝ) by positivity)
  dsimp [B] at htail hH hmul
  linarith

end RiemannResearch.RH.Pareto

namespace RiemannResearch.RH.Pareto

/-- The precise logarithmic majorant required by the residue Fourier bridge. -/
theorem dyadicResidueFourierKernel_logarithmic_majorant
    (a : ℕ) (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K h,
      ‖dyadicResidueFourierKernel a K h‖ ≤
        C * (1 + Real.log (2 + |(h : ℝ)|)) := by
  let A : ℝ := |2 * Real.pi / Real.log 2|
  let L : ℝ := Real.log (1+A)
  let C : ℝ := (a : ℝ)*(4+2*L)
  have hA : 0 ≤ A := abs_nonneg _
  have hL : 0 ≤ L := Real.log_nonneg (by linarith)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro K h
  have hω : |dyadicLogFrequency h| = A * |(h : ℝ)| := by
    unfold dyadicLogFrequency
    calc
      |2 * Real.pi * (h : ℝ) / Real.log 2| =
          |(2 * Real.pi / Real.log 2)*(h : ℝ)| := by congr 1; ring
      _ = A * |(h : ℝ)| := abs_mul _ _
  have hlog : Real.log (1+|dyadicLogFrequency h|) ≤
      L + Real.log (2+|(h : ℝ)|) := by
    rw [hω]
    calc
      Real.log (1+A*|(h : ℝ)|) ≤ Real.log ((1+A)*(2+|(h : ℝ)|)) := by
        apply Real.log_le_log (by positivity)
        nlinarith [abs_nonneg (h : ℝ)]
      _ = L + Real.log (2+|(h : ℝ)|) := by
        rw [Real.log_mul (by positivity : 1+A ≠ 0) (by positivity : 2+|(h : ℝ)| ≠ 0)]
  have hhL : 0 ≤ Real.log (2+|(h : ℝ)|) :=
    Real.log_nonneg (by linarith [abs_nonneg (h : ℝ)])
  have hcoeff : 2*(a : ℝ) ≤ C := by
    dsimp [C]
    have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    nlinarith [mul_nonneg ha0 hL]
  calc
    ‖dyadicResidueFourierKernel a K h‖ ≤
        4*(a : ℝ)+2*(a : ℝ)*Real.log (1+|dyadicLogFrequency h|) :=
      norm_dyadicResidueFourierKernel_le_log_frequency a ha K h
    _ ≤ 4*(a : ℝ)+2*(a : ℝ)*(L+Real.log (2+|(h : ℝ)|)) := by
      gcongr
    _ = C + 2*(a : ℝ)*Real.log (2+|(h : ℝ)|) := by dsimp [C]; ring
    _ ≤ C + C*Real.log (2+|(h : ℝ)|) := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hcoeff hhL)
    _ = C * (1+Real.log (2+|(h : ℝ)|)) := by ring

end RiemannResearch.RH.Pareto


namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis
noncomputable section

theorem norm_dyadicResidue_abelTerm_le (a : ℕ) (ha : 0 < a) (h : ℤ) (j : ℕ) :
    ‖(((j+1) % a : ℕ) : ℂ) *
      (dyadicHarmonicFourierWeight h (j+1) -
        dyadicHarmonicFourierWeight h (j+2))‖ ≤
      ((a : ℝ) * (1 + |dyadicLogFrequency h|)) * positiveWeight (j+1) := by
  rw [norm_mul, Complex.norm_natCast]
  have hr : (((j+1) % a : ℕ) : ℝ) ≤ a := by
    exact_mod_cast (Nat.mod_lt (j+1) ha).le
  have hv := norm_dyadicHarmonicFourierWeight_sub_succ_le h (j+1) (by omega)
  have hi : j+1+1 = j+2 := by omega
  rw [hi] at hv
  calc
    _ ≤ (a : ℝ) * ((1 + |dyadicLogFrequency h|) /
        (((j+1 : ℕ) : ℝ)*(((j+1 : ℕ) : ℝ)+1))) :=
      mul_le_mul hr hv (norm_nonneg _) (Nat.cast_nonneg _)
    _ = _ := by unfold positiveWeight; ring

theorem summable_norm_dyadicResidue_abelTerm
    (a : ℕ) (ha : 0 < a) (h : ℤ) :
    Summable (fun j : ℕ => ‖(((j+1) % a : ℕ) : ℂ) *
      (dyadicHarmonicFourierWeight h (j+1) -
        dyadicHarmonicFourierWeight h (j+2))‖) := by
  have hp : Summable (fun j : ℕ => positiveWeight (j+1)) :=
    (summable_nat_add_iff 1).mpr positiveWeight_summable
  exact (hp.mul_left ((a : ℝ) * (1 + |dyadicLogFrequency h|))).of_nonneg_of_le
    (fun j => norm_nonneg _) (norm_dyadicResidue_abelTerm_le a ha h)

theorem dyadicResidueFourierKernel_tendsto_modular_series
    (a : ℕ) (ha : 0 < a) (h : ℤ) :
    Filter.Tendsto (fun K : ℕ => dyadicResidueFourierKernel a K h)
      Filter.atTop (nhds (∑' j : ℕ, (((j+1) % a : ℕ) : ℂ) *
        (dyadicHarmonicFourierWeight h (j+1) -
          dyadicHarmonicFourierWeight h (j+2)))) := by
  have hs := (summable_norm_dyadicResidue_abelTerm a ha h).of_norm.hasSum.tendsto_sum_nat
  simpa only [dyadicResidueFourierKernel_eq_modular_abel a ha, zero_add] using
    (dyadicResidueFourierKernel_endpoint_tendsto_zero a ha h).add hs
end
end RiemannResearch.RH.Pareto
