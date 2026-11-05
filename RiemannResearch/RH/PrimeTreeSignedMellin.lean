/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ParetoAtomMellinSignature
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Ring

/-! # Physical Mellin transform of finite signed CRT combinations
Equation (19) of the prime-tree paper follows from the normalized residue
identity of Báez-Duarte and the repository's positive-half-plane continuation.
Integer CRT lifts form a special case of this statement for all real coefficients. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace RiemannResearch.RH.PrimeTreeSignedMellin
open Pareto ParetoAtomMellinSignature
variable {ι : Type*} [Fintype ι]

def signedValue (a : ι → ℕ) (c : ι → ℝ) (D n : ℕ) : ℝ :=
  (∑ j, c j * normalizedAtom (a j) n) - normalizedAtom D n

def liftOffset (a : ι → ℕ) (c : ι → ℝ) (D : ℕ) : ℝ :=
  (∑ j, c j / (a j : ℝ)) - 1 / D

theorem signed_step (a : ι → ℕ) (c : ι → ℝ) (D : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    signedValue a c D ⌊x⌋₊ =
      (∑ j, c j * Int.fract (x / (a j : ℝ))) - Int.fract (x / (D : ℝ)) -
        liftOffset a c D * Int.fract x := by
  classical
  unfold signedValue liftOffset
  simp_rw [normalizedAtom_floor_eq_corrected_fract _ x hx, mul_sub, Finset.sum_sub_distrib]
  rw [sub_mul, Finset.sum_mul]
  have h : (∑ j, c j * (Int.fract x / (a j : ℝ))) =
      ∑ j, c j / (a j : ℝ) * Int.fract x := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [h]
  ring

private def kernel (a : ℕ) (s : ℂ) (x : ℝ) : ℂ :=
  (((Int.fract (x / (a : ℝ)) - Int.fract x / (a : ℝ) : ℝ)) : ℂ) *
    (x : ℂ) ^ (-s - 1)

theorem signed_integral (a : ι → ℕ) (ha : ∀ j, 0 < a j) (c : ι → ℝ)
    (D : ℕ) (hD : 0 < D) (s : ℂ) (hpos : 0 < s.re) (hs1 : s ≠ 1) :
    (∫ x in Ioi (1 : ℝ), (signedValue a c D ⌊x⌋₊ : ℂ) * (x : ℂ) ^ (-s - 1)) =
      riemannZeta s / s * ((liftOffset a c D : ℂ) + (D : ℂ) ^ (-s) -
        ∑ j, (c j : ℂ) * (a j : ℂ) ^ (-s)) := by
  classical
  have hi (d : ℕ) (hd : 0 < d) : IntegrableOn (kernel d s) (Ioi 1) :=
    corrected_fract_integrable _ hd _ hpos
  have he (d : ℕ) (hd : 0 < d) : (∫ x in Ioi (1 : ℝ), kernel d s x) =
      riemannZeta s / s * (1 / (d : ℂ) - (d : ℂ) ^ (-s)) :=
    corrected_fract_integral_eq_zeta _ hd _ hpos hs1
  calc
    _ = ∫ x in Ioi (1 : ℝ), (∑ j, (c j : ℂ) * kernel (a j) s x) - kernel D s x := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      have hx0 : 0 ≤ x := (zero_lt_one.trans hx).le
      simp only [signedValue, kernel, normalizedAtom_floor_eq_corrected_fract _ x hx0,
        Complex.ofReal_sub, Complex.ofReal_sum, Complex.ofReal_mul, sub_mul, Finset.sum_mul]
      simp only [mul_assoc, sub_mul]
    _ = _ := by
      rw [integral_sub (integrable_finsetSum _ (fun j _ => (hi (a j) (ha j)).const_mul _))
        (hi D hD), integral_finsetSum _ (fun j _ => (hi (a j) (ha j)).const_mul _)]
      simp_rw [integral_const_mul, he _ (ha _)]
      rw [he _ hD]
      unfold liftOffset
      push_cast
      simp only [Finset.mul_sum, mul_sub, Finset.sum_sub_distrib, mul_add, div_eq_mul_inv, one_mul]
      have hp : (∑ j, ↑(c j) * (riemannZeta s * s⁻¹ * (a j : ℂ)⁻¹)) =
          ∑ j, riemannZeta s * s⁻¹ * (↑(c j) * (a j : ℂ)⁻¹) := by
        apply Finset.sum_congr rfl
        intro j _
        ring
      have hq : (∑ j, ↑(c j) * (riemannZeta s * s⁻¹ * (a j : ℂ) ^ (-s))) =
          ∑ j, riemannZeta s * s⁻¹ * (↑(c j) * (a j : ℂ) ^ (-s)) := by
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [hp, hq]
      ring

/-- The integrated-domination extension after (19). The observation kernel
may include any fixed power of log x. -/
theorem signed_series_observation (C : ℕ → ℝ → ℂ) (v : ℕ → ℂ) (K : ℝ → ℂ)
    (hi : ∀ j, IntegrableOn (fun x => v j * C j x * K x) (Ioi (1 : ℝ)))
    (hsum : Summable (fun j => ∫ x in Ioi (1 : ℝ), ‖v j * C j x * K x‖)) :
    HasSum (fun j => ∫ x in Ioi (1 : ℝ), v j * C j x * K x)
      (∫ x in Ioi (1 : ℝ), (∑' j, v j * C j x) * K x) := by
  simpa only [tsum_mul_right] using hasSum_integral_of_summable_integral_norm hi hsum

theorem signed_series_observation_zero (C : ℕ → ℝ → ℂ) (v : ℕ → ℂ) (K : ℝ → ℂ)
    (hi : ∀ j, IntegrableOn (fun x => v j * C j x * K x) (Ioi (1 : ℝ)))
    (hsum : Summable (fun j => ∫ x in Ioi (1 : ℝ), ‖v j * C j x * K x‖))
    (hz : ∀ j, (∫ x in Ioi (1 : ℝ), v j * C j x * K x) = 0) :
    (∫ x in Ioi (1 : ℝ), (∑' j, v j * C j x) * K x) = 0 := by
  rw [← (signed_series_observation C v K hi hsum).tsum_eq]
  simp only [hz, tsum_zero]

end RiemannResearch.RH.PrimeTreeSignedMellin
