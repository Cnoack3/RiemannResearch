/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.PrimeTorusFourierInversion
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Tactic.Ring

/-!
# Absolutely convergent Fourier products and coefficient fibers

Source: the user's prime-torus Plancherel question (2026-10-28),
Mathlib finite-torus Fourier theory, and the cited project modules.
-/


noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace RiemannResearch.Analysis.PrimeTorusHaar
variable {ι κ η : Type*} [Fintype ι] [DecidableEq ι]

theorem character_mul_star (h k : ι → ℤ) :
    character h * star (character k) = character (h - k) := by
  ext x
  simp only [ContinuousMap.mul_apply, ContinuousMap.star_apply,
    character_eq_mFourier, Complex.star_def, sub_eq_add_neg,
    UnitAddTorus.mFourier_add, UnitAddTorus.mFourier_neg]

theorem fourierSeries_mul_star
    (a : κ → ℂ) (b : η → ℂ) (k : κ → ι → ℤ) (l : η → ι → ℤ)
    (ha : Summable (fun i => ‖a i‖)) (hb : Summable (fun j => ‖b j‖)) :
    fourierSeries a k * star (fourierSeries b l) =
      fourierSeries (fun j : κ × η => a j.1 * conj (b j.2))
        (fun j => k j.1 - l j.2) := by
  let A : κ → C(Torus ι, ℂ) := fun i => a i • character (k i)
  let B : η → C(Torus ι, ℂ) := fun j => star (b j • character (l j))
  have hA : Summable (fun i => ‖A i‖) := by
    apply ha.of_norm_bounded
    intro i
    rw [norm_norm]
    change ‖a i • character (k i)‖ ≤ ‖a i‖
    rw [norm_smul]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (norm_character_le (k i)) (norm_nonneg (a i))
  have hB : Summable (fun j => ‖B j‖) := by
    apply hb.of_norm_bounded
    intro j
    rw [norm_norm]
    change ‖star (b j • character (l j))‖ ≤ ‖b j‖
    rw [norm_star, norm_smul]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (norm_character_le (l j)) (norm_nonneg (b j))
  have hAB : Summable (fun j : κ × η => A j.1 * B j.2) :=
    summable_mul_of_summable_norm hA hB
  have hprod : (∑' i, A i) * (∑' j, B j) =
      ∑' j : κ × η, A j.1 * B j.2 :=
    hA.of_norm.tsum_mul_tsum hB.of_norm hAB
  unfold fourierSeries
  rw [tsum_star]
  change (∑' i, A i) * (∑' j, B j) = _
  rw [hprod]
  change (∑' j : κ × η, A j.1 * B j.2) =
    ∑' j : κ × η, (a j.1 * conj (b j.2)) • character (k j.1 - l j.2)
  apply tsum_congr
  rintro ⟨i, j⟩
  simp only [A, B, star_smul, smul_mul_assoc, mul_smul_comm,
    smul_smul, character_mul_star, Complex.star_def, mul_comm]

theorem product_fourierSeries_mFourierCoeff (f g : C(Torus ι, ℂ))
    (hf : Summable (fun k => ‖UnitAddTorus.mFourierCoeff (f : Torus ι → ℂ) k‖))
    (hg : Summable (fun k => ‖UnitAddTorus.mFourierCoeff (g : Torus ι → ℂ) k‖)) :
    f * star g = fourierSeries
      (fun j : (ι → ℤ) × (ι → ℤ) =>
        UnitAddTorus.mFourierCoeff (f : Torus ι → ℂ) j.1 *
          conj (UnitAddTorus.mFourierCoeff (g : Torus ι → ℂ) j.2))
      (fun j => j.1 - j.2) := by
  have h := fourierSeries_mul_star
    (UnitAddTorus.mFourierCoeff (f : Torus ι → ℂ))
    (UnitAddTorus.mFourierCoeff (g : Torus ι → ℂ)) id id hf hg
  rw [fourierSeries_mFourierCoeff f hf, fourierSeries_mFourierCoeff g hg] at h
  exact h

theorem normSq_product_apply (f : C(Torus ι, ℂ)) (x : Torus ι) :
    (f * star f) x = (‖f x‖ ^ 2 : ℝ) := by
  change f x * conj (f x) = _
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

end RiemannResearch.Analysis.PrimeTorusHaar

namespace RiemannResearch.Analysis.PrimeTorusHaar
open MeasureTheory
open scoped BigOperators ComplexConjugate
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]
def fourierCoeffCLM (n : ι → ℤ) : C(Torus ι, ℂ) →L[ℂ] ℂ :=
  torusHaarIntegralCLM.comp
    ((ContinuousLinearMap.mul ℂ C(Torus ι, ℂ)) (character (-n)))
@[simp] theorem fourierCoeffCLM_apply (n : ι → ℤ) (f : C(Torus ι, ℂ)) :
    fourierCoeffCLM n f = UnitAddTorus.mFourierCoeff (f : Torus ι → ℂ) n := by
  change haarIntegral (character (-n) * f) = _
  rw [character_eq_mFourier, haarIntegral_apply]
  rfl

theorem mFourierCoeff_character (k n : ι → ℤ) :
    UnitAddTorus.mFourierCoeff (character k : Torus ι → ℂ) n =
      if k = n then 1 else 0 := by
  rw [← fourierCoeffCLM_apply]
  change haarIntegral (character (-n) * character k) = _
  have he : character (-n) * character k = character (k - n) := by
    rw [character_eq_mFourier, character_eq_mFourier, character_eq_mFourier]
    ext x
    change UnitAddTorus.mFourier (-n) x * UnitAddTorus.mFourier k x =
      UnitAddTorus.mFourier (k - n) x
    simpa only [sub_eq_add_neg, add_comm] using
      (UnitAddTorus.mFourier_add (m := -n) (n := k) (x := x)).symm
  rw [he, haarIntegral_character_eq]
  simp only [sub_eq_zero]

theorem mFourierCoeff_fourierSeries_fiber
    (a : κ → ℂ) (k : κ → ι → ℤ)
    (ha : Summable (fun i => ‖a i‖)) (n : ι → ℤ) :
    UnitAddTorus.mFourierCoeff (fourierSeries a k : Torus ι → ℂ) n =
      ∑' i : (k ⁻¹' ({n} : Set (ι → ℤ))), a i := by
  have h := (fourierCoeffCLM n).map_tsum (summable_fourierSeries a k ha)
  simp only [fourierSeries, fourierCoeffCLM_apply, map_smul, smul_eq_mul,
    mFourierCoeff_character] at h
  change UnitAddTorus.mFourierCoeff (fourierSeries a k : Torus ι → ℂ) n =
    ∑' i, a i * (if k i = n then 1 else 0) at h
  rw [h]
  calc
    _ = ∑' i, if k i = n then a i else 0 := by
      apply tsum_congr
      intro i
      split_ifs <;> simp
    _ = ∑' i, (k ⁻¹' ({n} : Set (ι → ℤ))).indicator a i := by
      apply tsum_congr
      intro i
      by_cases hi : k i = n <;> simp [Set.indicator, hi]
    _ = _ := (tsum_subtype (k ⁻¹' ({n} : Set (ι → ℤ))) a).symm

end RiemannResearch.Analysis.PrimeTorusHaar
