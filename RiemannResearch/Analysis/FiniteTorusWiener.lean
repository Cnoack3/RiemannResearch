/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.PrimeTorusFourierProducts
import RiemannResearch.Analysis.WeightedFourierFibers
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The squared-height Wiener class and its algebra bounds

Source: the user's prime-torus Plancherel question (2026-10-28),
Mathlib finite-torus Fourier theory, and the cited project modules.
-/


noncomputable section
open scoped BigOperators ComplexConjugate
namespace RiemannResearch.Analysis.FiniteTorusWiener
open PrimeTorusHaar
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
abbrev coeff (f : C(Torus ι, ℂ)) (k : ι → ℤ) : ℂ :=
  UnitAddTorus.mFourierCoeff (f : Torus ι → ℂ) k
def height (ell : ι → ℝ) (k : ι → ℤ) : ℝ := ∑ i, |(k i : ℝ)| * ell i
def weight (ell : ι → ℝ) (k : ι → ℤ) : ℝ := 1 + height ell k
def MemA2 (ell : ι → ℝ) (f : C(Torus ι, ℂ)) : Prop :=
  Summable (fun k => ‖coeff f k‖ * (weight ell k)^2)
def a2Mass (ell : ι → ℝ) (f : C(Torus ι, ℂ)) : ℝ :=
  ∑' k, ‖coeff f k‖ * (weight ell k)^2
def pairCoeff (f g : C(Torus ι, ℂ)) (j : (ι → ℤ) × (ι → ℤ)) : ℂ :=
  coeff f j.1 * star (coeff g j.2)
def pairMode (j : (ι → ℤ) × (ι → ℤ)) : ι → ℤ := j.1 - j.2

theorem height_nonneg (ell : ι → ℝ) (hell : ∀ i, 0 ≤ ell i) (k : ι → ℤ) :
    0 ≤ height ell k :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (hell i))
theorem one_le_weight (ell : ι → ℝ) (hell : ∀ i, 0 ≤ ell i) (k : ι → ℤ) :
    1 ≤ weight ell k := by
  unfold weight
  linarith [height_nonneg ell hell k]
theorem weight_nonneg (ell : ι → ℝ) (hell : ∀ i, 0 ≤ ell i) (k : ι → ℤ) :
    0 ≤ weight ell k := (by norm_num : (0:ℝ) ≤ 1).trans (one_le_weight ell hell k)
theorem height_sub_le (ell : ι → ℝ) (hell : ∀ i, 0 ≤ ell i) (h k : ι → ℤ) :
    height ell (h-k) ≤ height ell h + height ell k := by
  unfold height
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  simp only [Pi.sub_apply, Int.cast_sub]
  have hb : |(h i : ℝ) - (k i : ℝ)| ≤ |(h i : ℝ)| + |(k i : ℝ)| := by
    simpa only [Real.norm_eq_abs] using (norm_sub_le (h i : ℝ) (k i : ℝ))
  simpa only [add_mul] using mul_le_mul_of_nonneg_right hb (hell i)
theorem weight_sub_le_mul (ell : ι → ℝ) (hell : ∀ i, 0 ≤ ell i) (h k : ι → ℤ) :
    weight ell (h-k) ≤ weight ell h * weight ell k := by
  have hs := height_sub_le ell hell h k
  have hp := mul_nonneg (height_nonneg ell hell h) (height_nonneg ell hell k)
  unfold weight
  nlinarith
theorem weight_sub_sq_le (ell : ι → ℝ) (hell : ∀ i, 0 ≤ ell i) (h k : ι → ℤ) :
    (weight ell (h-k))^2 ≤ (weight ell h)^2 * (weight ell k)^2 := by
  have hs := mul_self_le_mul_self (weight_nonneg ell hell (h-k))
    (weight_sub_le_mul ell hell h k)
  simpa only [← pow_two, mul_pow] using hs

theorem memA2_summable_norm (ell : ι → ℝ) (hell : ∀ i, 0 ≤ ell i)
    (f : C(Torus ι, ℂ)) (hf : MemA2 ell f) : Summable (fun k => ‖coeff f k‖) := by
  apply hf.of_norm_bounded
  intro k
  rw [norm_norm]
  have hw := one_le_weight ell hell k
  have hw2 : 1 ≤ (weight ell k)^2 := by nlinarith
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hw2 (norm_nonneg (coeff f k))

theorem pairWeighted_le (ell : ι → ℝ) (hell : ∀ i, 0 ≤ ell i)
    (f g : C(Torus ι, ℂ)) (j : (ι → ℤ) × (ι → ℤ)) :
    ‖pairCoeff f g j‖ * (weight ell (pairMode j))^2 ≤
      (‖coeff f j.1‖ * (weight ell j.1)^2) *
      (‖coeff g j.2‖ * (weight ell j.2)^2) := by
  simp only [pairCoeff, pairMode, norm_mul, norm_star]
  calc
    _ ≤ (‖coeff f j.1‖ * ‖coeff g j.2‖) *
        ((weight ell j.1)^2 * (weight ell j.2)^2) :=
      mul_le_mul_of_nonneg_left (weight_sub_sq_le ell hell j.1 j.2) (by positivity)
    _ = _ := by ring

theorem summable_pairWeighted (ell : ι → ℝ) (hell : ∀ i, 0 ≤ ell i)
    (f g : C(Torus ι, ℂ)) (hf : MemA2 ell f) (hg : MemA2 ell g) :
    Summable (fun j => ‖pairCoeff f g j‖ * (weight ell (pairMode j))^2) := by
  have hm := summable_mul_of_summable_norm hf.norm hg.norm
  apply hm.of_norm_bounded
  intro j
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pairWeighted_le ell hell f g j

theorem pairWeighted_mass_le (ell : ι → ℝ) (hell : ∀ i, 0 ≤ ell i)
    (f g : C(Torus ι, ℂ)) (hf : MemA2 ell f) (hg : MemA2 ell g) :
    (∑' j, ‖pairCoeff f g j‖ * (weight ell (pairMode j))^2) ≤
      a2Mass ell f * a2Mass ell g := by
  have hm := summable_mul_of_summable_norm hf.norm hg.norm
  calc
    _ ≤ ∑' j : (ι → ℤ) × (ι → ℤ),
        (‖coeff f j.1‖ * (weight ell j.1)^2) *
        (‖coeff g j.2‖ * (weight ell j.2)^2) :=
      Summable.tsum_le_tsum (pairWeighted_le ell hell f g)
        (summable_pairWeighted ell hell f g hf hg) hm
    _ = _ := (hf.tsum_mul_tsum hg hm).symm

@[simp] theorem coeff_zero (k : ι → ℤ) : coeff (0 : C(Torus ι, ℂ)) k = 0 := by
  simpa only [fourierCoeffCLM_apply] using (fourierCoeffCLM k).map_zero
@[simp] theorem coeff_add (f g : C(Torus ι, ℂ)) (k : ι → ℤ) :
    coeff (f+g) k = coeff f k + coeff g k := by
  simpa only [fourierCoeffCLM_apply] using (fourierCoeffCLM k).map_add f g
@[simp] theorem coeff_smul (z : ℂ) (f : C(Torus ι, ℂ)) (k : ι → ℤ) :
    coeff (z • f) k = z * coeff f k := by
  simpa only [fourierCoeffCLM_apply, smul_eq_mul] using (fourierCoeffCLM k).map_smul z f

theorem a2Mass_nonneg (ell : ι → ℝ) (f : C(Torus ι, ℂ)) : 0 ≤ a2Mass ell f :=
  tsum_nonneg (fun k => mul_nonneg (norm_nonneg _) (sq_nonneg _))
theorem memA2_zero (ell : ι → ℝ) : MemA2 ell (0 : C(Torus ι, ℂ)) := by
  simp [MemA2]
theorem weightedCoeff_add_le (ell : ι → ℝ) (f g : C(Torus ι, ℂ)) (k : ι → ℤ) :
    ‖coeff (f+g) k‖ * (weight ell k)^2 ≤
      ‖coeff f k‖ * (weight ell k)^2 + ‖coeff g k‖ * (weight ell k)^2 := by
  rw [coeff_add]
  simpa only [add_mul] using
    mul_le_mul_of_nonneg_right (norm_add_le (coeff f k) (coeff g k)) (sq_nonneg (weight ell k))
theorem memA2_add (ell : ι → ℝ) (f g : C(Torus ι, ℂ))
    (hf : MemA2 ell f) (hg : MemA2 ell g) : MemA2 ell (f+g) := by
  apply (hf.add hg).of_norm_bounded
  intro k
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact weightedCoeff_add_le ell f g k
theorem a2Mass_add_le (ell : ι → ℝ) (f g : C(Torus ι, ℂ))
    (hf : MemA2 ell f) (hg : MemA2 ell g) :
    a2Mass ell (f+g) ≤ a2Mass ell f + a2Mass ell g := by
  calc
    _ ≤ ∑' k, (‖coeff f k‖ * (weight ell k)^2 + ‖coeff g k‖ * (weight ell k)^2) :=
      Summable.tsum_le_tsum (weightedCoeff_add_le ell f g)
        (memA2_add ell f g hf hg) (hf.add hg)
    _ = _ := hf.tsum_add hg

theorem memA2_smul (ell : ι → ℝ) (z : ℂ) (f : C(Torus ι, ℂ))
    (hf : MemA2 ell f) : MemA2 ell (z • f) := by
  unfold MemA2
  simp_rw [coeff_smul, norm_mul, mul_assoc]
  exact hf.mul_left ‖z‖
theorem a2Mass_smul (ell : ι → ℝ) (z : ℂ) (f : C(Torus ι, ℂ)) :
    a2Mass ell (z • f) = ‖z‖ * a2Mass ell f := by
  simp only [a2Mass, coeff_smul, norm_mul, mul_assoc, tsum_mul_left]

theorem memA2_of_coeff_zero_off_finset (ell : ι → ℝ) (f : C(Torus ι, ℂ))
    (s : Finset (ι → ℤ)) (hs : ∀ k ∉ s, coeff f k = 0) : MemA2 ell f := by
  apply summable_of_ne_finset_zero (s := s)
  intro k hk
  rw [hs k hk, norm_zero, zero_mul]
theorem memA2_character (ell : ι → ℝ) (k : ι → ℤ) : MemA2 ell (character k) := by
  classical
  apply memA2_of_coeff_zero_off_finset ell (character k) {k}
  intro n hn
  simp only [Finset.mem_singleton] at hn
  simp [coeff, mFourierCoeff_character, Ne.symm hn]
theorem memA2_fourierPolynomial (ell : ι → ℝ) (s : Finset (ι → ℤ))
    (a : (ι → ℤ) → ℂ) : MemA2 ell (∑ k ∈ s, a k • character k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using memA2_zero ell
  | @insert k s hks ih =>
    rw [Finset.sum_insert hks]
    exact memA2_add ell _ _ (memA2_smul ell (a k) (character k)
      (memA2_character ell k)) ih

theorem a2Mass_character (ell : ι → ℝ) (k : ι → ℤ) :
    a2Mass ell (character k) = (weight ell k) ^ 2 := by
  classical
  unfold a2Mass
  rw [tsum_eq_single k]
  · simp [coeff, mFourierCoeff_character]
  · intro n hn
    simp [coeff, mFourierCoeff_character, Ne.symm hn]

theorem summable_pairCoeff_norm (ell : ι → ℝ) (hell : ∀ i, 0 ≤ ell i)
    (f g : C(Torus ι, ℂ)) (hf : MemA2 ell f) (hg : MemA2 ell g) :
    Summable (fun j => ‖pairCoeff f g j‖) := by
  have hf0 := memA2_summable_norm ell hell f hf
  have hg0 := memA2_summable_norm ell hell g hg
  have hm : Summable (fun j : (ι → ℤ) × (ι → ℤ) =>
      ‖coeff f j.1‖ * ‖coeff g j.2‖) :=
    summable_mul_of_summable_norm hf0.norm hg0.norm
  have he (j : (ι → ℤ) × (ι → ℤ)) :
      ‖pairCoeff f g j‖ = ‖coeff f j.1‖ * ‖coeff g j.2‖ := by
    change ‖coeff f j.1 * (star (coeff g j.2) : ℂ)‖ = _
    rw [norm_mul, norm_star]
  exact hm.congr (fun j => (he j).symm)

theorem product_eq_pairSeries (ell : ι → ℝ) (hell : ∀ i, 0 ≤ ell i)
    (f g : C(Torus ι, ℂ)) (hf : MemA2 ell f) (hg : MemA2 ell g) :
    f * star g = fourierSeries (pairCoeff f g) pairMode :=
  product_fourierSeries_mFourierCoeff f g
    (memA2_summable_norm ell hell f hf) (memA2_summable_norm ell hell g hg)

theorem memA2_mul_star_and_mass_le (ell : ι → ℝ) (hell : ∀ i, 0 ≤ ell i)
    (f g : C(Torus ι, ℂ)) (hf : MemA2 ell f) (hg : MemA2 ell g) :
    MemA2 ell (f * star g) ∧ a2Mass ell (f * star g) ≤ a2Mass ell f * a2Mass ell g := by
  have hp := summable_pairWeighted ell hell f g hf hg
  have hw (n : ι → ℤ) : 1 ≤ (weight ell n)^2 := by
    have hh := one_le_weight ell hell n
    nlinarith
  obtain ⟨hs, hb⟩ := weighted_fiber_sum_bound (pairCoeff f g) pairMode
    (fun n => (weight ell n)^2) hw hp
  have he (n : ι → ℤ) : coeff (f * star g) n =
      ∑' j : (pairMode ⁻¹' ({n} : Set (ι → ℤ))), pairCoeff f g j := by
    rw [product_eq_pairSeries ell hell f g hf hg]
    exact mFourierCoeff_fourierSeries_fiber _ _
      (summable_pairCoeff_norm ell hell f g hf hg) n
  constructor
  · simpa only [MemA2, ← he] using hs
  · change (∑' n, ‖coeff (f * star g) n‖ * (weight ell n)^2) ≤ _
    simp_rw [he]
    exact hb.trans (pairWeighted_mass_le ell hell f g hf hg)

theorem norm_le_a2Mass (ell : ι → ℝ) (hell : ∀ i, 0 ≤ ell i)
    (f : C(Torus ι, ℂ)) (hf : MemA2 ell f) : ‖f‖ ≤ a2Mass ell f := by
  have ha := memA2_summable_norm ell hell f hf
  have hs : Summable (fun k => ‖coeff f k • character k‖) := by
    apply ha.of_norm_bounded
    intro k
    rw [norm_norm, norm_smul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (norm_character_le k) (norm_nonneg (coeff f k))
  calc
    ‖f‖ = ‖∑' k, coeff f k • character k‖ :=
      congrArg norm (fourierSeries_mFourierCoeff f ha).symm
    _ ≤ ∑' k, ‖coeff f k • character k‖ := norm_tsum_le_tsum_norm hs
    _ ≤ a2Mass ell f := by
      apply Summable.tsum_le_tsum _ hs hf
      intro k
      rw [norm_smul]
      have hw := one_le_weight ell hell k
      have hw2 : 1 ≤ (weight ell k)^2 := by nlinarith
      exact mul_le_mul_of_nonneg_left ((norm_character_le k).trans hw2)
        (norm_nonneg (coeff f k))

theorem a2Mass_eq_zero_iff (ell : ι → ℝ) (hell : ∀ i, 0 ≤ ell i)
    (f : C(Torus ι, ℂ)) (hf : MemA2 ell f) :
    a2Mass ell f = 0 ↔ f = 0 := by
  constructor
  · intro hz
    apply norm_eq_zero.mp
    exact le_antisymm (by simpa only [hz] using norm_le_a2Mass ell hell f hf)
      (norm_nonneg _)
  · rintro rfl
    simp [a2Mass]


theorem character_zero_eq_one : character (0 : ι → ℤ) = (1 : C(Torus ι, ℂ)) := by
  rw [character_eq_mFourier]
  exact UnitAddTorus.mFourier_zero

@[simp] theorem weight_zero (ell : ι → ℝ) : weight ell (0 : ι → ℤ) = 1 := by
  simp [weight, height]

theorem memA2_one (ell : ι → ℝ) : MemA2 ell (1 : C(Torus ι, ℂ)) := by
  rw [← character_zero_eq_one]
  exact memA2_character ell 0

@[simp] theorem a2Mass_one (ell : ι → ℝ) : a2Mass ell (1 : C(Torus ι, ℂ)) = 1 := by
  rw [← character_zero_eq_one, a2Mass_character, weight_zero]
  norm_num

theorem memA2_star_and_mass_eq (ell : ι → ℝ) (hell : ∀ i, 0 ≤ ell i)
    (f : C(Torus ι, ℂ)) (hf : MemA2 ell f) :
    MemA2 ell (star f) ∧ a2Mass ell (star f) = a2Mass ell f := by
  have hs (g : C(Torus ι, ℂ)) (hg : MemA2 ell g) :
      MemA2 ell (star g) ∧ a2Mass ell (star g) ≤ a2Mass ell g := by
    have h := memA2_mul_star_and_mass_le ell hell 1 g (memA2_one ell) hg
    simpa only [one_mul, a2Mass_one] using h
  obtain ⟨hfstar, hle⟩ := hs f hf
  refine ⟨hfstar, le_antisymm hle ?_⟩
  simpa only [star_star] using (hs (star f) hfstar).2

theorem memA2_mul_and_mass_le (ell : ι → ℝ) (hell : ∀ i, 0 ≤ ell i)
    (f g : C(Torus ι, ℂ)) (hf : MemA2 ell f) (hg : MemA2 ell g) :
    MemA2 ell (f * g) ∧ a2Mass ell (f * g) ≤ a2Mass ell f * a2Mass ell g := by
  obtain ⟨hgstar, hmass⟩ := memA2_star_and_mass_eq ell hell g hg
  have h := memA2_mul_star_and_mass_le ell hell f (star g) hf hgstar
  simpa only [star_star, hmass] using h

end RiemannResearch.Analysis.FiniteTorusWiener
