/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.HurwitzEulerMaclaurin
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Uniform Hurwitz strip bounds with explicit parameter and modulus dependence

The actual Euler--Maclaurin provider is already established in
`HurwitzEulerMaclaurin`. This module strengthens its uniformity: a single
explicit constant works for every q in [delta,1] and every shift whose real
part is in a prescribed interval. The imaginary part affects only the height
threshold, not the constant. Rational classes have representatives in [1/K,1],
including the zero class represented by 1, giving explicit power growth in K.

Source: the corrected Euler--Maclaurin identity, NIST DLMF 25.11.6,
https://dlmf.nist.gov/25.11.E6, as proved in HurwitzEulerMaclaurin.
The new bounds are elementary consequences of that exact identity; no
growth hypothesis, RH premise, or density conclusion is introduced.
The concrete RH consumer is ConreyBaluyotEstermannUniformGrowth.
-/

open Complex Set
noncomputable section
namespace RiemannResearch.Analysis.HurwitzUniformStripBounds
open HurwitzEulerMaclaurin

/-- Strip constant independent of the Hurwitz parameter and height. -/
def stripConstant (a b : ℝ) : ℝ :=
  3 / 2 + ((max |a| |b| + 1) * (max |a| |b| + 2) / 8) / (a + 1)

def parameterExponent (b : ℝ) : ℝ := max b 0 + 1

theorem stripConstant_pos {a b : ℝ} (ha : -1 < a) : 0 < stripConstant a b := by
  have ha1 : 0 < a + 1 := by linarith
  have hR : 0 ≤ max |a| |b| := (abs_nonneg a).trans (le_max_left _ _)
  unfold stripConstant
  positivity

theorem parameterExponent_pos (b : ℝ) : 0 < parameterExponent b := by
  unfold parameterExponent
  have := le_max_right b 0
  linarith

/-- Explicit growth in the Hurwitz parameter, with no growth premise. -/
theorem norm_hurwitzZeta_parameter_bound {q a b r t : ℝ}
    (hq : 0 < q) (hq1 : q ≤ 1) (ha : -1 < a)
    (hr : r ∈ Icc a b) (ht : 1 ≤ |t|) :
    ‖HurwitzZeta.hurwitzZeta q ((r : ℂ) + t * I)‖ ≤
      stripConstant a b * q ^ (-parameterExponent b) * |t| ^ 2 := by
  have ha1 : 0 < a + 1 := by linarith
  have hp : b ≤ max b 0 := le_max_left _ _
  have hqpow : q ^ (-b) ≤ q ^ (-parameterExponent b) :=
    Real.rpow_le_rpow_of_exponent_ge hq hq1 (by dsimp [parameterExponent]; linarith)
  have hqpow1 : q ^ (-b - 1) ≤ q ^ (-parameterExponent b) :=
    Real.rpow_le_rpow_of_exponent_ge hq hq1 (by dsimp [parameterExponent]; linarith)
  have hR : 0 ≤ max |a| |b| := (abs_nonneg a).trans (le_max_left _ _)
  have hfirst : q ^ (-b) * (1 / 2 + q) ≤ q ^ (-parameterExponent b) * (3 / 2) :=
    mul_le_mul hqpow (by linarith) (by positivity) (by positivity)
  have hsecond :
      ((max |a| |b| + 1) * (max |a| |b| + 2) / 8) *
        (q ^ (-b - 1) / (a + 1)) ≤
      ((max |a| |b| + 1) * (max |a| |b| + 2) / 8) *
        (q ^ (-parameterExponent b) / (a + 1)) :=
    mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hqpow1 ha1.le) (by positivity)
  calc
    _ ≤ (q ^ (-b) * (1 / 2 + q) +
        ((max |a| |b| + 1) * (max |a| |b| + 2) / 8) *
          (q ^ (-b - 1) / (a + 1))) * |t| ^ 2 :=
      norm_hurwitzZeta_strip_le hq hq1 ha hr ht
    _ ≤ (q ^ (-parameterExponent b) * (3 / 2) +
        ((max |a| |b| + 1) * (max |a| |b| + 2) / 8) *
          (q ^ (-parameterExponent b) / (a + 1))) * |t| ^ 2 :=
      mul_le_mul_of_nonneg_right (add_le_add hfirst hsecond) (sq_nonneg _)
    _ = _ := by unfold stripConstant; ring

/-- One constant works for every parameter q in [delta,1]. -/
theorem norm_hurwitzZeta_uniform_parameter_bound {δ q a b r t : ℝ}
    (hδ : 0 < δ) (hδq : δ ≤ q) (hq1 : q ≤ 1) (ha : -1 < a)
    (hr : r ∈ Icc a b) (ht : 1 ≤ |t|) :
    ‖HurwitzZeta.hurwitzZeta q ((r : ℂ) + t * I)‖ ≤
      stripConstant a b * δ ^ (-parameterExponent b) * |t| ^ 2 := by
  have hp := Real.rpow_le_rpow_of_nonpos hδ hδq
    (neg_nonpos.mpr (parameterExponent_pos b).le)
  exact (norm_hurwitzZeta_parameter_bound (hδ.trans_le hδq) hq1 ha hr ht).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hp (stripConstant_pos ha).le) (sq_nonneg _))

/-- Uniform real shifts; imaginary shifts affect only the height threshold.
The constant has no dependence on q, r, t, or the particular shift alpha. -/
theorem norm_hurwitzZeta_uniform_shift_bound {δ q a b A B r t : ℝ} {α : ℂ}
    (hδ : 0 < δ) (hδq : δ ≤ q) (hq1 : q ≤ 1)
    (ha : -1 < a + A) (hα : α.re ∈ Icc A B) (hr : r ∈ Icc a b)
    (ht : 2 * (1 + |α.im|) ≤ |t|) :
    ‖HurwitzZeta.hurwitzZeta q ((r : ℂ) + t * I + α)‖ ≤
      ((9 / 4 : ℝ) * stripConstant (a + A) (b + B)) *
        δ ^ (-parameterExponent (b + B)) * |t| ^ 2 := by
  have hlow : 1 ≤ |t + α.im| := by
    have hh : |t| ≤ |t + α.im| + |α.im| := by
      simpa using abs_sub (t + α.im) α.im
    nlinarith [abs_nonneg α.im]
  have hupp : |t + α.im| ≤ (3 / 2 : ℝ) * |t| := by
    have hh := abs_add_le t α.im
    linarith
  have hid : (r : ℂ) + t * I + α =
      ((r + α.re : ℝ) : ℂ) + ((t + α.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [hid]
  have hh := norm_hurwitzZeta_uniform_parameter_bound hδ hδq hq1 ha
    (r := r + α.re) (t := t + α.im)
    ⟨add_le_add hr.1 hα.1, add_le_add hr.2 hα.2⟩ hlow
  refine hh.trans ?_
  calc
    _ ≤ stripConstant (a + A) (b + B) * δ ^ (-parameterExponent (b + B)) *
        ((3 / 2 : ℝ) * |t|) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hupp 2)
        (mul_nonneg (stripConstant_pos ha).le (Real.rpow_nonneg hδ.le _))
    _ = _ := by ring

/-- Every rational class, including zero, has a positive representative >= 1/K. -/
theorem exists_positive_representative {K : ℕ} [NeZero K] (j : ZMod K) :
    ∃ q : ℝ, 1 / (K : ℝ) ≤ q ∧ q ≤ 1 ∧
      (q : UnitAddCircle) = ZMod.toAddCircle j := by
  have hK : 0 < (K : ℝ) := Nat.cast_pos.mpr (NeZero.pos K)
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast NeZero.pos K
  by_cases hj : j = 0
  · subst j
    refine ⟨1, (div_le_one hK).mpr hK1, le_rfl, ?_⟩
    simp
  · have hjv : 1 ≤ j.val := by
      apply Nat.one_le_iff_ne_zero.mpr
      intro hv
      apply hj
      calc
        j = (j.val : ZMod K) := (ZMod.natCast_zmod_val j).symm
        _ = 0 := by rw [hv]; simp
    refine ⟨(j.val : ℝ) / K, ?_, ?_, (ZMod.toAddCircle_apply j).symm⟩
    · exact div_le_div_of_nonneg_right (by exact_mod_cast hjv) hK.le
    · exact (div_le_one hK).mpr (by exact_mod_cast (ZMod.val_lt j).le)

/-- Explicit modulus dependence, uniformly over all rational classes and shifts. -/
theorem norm_hurwitzZeta_rational_uniform_shift_bound
    {K : ℕ} [NeZero K] (j : ZMod K) {a b A B r t : ℝ} {α : ℂ}
    (ha : -1 < a + A) (hα : α.re ∈ Icc A B) (hr : r ∈ Icc a b)
    (ht : 2 * (1 + |α.im|) ≤ |t|) :
    ‖HurwitzZeta.hurwitzZeta (ZMod.toAddCircle j) ((r : ℂ) + t * I + α)‖ ≤
      ((9 / 4 : ℝ) * stripConstant (a + A) (b + B)) *
        (K : ℝ) ^ parameterExponent (b + B) * |t| ^ 2 := by
  obtain ⟨q, hq, hq1, hj⟩ := exists_positive_representative j
  have hK : 0 < (K : ℝ) := Nat.cast_pos.mpr (NeZero.pos K)
  have hb := norm_hurwitzZeta_uniform_shift_bound (by positivity : 0 < 1 / (K : ℝ))
    hq hq1 ha hα hr ht
  rw [hj] at hb
  simpa only [one_div, Real.inv_rpow hK.le, Real.rpow_neg hK.le, inv_inv] using hb


/-- info: 'RiemannResearch.Analysis.HurwitzUniformStripBounds.norm_hurwitzZeta_uniform_shift_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_hurwitzZeta_uniform_shift_bound

/-- info: 'RiemannResearch.Analysis.HurwitzUniformStripBounds.norm_hurwitzZeta_rational_uniform_shift_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_hurwitzZeta_rational_uniform_shift_bound

end RiemannResearch.Analysis.HurwitzUniformStripBounds
