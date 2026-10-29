/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Arithmetic for the explicit squarefree-gap argument

Source: Kumchev et al., arXiv:2211.09975v3, Lemma 6, equations (4.3)--(4.4).
The reciprocal inequality in (4.3) is reversed. This file certifies that
algebraic obstruction and the corrected terminal spacing argument.
It does not prove the paper's interval theorem. The final spacing theorem
discharges numerator nonvanishing from an explicit preceding triple-product
bound; that bound and the counting argument remain separate obligations.
-/

namespace RiemannResearch.NumberTheory.SquarefreeGapSpacing

/-- The numerical inference in (4.3) fails even with positive even gaps,
a nonzero even numerator, and zero error. This is not a counterexample
to the squarefree interval theorem. -/
theorem reciprocal_step_counterexample :
    (0 : ℝ) < 2 ∧ 2 * (2 : ℝ) ≤ 8 ∧
    (3 / 4 : ℝ) * 8 ^ 2 ≤ 8 ^ 2 - 2 ^ 2 ∧
    ¬ ((99 / 50 : ℝ) / ((3 / 4) * 2 * 8 ^ 3) ≤
      |(2 : ℝ) - 0| / (2 * 8 * (8 ^ 2 - 2 ^ 2))) := by
  norm_num

/-- Positive magnitude of the third divided difference of x/t²,
written as a sum whose four denominators each have degree five. -/
noncomputable def inverseSquareThirdMagnitude (x u v w z : ℝ) : ℝ :=
  x * (1 / (u ^ 2 * v * w * z) + 1 / (u * v ^ 2 * w * z) +
    1 / (u * v * w ^ 2 * z) + 1 / (u * v * w * z ^ 2))

/-- Exact paired-node third divided difference; no mean-value theorem is needed. -/
theorem paired_divided_difference (x u a b : ℝ)
    (hu : 0 < u) (ha : 0 < a) (hab : a < b) :
    (x / (u + a + b) ^ 2 - x / u ^ 2) / (a * b * (a + b)) -
      (x / (u + b) ^ 2 - x / (u + a) ^ 2) / (a * b * (b - a)) =
      -inverseSquareThirdMagnitude x u (u + a) (u + b) (u + a + b) := by
  have hb : 0 < b := lt_trans ha hab
  have hua : u + a ≠ 0 := ne_of_gt (by positivity)
  have hub : u + b ≠ 0 := ne_of_gt (by positivity)
  have huab : u + a + b ≠ 0 := ne_of_gt (by positivity)
  have hba : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  have hapb : a + b ≠ 0 := ne_of_gt (by positivity)
  unfold inverseSquareThirdMagnitude
  field_simp
  ring

/-- The upper derivative bound follows directly from the exact rational formula. -/
theorem inverseSquareThirdMagnitude_le {x M u v w z : ℝ}
    (hx : 0 ≤ x) (hM : 0 < M)
    (hu : M ≤ u) (hv : M ≤ v) (hw : M ≤ w) (hz : M ≤ z) :
    inverseSquareThirdMagnitude x u v w z ≤ 4 * x / M ^ 5 := by
  have hu0 : 0 < u := lt_of_lt_of_le hM hu
  have hv0 : 0 < v := lt_of_lt_of_le hM hv
  have hw0 : 0 < w := lt_of_lt_of_le hM hw
  have hz0 : 0 < z := lt_of_lt_of_le hM hz
  have h1 : M ^ 5 ≤ u ^ 2 * v * w * z := by
    calc
      M ^ 5 = M ^ 2 * M * M * M := by ring
      _ ≤ u ^ 2 * v * w * z := by gcongr
  have h2 : M ^ 5 ≤ u * v ^ 2 * w * z := by
    calc
      M ^ 5 = M * M ^ 2 * M * M := by ring
      _ ≤ u * v ^ 2 * w * z := by gcongr
  have h3 : M ^ 5 ≤ u * v * w ^ 2 * z := by
    calc
      M ^ 5 = M * M * M ^ 2 * M := by ring
      _ ≤ u * v * w ^ 2 * z := by gcongr
  have h4 : M ^ 5 ≤ u * v * w * z ^ 2 := by
    calc
      M ^ 5 = M * M * M * M ^ 2 := by ring
      _ ≤ u * v * w * z ^ 2 := by gcongr
  have q1 : 1 / (u ^ 2 * v * w * z) ≤ 1 / M ^ 5 :=
    one_div_le_one_div_of_le (by positivity) h1
  have q2 : 1 / (u * v ^ 2 * w * z) ≤ 1 / M ^ 5 :=
    one_div_le_one_div_of_le (by positivity) h2
  have q3 : 1 / (u * v * w ^ 2 * z) ≤ 1 / M ^ 5 :=
    one_div_le_one_div_of_le (by positivity) h3
  have q4 : 1 / (u * v * w * z ^ 2) ≤ 1 / M ^ 5 :=
    one_div_le_one_div_of_le (by positivity) h4
  unfold inverseSquareThirdMagnitude
  calc
    _ ≤ x * (4 * (1 / M ^ 5)) := mul_le_mul_of_nonneg_left (by linarith) hx
    _ = 4 * x / M ^ 5 := by ring

/-- Separation of a nonzero even integer from an error of magnitude at most 1/50. -/
theorem even_integer_error_lower {n : ℤ} {θ : ℝ}
    (heven : Even n) (hn : n ≠ 0) (hθ : |θ| ≤ 1 / 50) :
    (99 / 50 : ℝ) ≤ |(n : ℝ) - θ| := by
  obtain ⟨k, hk⟩ := heven
  have hk0 : k ≠ 0 := by intro h; apply hn; simp [hk, h]
  have hkabs : (1 : ℤ) ≤ |k| := by
    exact Int.one_le_abs hk0
  have hnr : (2 : ℝ) ≤ |(n : ℝ)| := by
    have hr : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast hkabs
    rw [hk]
    push_cast
    rw [← two_mul, abs_mul]
    norm_num
    linarith
  have ht := abs_add_le ((n : ℝ) - θ) θ
  have hid : (n : ℝ) - θ + θ = n := by ring
  rw [hid] at ht
  linarith

/-- Corrected terminal step of Lemma 6: the constant justified by the stated
numerator and divided-difference bounds is 0.4950. All remaining analytic
and arithmetic premises are explicit. -/
theorem corrected_spacing_of_numerator {x M a b θ D : ℝ} {n : ℤ}
    (hx : 0 < x) (hM : 0 < M) (ha : 0 < a) (hab : a < b)
    (heven : Even n) (hn : n ≠ 0) (hθ : |θ| ≤ 1 / 50)
    (hD : |D| = |(n : ℝ) - θ| / (a * b * (b ^ 2 - a ^ 2)))
    (hupper : |D| ≤ 4 * x / M ^ 5) :
    (99 / 200 : ℝ) * M ^ 5 / x ≤ a * b ^ 3 := by
  have hb : 0 < b := lt_trans ha hab
  have hdiff : 0 < b ^ 2 - a ^ 2 := by nlinarith
  have hV : 0 < a * b * (b ^ 2 - a ^ 2) := by positivity
  have hnum := even_integer_error_lower heven hn hθ
  have hquot : (99 / 50 : ℝ) / (a * b * (b ^ 2 - a ^ 2)) ≤
      4 * x / M ^ 5 := by
    calc
      _ ≤ |(n : ℝ) - θ| / (a * b * (b ^ 2 - a ^ 2)) :=
        div_le_div_of_nonneg_right hnum (le_of_lt hV)
      _ = |D| := hD.symm
      _ ≤ _ := hupper
  have hcross := (div_le_div_iff₀ hV (pow_pos hM 5)).mp hquot
  have hden : a * b * (b ^ 2 - a ^ 2) ≤ a * b ^ 3 := by
    nlinarith [mul_nonneg (le_of_lt (mul_pos ha hb)) (sq_nonneg a)]
  have hmul := mul_le_mul_of_nonneg_left hden (show 0 ≤ 4 * x by positivity)
  apply (div_le_iff₀ hx).mpr
  nlinarith

/-- The paired-node denominator and numerator identity before taking absolute values. -/
theorem paired_numerator_identity {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (f₀ f₁ f₂ f₃ : ℝ) :
    (f₃ - f₀) / (a * b * (a + b)) - (f₂ - f₁) / (a * b * (b - a)) =
      ((b - a) * (f₃ - f₀) - (a + b) * (f₂ - f₁)) /
        (a * b * (b ^ 2 - a ^ 2)) := by
  have hb : 0 < b := lt_trans ha hab
  have hp : a + b ≠ 0 := ne_of_gt (by positivity)
  have hm : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  have hs : b ^ 2 - a ^ 2 ≠ 0 := ne_of_gt (by nlinarith)
  field_simp
  ring

/-- The even numerator arising from two pairs of odd integer nodes. -/
def pairedNumerator (a b n₀ n₁ n₂ n₃ : ℤ) : ℤ :=
  (b - a) * (n₃ - n₀) - (a + b) * (n₂ - n₁)

theorem pairedNumerator_even {a b : ℤ} (ha : Even a) (hb : Even b)
    (n₀ n₁ n₂ n₃ : ℤ) : Even (pairedNumerator a b n₀ n₁ n₂ n₃) := by
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  refine ⟨(b' - a') * (n₃ - n₀) - (a' + b') * (n₂ - n₁), ?_⟩
  unfold pairedNumerator
  ring

/-- Corrected paired-node spacing using the actual reciprocal-square values.
The nonzero even integer numerator and its small error remain explicit;
the analytic upper bound is proved here from the node locations. -/
theorem paired_spacing_of_even_numerator {x M u a b θ : ℝ} {n : ℤ}
    (hx : 0 < x) (hM : 0 < M) (hu : M ≤ u)
    (ha : 0 < a) (hab : a < b)
    (heven : Even n) (hn : n ≠ 0) (hθ : |θ| ≤ 1 / 50)
    (hrep : (n : ℝ) - θ =
      (b - a) * (x / (u + a + b) ^ 2 - x / u ^ 2) -
      (a + b) * (x / (u + b) ^ 2 - x / (u + a) ^ 2)) :
    (99 / 200 : ℝ) * M ^ 5 / x ≤ a * b ^ 3 := by
  have hb : 0 < b := lt_trans ha hab
  have hu0 : 0 < u := lt_of_lt_of_le hM hu
  have hdiff : 0 < b ^ 2 - a ^ 2 := by nlinarith
  have hV : 0 < a * b * (b ^ 2 - a ^ 2) := by positivity
  let D := (x / (u + a + b) ^ 2 - x / u ^ 2) / (a * b * (a + b)) -
    (x / (u + b) ^ 2 - x / (u + a) ^ 2) / (a * b * (b - a))
  have hD : |D| = |(n : ℝ) - θ| / (a * b * (b ^ 2 - a ^ 2)) := by
    dsimp [D]
    rw [paired_numerator_identity ha hab, ← hrep, abs_div, abs_of_pos hV]
  have hnonneg : 0 ≤ inverseSquareThirdMagnitude x u (u + a)
      (u + b) (u + a + b) := by
    unfold inverseSquareThirdMagnitude
    positivity
  have hupper : |D| ≤ 4 * x / M ^ 5 := by
    dsimp [D]
    rw [paired_divided_difference x u a b hu0 ha hab, abs_neg, abs_of_nonneg hnonneg]
    exact inverseSquareThirdMagnitude_le hx.le hM hu
      (by linarith) (by linarith) (by linarith)
  exact corrected_spacing_of_numerator hx hM ha hab heven hn hθ hD hupper

/-- A lower bound from positive nodes bounded above by L. -/
theorem inverseSquareThirdMagnitude_lower {x L u v w z : ℝ}
    (hx : 0 ≤ x) (hu0 : 0 < u) (hv0 : 0 < v) (hw0 : 0 < w) (hz0 : 0 < z)
    (hu : u ≤ L) (hv : v ≤ L) (hw : w ≤ L) (hz : z ≤ L) :
    4 * x / L ^ 5 ≤ inverseSquareThirdMagnitude x u v w z := by
  have hL : 0 < L := lt_of_lt_of_le hu0 hu
  have h1 : u ^ 2 * v * w * z ≤ L ^ 5 := by
    calc
      _ ≤ L ^ 2 * L * L * L := by gcongr
      _ = L ^ 5 := by ring
  have h2 : u * v ^ 2 * w * z ≤ L ^ 5 := by
    calc
      _ ≤ L * L ^ 2 * L * L := by gcongr
      _ = L ^ 5 := by ring
  have h3 : u * v * w ^ 2 * z ≤ L ^ 5 := by
    calc
      _ ≤ L * L * L ^ 2 * L := by gcongr
      _ = L ^ 5 := by ring
  have h4 : u * v * w * z ^ 2 ≤ L ^ 5 := by
    calc
      _ ≤ L * L * L * L ^ 2 := by gcongr
      _ = L ^ 5 := by ring
  have q1 := one_div_le_one_div_of_le (show 0 < u ^ 2 * v * w * z by positivity) h1
  have q2 := one_div_le_one_div_of_le (show 0 < u * v ^ 2 * w * z by positivity) h2
  have q3 := one_div_le_one_div_of_le (show 0 < u * v * w ^ 2 * z by positivity) h3
  have q4 := one_div_le_one_div_of_le (show 0 < u * v * w * z ^ 2 by positivity) h4
  unfold inverseSquareThirdMagnitude
  calc
    4 * x / L ^ 5 = x * (4 * (1 / L ^ 5)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hx

/-- Nonvanishing of the paired numerator from the corrected triple-product
bound. This avoids using the paper's small-b estimate outside its proved range. -/
theorem paired_numerator_ne_zero {x M a b h θ D : ℝ} {n : ℤ}
    (_hx : 0 < x) (hM : 0 < M) (ha : 0 < a) (hab : a < b)
    (hscale : 5 * h ≤ M)
    (htriple : (199 / 100 : ℝ) * M ^ 4 ≤ 3 * x * a * b * (b - a))
    (herror : |θ| ≤ 2 * b * h / M ^ 2)
    (hD : |D| = |(n : ℝ) - θ| / (a * b * (b ^ 2 - a ^ 2)))
    (hlower : 2 * x / M ^ 5 ≤ |D|) : n ≠ 0 := by
  intro hn
  have hb : 0 < b := lt_trans ha hab
  have hdiff : 0 < b ^ 2 - a ^ 2 := by nlinarith
  have hV : 0 < a * b * (b ^ 2 - a ^ 2) := by positivity
  have hquot : 2 * x / M ^ 5 ≤ (2 * b * h / M ^ 2) /
      (a * b * (b ^ 2 - a ^ 2)) := by
    calc
      _ ≤ |D| := hlower
      _ = |θ| / (a * b * (b ^ 2 - a ^ 2)) := by simpa [hn] using hD
      _ ≤ _ := div_le_div_of_nonneg_right herror hV.le
  rw [div_div] at hquot
  have hc := (div_le_div_iff₀ (pow_pos hM 5) (mul_pos (pow_pos hM 2) hV)).mp hquot
  have hcancel : x * (a * b * (b ^ 2 - a ^ 2)) ≤ b * h * M ^ 3 := by
    by_contra hnot
    have hp := mul_pos (show 0 < 2 * M ^ 2 by positivity)
      (show 0 < x * (a * b * (b ^ 2 - a ^ 2)) - b * h * M ^ 3 by linarith)
    nlinarith [hc]
  have ht := mul_le_mul_of_nonneg_right htriple (show 0 ≤ a + b by positivity)
  have hs := mul_le_mul_of_nonneg_left hscale (show 0 ≤ 3 * b * M ^ 3 by positivity)
  have hp : 0 < a * M ^ 4 := mul_pos ha (pow_pos hM 4)
  have hp' : 0 < b * M ^ 4 := mul_pos hb (pow_pos hM 4)
  nlinarith

/-- Corrected Lemma 6 spacing from the preceding triple-product estimate and
the actual near-integer paired numerator. No nonzero-numerator premise remains.
The preceding triple-product estimate is still an explicit obligation. -/
theorem paired_spacing_of_triple_product {x M u a b h θ : ℝ} {n : ℤ}
    (hx : 0 < x) (hM : 0 < M) (hu : M ≤ u)
    (ha : 0 < a) (hab : a < b) (hh : 0 ≤ h) (hscale : 5 * h ≤ M)
    (hsize : u + a + b ≤ (21 / 20 : ℝ) * M)
    (htriple : (199 / 100 : ℝ) * M ^ 4 ≤ 3 * x * a * b * (b - a))
    (heven : Even n) (herror : |θ| ≤ 2 * b * h / M ^ 2)
    (hrep : (n : ℝ) - θ =
      (b - a) * (x / (u + a + b) ^ 2 - x / u ^ 2) -
      (a + b) * (x / (u + b) ^ 2 - x / (u + a) ^ 2)) :
    (99 / 200 : ℝ) * M ^ 5 / x ≤ a * b ^ 3 := by
  have hb : 0 < b := lt_trans ha hab
  have hu0 : 0 < u := lt_of_lt_of_le hM hu
  have hdiff : 0 < b ^ 2 - a ^ 2 := by nlinarith
  have hV : 0 < a * b * (b ^ 2 - a ^ 2) := by positivity
  let D := (x / (u + a + b) ^ 2 - x / u ^ 2) / (a * b * (a + b)) -
    (x / (u + b) ^ 2 - x / (u + a) ^ 2) / (a * b * (b - a))
  have hD : |D| = |(n : ℝ) - θ| / (a * b * (b ^ 2 - a ^ 2)) := by
    dsimp [D]
    rw [paired_numerator_identity ha hab, ← hrep, abs_div, abs_of_pos hV]
  have hnonneg : 0 ≤ inverseSquareThirdMagnitude x u (u + a)
      (u + b) (u + a + b) := by
    unfold inverseSquareThirdMagnitude
    positivity
  have hlow : 2 * x / M ^ 5 ≤ |D| := by
    dsimp [D]
    rw [paired_divided_difference x u a b hu0 ha hab, abs_neg, abs_of_nonneg hnonneg]
    have hl := inverseSquareThirdMagnitude_lower hx.le hu0
      (show 0 < u + a by positivity) (show 0 < u + b by positivity)
      (show 0 < u + a + b by positivity)
      (show u ≤ (21 / 20 : ℝ) * M by linarith)
      (show u + a ≤ (21 / 20 : ℝ) * M by linarith)
      (show u + b ≤ (21 / 20 : ℝ) * M by linarith) hsize
    refine le_trans ?_ hl
    apply (div_le_div_iff₀ (pow_pos hM 5) (by positivity)).mpr
    norm_num [mul_pow]
    nlinarith [mul_pos hx (pow_pos hM 5)]
  have hn := paired_numerator_ne_zero hx hM ha hab hscale htriple herror hD hlow
  have hbh : b * h ≤ M / 20 * (M / 5) :=
    mul_le_mul (by linarith) (by linarith) hh (by positivity)
  have hsmall : |θ| ≤ 1 / 50 := by
    refine le_trans herror ?_
    apply (div_le_iff₀ (pow_pos hM 2)).mpr
    nlinarith
  exact paired_spacing_of_even_numerator hx hM hu ha hab heven hn hsmall hrep

end RiemannResearch.NumberTheory.SquarefreeGapSpacing
