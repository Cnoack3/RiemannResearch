import RiemannResearch.Analysis.IntegerTentSupport

/-!
# Exact dyadic refinement of the actual centered hat

Source: user-provided argument, `RH_Layer_Cake_Sublevel_Program_and_Next_Attack_2026-09-16_Continued.md`,
Sections 29.1 and 39.  The source supplies the pointwise refinement identity.

The centered hat is a rescaling of the existing `rootTent`, so this file proves
an identity of the actual piecewise linear functions.  It does not assert spline
density, an autocorrelation integral, a prime discrepancy identity, or an RH bound.
-/

noncomputable section

namespace RiemannResearch.Analysis

/-- The height-one hat of half-width `h`, centered at the origin. -/
def centeredHat (h x : ℝ) : ℝ := rootTent (-1) (x / h)

theorem centeredHat_eq_max (h x : ℝ) :
    centeredHat h x = max 0 (1 - |x| / |h|) := by
  simp [centeredHat, rootTent, abs_div]

theorem centeredHat_eq_max_of_pos {h : ℝ} (hh : 0 < h) (x : ℝ) :
    centeredHat h x = max 0 (1 - |x| / h) := by
  rw [centeredHat_eq_max, abs_of_pos hh]

theorem centeredHat_nonneg (h x : ℝ) : 0 ≤ centeredHat h x :=
  rootTent_nonneg _ _

theorem centeredHat_le_one (h x : ℝ) : centeredHat h x ≤ 1 :=
  rootTent_le_one _ _

@[simp] theorem centeredHat_zero (h : ℝ) : centeredHat h 0 = 1 := by
  simp [centeredHat, rootTent]

@[simp] theorem centeredHat_neg (h x : ℝ) : centeredHat h (-x) = centeredHat h x := by
  simp [centeredHat, rootTent, neg_div]

theorem continuous_centeredHat (h : ℝ) : Continuous (centeredHat h) := by
  exact (continuous_rootTent (-1)).comp (continuous_id.div_const h)

theorem centeredHat_pos_iff {h x : ℝ} (hh : 0 < h) :
    0 < centeredHat h x ↔ -h < x ∧ x < h := by
  rw [centeredHat, rootTent_pos_iff]
  constructor
  · rintro ⟨hl, hr⟩
    constructor
    · have := (lt_div_iff₀ hh).mp hl
      linarith
    · have := (div_lt_iff₀ hh).mp hr
      linarith
  · rintro ⟨hl, hr⟩
    constructor
    · apply (lt_div_iff₀ hh).mpr
      linarith
    · apply (div_lt_iff₀ hh).mpr
      linarith

theorem centeredHat_eq_zero_iff {h x : ℝ} (hh : 0 < h) :
    centeredHat h x = 0 ↔ h ≤ |x| := by
  rw [centeredHat_eq_max_of_pos hh, max_eq_left_iff]
  constructor
  · intro hx
    have hx' : 1 ≤ |x| / h := by linarith
    have := (le_div_iff₀ hh).mp hx'
    linarith
  · intro hx
    have hx' : 1 ≤ |x| / h := (le_div_iff₀ hh).mpr (by simpa using hx)
    linarith

theorem support_centeredHat {h : ℝ} (hh : 0 < h) :
    Function.support (centeredHat h) = Set.Ioo (-h) h := by
  ext x
  change centeredHat h x ≠ 0 ↔ -h < x ∧ x < h
  rw [← centeredHat_pos_iff hh]
  constructor
  · intro hn
    exact lt_of_le_of_ne (centeredHat_nonneg h x) (Ne.symm hn)
  · exact ne_of_gt

/-- The three nonzero mask coefficients are exactly `1/2`, `1`, and `1/2`. -/
theorem rootTent_centered_dyadic_refinement (x : ℝ) :
    rootTent (-1) x =
      (1 / 2 : ℝ) * rootTent (-1) (2 * x + 1) +
      rootTent (-1) (2 * x) +
      (1 / 2 : ℝ) * rootTent (-1) (2 * x - 1) := by
  by_cases h₁ : x ≤ -1
  · rw [rootTent_eq_zero_of_le h₁,
      rootTent_eq_zero_of_le (a := -1) (x := 2 * x + 1) (by linarith),
      rootTent_eq_zero_of_le (a := -1) (x := 2 * x) (by linarith),
      rootTent_eq_zero_of_le (a := -1) (x := 2 * x - 1) (by linarith)]
    ring
  by_cases h₂ : x ≤ -(1 / 2 : ℝ)
  · rw [rootTent_eq_left (a := -1) (x := x) (by linarith) (by linarith),
      rootTent_eq_left (a := -1) (x := 2 * x + 1) (by linarith) (by linarith),
      rootTent_eq_zero_of_le (a := -1) (x := 2 * x) (by linarith),
      rootTent_eq_zero_of_le (a := -1) (x := 2 * x - 1) (by linarith)]
    ring
  by_cases h₃ : x ≤ 0
  · rw [rootTent_eq_left (a := -1) (x := x) (by linarith) (by linarith),
      rootTent_eq_right (a := -1) (x := 2 * x + 1) (by linarith) (by linarith),
      rootTent_eq_left (a := -1) (x := 2 * x) (by linarith) (by linarith),
      rootTent_eq_zero_of_le (a := -1) (x := 2 * x - 1) (by linarith)]
    ring
  by_cases h₄ : x ≤ (1 / 2 : ℝ)
  · rw [rootTent_eq_right (a := -1) (x := x) (by linarith) (by linarith),
      rootTent_eq_zero_of_ge (a := -1) (x := 2 * x + 1) (by linarith),
      rootTent_eq_right (a := -1) (x := 2 * x) (by linarith) (by linarith),
      rootTent_eq_left (a := -1) (x := 2 * x - 1) (by linarith) (by linarith)]
    ring
  by_cases h₅ : x ≤ 1
  · rw [rootTent_eq_right (a := -1) (x := x) (by linarith) (by linarith),
      rootTent_eq_zero_of_ge (a := -1) (x := 2 * x + 1) (by linarith),
      rootTent_eq_zero_of_ge (a := -1) (x := 2 * x) (by linarith),
      rootTent_eq_right (a := -1) (x := 2 * x - 1) (by linarith) (by linarith)]
    ring
  · rw [rootTent_eq_zero_of_ge (a := -1) (x := x) (by linarith),
      rootTent_eq_zero_of_ge (a := -1) (x := 2 * x + 1) (by linarith),
      rootTent_eq_zero_of_ge (a := -1) (x := 2 * x) (by linarith),
      rootTent_eq_zero_of_ge (a := -1) (x := 2 * x - 1) (by linarith)]
    ring

/-- Exact physical-width refinement; this is an equality for every real `x`. -/
theorem centeredHat_dyadic_refinement {h : ℝ} (hh : h ≠ 0) (x : ℝ) :
    centeredHat h x =
      (1 / 2 : ℝ) * centeredHat (h / 2) (x + h / 2) +
      centeredHat (h / 2) x +
      (1 / 2 : ℝ) * centeredHat (h / 2) (x - h / 2) := by
  have hp : (x + h / 2) / (h / 2) = 2 * (x / h) + 1 := by
    field_simp [hh]
  have hz : x / (h / 2) = 2 * (x / h) := by
    field_simp [hh]
  have hm : (x - h / 2) / (h / 2) = 2 * (x / h) - 1 := by
    field_simp [hh]
  simp only [centeredHat, hp, hz, hm]
  exact rootTent_centered_dyadic_refinement (x / h)

/-- The translated form used for every interior mesh basis function. -/
theorem centeredHat_translate_dyadic_refinement {h : ℝ} (hh : h ≠ 0)
    (c x : ℝ) :
    centeredHat h (x - c) =
      (1 / 2 : ℝ) * centeredHat (h / 2) (x - (c - h / 2)) +
      centeredHat (h / 2) (x - c) +
      (1 / 2 : ℝ) * centeredHat (h / 2) (x - (c + h / 2)) := by
  have hp : x - (c - h / 2) = (x - c) + h / 2 := by ring
  have hm : x - (c + h / 2) = (x - c) - h / 2 := by ring
  rw [hp, hm]
  exact centeredHat_dyadic_refinement hh (x - c)

end RiemannResearch.Analysis
