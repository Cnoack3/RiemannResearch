import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Separation from rational logarithmic resonances

The real logarithm estimate comes directly from the two tangent inequalities
`Real.one_sub_inv_le_log_of_pos` and `Real.log_le_sub_one_of_pos`.
The rational estimate retains the arithmetic hypothesis `n ≠ m * q` explicitly.
-/

namespace RiemannResearch.Analysis.RationalLogSeparation

/-- A positive real number is separated from `1` by its logarithm, with the
natural normalization that works on either side of `1`. -/
theorem abs_sub_one_div_max_le_abs_log {x : ℝ} (hx : 0 < x) :
    |x - 1| / max x 1 ≤ |Real.log x| := by
  by_cases hx1 : 1 ≤ x
  · rw [max_eq_left hx1, abs_of_nonneg (sub_nonneg.mpr hx1)]
    calc
      (x - 1) / x = 1 - x⁻¹ := by
        field_simp [ne_of_gt hx]
        <;> ring
      _ ≤ Real.log x := Real.one_sub_inv_le_log_of_pos hx
      _ ≤ |Real.log x| := le_abs_self _
  · have hx1' : x ≤ 1 := (lt_of_not_ge hx1).le
    rw [max_eq_right hx1', div_one, abs_of_nonpos (sub_nonpos.mpr hx1')]
    calc
      -(x - 1) ≤ -Real.log x := by
        linarith [Real.log_le_sub_one_of_pos hx]
      _ ≤ |Real.log x| := neg_le_abs _

/-- The logarithm of a ratio controls the difference of its positive inputs. -/
theorem abs_sub_div_max_le_abs_log_div {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    |a - b| / max a b ≤ |Real.log (a / b)| := by
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hsub : a / b - 1 = (a - b) / b := by
    field_simp [hb0]
    <;> ring
  have hmax : max (a / b) 1 = max a b / b := by
    simpa only [div_self hb0] using max_div_div_right hb.le a b
  calc
    |a - b| / max a b = |a / b - 1| / max (a / b) 1 := by
      rw [hsub, hmax, abs_div, abs_of_pos hb,
        div_div_div_cancel_right₀ hb0]
    _ ≤ |Real.log (a / b)| :=
      abs_sub_one_div_max_le_abs_log (div_pos ha hb)

/-- Two unequal natural numbers have real distance at least one.  The
product is kept explicit to match the rational resonance condition. -/
theorem integer_gap {m n q : ℕ} (hne : n ≠ m * q) :
    1 ≤ |(n : ℝ) - (m : ℝ) * (q : ℝ)| := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hstep : n + 1 ≤ m * q := Nat.succ_le_of_lt hlt
    have hreal : (n : ℝ) + 1 ≤ (m : ℝ) * (q : ℝ) := by
      exact_mod_cast hstep
    rw [abs_of_nonpos (by linarith)]
    linarith
  · have hstep : m * q + 1 ≤ n := Nat.succ_le_of_lt hgt
    have hreal : (m : ℝ) * (q : ℝ) + 1 ≤ (n : ℝ) := by
      exact_mod_cast hstep
    rw [abs_of_nonneg (by linarith)]
    linarith

/-- The exact arithmetic separation of `n / m` from an integral `q`. -/
theorem rational_gap {m n q : ℕ} (hm : 0 < m) (hne : n ≠ m * q) :
    1 / (m : ℝ) ≤ |(n : ℝ) / (m : ℝ) - (q : ℝ)| := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hsub : (n : ℝ) / (m : ℝ) - (q : ℝ) =
      ((n : ℝ) - (m : ℝ) * (q : ℝ)) / (m : ℝ) := by
    field_simp [ne_of_gt hmR]
    <;> ring
  rw [hsub, abs_div, abs_of_pos hmR]
  exact div_le_div_of_nonneg_right (integer_gap hne) hmR.le

/-- Away from exact resonance, a natural `q` with `q ≤ 2n/m` has logarithmic
separation at least `1/(2n)` from `n/m`. -/
theorem rational_log_separation {m n q : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hq : 0 < q)
    (hq_upper : (q : ℝ) ≤ 2 * (n : ℝ) / (m : ℝ))
    (hne : n ≠ m * q) :
    1 / (2 * (n : ℝ)) ≤ |Real.log ((n : ℝ) / (m : ℝ) / (q : ℝ))| := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hmq : (m : ℝ) * (q : ℝ) ≤ 2 * (n : ℝ) := by
    have h := (le_div_iff₀ hmR).mp hq_upper
    nlinarith
  have hmax : max (n : ℝ) ((m : ℝ) * (q : ℝ)) ≤ 2 * (n : ℝ) :=
    max_le (by linarith) hmq
  have hmaxpos : 0 < max (n : ℝ) ((m : ℝ) * (q : ℝ)) :=
    lt_of_lt_of_le hnR (le_max_left _ _)
  calc
    1 / (2 * (n : ℝ)) ≤ 1 / max (n : ℝ) ((m : ℝ) * (q : ℝ)) :=
      one_div_le_one_div_of_le hmaxpos hmax
    _ ≤ |(n : ℝ) - (m : ℝ) * (q : ℝ)| /
        max (n : ℝ) ((m : ℝ) * (q : ℝ)) :=
      div_le_div_of_nonneg_right (integer_gap hne) hmaxpos.le
    _ ≤ |Real.log ((n : ℝ) / ((m : ℝ) * (q : ℝ)))| :=
      abs_sub_div_max_le_abs_log_div hnR (mul_pos hmR hqR)
    _ = |Real.log ((n : ℝ) / (m : ℝ) / (q : ℝ))| := by
      rw [div_div]

end RiemannResearch.Analysis.RationalLogSeparation
