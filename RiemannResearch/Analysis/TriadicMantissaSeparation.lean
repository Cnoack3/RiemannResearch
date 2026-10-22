import RiemannResearch.Analysis.TriadicRotationSeparation

/-!
# Separation of normalized triadic mantissas

Source: user-provided continuation and
`RH/Dyadic_Gram_Prefix_Ordinary_Proof_20260910.md`, Section 2, equation (5).
The exponents normalizing by powers of two are arbitrary: only the resulting
mantissas being at least one is required. This includes dyadic normalization
into [1,2]. The intended RH consumer is the off-diagonal logarithmic Gram bound.
-/

namespace Real

/-- On [1,∞), the logarithm grows by at most the change in its argument. -/
theorem log_sub_le_sub_of_one_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    log b - log a ≤ b - a := by
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) ha
  have hb0 : 0 < b := lt_of_lt_of_le ha0 hab
  have hlog := log_le_sub_one_of_pos (div_pos hb0 ha0)
  rw [log_div (ne_of_gt hb0) (ne_of_gt ha0)] at hlog
  have hdiv : b / a - 1 ≤ b - a := by
    apply (sub_le_iff_le_add).2
    apply (div_le_iff₀ ha0).2
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hab)]
  exact hlog.trans hdiv

/-- The logarithm is 1-Lipschitz on [1,∞), in absolute-value form. -/
theorem abs_log_sub_le_abs_sub_of_one_le {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    |log b - log a| ≤ |b - a| := by
  rcases le_total a b with hab | hba
  · have hlog : log a ≤ log b := log_le_log (by linarith) hab
    rw [abs_of_nonneg (sub_nonneg.mpr hlog), abs_of_nonneg (sub_nonneg.mpr hab)]
    exact log_sub_le_sub_of_one_le ha hab
  · have hlog : log b ≤ log a := log_le_log (by linarith) hba
    rw [abs_of_nonpos (sub_nonpos.mpr hlog), abs_of_nonpos (sub_nonpos.mpr hba)]
    have h := log_sub_le_sub_of_one_le hb hba
    linarith

end Real

namespace RiemannResearch.Analysis

/-- A triadic integer normalized by an arbitrary natural power of two. -/
noncomputable def triadicDyadicMantissa (j r : ℕ) : ℝ :=
  (3 : ℝ) ^ (j + 1) / (2 : ℝ) ^ r

theorem triadicDyadicMantissa_pos (j r : ℕ) : 0 < triadicDyadicMantissa j r := by
  unfold triadicDyadicMantissa
  positivity

theorem triadicDyadicMantissa_log (j r : ℕ) :
    Real.log (triadicDyadicMantissa j r) =
      ((j : ℝ) + 1) * Real.log 3 - (r : ℝ) * Real.log 2 := by
  unfold triadicDyadicMantissa
  rw [Real.log_div (by positivity : (3 : ℝ) ^ (j + 1) ≠ 0)
    (by positivity : (2 : ℝ) ^ r ≠ 0), Real.log_pow, Real.log_pow]
  simp only [Nat.cast_add, Nat.cast_one]

/-- Exact logarithmic difference, retaining the integer normalization defect. -/
theorem triadicDyadicMantissa_log_difference {j k : ℕ} (hjk : j ≤ k) (r s : ℕ) :
    Real.log (triadicDyadicMantissa k s) - Real.log (triadicDyadicMantissa j r) =
      Real.log 2 * (((k - j : ℕ) : ℝ) * triadicRotation -
        (((s : ℤ) - (r : ℤ) : ℤ) : ℝ)) := by
  rw [triadicDyadicMantissa_log, triadicDyadicMantissa_log,
    Nat.cast_sub hjk, Int.cast_sub, Int.cast_natCast, Int.cast_natCast]
  dsimp [triadicRotation]
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp [hlog2]
  <;> ring

/-- Actual triadic mantissas dominate the rotation distance. No hypothesis
on the quality of the nearest-integer approximation is used. -/
theorem triadicDyadicMantissa_separation {j k r s : ℕ} (hjk : j ≤ k)
    (hj : 1 ≤ triadicDyadicMantissa j r) (hk : 1 ≤ triadicDyadicMantissa k s) :
    Real.log 2 * rotationNearestDistance triadicRotation (k - j) ≤
      |triadicDyadicMantissa j r - triadicDyadicMantissa k s| := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hnearest := rotationNearestDistance_le_integer_error triadicRotation (k - j)
    ((s : ℤ) - (r : ℤ))
  have hmul := mul_le_mul_of_nonneg_left hnearest hlog2.le
  have heq : Real.log 2 *
        |((k - j : ℕ) : ℝ) * triadicRotation -
          (((s : ℤ) - (r : ℤ) : ℤ) : ℝ)| =
      |Real.log (triadicDyadicMantissa k s) - Real.log (triadicDyadicMantissa j r)| := by
    rw [triadicDyadicMantissa_log_difference hjk r s,
      abs_mul, abs_of_pos hlog2]
  have hlogs := Real.abs_log_sub_le_abs_sub_of_one_le hj hk
  have h := (hmul.trans_eq heq).trans hlogs
  simpa only [abs_sub_comm] using h

theorem triadicDyadicMantissa_separation_pos {j k r s : ℕ} (hjk : j < k)
    (hj : 1 ≤ triadicDyadicMantissa j r) (hk : 1 ≤ triadicDyadicMantissa k s) :
    0 < |triadicDyadicMantissa j r - triadicDyadicMantissa k s| := by
  exact lt_of_lt_of_le
    (mul_pos (Real.log_pos (by norm_num))
      (triadicRotation_distance_pos (Nat.sub_pos_of_lt hjk)))
    (triadicDyadicMantissa_separation (Nat.le_of_lt hjk) hj hk)

theorem triadicDyadicMantissa_ne {j k r s : ℕ} (hjk : j < k)
    (hj : 1 ≤ triadicDyadicMantissa j r) (hk : 1 ≤ triadicDyadicMantissa k s) :
    triadicDyadicMantissa j r ≠ triadicDyadicMantissa k s :=
  sub_ne_zero.mp (abs_pos.mp (triadicDyadicMantissa_separation_pos hjk hj hk))

end RiemannResearch.Analysis
