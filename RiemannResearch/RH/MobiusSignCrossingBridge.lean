import RiemannResearch.RH.CanonicalMobiusCesaro
import RiemannResearch.RH.ParetoPrimeSourceDivergence

/-!
# Finite Möbius sign-crossing bounds in the critical Pareto norm

The only arithmetic hypothesis is the displayed, decidable finite sign crossing.
No cofinality of these cutoffs, no Hardy identification, and no RH conclusion
is asserted here. Landau's theorem about infinitely many sign changes remains
external to this module. For that external statement, see Alladi and Johnson,
https://arxiv.org/html/2410.18259v1 , discussion after equation (3.19).
The finite inequalities below are elementary consequences of the exact Möbius
increment and the project's normalized-residue norm bound.
-/

noncomputable section

namespace RiemannResearch.RH.Pareto

private theorem abs_right_le_abs_sub_of_mul_nonpos {a b : ℝ}
    (h : a * b ≤ 0) : |b| ≤ |b - a| := by
  by_cases hb : b = 0
  · simp [hb]
  rcases lt_or_gt_of_ne hb with hbn | hbp
  · rw [abs_of_neg hbn]
    have ha : 0 ≤ a := by nlinarith
    calc
      -b ≤ -(b - a) := by linarith
      _ ≤ |b - a| := neg_le_abs _
  · rw [abs_of_pos hbp]
    have ha : a ≤ 0 := by nlinarith
    calc
      b ≤ b - a := by linarith
      _ ≤ |b - a| := le_abs_self _

/-- A sign crossing forces the new reciprocal sum below its single-step size. -/
theorem mobiusReciprocalSum_abs_le_inv_of_sign_crossing (N : ℕ)
    (hcross : mobiusReciprocalSum N * mobiusReciprocalSum (N + 1) ≤ 0) :
    |mobiusReciprocalSum (N + 1)| ≤ 1 / ((N + 1 : ℕ) : ℝ) := by
  have hden : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have hmu : |(ArithmeticFunction.moebius (N + 1) : ℝ)| ≤ 1 := by
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := N + 1))
  have hstep : mobiusReciprocalSum (N + 1) - mobiusReciprocalSum N =
      (ArithmeticFunction.moebius (N + 1) : ℝ) / ((N + 1 : ℕ) : ℝ) := by
    rw [mobiusReciprocalSum_succ]
    ring
  calc
    |mobiusReciprocalSum (N + 1)| ≤
        |mobiusReciprocalSum (N + 1) - mobiusReciprocalSum N| :=
      abs_right_le_abs_sub_of_mul_nonpos hcross
    _ = |(ArithmeticFunction.moebius (N + 1) : ℝ)| /
        ((N + 1 : ℕ) : ℝ) := by rw [hstep, abs_div, abs_of_pos hden]
    _ ≤ 1 / ((N + 1 : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right hmu hden.le

/-- At a crossing the critical finite-head ceiling is at most one over cutoff. -/
theorem mobiusReciprocalSum_critical_head_ceiling_of_sign_crossing (N : ℕ)
    (hcross : mobiusReciprocalSum N * mobiusReciprocalSum (N + 1) ≤ 0) :
    mobiusReciprocalSum (N + 1) ^ 2 * ((N + 1 : ℕ) : ℝ) ≤
      1 / ((N + 1 : ℕ) : ℝ) := by
  have hden : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have hs : mobiusReciprocalSum (N + 1) ^ 2 ≤
      (1 / ((N + 1 : ℕ) : ℝ)) ^ 2 := by
    have h := mul_self_le_mul_self (abs_nonneg (mobiusReciprocalSum (N + 1)))
      (mobiusReciprocalSum_abs_le_inv_of_sign_crossing N hcross)
    simpa only [← pow_two, sq_abs] using h
  calc
    _ ≤ (1 / ((N + 1 : ℕ) : ℝ)) ^ 2 * ((N + 1 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right hs hden.le
    _ = _ := by field_simp [ne_of_gt hden]

/-- The actual correction vector at cutoff `N + 1`, in the critical Hilbert space. -/
def mobiusBoundaryCorrectionAtCrossing (N : ℕ) : ThresholdHilbert :=
  (((N + 2 : ℕ) : ℝ) * mobiusReciprocalSum (N + 1)) •
    normalizedResidueHilbert (N + 2) (by omega)

/-- Finite sign crossings make the boundary correction quantitatively small
in the undamped, critical Pareto norm. -/
theorem mobiusBoundaryCorrectionAtCrossing_norm_sq_le (N : ℕ)
    (hcross : mobiusReciprocalSum N * mobiusReciprocalSum (N + 1) ≤ 0) :
    ‖mobiusBoundaryCorrectionAtCrossing N‖ ^ 2 ≤
      2 * ((N + 2 : ℕ) : ℝ) / ((N + 1 : ℕ) : ℝ) ^ 2 := by
  have hden : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have hnext : (0 : ℝ) < ((N + 2 : ℕ) : ℝ) := by positivity
  have hs : mobiusReciprocalSum (N + 1) ^ 2 ≤
      (1 / ((N + 1 : ℕ) : ℝ)) ^ 2 := by
    have h := mul_self_le_mul_self (abs_nonneg (mobiusReciprocalSum (N + 1)))
      (mobiusReciprocalSum_abs_le_inv_of_sign_crossing N hcross)
    simpa only [← pow_two, sq_abs] using h
  unfold mobiusBoundaryCorrectionAtCrossing
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  calc
    _ ≤ (((N + 2 : ℕ) : ℝ) * mobiusReciprocalSum (N + 1)) ^ 2 *
        (2 / ((N + 2 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (normalizedResidue_norm_sq_le (N + 2) (by omega)) (sq_nonneg _)
    _ = (2 * ((N + 2 : ℕ) : ℝ)) * mobiusReciprocalSum (N + 1) ^ 2 := by
      field_simp [ne_of_gt hnext]
      <;> ring
    _ ≤ (2 * ((N + 2 : ℕ) : ℝ)) *
        (1 / ((N + 1 : ℕ) : ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

end RiemannResearch.RH.Pareto
