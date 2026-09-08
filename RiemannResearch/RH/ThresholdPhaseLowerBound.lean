import RiemannResearch.RH.ThresholdPhaseSharpBound

/-!
# The matching lower correction for the phase summands

Source: Christian Noack, `RH_Two_Seed_Threshold.tex`, 8 September 2026,
Section 8, Lemma `lem:delta`. The proof uses a three-term logarithm upper
enclosure already proved in Mathlib, followed by an exact rational identity.
The positive numerator is written in powers of `k-1`, valid for every
positive integer `k`. This module does not certify the decimal constants.
-/

namespace RiemannResearch.RH.TwoSeedThreshold

open scoped BigOperators
open Pareto

theorem phaseDelta_lower_correction {k : ℕ} (hk : 0 < k) :
    positiveWeight k / 12 - 1 / (48 * ((k : ℝ) * ((k : ℝ) + 1))^2) ≤
      phaseDelta k := by
  have hk0 : 0 < (k : ℝ) := by exact_mod_cast hk
  have hk1 : 1 ≤ (k : ℝ) := by exact_mod_cast hk
  have hkm : 0 ≤ (k : ℝ) - 1 := by linarith
  have hkne : (k : ℝ) ≠ 0 := ne_of_gt hk0
  let z : ℝ := 1 / (2 * (k : ℝ) + 1)
  let U : ℝ := 2 * (z + z^3 / 3 + z^5 / 5 + z^7 / (1 - z^2))
  have hd : 0 < 2 * (k : ℝ) + 1 := by positivity
  have hz0 : 0 < z := by dsimp [z]; positivity
  have hz1 : z < 1 := by
    dsimp [z]
    apply (div_lt_one hd).2
    linarith
  have hzden : 0 < 1 - z^2 := by nlinarith
  have hzdenne : 1 - z^2 ≠ 0 := ne_of_gt hzden
  have hr : (1 + z) / (1 - z) = 1 + 1 / (k : ℝ) := by
    dsimp [z]
    field_simp
    <;> ring
  have h := Real.log_div_le_sum_range_add (le_of_lt hz0) hz1 3
  norm_num [Finset.sum_range_succ] at h
  rw [hr] at h
  have hU : Real.log (1 + 1 / (k : ℝ)) ≤ U := by dsimp [U]; linarith
  have hlog : 0 ≤ Real.log (1 + 1 / (k : ℝ)) :=
    Real.log_nonneg (by
      have hi : 0 ≤ 1 / (k : ℝ) := by positivity
      linarith)
  have hsq := (sq_le_sq₀ hlog (le_trans hlog hU)).2 hU
  have hid : (1 / ((k : ℝ) * ((k : ℝ) + 1)) -
      1 / (12 * ((k : ℝ) * ((k : ℝ) + 1))^2) +
      1 / (48 * ((k : ℝ) * ((k : ℝ) + 1))^3)) - U^2 =
      (1819044 + 35911728 * ((k : ℝ) - 1) +
        179887248 * ((k : ℝ) - 1)^2 +
        444259584 * ((k : ℝ) - 1)^3 +
        653303424 * ((k : ℝ) - 1)^4 +
        618388992 * ((k : ℝ) - 1)^5 +
        388044288 * ((k : ℝ) - 1)^6 +
        160911360 * ((k : ℝ) - 1)^7 +
        42439680 * ((k : ℝ) - 1)^8 +
        6451200 * ((k : ℝ) - 1)^9 +
        430080 * ((k : ℝ) - 1)^10) /
      (43200 * ((k : ℝ) * ((k : ℝ) + 1))^3 * (2 * (k : ℝ) + 1)^10) := by
    dsimp [U, z]
    field_simp
    ring_nf
    field_simp
    <;> ring
  have hnum : 0 ≤ (1819044 + 35911728 * ((k : ℝ) - 1) +
        179887248 * ((k : ℝ) - 1)^2 +
        444259584 * ((k : ℝ) - 1)^3 +
        653303424 * ((k : ℝ) - 1)^4 +
        618388992 * ((k : ℝ) - 1)^5 +
        388044288 * ((k : ℝ) - 1)^6 +
        160911360 * ((k : ℝ) - 1)^7 +
        42439680 * ((k : ℝ) - 1)^8 +
        6451200 * ((k : ℝ) - 1)^9 +
        430080 * ((k : ℝ) - 1)^10) /
      (43200 * ((k : ℝ) * ((k : ℝ) + 1))^3 * (2 * (k : ℝ) + 1)^10) := by positivity
  have hupper : Real.log (1 + 1 / (k : ℝ))^2 ≤
      1 / ((k : ℝ) * ((k : ℝ) + 1)) -
      1 / (12 * ((k : ℝ) * ((k : ℝ) + 1))^2) +
      1 / (48 * ((k : ℝ) * ((k : ℝ) + 1))^3) := by linarith
  have hm := mul_le_mul_of_nonneg_left hupper
    (by positivity : 0 ≤ (k : ℝ) * ((k : ℝ) + 1))
  have he : (k : ℝ) * ((k : ℝ) + 1) *
      (1 / ((k : ℝ) * ((k : ℝ) + 1)) -
        1 / (12 * ((k : ℝ) * ((k : ℝ) + 1))^2) +
        1 / (48 * ((k : ℝ) * ((k : ℝ) + 1))^3)) =
      1 - (positiveWeight k / 12 -
        1 / (48 * ((k : ℝ) * ((k : ℝ) + 1))^2)) := by
    unfold positiveWeight
    field_simp
    <;> ring
  rw [he] at hm
  unfold phaseDelta
  linarith

/-- A telescoping majorant for the retained fourth-order correction. -/
private theorem correction_step (x : ℝ) (hx : 0 < x) :
    1 / (48 * (x * (x + 1))^2) ≤
      1 / (144 * x^3) - 1 / (144 * (x + 1)^3) := by
  have he : (1 / (144 * x^3) - 1 / (144 * (x + 1)^3)) -
      1 / (48 * (x * (x + 1))^2) =
      1 / (144 * (x * (x + 1))^3) := by
    field_simp
    <;> ring
  have hn : 0 ≤ 1 / (144 * (x * (x + 1))^3) := by positivity
  linarith

/-- A direct finite lower certificate with its final rational boundary
term retained.  Its infinite limit requires no integral comparison. -/
theorem phase_sum_lower_telescoping (N J : ℕ) :
    (1 / (12 * ((N : ℝ) + 1)) -
      1 / (144 * ((N : ℝ) + 1)^3)) -
      (1 / (12 * ((N : ℝ) + J + 1)) -
        1 / (144 * ((N : ℝ) + J + 1)^3)) ≤
      ∑ k ∈ Finset.range J, phaseDelta (k + N + 1) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ]
    have hdelta := phaseDelta_lower_correction (k := J + N + 1) (by omega)
    have hstep := correction_step ((N : ℝ) + J + 1) (by positivity)
    have hw : positiveWeight (J + N + 1) =
        1 / ((N : ℝ) + J + 1) - 1 / ((N : ℝ) + J + 2) := by
      rw [positiveWeight_difference _ (by omega)]
      push_cast
      congr 2 <;> ring
    rw [hw] at hdelta
    push_cast at hdelta ⊢
    have hc : (↑J + ↑N + 1 : ℝ) * (↑J + ↑N + 1 + 1) =
        ((N : ℝ) + J + 1) * (((N : ℝ) + J + 1) + 1) := by ring
    rw [hc] at hdelta
    have hidx : (N : ℝ) + (J + 1) + 1 = (N : ℝ) + J + 1 + 1 := by ring
    rw [hidx]
    have hidx2 : (N : ℝ) + J + 2 = (N : ℝ) + J + 1 + 1 := by ring
    rw [hidx2] at hdelta
    norm_num [div_eq_mul_inv, mul_inv_rev] at ih hstep hdelta ⊢
    linarith

end RiemannResearch.RH.TwoSeedThreshold
