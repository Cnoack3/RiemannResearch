import RiemannResearch.RH.CRTTrigammaMeanValue

/-!
# Uniform error of the physical trigamma mean point

The cubic fixed-residue estimate combines with the geometric/arithmetic
mean sandwich to give a bound uniform over all real residues at least one.
This is a scalar statement; it supplies no Gram-inverse or saturation bound.

Source: continuation of the user-provided mean-point argument, 24 September 2026.
-/

namespace RiemannResearch.RH.CRTBlock
noncomputable section

/-- A uniform fourth-power error bound for every real residue at least one.
Unlike the original cubic estimate, its right side is independent of `r`. -/
theorem progressionAlpha_scaled_error_fourth_uniform
    (r L : ℝ) (hr : 1 ≤ r) (hL : 0 < L) :
    (L * progressionAlpha r L (by linarith) hL -
      Real.sqrt (r * (r + 1))) ^ 4 ≤ trigamma 1 / (512 * L ^ 3) := by
  have cancel {a b c : ℝ} (hc : 0 < c) (hab : c*a ≤ c*b) : a ≤ b := by
    by_contra hn
    have hp := mul_pos hc (sub_pos.mpr (lt_of_not_ge hn))
    nlinarith
  have hrpos : 0 < r := by linarith
  let s : ℝ := Real.sqrt (r * (r + 1))
  let e : ℝ := L * progressionAlpha r L hrpos hL - s
  let K : ℝ := trigamma 1
  have hspos : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hs2 : s ^ 2 = r * (r + 1) := Real.sq_sqrt (by positivity)
  have hK : 0 < K := trigamma_pos (by norm_num)
  have herror := progressionAlpha_scaled_error_cubic r L hrpos hL
  have he : 0 ≤ e := herror.1
  have hupper : e ≤ K * r * (r + 1) ^ 3 / (2 * s * L ^ 3) := by
    calc
      e ≤ (K * r * (r + 1) * (r + 1) ^ 2) / (2 * s * L ^ 3) := herror.2
      _ = _ := by ring
  have hm := trigammaMean_lt_midpoint (r / L) ((r + 1) / L)
    (div_pos hrpos hL) ((div_lt_div_iff_of_pos_right hL).2 (by linarith))
  change progressionAlpha r L hrpos hL < (r / L + (r + 1) / L) / 2 at hm
  have hmid : s + e < r + 1 / 2 := by
    calc
      s + e = L * progressionAlpha r L hrpos hL := by dsimp [e]; ring
      _ < L * ((r / L + (r + 1) / L) / 2) := mul_lt_mul_of_pos_left hm hL
      _ = r + 1 / 2 := by field_simp [ne_of_gt hL]; ring
  have hmidSquare := mul_nonneg
    (show 0 ≤ r + 1 / 2 - (s + e) by linarith)
    (show 0 ≤ r + 1 / 2 + (s + e) by positivity)
  have hsmall : 8 * s * e ≤ 1 := by
    nlinarith only [hmidSquare, hs2, sq_nonneg e]
  have hsmallNonneg : 0 ≤ 8 * s * e := by positivity
  have hsmallSq : (8 * s * e) ^ 2 ≤ 1 := by
    have h := mul_nonneg (sub_nonneg.mpr hsmall)
      (show 0 ≤ 1 + 8 * s * e by positivity)
    nlinarith only [h]
  have hsmallCube : 512 * s ^ 3 * e ^ 3 ≤ 1 := by
    calc
      512 * s ^ 3 * e ^ 3 = (8 * s * e) ^ 2 * (8 * s * e) := by ring
      _ ≤ 1 * 1 := mul_le_mul hsmallSq hsmall hsmallNonneg (by norm_num)
      _ = 1 := by norm_num
  have hupperScaled : e * (2 * s * L ^ 3) ≤ K * r * (r + 1) ^ 3 :=
    (le_div_iff₀ (show 0 < 2 * s * L ^ 3 by positivity)).mp hupper
  have hproduct := mul_le_mul hupperScaled hsmallCube
    (show 0 ≤ 512 * s ^ 3 * e ^ 3 by positivity)
    (show 0 ≤ K * r * (r + 1) ^ 3 by positivity)
  have hs4 : s ^ 4 = (r * (r + 1)) ^ 2 := by
    calc
      s ^ 4 = (s ^ 2) ^ 2 := by ring
      _ = _ := by rw [hs2]
  have hidentity :
      (e * (2 * s * L ^ 3)) * (512 * s ^ 3 * e ^ 3) =
        (r * (r + 1) ^ 2) * (1024 * r * L ^ 3 * e ^ 4) := by
    calc
      _ = 1024 * s ^ 4 * L ^ 3 * e ^ 4 := by ring
      _ = _ := by rw [hs4]; ring
  have hscaled : 1024 * r * L ^ 3 * e ^ 4 ≤ K * (r + 1) := by
    apply cancel (show 0 < r * (r + 1) ^ 2 by positivity)
    calc
      _ = (e * (2 * s * L ^ 3)) * (512 * s ^ 3 * e ^ 3) := hidentity.symm
      _ ≤ (K * r * (r + 1) ^ 3) * 1 := hproduct
      _ = _ := by ring
  have hresidue : r + 1 ≤ 2 * r := by linarith
  have hfinal : 512 * L ^ 3 * e ^ 4 ≤ K := by
    apply cancel (show 0 < 2 * r by positivity)
    calc
      _ = 1024 * r * L ^ 3 * e ^ 4 := by ring
      _ ≤ K * (r + 1) := hscaled
      _ ≤ K * (2 * r) := mul_le_mul_of_nonneg_left hresidue hK.le
      _ = _ := by ring
  change e ^ 4 ≤ K / (512 * L ^ 3)
  apply (le_div_iff₀ (show 0 < 512 * L ^ 3 by positivity)).mpr
  nlinarith only [hfinal]

end
end RiemannResearch.RH.CRTBlock
