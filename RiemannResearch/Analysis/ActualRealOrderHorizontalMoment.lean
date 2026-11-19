/-
Copyright (c) 2026 RiemannResearch contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.ActualSizeBiasedDisplacement
import RiemannResearch.Analysis.FiniteSizeBiasedRealPowers
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Sharp first-moment feedback at every real order above one

Source for the asymptotic coefficient and the extremal-law question:
SparseHorizontalMomentModulus20261119.md. Here the high part of the moment
is bounded by a size-biased exponential tilt, with slack in the tilt and
in the moving cut. No uniformity in the tilt parameter is used.
-/

noncomputable section
open Filter Set Zeta23
open scoped Topology BigOperators

namespace RiemannResearch.Analysis.ActualZeroOrdinate

def microscopicRealMoment (T s : ℝ) : ℝ :=
  (∑ j : Copies T, (copyDisplacement T j * Real.log T) ^ s) / (Ncount 0 T : ℝ)

private theorem real_moment_cut {T v a b r : ℝ} (hT : 1 < T) (hv : 0 < v)
    (hb : 0 < b) (hab : b < a) (hr : 0 ≤ r) :
    microscopicRealMoment T (1 + v) ≤ r ^ v * (displacementMoment T 1 * Real.log T) +
      ((v / (a - b)) ^ v * Real.exp (-(b * r))) * microscopicSizeBiasedTilt T a := by
  let x := fun j : Copies T => copyDisplacement T j * Real.log T
  let K := (v / (a - b)) ^ v
  have hK : 0 ≤ K := Real.rpow_nonneg (div_nonneg hv.le (sub_nonneg.mpr hab.le)) _
  have hmean : (∑ j : Copies T, x j) / (Ncount 0 T : ℝ) =
      displacementMoment T 1 * Real.log T := by
    simp only [x, ← Finset.sum_mul, displacementMoment, pow_one]
    ring
  have hpoint (j : Copies T) : x j ^ (1 + v) ≤
      r ^ v * x j + (K * Real.exp (-(b * r))) * (x j * Real.exp (a * x j)) := by
    have hx : 0 ≤ x j := mul_nonneg (abs_nonneg _) (Real.log_pos hT).le
    rcases eq_or_lt_of_le hx with hz | hp
    · rw [← hz, Real.zero_rpow (by linarith : (1 : ℝ) + v ≠ 0)]
      simp
    rw [Real.rpow_add hp, Real.rpow_one]
    rcases le_total (x j) r with hlow | hhigh
    · apply (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx hlow hv.le) hx).trans
      rw [mul_comm (x j) (r ^ v)]
      exact le_add_of_nonneg_right (by positivity)
    · have H := FiniteSizeBiasedExponential.rpow_le_exp_multiple hv (sub_pos.mpr hab) hx
      have he : Real.exp ((a - b) * x j) ≤ Real.exp (-(b * r)) * Real.exp (a * x j) := by
        rw [← Real.exp_add, Real.exp_le_exp]
        nlinarith only [mul_nonneg hb.le (sub_nonneg.mpr hhigh)]
      have htail := mul_le_mul_of_nonneg_left (H.trans (mul_le_mul_of_nonneg_left he hK)) hx
      calc
        _ ≤ x j * (K * (Real.exp (-(b * r)) * Real.exp (a * x j))) := htail
        _ = (K * Real.exp (-(b * r))) * (x j * Real.exp (a * x j)) := by ring
        _ ≤ _ := le_add_of_nonneg_left (mul_nonneg (Real.rpow_nonneg hr _) hx)
  rw [← hmean]
  unfold microscopicRealMoment microscopicSizeBiasedTilt
  change (∑ j : Copies T, x j ^ (1 + v)) / _ ≤
    _ + (K * _) * ((∑ j : Copies T, x j * Real.exp (a * x j)) / _)
  rw [← mul_div_assoc, ← mul_div_assoc, ← add_div, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun j _ => hpoint j) (Nat.cast_nonneg _)

local notation "m₁" => (fun T : ℝ => displacementMoment T 1 * Real.log T)
local notation "M₁" => (fun T : ℝ => Real.log (1 / m₁ T))

/-- The coefficient (7/8)^(s-1) at every fixed real s>1 along a family of
heights with positive, vanishing microscopic mean. -/
theorem actual_realMoment_ratio_le_of_conreyBaluyot
    (hD : ConreyBaluyotDensityHypothesis) {s c : ℝ} (hs : 1 < s)
    (hc : (7 / 8 : ℝ) ^ (s - 1) < c)
    {ι : Type*} {l : Filter ι} {T : ι → ℝ} (hT : Tendsto T l atTop)
    (hm : Tendsto (fun i => m₁ (T i)) l (𝓝 0))
    (hp : ∀ᶠ i in l, 0 < m₁ (T i)) :
    ∀ᶠ i in l, microscopicRealMoment (T i) s / (m₁ (T i) * M₁ (T i) ^ (s - 1)) ≤ c := by
  let v := s - 1
  have hv : 0 < v := sub_pos.mpr hs
  have hcont : ContinuousAt (fun u : ℝ => u ^ v) (7 / 8) := by fun_prop (disch := norm_num)
  have hnear : ∀ᶠ u : ℝ in 𝓝[>] (7 / 8 : ℝ), u ^ v < c :=
    (hcont.tendsto.mono_left nhdsWithin_le_nhds).eventually_lt_const hc
  have hright : ∀ᶠ u : ℝ in 𝓝[>] (7 / 8 : ℝ), 7 / 8 < u := self_mem_nhdsWithin
  obtain ⟨k, hk, hkc⟩ := (hright.and hnear).exists
  change 7 / 8 < k at hk
  have hk0 : 0 < k := lt_trans (by norm_num : (0 : ℝ) < 7 / 8) hk
  have hkA : 1 / k < 8 / 7 := (div_lt_iff₀ hk0).mpr (by linarith only [hk])
  obtain ⟨b, hb, hbA⟩ := exists_between hkA
  obtain ⟨a, hba, haA⟩ := exists_between hbA
  have hb0 := (one_div_pos.mpr hk0).trans hb
  have hδ : 0 < b * k - 1 := sub_pos.mpr ((div_lt_iff₀ hk0).mp hb)
  obtain ⟨K,hK,htilt⟩ := exists_actual_sizeBiased_cap_of_conreyBaluyot hD (hb0.trans hba) haA
  let B := (v / (a - b)) ^ v
  have hB : 0 ≤ B := Real.rpow_nonneg (div_nonneg hv.le (sub_nonneg.mpr hba.le)) _
  have hM : Tendsto (fun i => M₁ (T i)) l atTop := by
    apply tendsto_atTop.2
    intro z
    filter_upwards [hp, hm.eventually (Iio_mem_nhds (Real.exp_pos (-z)))] with i hi hm'
    have H := Real.log_le_log hi hm'.le
    rw [Real.log_exp] at H
    change z ≤ Real.log (1 / m₁ (T i))
    rw [Real.log_div one_ne_zero hi.ne', Real.log_one]
    linarith
  have hscale : Tendsto (fun i => (b * k - 1) * M₁ (T i)) l atTop := by
    apply tendsto_atTop.2
    intro z
    filter_upwards [(tendsto_atTop.1 hM) (z / (b * k - 1))] with i hi
    simpa only [mul_comm] using (div_le_iff₀ hδ).mp hi
  have herr : Tendsto (fun i => B * K * Real.exp (-((b * k - 1) * M₁ (T i)))) l (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp hscale).const_mul (B * K)
  filter_upwards [hp, hM.eventually (eventually_ge_atTop (1 : ℝ)), hT.eventually htilt,
    hT.eventually (eventually_gt_atTop (1 : ℝ)), herr.eventually_lt_const (sub_pos.mpr hkc)]
    with i hi hM1 hcap ht he
  let m := m₁ (T i)
  let M := M₁ (T i)
  have hMp : 0 < M := zero_lt_one.trans_le hM1
  have hmexp : Real.exp (-M) = m := by
    change Real.exp (-Real.log (1 / m)) = m
    rw [Real.log_div one_ne_zero hi.ne', Real.log_one, zero_sub, neg_neg, Real.exp_log hi]
  have hex : Real.exp (-(b * (k * M))) = m * Real.exp (-((b * k - 1) * M)) := by
    rw [← hmexp, ← Real.exp_add]
    congr 1
    ring
  have hMv : 1 ≤ M ^ v := Real.one_le_rpow hM1 hv.le
  have hraw := real_moment_cut ht hv hb0 hba (mul_nonneg hk0.le hMp.le)
  rw [show 1 + v = s by dsimp [v]; ring, Real.mul_rpow hk0.le hMp.le, hex] at hraw
  have hKcap := mul_le_mul_of_nonneg_left hcap.1
    (mul_nonneg hB (mul_nonneg hi.le (Real.exp_pos (-((b * k - 1) * M))).le))
  apply (div_le_iff₀ (mul_pos hi (Real.rpow_pos_of_pos hMp v))).mpr
  apply (hraw.trans (add_le_add le_rfl hKcap)).trans
  let E := B * K * Real.exp (-((b * k - 1) * M))
  have he0 : 0 ≤ E := mul_nonneg (mul_nonneg hB hK.le) (Real.exp_pos _).le
  have hz := mul_le_mul_of_nonneg_left hMv (mul_nonneg hi.le he0)
  calc
    _ = (k ^ v) * (m * M ^ v) + m * E := by dsimp only [E]; ring
    _ ≤ (k ^ v) * (m * M ^ v) + (m * E) * M ^ v := add_le_add le_rfl (by simpa using hz)
    _ = (k ^ v + E) * (m * M ^ v) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by change k ^ v + E ≤ c; change E < c - k ^ v at he; linarith)
      (mul_nonneg hi.le (Real.rpow_nonneg hMp.le v))

end RiemannResearch.Analysis.ActualZeroOrdinate
