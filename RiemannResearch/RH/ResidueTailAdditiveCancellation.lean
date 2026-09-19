import RiemannResearch.RH.ResidueTailCertificateRegularity
import RiemannResearch.RH.ParetoSignedTails
import RiemannResearch.Analysis.BoundedPrimitiveAbel
import RiemannResearch.Analysis.FirstMomentTails
import RiemannResearch.Analysis.LogPowerSummability
import Mathlib.Tactic.FieldSimp

/-!
# Additive cancellation excludes residue tail certificates

Source: user-provided
`RH_First_Coordinate_and_Tail_Capacity_Continuation_2026-09-19.md`,
Section 26.1, equations (26.5)--(26.8), for the Abel identity and sufficient
cancellation condition. The proof retains the signed Abel boundary. Weighted
summability of the ordinary signed partial sums is an additional hypothesis;
the actual canonical certificate has not been shown to satisfy it.
-/

noncomputable section
namespace RiemannResearch.RH.Pareto
open scoped BigOperators
open Filter

/-- Ordinary signed partial sum through the positive physical coordinate n.
For a tail certificate the first physical coordinate is zero, so this is
exactly the sum of its coordinates from 2 through n. -/
def additivePartialSum (h : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, h (k + 1)

@[simp] theorem additivePartialSum_zero (h : ℕ → ℝ) :
    additivePartialSum h 0 = 0 := by simp [additivePartialSum]

theorem additivePartialSum_succ (h : ℕ → ℝ) (n : ℕ) :
    additivePartialSum h (n + 1) = additivePartialSum h n + h (n + 1) := by
  simp [additivePartialSum, Finset.sum_range_succ]

private def abelWeight (n : ℕ) : ℝ :=
  1 / (((n : ℝ) + 1) * ((n : ℝ) + 2))

private theorem abelWeight_eq (n : ℕ) :
    abelWeight n = positiveWeight (n + 1) := by
  unfold abelWeight positiveWeight
  push_cast
  congr 1
  ring

private theorem abelWeight_nonneg (n : ℕ) : 0 ≤ abelWeight n := by
  unfold abelWeight
  positivity

private theorem abelWeight_difference (n : ℕ) :
    abelWeight n - abelWeight (n + 1) =
      2 / (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)) := by
  have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
  have h3 : (n : ℝ) + 3 ≠ 0 := by positivity
  have he : abelWeight (n + 1) =
      1 / (((n : ℝ) + 2) * ((n : ℝ) + 3)) := by
    unfold abelWeight
    push_cast
    congr 1
    ring
  rw [he]
  unfold abelWeight
  field_simp [h1, h2, h3]
  <;> ring

private def abelCorrection (h : ℕ → ℝ) (n : ℕ) : ℝ :=
  additivePartialSum h (n + 1) * (abelWeight n - abelWeight (n + 1))

private theorem abelBoundary_norm_le (h : ℕ → ℝ) (n : ℕ) :
    ‖additivePartialSum h n * abelWeight n‖ ≤
      |additivePartialSum h n| / ((n : ℝ) + 1) ^ 2 := by
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (abelWeight_nonneg n)]
  unfold abelWeight
  rw [mul_one_div]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  exact mul_le_mul_of_nonneg_left
    (by nlinarith [Nat.cast_nonneg (α := ℝ) n]) (abs_nonneg _)

private theorem abelCorrection_weighted_norm_le (h : ℕ → ℝ) (n : ℕ) :
    ((n : ℝ) + 1) * ‖abelCorrection h n‖ ≤
      2 * (|additivePartialSum h (n + 1)| / (((n + 1 : ℕ) : ℝ) + 1) ^ 2) := by
  have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
  have h3 : (n : ℝ) + 3 ≠ 0 := by positivity
  have he : ((n : ℝ) + 1) * ‖abelCorrection h n‖ =
      2 * |additivePartialSum h (n + 1)| /
        (((n : ℝ) + 2) * ((n : ℝ) + 3)) := by
    have hdnonneg : 0 ≤
        2 / (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)) := by positivity
    rw [abelCorrection, Real.norm_eq_abs, abs_mul, abelWeight_difference,
      abs_of_nonneg hdnonneg]
    field_simp [h1, h2, h3]
    <;> ring
  rw [he]
  have hc : (((n + 1 : ℕ) : ℝ) + 1) = (n : ℝ) + 2 := by push_cast; ring
  rw [hc, ← mul_div_assoc]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  exact mul_le_mul_of_nonneg_left
    (by nlinarith [Nat.cast_nonneg (α := ℝ) n]) (by positivity)

/-- The weighted signed partial-sum condition makes the Abel boundary a
summable sequence. In particular its value tends to zero. -/
private theorem abelBoundary_summable (h : ℕ → ℝ)
    (hc : Summable (fun n : ℕ =>
      |additivePartialSum h n| / ((n : ℝ) + 1) ^ 2)) :
    Summable (fun n => additivePartialSum h n * abelWeight n) := by
  exact hc.of_norm_bounded (abelBoundary_norm_le h)

private theorem abelCorrection_summable_firstMoment (h : ℕ → ℝ)
    (hc : Summable (fun n : ℕ =>
      |additivePartialSum h n| / ((n : ℝ) + 1) ^ 2)) :
    Summable (abelCorrection h) ∧
      Summable (fun n : ℕ => (n : ℝ) * |abelCorrection h n|) := by
  have hd := ((summable_nat_add_iff 1).mpr hc).mul_left (2 : ℝ)
  constructor
  · apply hd.of_norm_bounded
    intro n
    calc
      ‖abelCorrection h n‖ ≤ ((n : ℝ) + 1) * ‖abelCorrection h n‖ := by
        nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) n)
          (norm_nonneg (abelCorrection h n))]
      _ ≤ _ := abelCorrection_weighted_norm_le h n
  · apply hd.of_norm_bounded
    intro n
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Nat.cast_nonneg n), abs_abs]
    calc
      (n : ℝ) * |abelCorrection h n| ≤
          ((n : ℝ) + 1) * ‖abelCorrection h n‖ := by
        rw [Real.norm_eq_abs]
        nlinarith [abs_nonneg (abelCorrection h n)]
      _ ≤ _ := abelCorrection_weighted_norm_le h n

/-- Exact Abel formula (26.5) under the sufficient cancellation hypothesis.
The full infinite signed tail is retained; n indexes the physical tail
beginning at n+1. -/
theorem signedTail_abel_of_additiveCancellation (h : ℕ → ℝ)
    (hs : Summable (fun k => positiveWeight k * h k ^ 2))
    (hc : Summable (fun n : ℕ =>
      |additivePartialSum h n| / ((n : ℝ) + 1) ^ 2)) (n : ℕ) :
    signedTail h (n + 1) =
      -additivePartialSum h n * positiveWeight (n + 1) +
        ∑' j : ℕ, additivePartialSum h (j + n + 1) *
          (positiveWeight (j + n + 1) - positiveWeight (j + n + 2)) := by
  have hleft : Summable (fun k : ℕ =>
      (additivePartialSum h (k + 1 + n) - additivePartialSum h (k + n)) *
        abelWeight (k + n)) := by
    have hl := (summable_nat_add_iff (n + 1)).mpr (signedCoefficient_summable hs)
    apply hl.congr
    intro k
    rw [show k + 1 + n = (k + n) + 1 by omega, additivePartialSum_succ,
      add_sub_cancel_left, abelWeight_eq]
    simp only [signedCoefficient]
    rw [show k + n + 1 = k + (n + 1) by omega]
    ring
  have hright : Summable (fun k : ℕ =>
      additivePartialSum h (k + 1 + n) *
        (abelWeight (k + n) - abelWeight (k + 1 + n))) := by
    have hr := (summable_nat_add_iff n).mpr (abelCorrection_summable_firstMoment h hc).1
    apply hr.congr
    intro k
    simp only [abelCorrection, show k + 1 + n = k + n + 1 by omega]
  have hend : Tendsto (fun N : ℕ => additivePartialSum h (N + n) *
      abelWeight (N + n)) atTop (nhds 0) :=
    ((summable_nat_add_iff n).mpr (abelBoundary_summable h hc)).tendsto_atTop_zero
  have hab := RiemannResearch.Analysis.boundedPrimitive_abel_tsum
    (fun k => additivePartialSum h (k + n)) (fun k => abelWeight (k + n))
    hleft hright hend
  have heleft : (∑' k : ℕ,
      (additivePartialSum h (k + 1 + n) - additivePartialSum h (k + n)) *
        abelWeight (k + n)) = signedTail h (n + 1) := by
    apply tsum_congr
    intro k
    rw [show k + 1 + n = (k + n) + 1 by omega, additivePartialSum_succ,
      add_sub_cancel_left, abelWeight_eq]
    simp only [signedCoefficient]
    rw [show k + n + 1 = k + (n + 1) by omega]
    ring
  rw [heleft] at hab
  calc
    signedTail h (n + 1) = _ := hab
    _ = _ := by
      simp only [Nat.zero_add, abelWeight_eq]
      congr 1
      apply tsum_congr
      intro k
      simp only [show k + 1 + n = k + n + 1 by omega]

/-- The substantive analytic step in Corollary 26.2: weighted additive
cancellation implies absolute summability of all signed Pareto tails. -/
theorem anchoredSignedTail_summable_of_additiveCancellation (h : ℕ → ℝ)
    (hs : Summable (fun k => positiveWeight k * h k ^ 2))
    (hc : Summable (fun n : ℕ =>
      |additivePartialSum h n| / ((n : ℝ) + 1) ^ 2)) :
    Summable (anchoredSignedTail h) := by
  obtain ⟨ha, hm⟩ := abelCorrection_summable_firstMoment h hc
  have ht := RiemannResearch.Analysis.rawTail_summable_of_firstMoment
    (abelCorrection h) ha hm
  have hb := abelBoundary_summable h hc
  have hpos : Summable (fun n : ℕ => anchoredSignedTail h (n + 1)) := by
    apply (hb.neg.add ht).congr
    intro n
    rw [anchoredSignedTail_pos h (by omega),
      signedTail_abel_of_additiveCancellation h hs hc n]
    simp only [abelWeight_eq, neg_mul, abelCorrection]
  exact (summable_nat_add_iff 1).mp hpos

/-- Equation (26.7) excludes every actual tail certificate. This is a
conditional obstruction: no estimate on an actual certificate is assumed
merely from its Hilbert-space membership. -/
theorem tailCertificate_not_summable_additiveCancellation (z : ThresholdHilbert)
    (hz : IsResidueTailCertificate z) :
    ¬ Summable (fun n : ℕ =>
      |additivePartialSum (hilbertSequence z) n| / ((n : ℝ) + 1) ^ 2) := by
  intro hc
  exact tailCertificate_not_summable_signedTail z hz
    (anchoredSignedTail_summable_of_additiveCancellation (hilbertSequence z)
      (hilbertSequence_square_summable z) hc)

/-- The unshifted square denominator in (26.7) implies the condition used
in the Abel proof. The zero term is zero under Lean's division convention. -/
theorem summable_additiveCancellation_of_div_square (h : ℕ → ℝ)
    (hc : Summable (fun n : ℕ =>
      |additivePartialSum h n| / (n : ℝ) ^ 2)) :
    Summable (fun n : ℕ =>
      |additivePartialSum h n| / ((n : ℝ) + 1) ^ 2) := by
  apply hc.of_norm_bounded
  intro n
  by_cases hn : n = 0
  · subst n
    simp
  · have hnR : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    exact mul_le_mul_of_nonneg_left
      (by nlinarith [Nat.cast_nonneg (α := ℝ) n]) (abs_nonneg _)

/-- Literal square-denominator form of the certificate exclusion (26.7).
For an actual tail certificate, additivePartialSum is precisely Z. -/
theorem tailCertificate_not_summable_partialSum_div_square (z : ThresholdHilbert)
    (hz : IsResidueTailCertificate z) :
    ¬ Summable (fun n : ℕ =>
      |additivePartialSum (hilbertSequence z) n| / (n : ℝ) ^ 2) := by
  intro hc
  exact tailCertificate_not_summable_additiveCancellation z hz
    (summable_additiveCancellation_of_div_square (hilbertSequence z) hc)


/-- The power-saving alternative in (26.8), expressed as an eventual
explicit bound, supplies the weighted cancellation hypothesis (26.7). -/
theorem additiveCancellation_of_eventual_power_saving (h : ℕ → ℝ)
    {η C : ℝ} (hη : 0 < η)
    (hb : ∀ᶠ n : ℕ in atTop,
      |additivePartialSum h n| ≤ C * (n : ℝ) ^ (1 - η)) :
    Summable (fun n : ℕ => |additivePartialSum h n| / (n : ℝ) ^ 2) := by
  have hp : Summable (fun n : ℕ => (n : ℝ) ^ (-1 - η)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  apply (hp.mul_left C).of_norm_bounded_eventually_nat
  filter_upwards [hb, eventually_ge_atTop 1] with n hn hn1
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have he : (n : ℝ) ^ (1 - η) / (n : ℝ) ^ 2 =
      (n : ℝ) ^ (-1 - η) := by
    rw [← Real.rpow_natCast (n : ℝ) 2, ← Real.rpow_sub hnR]
    congr 1
    norm_num
    <;> ring
  calc
    |additivePartialSum h n| / (n : ℝ) ^ 2 ≤
        (C * (n : ℝ) ^ (1 - η)) / (n : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hn (sq_nonneg _)
    _ = C * (n : ℝ) ^ (-1 - η) := by rw [mul_div_assoc, he]

/-- Every positive power saving for the ordinary signed partial sums is
incompatible with being an actual residue tail certificate. -/
theorem tailCertificate_no_eventual_power_saving (z : ThresholdHilbert)
    (hz : IsResidueTailCertificate z) {η C : ℝ} (hη : 0 < η) :
    ¬ (∀ᶠ n : ℕ in atTop,
      |additivePartialSum (hilbertSequence z) n| ≤ C * (n : ℝ) ^ (1 - η)) := by
  intro hb
  exact tailCertificate_not_summable_partialSum_div_square z hz
    (additiveCancellation_of_eventual_power_saving (hilbertSequence z) hη hb)


/-- The logarithmic-saving alternative in (26.8) supplies (26.7), with
summability of the classical majorant established above. -/
theorem additiveCancellation_of_eventual_log_saving (h : ℕ → ℝ)
    {η C : ℝ} (hη : 0 < η)
    (hb : ∀ᶠ n : ℕ in atTop,
      |additivePartialSum h n| ≤
        C * (n : ℝ) / Real.log (2 * (n : ℝ)) ^ (1 + η)) :
    Summable (fun n : ℕ => |additivePartialSum h n| / (n : ℝ) ^ 2) := by
  have hs := RiemannResearch.Analysis.summable_log_power_majorant
    (show 1 < 1 + η by linarith)
  apply (hs.mul_left C).of_norm_bounded_eventually_nat
  filter_upwards [hb, eventually_ge_atTop 1] with n hn hn1
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hnR1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hlog : 0 < Real.log (2 * (n : ℝ)) := Real.log_pos (by linarith)
  have hp : Real.log (2 * (n : ℝ)) ^ (1 + η) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hlog _)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    |additivePartialSum h n| / (n : ℝ) ^ 2 ≤
        (C * (n : ℝ) / Real.log (2 * (n : ℝ)) ^ (1 + η)) / (n : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hn (sq_nonneg _)
    _ = C * (1 / ((n : ℝ) * Real.log (2 * (n : ℝ)) ^ (1 + η))) := by
      field_simp [ne_of_gt hnR, hp]
      <;> ring

theorem tailCertificate_no_eventual_log_saving (z : ThresholdHilbert)
    (hz : IsResidueTailCertificate z) {η C : ℝ} (hη : 0 < η) :
    ¬ (∀ᶠ n : ℕ in atTop,
      |additivePartialSum (hilbertSequence z) n| ≤
        C * (n : ℝ) / Real.log (2 * (n : ℝ)) ^ (1 + η)) := by
  intro hb
  exact tailCertificate_not_summable_partialSum_div_square z hz
    (additiveCancellation_of_eventual_log_saving (hilbertSequence z) hη hb)

end RiemannResearch.RH.Pareto
