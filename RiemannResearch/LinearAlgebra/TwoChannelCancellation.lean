import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact two-channel variance cancellation

Source: user-provided `ParetoCovarianceRepairReport_Advanced_2026-09-08.md`,
Section 3.4. These are genuine Hilbert-space identities. Quantitative channel
lower bounds remain explicit hypotheses; this module does not assert that the
arithmetic Mellin providers have been constructed.
-/

namespace RiemannResearch.LinearAlgebra.TwoChannelCancellation
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def centered (u f : E) : E := f - (inner ℝ u f) • u
def variance (u f : E) : ℝ := ‖centered u f‖ ^ 2
def covariance (u f g : E) : ℝ := inner ℝ (centered u f) (centered u g)
def correlation (u f g : E) : ℝ :=
  covariance u f g / (‖centered u f‖ * ‖centered u g‖)

theorem norm_add_sq (x y : E) :
    ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 + 2 * inner ℝ x y := by
  rw [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
    inner_add_right, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    real_inner_comm y x]
  ring

theorem centered_add (u f g : E) : centered u (f + g) = centered u f + centered u g := by
  simp only [centered, inner_add_right, add_smul]
  abel

theorem centered_sub (u f g : E) : centered u (f - g) = centered u f - centered u g := by
  simp only [centered, inner_sub_right, sub_smul]
  abel

theorem centered_self (u : E) (hu : ‖u‖ = 1) : centered u u = 0 := by
  simp [centered, real_inner_self_eq_norm_sq, hu]

theorem centered_energy (u f : E) (hu : ‖u‖ = 1) :
    variance u f = ‖f‖ ^ 2 - (inner ℝ u f)^2 := by
  have huu : inner ℝ u u = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  change ‖f - (inner ℝ u f) • u‖^2 = _
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, real_inner_self_eq_norm_sq, real_inner_comm f u,
    norm_smul, Real.norm_eq_abs, hu, mul_one, sq_abs]
  ring

theorem centered_norm_le (u f : E) (hu : ‖u‖ = 1) : ‖centered u f‖ ≤ ‖f‖ := by
  have h := centered_energy u f hu
  unfold variance at h
  nlinarith [sq_nonneg (inner ℝ u f), norm_nonneg (centered u f), norm_nonneg f]

theorem variance_add_identity (u f g : E) :
    variance u (f + g) = variance u f + variance u g + 2 * covariance u f g := by
  unfold variance covariance
  rw [centered_add, norm_add_sq]

theorem covariance_exact (u f g : E) :
    covariance u f g = (variance u (f+g) - variance u f - variance u g) / 2 := by
  have h := variance_add_identity u f g
  linarith

theorem variance_sum_le_error (u f g : E) (hu : ‖u‖ = 1) :
    variance u (f+g) ≤ ‖u - (f+g)‖^2 := by
  have h := centered_norm_le u (u - (f+g)) hu
  rw [centered_sub, centered_self u hu, zero_sub, norm_neg] at h
  unfold variance
  nlinarith [norm_nonneg (centered u (f+g)), norm_nonneg (u-(f+g))]

theorem covariance_upper_of_cost (u f g : E) (hu : ‖u‖ = 1)
    (C ε : ℝ) (hε : 0 < ε) (herr : ‖u-(f+g)‖ ≤ ε)
    (hf : C / ε^2 ≤ variance u f) (hg : C / ε^2 ≤ variance u g) :
    covariance u f g ≤ -C / ε^2 + ε^2 / 2 := by
  have hsum := variance_sum_le_error u f g hu
  have hid := variance_add_identity u f g
  have herrsq : ‖u-(f+g)‖^2 ≤ ε^2 := by nlinarith [norm_nonneg (u-(f+g))]
  rw [neg_div]
  linarith

theorem correlation_identity (u f g : E)
    (hf : ‖centered u f‖ ≠ 0) (hg : ‖centered u g‖ ≠ 0) :
    2 * (‖centered u f‖ * ‖centered u g‖) * (1 + correlation u f g) =
      variance u (f+g) - (‖centered u f‖ - ‖centered u g‖)^2 := by
  rw [variance_add_identity]
  unfold correlation variance
  field_simp
  ring

/-- Small total error forces the channel standard deviations to agree. -/
theorem standard_deviation_difference_le (u f g : E) (hu : ‖u‖ = 1)
    (ε : ℝ) (herr : ‖u-(f+g)‖ ≤ ε) :
    |‖centered u f‖ - ‖centered u g‖| ≤ ε := by
  have h := abs_norm_sub_norm_le (centered u f) (-centered u g)
  rw [norm_neg, sub_neg_eq_add, ← centered_add] at h
  have hc := centered_norm_le u (u-(f+g)) hu
  rw [centered_sub, centered_self u hu, zero_sub, norm_neg] at hc
  exact h.trans (hc.trans herr)

/-- The exact correlation remainder is nonnegative and bounded by total error. -/
theorem correlation_remainder_bounds (u f g : E) (hu : ‖u‖ = 1)
    (ε : ℝ) (hε : 0 ≤ ε) (herr : ‖u-(f+g)‖ ≤ ε) :
    0 ≤ variance u (f+g) - (‖centered u f‖ - ‖centered u g‖)^2 ∧
      variance u (f+g) - (‖centered u f‖ - ‖centered u g‖)^2 ≤ ε^2 := by
  have htri := abs_norm_sub_norm_le (centered u f) (-centered u g)
  rw [norm_neg, sub_neg_eq_add, ← centered_add] at htri
  have hnonneg : (‖centered u f‖ - ‖centered u g‖)^2 ≤ variance u (f+g) := by
    unfold variance
    nlinarith [sq_abs (‖centered u f‖ - ‖centered u g‖),
      abs_nonneg (‖centered u f‖ - ‖centered u g‖), norm_nonneg (centered u (f+g))]
  have he := variance_sum_le_error u f g hu
  have he' : ‖u-(f+g)‖^2 ≤ ε^2 := by nlinarith [norm_nonneg (u-(f+g))]
  constructor
  · linarith
  · nlinarith [sq_nonneg (‖centered u f‖ - ‖centered u g‖)]

/-- Quantitative fourth-power correlation cancellation, conditional only on
the stated standard-deviation lower bounds for the two actual vectors. -/
theorem correlation_fourth_power (u f g : E) (hu : ‖u‖ = 1)
    (K ε : ℝ) (hK : 0 < K) (hε : 0 < ε) (herr : ‖u-(f+g)‖ ≤ ε)
    (hf : K / ε ≤ ‖centered u f‖) (hg : K / ε ≤ ‖centered u g‖) :
    0 ≤ 1 + correlation u f g ∧ 1 + correlation u f g ≤ ε^4 / (2*K^2) := by
  have hpos := div_pos hK hε
  have hfp : 0 < ‖centered u f‖ := lt_of_lt_of_le hpos hf
  have hgp : 0 < ‖centered u g‖ := lt_of_lt_of_le hpos hg
  have hprod : (K / ε)^2 ≤ ‖centered u f‖ * ‖centered u g‖ := by
    simpa only [pow_two] using mul_le_mul hf hg hpos.le hfp.le
  have hid := correlation_identity u f g (ne_of_gt hfp) (ne_of_gt hgp)
  obtain ⟨hl, hr⟩ := correlation_remainder_bounds u f g hu ε hε.le herr
  have hden : 0 < 2 * (‖centered u f‖ * ‖centered u g‖) := by positivity
  have hc : 0 ≤ 1 + correlation u f g := by nlinarith
  refine ⟨hc, ?_⟩
  have hm := mul_le_mul_of_nonneg_right hprod hc
  have hbound : 2 * (K / ε)^2 * (1 + correlation u f g) ≤ ε^2 := by nlinarith
  have hε2 : 0 < ε^2 := sq_pos_of_pos hε
  have hK2 : 0 < 2*K^2 := by positivity
  apply (le_div_iff₀ hK2).mpr
  have he := (mul_le_mul_of_nonneg_right hbound hε2.le)
  have heq : (2 * (K / ε)^2 * (1 + correlation u f g)) * ε^2 =
      (1 + correlation u f g) * (2*K^2) := by
    field_simp
  rw [heq] at he
  nlinarith

end
end RiemannResearch.LinearAlgebra.TwoChannelCancellation
