import RiemannResearch.RH.CanonicalMobiusMovingBoundary
import Mathlib.Tactic.FieldSimp

/-!
# Midpoint tail energies and exact-head Hardy transfer

Source: user's comparison of commits d66e444 and 1235e6b.
The elementary midpoint weight identity connects trigamma quadrature to
the complete Pareto energy, without requiring a bound for any Gram inverse.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.Pareto
open WeightedMellin

def midpointTailFactor (N : ℕ) : ℝ := 1 - 1 / (2 * (N : ℝ) + 3)^2

def midpointEnergy (f : ThresholdHilbert) : ℝ :=
  ∑' n : ℕ, (positiveWeight n * hilbertSequence f n ^ 2) *
    (1 - 1 / (2 * (n : ℝ) + 1)^2)

/-- The energy is precisely the untruncated physical midpoint sum. -/
theorem midpointEnergy_eq_physical (f : ThresholdHilbert) :
    midpointEnergy f = ∑' n : ℕ, hilbertSequence f n ^ 2 / ((n : ℝ) + 1/2)^2 := by
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst n
    simp
  · have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have hn2 : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
    have hn3 : (n : ℝ) + 1/2 ≠ 0 := by positivity
    unfold positiveWeight
    field_simp [hn0, hn1, hn2, hn3]
    ring

private theorem midpoint_ratio_mem_Icc (n : ℕ) :
    0 ≤ 1 - 1 / (2 * (n : ℝ) + 1)^2 ∧
      1 - 1 / (2 * (n : ℝ) + 1)^2 ≤ 1 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hp : 0 < (2 * (n : ℝ) + 1)^2 := by positivity
  have hle : 1 / (2 * (n : ℝ) + 1)^2 ≤ 1 :=
    (div_le_iff₀ hp).2 (by nlinarith)
  have hlo : 0 ≤ 1 / (2 * (n : ℝ) + 1)^2 := by positivity
  constructor <;> linarith

theorem midpointEnergy_summable (f : ThresholdHilbert) :
    Summable (fun n : ℕ => (positiveWeight n * hilbertSequence f n ^ 2) *
      (1 - 1 / (2 * (n : ℝ) + 1)^2)) := by
  apply Summable.of_nonneg_of_le _ _ (hilbertSequence_square_summable f)
  · intro n
    exact mul_nonneg (mul_nonneg (positiveWeight_nonneg n) (sq_nonneg _))
      (midpoint_ratio_mem_Icc n).1
  · intro n
    exact mul_le_of_le_one_right
      (mul_nonneg (positiveWeight_nonneg n) (sq_nonneg _))
      (midpoint_ratio_mem_Icc n).2

theorem midpointEnergy_nonneg (f : ThresholdHilbert) : 0 ≤ midpointEnergy f := by
  apply tsum_nonneg
  intro n
  exact mul_nonneg (mul_nonneg (positiveWeight_nonneg n) (sq_nonneg _))
    (midpoint_ratio_mem_Icc n).1

theorem midpointEnergy_le_norm_sq (f : ThresholdHilbert) :
    midpointEnergy f ≤ ‖f‖^2 := by
  rw [hilbert_norm_weighted_sq]
  apply (midpointEnergy_summable f).tsum_le_tsum _ (hilbertSequence_square_summable f)
  intro n
  exact mul_le_of_le_one_right
    (mul_nonneg (positiveWeight_nonneg n) (sq_nonneg _))
    (midpoint_ratio_mem_Icc n).2

theorem midpointTailFactor_pos (N : ℕ) : 0 < midpointTailFactor N := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hp : 0 < (2 * (N : ℝ) + 3)^2 := by positivity
  have hlt : 1 / (2 * (N : ℝ) + 3)^2 < 1 :=
    (div_lt_iff₀ hp).2 (by nlinarith)
  unfold midpointTailFactor
  linarith

theorem midpointTailFactor_ge (N : ℕ) : (8/9 : ℝ) ≤ midpointTailFactor N := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hden : (9 : ℝ) ≤ (2 * (N : ℝ) + 3)^2 := by nlinarith
  have hinv : 1 / (2 * (N : ℝ) + 3)^2 ≤ 1 / 9 :=
    div_le_div_of_nonneg_left zero_le_one (by norm_num) hden
  unfold midpointTailFactor
  linarith

theorem midpointEnergy_ge_of_zero_head (f : ThresholdHilbert) (N : ℕ)
    (hhead : ∀ n, 0 < n → n ≤ N → hilbertSequence f n = 0) :
    midpointTailFactor N * ‖f‖^2 ≤ midpointEnergy f := by
  rw [hilbert_norm_weighted_sq, ← tsum_mul_left]
  apply ((hilbertSequence_square_summable f).mul_left _).tsum_le_tsum _
    (midpointEnergy_summable f)
  intro n
  by_cases hn0 : n = 0
  · subst n
    simp
  by_cases hn : n ≤ N
  · simp [hhead n (Nat.pos_of_ne_zero hn0) hn]
  · have hnr : (N : ℝ) + 1 ≤ n := by
      exact_mod_cast (Nat.succ_le_of_lt (Nat.lt_of_not_ge hn))
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have hden : (2 * (N : ℝ) + 3)^2 ≤ (2 * (n : ℝ) + 1)^2 := by
      nlinarith
    have hinv : 1 / (2 * (n : ℝ) + 1)^2 ≤ 1 / (2 * (N : ℝ) + 3)^2 :=
      div_le_div_of_nonneg_left zero_le_one (by positivity) hden
    have hfac : midpointTailFactor N ≤ 1 - 1 / (2 * (n : ℝ) + 1)^2 := by
      unfold midpointTailFactor
      linarith
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right hfac
      (mul_nonneg (positiveWeight_nonneg n) (sq_nonneg _))

/-- The full Pareto norm of any exact-head residual is certified by its
midpoint energy with a relative loss tending to one. -/
theorem norm_sq_le_midpointEnergy_of_zero_head (f : ThresholdHilbert) (N : ℕ)
    (hhead : ∀ n, 0 < n → n ≤ N → hilbertSequence f n = 0) :
    ‖f‖^2 ≤ midpointEnergy f / midpointTailFactor N := by
  apply (le_div_iff₀ (midpointTailFactor_pos N)).2
  simpa only [mul_comm] using midpointEnergy_ge_of_zero_head f N hhead

/-- Complete positive quadrature error; there is no discarded residue tail. -/
theorem midpointEnergy_zeroHead_error (f : ThresholdHilbert) (N : ℕ)
    (hhead : ∀ n, 0 < n → n ≤ N → hilbertSequence f n = 0) :
    0 ≤ ‖f‖^2 - midpointEnergy f ∧
      ‖f‖^2 - midpointEnergy f ≤ ‖f‖^2 / (2 * (N : ℝ) + 3)^2 := by
  have hlo := midpointEnergy_ge_of_zero_head f N hhead
  have hup := midpointEnergy_le_norm_sq f
  unfold midpointTailFactor at hlo
  constructor
  · linarith
  · rw [div_eq_mul_inv] at hlo ⊢
    nlinarith

theorem midpointEnergy_competitor_norm_bound
    (f g : ThresholdHilbert) (N : ℕ)
    (hhead : ∀ n, 0 < n → n ≤ N → hilbertSequence f n = 0)
    (hmin : midpointEnergy f ≤ midpointEnergy g) :
    ‖f‖^2 ≤ ‖g‖^2 / midpointTailFactor N := by
  exact (norm_sq_le_midpointEnergy_of_zero_head f N hhead).trans
    (div_le_div_of_nonneg_right (hmin.trans (midpointEnergy_le_norm_sq g))
      (midpointTailFactor_pos N).le)

theorem zeroHead_hardyLine_le (f : ThresholdHilbert) (N : ℕ)
    (hhead : ∀ n, 0 < n → n ≤ N → hilbertSequence f n = 0)
    (u σ : ℝ) (hu : 1 ≤ u) (hσ : u/2 < σ) :
    (∫ w : ℝ, ‖paretoMellin f (verticalPoint σ w)‖^2) ≤
      ((N : ℝ)+1)^(1-u) * ‖f‖^2 := by
  have hf := finiteEnergy_mono (complexPhysicalStep_finiteEnergy f) hu
  have h := hardy_energy_le hf hσ
  rw [complexPhysicalStep_transform] at h
  exact h.trans (zeroHead_weightedEnergy_le f N hhead u hu)

/-- Any finite midpoint optimizer preserving the exact head and beating the
canonical residual inherits its complete Hardy estimate. -/
theorem midpointEnergy_competitor_hardy_bound
    (f : ThresholdHilbert) (N : ℕ)
    (hhead : ∀ n, 0 < n → n ≤ N → hilbertSequence f n = 0)
    (hmin : midpointEnergy f ≤ midpointEnergy (hilbertOne - canonicalMobiusHilbert N))
    (u σ : ℝ) (hu : 1 ≤ u) (hσ : u/2 < σ) :
    (∫ w : ℝ, ‖paretoMellin f (verticalPoint σ w)‖^2) ≤
      ((N : ℝ)+1)^(1-u) * ‖hilbertOne-canonicalMobiusHilbert N‖^2 /
        midpointTailFactor N := by
  have hnorm := midpointEnergy_competitor_norm_bound f
    (hilbertOne-canonicalMobiusHilbert N) N hhead hmin
  calc
    _ ≤ ((N : ℝ)+1)^(1-u) * ‖f‖^2 := zeroHead_hardyLine_le f N hhead u σ hu hσ
    _ ≤ ((N : ℝ)+1)^(1-u) *
        (‖hilbertOne-canonicalMobiusHilbert N‖^2 / midpointTailFactor N) :=
      mul_le_mul_of_nonneg_left hnorm (Real.rpow_nonneg (by positivity) _)
    _ = _ := by ring

/-- Full logarithmic scheduling family for any exact-head midpoint competitor.
The conclusion has no inverse-Gram hypothesis and retains the entire tail. -/
theorem midpointEnergy_competitor_scheduled_line_bound
    (f : ThresholdHilbert) (N : ℕ) (hN : 0 < N)
    (hhead : ∀ n, 0 < n → n ≤ N → hilbertSequence f n = 0)
    (hmin : midpointEnergy f ≤ midpointEnergy (hilbertOne - canonicalMobiusHilbert N))
    (q θ σ : ℝ) (hq : 0 < q)
    (hql : ((N : ℝ)+1)⁻¹ ≤ q) (hqu : q ≤ 1)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hbudget : ‖hilbertOne-canonicalMobiusHilbert N‖^2 ≤ ((N : ℝ)+1)*q)
    (hσ : (2+θ*Real.log q/Real.log ((N : ℝ)+1))/2 < σ) :
    (∫ w : ℝ, ‖paretoMellin f (verticalPoint σ w)‖^2) ≤
      q^(1-θ) / midpointTailFactor N := by
  have hb : 1 < (N : ℝ)+1 := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    linarith
  have hu := log_schedule_mem_Icc hb hq hql hqu hθ0 hθ1
  apply (midpointEnergy_competitor_hardy_bound f N hhead hmin _ σ hu.1 hσ).trans
  exact div_le_div_of_nonneg_right (cutoff_power_times_energy_le hb hq hbudget)
    (midpointTailFactor_pos N).le

/-- The inherited moving bound tends to zero uniformly over all admissible
lines. This only requires a numerical certificate relative to the explicitly
constructed canonical residual, not an arithmetic conjecture. -/
theorem midpointEnergy_competitor_moving_lines_tendsto
    (f : ℕ → ThresholdHilbert) {q σ : ℕ → ℝ}
    (hq : Tendsto q atTop (𝓝 0))
    (hql : ∀ᶠ N : ℕ in atTop, ((N : ℝ)+1)⁻¹ ≤ q N)
    (hbudget : ∀ᶠ N : ℕ in atTop,
      ‖hilbertOne-canonicalMobiusHilbert N‖^2 ≤ ((N : ℝ)+1)*q N)
    (hhead : ∀ N n, 0 < n → n ≤ N → hilbertSequence (f N) n = 0)
    (hmin : ∀ N, midpointEnergy (f N) ≤
      midpointEnergy (hilbertOne-canonicalMobiusHilbert N))
    (hσ : ∀ᶠ N : ℕ in atTop, mobiusBudgetExponent q N / 2 < σ N) :
    Tendsto (fun N => ∫ w : ℝ, ‖paretoMellin (f N)
      (verticalPoint (σ N) w)‖^2) atTop (𝓝 0) := by
  have hs : Tendsto (fun N => (9/8 : ℝ) * Real.sqrt (q N)) atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.continuousAt.tendsto.comp hq).const_mul (9/8 : ℝ)
    simpa [Function.comp_def] using h
  apply squeeze_zero' (Filter.Eventually.of_forall
    (fun N => integral_nonneg (fun w => sq_nonneg _))) _ hs
  have hqu : ∀ᶠ N : ℕ in atTop, q N < 1 := hq.eventually (gt_mem_nhds zero_lt_one)
  filter_upwards [hql, hbudget, hqu, hσ, eventually_ge_atTop (1 : ℕ)]
    with N hl hb hqup hsig hN
  have hpos : 0 < q N := lt_of_lt_of_le (inv_pos.mpr (by positivity)) hl
  have hbound := midpointEnergy_competitor_scheduled_line_bound (f N) N (by omega)
    (hhead N) (hmin N) (q N) (1/2) (σ N) hpos hl hqup.le
    (by norm_num) (by norm_num) hb hsig
  rw [show (1 : ℝ)-1/2 = 1/2 by norm_num, ← Real.sqrt_eq_rpow] at hbound
  apply hbound.trans
  apply (div_le_iff₀ (midpointTailFactor_pos N)).2
  have hc := mul_le_mul_of_nonneg_left (midpointTailFactor_ge N) (Real.sqrt_nonneg (q N))
  nlinarith

end RiemannResearch.RH.Pareto
