import RiemannResearch.Analysis.MontgomeryIncomingEnergy

/-! # Resolvent cutoff errors on fixed and moving subunit frequency bands -/

noncomputable section
open MeasureTheory Complex Set Filter
open scoped Topology
namespace RiemannResearch.Analysis.MontgomeryResolventBoundaryLimit
open MontgomeryFiniteResolventSignal MontgomeryIncomingResolvent MontgomeryIncomingEnergy
open MontgomeryHorizontalTransfer

/-- The uniform incoming squared error, normalized by the natural spectral
energy T log T, vanishes on every fixed 0 ≤ α < 1. -/
theorem incoming_cutoff_normalized_tendsto_zero {α : ℝ} (hα : 0 ≤ α) (h₁ : α < 1) :
    Tendsto (fun T : ℝ => (∫ t in (0:ℝ)..T,
      ‖allSignal (α*Real.log T) t-actualSignal T (α*Real.log T) t‖^2)/(T*Real.log T)) atTop (𝓝 0) := by
  obtain ⟨C,hC,h⟩ := exists_incoming_energy_bound
  have hlog := (isLittleO_log_rpow_atTop (by linarith : 0 < 1-α)).tendsto_div_nhds_zero
  apply squeeze_zero_norm' _ (by simpa using hlog.const_mul (4*C))
  filter_upwards [eventually_ge_atTop (5:ℝ)] with T hT
  have h1 : 1 < T := by linarith
  have ht := zero_lt_one.trans h1
  have hL := Real.log_pos h1
  have hB := (h T (α*Real.log T) hT (mul_nonneg hα hL.le)).2
  have hn : 0 ≤ ∫ t in (0:ℝ)..T, ‖allSignal (α*Real.log T) t-actualSignal T (α*Real.log T) t‖^2 :=
    intervalIntegral.integral_nonneg ht.le (fun _ _ => sq_nonneg _)
  rw [Real.norm_of_nonneg (div_nonneg hn (mul_pos ht hL).le)]
  have hlo : 0 ≤ Real.log (2*T+4) := Real.log_nonneg (by linarith)
  have hlu : Real.log (2*T+4) ≤ 2*Real.log T := by
    calc
      _ ≤ Real.log (T^2) := Real.log_le_log (by positivity) (by nlinarith [sq_nonneg (T-5)])
      _ = _ := by simp [Real.log_pow]
  have hexp : Real.exp (α*Real.log T) = T^α := by rw [Real.rpow_def_of_pos ht,mul_comm]
  rw [hexp] at hB
  have hr : T^α*T^(1-α)=T := by rw [← Real.rpow_add ht,show α+(1-α)=1 by ring,Real.rpow_one]
  have hp := Real.rpow_pos_of_pos ht (1-α)
  calc
    _ ≤ (C*T^α*(2*Real.log T)^2)/(T*Real.log T) := by
      apply div_le_div_of_nonneg_right _ (mul_pos ht hL).le
      exact hB.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlo hlu 2) (by positivity))
    _ = (4*C)*(Real.log T/T^(1-α)) := by
      field_simp [ht.ne',hL.ne',hp.ne']
      have hCeq := congrArg (fun v : ℝ => 4*C*v) hr
      nlinarith only [hCeq]

/-- Sum of the outgoing finite-signal energy excess and the incoming squared
signal error, on the spectral normalization. Both summands are nonnegative
for observation heights at least five. -/
def normalizedCutoffDefect (T u : ℝ) : ℝ :=
  (2 * Real.pi * (actualComplexPairSum T u).re -
    (∫ t in (0 : ℝ)..T, ‖actualSignal T u t‖ ^ 2) +
    (∫ t in (0 : ℝ)..T, ‖allSignal u t - actualSignal T u t‖ ^ 2)) /
    (T * Real.log T)

/-- A single constant controls both normalized cutoff errors for all physical
log frequencies and all observation heights at least five. -/
theorem exists_normalized_cutoff_defect_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ T u : ℝ, 5 ≤ T → 0 ≤ u →
      0 ≤ normalizedCutoffDefect T u ∧
      normalizedCutoffDefect T u ≤ K * (Real.exp u * Real.log T / T) := by
  obtain ⟨A, hA, hOut⟩ := exists_finite_cutoff_energy_bound
  obtain ⟨B, hB, hIn⟩ := exists_incoming_energy_bound
  refine ⟨4 * (A + B), by positivity, fun T u hT hu => ?_⟩
  have ht : 0 < T := by linarith
  have hL := Real.log_pos (by linarith : 1 < T)
  have hi := (hIn T u hT hu).2
  obtain ⟨hn, ho⟩ := hOut T u ht.le hu
  have hin : 0 ≤ ∫ t in (0 : ℝ)..T, ‖allSignal u t - actualSignal T u t‖ ^ 2 :=
    intervalIntegral.integral_nonneg ht.le (fun _ _ => sq_nonneg _)
  have houter : Real.log (2 * T + 4) ≤ 2 * Real.log T := by
    calc
      _ ≤ Real.log (T ^ 2) := Real.log_le_log (by positivity) (by nlinarith [sq_nonneg (T - 5)])
      _ = _ := by simp [Real.log_pow]
  have hinner : Real.log (T + 3) ≤ 2 * Real.log T :=
    (Real.log_le_log (by linarith) (by linarith : T + 3 ≤ 2 * T + 4)).trans houter
  have ho' := ho.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (Real.log_nonneg (by linarith)) hinner 2) (mul_nonneg hA (Real.exp_pos u).le))
  have hi' := hi.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (Real.log_nonneg (by linarith)) houter 2) (mul_nonneg hB (Real.exp_pos u).le))
  unfold normalizedCutoffDefect
  refine ⟨div_nonneg (add_nonneg hn hin) (mul_pos ht hL).le, ?_⟩
  calc
    _ ≤ (A * Real.exp u * (2 * Real.log T) ^ 2 + B * Real.exp u * (2 * Real.log T) ^ 2) /
        (T * Real.log T) := div_le_div_of_nonneg_right (add_le_add ho' hi') (mul_pos ht hL).le
    _ = _ := by field_simp [ht.ne', hL.ne']; ring

/-- Uniform decay throughout a moving band whose exponential cost is
little-o of the spectral height divided by its logarithm. -/
theorem moving_band_cutoff_defect {U : ℝ → ℝ}
    (hbudget : Tendsto (fun T => Real.exp (U T) * Real.log T / T) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ T in atTop,
      ∀ u ∈ Icc 0 (U T), |normalizedCutoffDefect T u| < ε := by
  obtain ⟨K, hK, hbound⟩ := exists_normalized_cutoff_defect_bound
  intro ε hε
  have hz : Tendsto (fun T => K * (Real.exp (U T) * Real.log T / T)) atTop (𝓝 0) := by
    simpa using hbudget.const_mul K
  filter_upwards [hz.eventually_lt_const hε, eventually_ge_atTop (5 : ℝ)] with T hεT hT u hu
  have h1 : 1 < T := by linarith
  obtain ⟨hn, hb⟩ := hbound T u hT hu.1
  rw [abs_of_nonneg hn]
  apply lt_of_le_of_lt (hb.trans ?_) hεT
  exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hu.2) (Real.log_pos h1).le)
    (zero_lt_one.trans h1).le) hK

/-- Both cutoff errors vanish uniformly up to log T minus twice log log T.
The resulting normalized frequency band approaches the unit edge. -/
theorem near_unit_cutoff_defect :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℝ in atTop,
      ∀ u ∈ Icc 0 (Real.log T - 2 * Real.log (Real.log T)),
        |normalizedCutoffDefect T u| < ε := by
  apply moving_band_cutoff_defect (U := fun T => Real.log T - 2 * Real.log (Real.log T))
  have hi := tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  apply hi.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
  have ht := zero_lt_one.trans hT
  have hL := Real.log_pos hT
  change (Real.log T)⁻¹ = Real.exp (Real.log T - 2 * Real.log (Real.log T)) * Real.log T / T
  rw [Real.exp_sub, Real.exp_log ht, show 2 * Real.log (Real.log T) =
    Real.log (Real.log T) + Real.log (Real.log T) by ring, Real.exp_add, Real.exp_log hL]
  field_simp [ht.ne', hL.ne']

end RiemannResearch.Analysis.MontgomeryResolventBoundaryLimit

namespace RiemannResearch.Analysis.MontgomeryResolventBoundaryLimit

/--
info: 'RiemannResearch.Analysis.MontgomeryResolventBoundaryLimit.incoming_cutoff_normalized_tendsto_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms incoming_cutoff_normalized_tendsto_zero

/--
info: 'RiemannResearch.Analysis.MontgomeryResolventBoundaryLimit.near_unit_cutoff_defect' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms near_unit_cutoff_defect

end RiemannResearch.Analysis.MontgomeryResolventBoundaryLimit
