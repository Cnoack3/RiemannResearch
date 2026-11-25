import RiemannResearch.Analysis.MontgomeryIncomingEnergy

/-! # Both cutoff errors at fixed subunit frequencies -/

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

end RiemannResearch.Analysis.MontgomeryResolventBoundaryLimit

namespace RiemannResearch.Analysis.MontgomeryResolventBoundaryLimit

/--
info: 'RiemannResearch.Analysis.MontgomeryResolventBoundaryLimit.incoming_cutoff_normalized_tendsto_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms incoming_cutoff_normalized_tendsto_zero

end RiemannResearch.Analysis.MontgomeryResolventBoundaryLimit
