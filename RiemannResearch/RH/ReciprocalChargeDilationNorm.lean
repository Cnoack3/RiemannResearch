import RiemannResearch.RH.BalazardReciprocalCharge
import RiemannResearch.RH.ReciprocalChargeDilationKernelLimit

/-!
# Hilbert realization of a sum of dilated reciprocal charges

The scalar quotient kernel is exactly the physical sequence of `Q_N + Q_(hN)`.
Consequently its finite square energy equals the actual Hilbert norm. This
identification preserves the signed mixed term without introducing an RH premise.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto

/-- Physical coordinates of the sum at cutoffs `N` and `h*N`. -/
theorem reciprocalChargeRiesz_add_dilation_sequence (h N k : ℕ)
    (hh : 0 < h) (hk : 0 < k) :
    hilbertSequence (reciprocalChargeRiesz N + reciprocalChargeRiesz (h * N)) k =
      (k : ℝ) * ((k : ℝ) + 1) *
        (dilationMobiusKernel h (h * N / k) / (k : ℝ) -
          dilationMobiusKernel h (h * N / (k + 1)) / ((k : ℝ) + 1)) := by
  rw [← anchoredEvaluationCLM_apply]
  simp only [map_add, anchoredEvaluationCLM_apply]
  rw [reciprocalChargeRiesz_sequence N k hk,
    reciprocalChargeRiesz_sequence (h * N) k hk,
    dilationMobiusKernel_at_dilated_quotient h N k hh,
    dilationMobiusKernel_at_dilated_quotient h N (k + 1) hh]
  ring

/-- The scalar dilation-kernel energy is exactly the norm of the actual sum. -/
theorem reciprocalChargeRiesz_add_dilation_norm_sq_eq_energy (h N : ℕ) (hh : 0 < h) :
    ‖reciprocalChargeRiesz N + reciprocalChargeRiesz (h * N)‖ ^ 2 =
      ∑ k ∈ Finset.Icc 1 (h * N),
        (k : ℝ) * ((k : ℝ) + 1) *
          (dilationMobiusKernel h (h * N / k) / (k : ℝ) -
            dilationMobiusKernel h (h * N / (k + 1)) / ((k : ℝ) + 1)) ^ 2 := by
  rw [hilbert_norm_weighted_sq]
  rw [tsum_eq_sum (s := Finset.Icc 1 (h * N)) (by
    intro k hk
    by_cases hk0 : k = 0
    · simp [hk0]
    · have hkN : h * N < k := by
        have hn : ¬ (1 ≤ k ∧ k ≤ h * N) := by simpa only [Finset.mem_Icc] using hk
        omega
      rw [reciprocalChargeRiesz_add_dilation_sequence h N k hh (Nat.pos_of_ne_zero hk0)]
      have hkS : h * N < k + 1 := by omega
      simp [Nat.div_eq_of_lt hkN, Nat.div_eq_of_lt hkS,
        dilationMobiusKernel, mobiusReciprocalSum])]
  apply Finset.sum_congr rfl
  intro k hk
  have hk0 : 0 < k := (Finset.mem_Icc.mp hk).1
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hk0
  have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
  rw [reciprocalChargeRiesz_add_dilation_sequence h N k hh hk0]
  unfold positiveWeight
  change 1 / ((k : ℝ) * ((k : ℝ) + 1)) *
    ((k : ℝ) * ((k : ℝ) + 1) *
      (dilationMobiusKernel h (h * N / k) / (k : ℝ) -
        dilationMobiusKernel h (h * N / (k + 1)) / ((k : ℝ) + 1))) ^ 2 = _
  field_simp

/-- Transfer any scalar dilation-energy limit to the actual Hilbert vectors. -/
theorem reciprocalChargeRiesz_add_dilation_norm_sq_tendsto_of_scalar
    (h : ℕ) (hh : 0 < h) (S : ℝ)
    (hscalar : Tendsto (fun M : ℕ => ∑ k ∈ Finset.Icc 1 M,
      (k : ℝ) * ((k : ℝ) + 1) *
        (dilationMobiusKernel h (M / k) / (k : ℝ) -
          dilationMobiusKernel h (M / (k + 1)) / ((k : ℝ) + 1)) ^ 2)
      atTop (𝓝 S)) :
    Tendsto (fun N => ‖reciprocalChargeRiesz N + reciprocalChargeRiesz (h * N)‖ ^ 2)
      atTop (𝓝 S) := by
  have hcofinal : Tendsto (fun N : ℕ => h * N) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with N hN
    have hh1 : 1 ≤ h := hh
    nlinarith
  have ht := hscalar.comp hcofinal
  simpa only [Function.comp_def, ← reciprocalChargeRiesz_add_dilation_norm_sq_eq_energy h _ hh]
    using ht

/-- Exact combined energy limit for the actual reciprocal-charge Hilbert vectors. -/
theorem reciprocalChargeRiesz_add_dilation_norm_sq_tendsto (h : ℕ) (hh : 0 < h) :
    Tendsto (fun N => ‖reciprocalChargeRiesz N + reciprocalChargeRiesz (h * N)‖ ^ 2)
      atTop (𝓝 (∑' n, dilationMobiusCoefficient h n ^ 2)) :=
  reciprocalChargeRiesz_add_dilation_norm_sq_tendsto_of_scalar h hh _
    (dilationMobiusKernel_square_energy_tendsto h hh)

end RiemannResearch.RH.Pareto
