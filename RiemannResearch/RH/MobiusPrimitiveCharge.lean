import RiemannResearch.RH.BalazardReciprocalCharge
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
/-!
# Normalized complete Möbius primitives

Source: user-directed signed-Abel continuation from 4557e290, 30 September 2026.
The reciprocal kernel bounds and weak limit are the repository's formalization
of Michel Balazard, arXiv:1812.04309, Propositions 6--7; that reference supports
the imported ingredient. The finite prefix identity and Cesaro subtraction
below are an elementary Kronecker argument assembled here.

Every conductor-one contribution remains in the exact finite identity.
The normalized primitive kernels are bounded by 14 and weakly null. Any
strongly convergent moving Hilbert test and any divergent conductor cutoff
are permitted, without a relative growth assumption. No RH is assumed.
-/

open Filter
open scoped Topology BigOperators
noncomputable section
namespace RiemannResearch.RH.Pareto

/-- Exact Cesaro subtraction of the complete reciprocal kernel. -/
def primitiveChargeRiesz (N : ℕ) : ThresholdHilbert :=
  reciprocalChargeRiesz N - (N : ℝ)⁻¹ •
    ∑ k ∈ Finset.range N, reciprocalChargeRiesz k

/-- Signed finite prefix identity, including conductor one. -/
theorem mobiusCharge_prefix_identity (N : ℕ) (f : ThresholdHilbert) :
    (∑ m ∈ Finset.Icc 1 N, mobiusDifferenceCLM m f) =
      (N : ℝ) * inner ℝ (reciprocalChargeRiesz N) f -
        ∑ k ∈ Finset.range N, inner ℝ (reciprocalChargeRiesz k) f := by
  induction N with
  | zero => simp [reciprocalChargeRiesz]
  | succ N ih =>
    have hs : inner ℝ (reciprocalChargeRiesz (N + 1)) f =
        inner ℝ (reciprocalChargeRiesz N) f +
          mobiusDifferenceCLM (N + 1) f / ((N + 1 : ℕ) : ℝ) := by
      rw [reciprocalChargeRiesz_inner, reciprocalChargeRiesz_inner,
        Finset.sum_Icc_succ_top (by omega)]
    rw [Finset.sum_Icc_succ_top (by omega), ih, hs, Finset.sum_range_succ]
    push_cast
    field_simp
    ring

/-- Riesz realization of the complete unweighted primitive divided by N. -/
theorem primitiveChargeRiesz_inner (N : ℕ) (f : ThresholdHilbert) :
    inner ℝ (primitiveChargeRiesz N) f =
      (∑ m ∈ Finset.Icc 1 N, mobiusDifferenceCLM m f) / (N : ℝ) := by
  cases N with
  | zero => simp [primitiveChargeRiesz, reciprocalChargeRiesz]
  | succ N =>
    rw [mobiusCharge_prefix_identity, primitiveChargeRiesz, inner_sub_left,
      real_inner_smul_left, sum_inner]
    have hN : ((N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp [hN]

theorem primitiveChargeRiesz_norm_le (N : ℕ) : ‖primitiveChargeRiesz N‖ ≤ 14 := by
  cases N with
  | zero => norm_num [primitiveChargeRiesz, reciprocalChargeRiesz]
  | succ N =>
    have hsum : ‖∑ k ∈ Finset.range (N + 1), reciprocalChargeRiesz k‖ ≤
        ((N + 1 : ℕ) : ℝ) * 7 := by
      calc
        _ ≤ ∑ k ∈ Finset.range (N + 1), ‖reciprocalChargeRiesz k‖ := norm_sum_le _ _
        _ ≤ ∑ k ∈ Finset.range (N + 1), (7 : ℝ) :=
          Finset.sum_le_sum (fun k _ => reciprocalChargeRiesz_norm_le k)
        _ = _ := by simp
    have havg : ‖((N + 1 : ℕ) : ℝ)⁻¹ •
        ∑ k ∈ Finset.range (N + 1), reciprocalChargeRiesz k‖ ≤ 7 := by
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      calc
        _ ≤ ((N + 1 : ℕ) : ℝ)⁻¹ * (((N + 1 : ℕ) : ℝ) * 7) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = 7 := by field_simp
    exact (norm_sub_le _ _).trans (by
      linarith [reciprocalChargeRiesz_norm_le (N + 1)])

theorem primitiveChargeRiesz_weak_zero (f : ThresholdHilbert) :
    Tendsto (fun N => inner ℝ (primitiveChargeRiesz N) f) atTop (𝓝 0) := by
  have h : Tendsto (fun N => inner ℝ (reciprocalChargeRiesz N) f) atTop (𝓝 0) := by
    simpa only [real_inner_comm] using reciprocalChargeRiesz_weak_zero f
  simpa only [primitiveChargeRiesz, inner_sub_left, real_inner_smul_left,
    sum_inner, sub_zero] using h.sub h.cesaro


theorem primitiveChargeRiesz_inner_moving_tendsto_zero
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (f : ℕ → ThresholdHilbert) (g : ThresholdHilbert)
    (hf : Tendsto f atTop (𝓝 g)) :
    Tendsto (fun N => inner ℝ (primitiveChargeRiesz (m N)) (f N)) atTop (𝓝 0) := by
  have hdiff : Tendsto (fun N => ‖f N - g‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using (hf.sub_const g).norm
  have herr : Tendsto (fun N => inner ℝ (primitiveChargeRiesz (m N)) (f N - g))
      atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) _ (by simpa using hdiff.const_mul 14)
    intro N
    exact (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
      (mul_le_mul_of_nonneg_right (primitiveChargeRiesz_norm_le (m N)) (norm_nonneg _))
  have hfixed := (primitiveChargeRiesz_weak_zero g).comp hm
  have he (N : ℕ) : inner ℝ (primitiveChargeRiesz (m N)) (f N) =
      inner ℝ (primitiveChargeRiesz (m N)) (f N - g) +
        inner ℝ (primitiveChargeRiesz (m N)) g := by
    rw [inner_sub_right]
    ring
  simpa only [Function.comp_def, ← he, add_zero] using herr.add hfixed

end RiemannResearch.RH.Pareto
