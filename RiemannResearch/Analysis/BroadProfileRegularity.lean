import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Choose

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Actual compact smooth broad-profile providers

All derivative regularity, compact support, integrability, uniform bounds,
positive-order zero means, and the base profile's Lipschitz bound are
derived from the actual real smooth compact function. Nonzero mean gives
strictly positive squared L2 mass.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace RiemannResearch.Analysis

noncomputable section

theorem broadProfile_hasCompactSupport_of_bounds {φ : ℝ → ℝ} {a b : ℝ}
    (ha : ∀ x < a, φ x = 0) (hb : ∀ x > b, φ x = 0) :
    HasCompactSupport φ := by
  have hs : tsupport φ ⊆ Icc a b := by
    apply closure_minimal _ isClosed_Icc
    intro x hx
    constructor
    · by_contra h
      exact hx (ha x (lt_of_not_ge h))
    · by_contra h
      exact hx (hb x (lt_of_not_ge h))
  exact isCompact_Icc.of_isClosed_subset isClosed_closure hs

theorem broadProfile_contDiff_iteratedDeriv {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ) (j : ℕ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (iteratedDeriv j φ) := by
  rw [iteratedDeriv_eq_iterate]
  exact ContDiff.iterate_deriv j hφ

theorem broadProfile_continuous_iteratedDeriv {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ) (j : ℕ) :
    Continuous (iteratedDeriv j φ) :=
  (broadProfile_contDiff_iteratedDeriv hφ j).continuous

theorem broadProfile_hasCompactSupport_iteratedDeriv {φ : ℝ → ℝ}
    (hc : HasCompactSupport φ) (j : ℕ) :
    HasCompactSupport (iteratedDeriv j φ) := by
  induction j with
  | zero => simpa only [iteratedDeriv_zero] using hc
  | succ j ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv

theorem broadProfile_integrable_iteratedDeriv {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ) (hc : HasCompactSupport φ) (j : ℕ) :
    Integrable (iteratedDeriv j φ) :=
  (broadProfile_continuous_iteratedDeriv hφ j).integrable_of_hasCompactSupport
    (broadProfile_hasCompactSupport_iteratedDeriv hc j)

/-- A chosen finite bound exists for each actual derivative. -/
theorem broadProfile_exists_derivative_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ) (hc : HasCompactSupport φ) (j : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, |iteratedDeriv j φ x| ≤ B := by
  have hb : HasCompactSupport (fun x : ℝ => |iteratedDeriv j φ x|) := by
    simpa only [Real.norm_eq_abs] using
      (broadProfile_hasCompactSupport_iteratedDeriv hc j).norm
  obtain ⟨x₀, hx₀⟩ :=
    ((broadProfile_continuous_iteratedDeriv hφ j).abs).exists_forall_ge_of_hasCompactSupport hb
  exact ⟨|iteratedDeriv j φ x₀|, abs_nonneg _, hx₀⟩

theorem broadProfile_exists_all_derivative_bounds {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ) (hc : HasCompactSupport φ) :
    ∃ M : ℕ → ℝ, (∀ j, 0 ≤ M j) ∧
      ∀ j (x : ℝ), |iteratedDeriv j φ x| ≤ M j := by
  choose M hM hbound using broadProfile_exists_derivative_bound hφ hc
  exact ⟨M, hM, hbound⟩

/-- Every positive-order derivative has exactly zero integral. -/
theorem broadProfile_integral_iteratedDeriv_succ {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ) (hc : HasCompactSupport φ) (j : ℕ) :
    (∫ x : ℝ, iteratedDeriv (j + 1) φ x) = 0 := by
  have hd := (broadProfile_contDiff_iteratedDeriv hφ j).differentiable (by simp)
  rw [iteratedDeriv_succ]
  apply integral_eq_zero_of_hasDerivAt_of_integrable (fun x => (hd x).hasDerivAt)
  · simpa only [iteratedDeriv_succ] using broadProfile_integrable_iteratedDeriv hφ hc (j + 1)
  · exact broadProfile_integrable_iteratedDeriv hφ hc j

theorem broadProfile_integral_iteratedDeriv_eq_zero {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ) (hc : HasCompactSupport φ)
    {j : ℕ} (hj : 0 < j) : (∫ x : ℝ, iteratedDeriv j φ x) = 0 := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
  exact broadProfile_integral_iteratedDeriv_succ hφ hc i

/-- A global Lipschitz constant is deduced from the first derivative. -/
theorem broadProfile_exists_lipschitz_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ) (hc : HasCompactSupport φ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x y : ℝ, |φ x - φ y| ≤ K * |x - y| := by
  obtain ⟨B, hB, hb⟩ := broadProfile_exists_derivative_bound hφ hc 1
  let K : NNReal := ⟨B, hB⟩
  have hlip : LipschitzWith K φ := by
    apply lipschitzWith_of_nnnorm_deriv_le (hφ.differentiable (by simp))
    intro x
    change ‖deriv φ x‖ ≤ B
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero, Real.norm_eq_abs] using hb x
  refine ⟨B, hB, fun x y => ?_⟩
  convert hlip.dist_le_mul x y using 1 <;>
    first | rfl | simp only [Real.dist_eq]

theorem broadProfile_integrable_sq {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ) (hc : HasCompactSupport φ) :
    Integrable (fun x : ℝ => φ x ^ 2) := by
  have hs : HasCompactSupport (fun x : ℝ => φ x * φ x) := hc.mul_right
  apply (hφ.continuous.pow 2).integrable_of_hasCompactSupport
  convert hs using 1 <;> first | rfl | (funext x; exact pow_two (φ x))

/-- Nonzero mean forces positive squared L2 mass of the actual seed. -/
theorem broadProfile_integral_sq_pos_of_integral_ne_zero {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ) (hc : HasCompactSupport φ)
    (hmass : (∫ x : ℝ, φ x) ≠ 0) : 0 < ∫ x : ℝ, φ x ^ 2 := by
  by_contra hpos
  have hz : (∫ x : ℝ, φ x ^ 2) = 0 :=
    le_antisymm (le_of_not_gt hpos) (integral_nonneg fun x => sq_nonneg (φ x))
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (φ x))
    (broadProfile_integrable_sq hφ hc)).mp hz
  have hzero : φ =ᵐ[volume] 0 := by
    filter_upwards [hae] with x hx
    exact sq_eq_zero_iff.mp hx
  apply hmass
  calc
    (∫ x : ℝ, φ x) = ∫ _ : ℝ, (0 : ℝ) := integral_congr_ae hzero
    _ = 0 := by simp

/-- Actual real-to-complex differentiation commutes at every order. -/
theorem iteratedDeriv_real_to_complex {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ) (j : ℕ) :
    iteratedDeriv j (fun x : ℝ => (φ x : ℂ)) =
      fun x : ℝ => ((iteratedDeriv j φ x : ℝ) : ℂ) := by
  induction j with
  | zero => simp only [iteratedDeriv_zero]
  | succ j ih =>
      rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]
      funext x
      have hd := (broadProfile_contDiff_iteratedDeriv hφ j).differentiable (by simp) x
      have h := hd.hasDerivAt.ofReal_comp
      convert h.deriv using 1 <;> rfl

end
end RiemannResearch.Analysis
