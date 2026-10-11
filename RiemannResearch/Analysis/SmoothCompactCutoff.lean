import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Tactic.GCongr

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Actual smooth compact cutoffs with uniform derivative bounds

A fixed smooth bump is dilated by N+1. On every fixed neighborhood its
product with a test eventually agrees with that test, so all derivatives
agree eventually. The finite Leibniz majorant is independent of N.
-/

noncomputable section
open scoped Topology BigOperators SchwartzMap
open Filter MeasureTheory

namespace RiemannResearch.Analysis

private def unitCutoffBump : ContDiffBump (0 : ℝ) where
  rIn := 1
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

private def unitCutoff (x : ℝ) : ℂ := (unitCutoffBump x : ℂ)

private theorem unitCutoff_contDiff : ContDiff ℝ (↑(⊤ : ℕ∞)) unitCutoff :=
  Complex.ofRealCLM.contDiff.comp unitCutoffBump.contDiff

private theorem unitCutoff_one {x : ℝ} (hx : |x| ≤ 1) : unitCutoff x = 1 := by
  unfold unitCutoff
  rw [unitCutoffBump.one_of_mem_closedBall]
  · norm_num
  · simpa [Metric.mem_closedBall, Real.dist_eq, unitCutoffBump] using hx

private theorem unitCutoff_zero {x : ℝ} (hx : 2 ≤ |x|) : unitCutoff x = 0 := by
  unfold unitCutoff
  rw [unitCutoffBump.zero_of_le_dist]
  · norm_num
  · simpa [Real.dist_eq, unitCutoffBump] using hx

private theorem unitCutoff_hasCompactSupport : HasCompactSupport unitCutoff := by
  have hs : tsupport unitCutoff ⊆ Set.Icc (-2 : ℝ) 2 := by
    apply closure_minimal _ isClosed_Icc
    intro x hx
    constructor
    · by_contra h
      exact hx (unitCutoff_zero (by nlinarith [neg_le_abs x, lt_of_not_ge h]))
    · by_contra h
      exact hx (unitCutoff_zero (by nlinarith [le_abs_self x, lt_of_not_ge h]))
  exact isCompact_Icc.of_isClosed_subset isClosed_closure hs

private def unitCutoffSchwartz : SchwartzMap ℝ ℂ :=
  unitCutoff_hasCompactSupport.toSchwartzMap unitCutoff_contDiff

/-- Fixed constants controlling every derivative of the chosen bump. -/
def cutoffDerivativeBound (j : ℕ) : ℝ :=
  SchwartzMap.seminorm ℂ 0 j unitCutoffSchwartz

theorem cutoffDerivativeBound_nonneg (j : ℕ) : 0 ≤ cutoffDerivativeBound j := by
  unfold cutoffDerivativeBound
  positivity

private theorem norm_iteratedDeriv_unitCutoff_le (j : ℕ) (x : ℝ) :
    ‖iteratedDeriv j unitCutoff x‖ ≤ cutoffDerivativeBound j := by
  have he : (unitCutoffSchwartz : ℝ → ℂ) = unitCutoff := rfl
  have h := SchwartzMap.le_seminorm' ℂ 0 j unitCutoffSchwartz x
  rw [he] at h
  simpa [cutoffDerivativeBound] using h

/-- χ_N(x)=χ(x/(N+1)); the positive shift handles N=0 without exceptions. -/
def smoothCutoff (N : ℕ) (x : ℝ) : ℂ :=
  unitCutoff (((N : ℝ) + 1)⁻¹ * x)

theorem smoothCutoff_contDiff (N : ℕ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (smoothCutoff N) :=
  unitCutoff_contDiff.comp (contDiff_const.mul contDiff_id)

theorem norm_smoothCutoff_le_one (N : ℕ) (x : ℝ) : ‖smoothCutoff N x‖ ≤ 1 := by
  change ‖(unitCutoffBump _ : ℂ)‖ ≤ 1
  simpa only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg unitCutoffBump.nonneg] using unitCutoffBump.le_one

theorem smoothCutoff_one {N : ℕ} {x : ℝ} (hx : |x| ≤ (N : ℝ) + 1) :
    smoothCutoff N x = 1 := by
  apply unitCutoff_one
  have hN : 0 < (N : ℝ) + 1 := by positivity
  rw [abs_mul, abs_inv, abs_of_pos hN, ← div_eq_inv_mul]
  exact (div_le_one hN).mpr hx

theorem smoothCutoff_zero {N : ℕ} {x : ℝ} (hx : 2 * ((N : ℝ) + 1) ≤ |x|) :
    smoothCutoff N x = 0 := by
  apply unitCutoff_zero
  have hN : 0 < (N : ℝ) + 1 := by positivity
  rw [abs_mul, abs_inv, abs_of_pos hN, ← div_eq_inv_mul]
  exact (le_div_iff₀ hN).mpr hx

theorem smoothCutoff_iteratedDeriv (N j : ℕ) :
    iteratedDeriv j (smoothCutoff N) =
      fun x => (((N : ℝ) + 1)⁻¹)^j •
        iteratedDeriv j unitCutoff (((N : ℝ) + 1)⁻¹ * x) := by
  exact iteratedDeriv_comp_const_smul
    (unitCutoff_contDiff.of_le
      (ENat.natCast_lt_of_coe_top_le_withTop le_rfl j).le) _

/-- Uniform derivative bounds are conclusions of actual dilation. -/
theorem norm_iteratedDeriv_smoothCutoff_le (N j : ℕ) (x : ℝ) :
    ‖iteratedDeriv j (smoothCutoff N) x‖ ≤ cutoffDerivativeBound j := by
  rw [smoothCutoff_iteratedDeriv]
  simp only [norm_smul, norm_pow, Real.norm_eq_abs]
  have hN : 0 < (N : ℝ) + 1 := by positivity
  have hinv : 0 ≤ ((N : ℝ) + 1)⁻¹ := inv_nonneg.mpr hN.le
  rw [abs_of_nonneg hinv]
  have hle : ((N : ℝ) + 1)⁻¹ ≤ 1 := (inv_le_one₀ hN).mpr (by linarith [(show (0 : ℝ) ≤ N from Nat.cast_nonneg N)])
  calc
    _ ≤ (((N : ℝ) + 1)⁻¹)^j * cutoffDerivativeBound j :=
      mul_le_mul_of_nonneg_left (norm_iteratedDeriv_unitCutoff_le _ _)
        (pow_nonneg hinv _)
    _ ≤ 1 * cutoffDerivativeBound j :=
      mul_le_mul_of_nonneg_right (pow_le_one₀ hinv hle) (cutoffDerivativeBound_nonneg _)
    _ = _ := one_mul _

/-- The actual compact approximation to a function. -/
def compactCutoff (N : ℕ) (f : ℝ → ℂ) : ℝ → ℂ := smoothCutoff N * f

theorem compactCutoff_contDiff {f : ℝ → ℂ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (N : ℕ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (compactCutoff N f) :=
  (smoothCutoff_contDiff N).mul hf

theorem compactCutoff_hasCompactSupport (N : ℕ) (f : ℝ → ℂ) :
    HasCompactSupport (compactCutoff N f) := by
  have hs : tsupport (compactCutoff N f) ⊆
      Set.Icc (-2 * ((N : ℝ) + 1)) (2 * ((N : ℝ) + 1)) := by
    apply closure_minimal _ isClosed_Icc
    intro x hx
    have hne : smoothCutoff N x ≠ 0 := by
      intro h
      exact hx (by simp [compactCutoff, h])
    constructor
    · by_contra h
      exact hne (smoothCutoff_zero (by nlinarith [neg_le_abs x, lt_of_not_ge h]))
    · by_contra h
      exact hne (smoothCutoff_zero (by nlinarith [le_abs_self x, lt_of_not_ge h]))
  exact isCompact_Icc.of_isClosed_subset isClosed_closure hs

/-- Agreement on a whole neighborhood, including every derivative. -/
theorem compactCutoff_eventuallyEq {N : ℕ} {x : ℝ}
    (hx : |x| < (N : ℝ) + 1) (f : ℝ → ℂ) :
    compactCutoff N f =ᶠ[𝓝 x] f := by
  have hn : {y : ℝ | |y| < (N : ℝ) + 1} ∈ 𝓝 x :=
    (isOpen_lt continuous_abs continuous_const).mem_nhds hx
  filter_upwards [hn] with y hy
  simp only [compactCutoff, Pi.mul_apply, smoothCutoff_one (le_of_lt hy), one_mul]

/-- At every fixed point, all derivative approximations are eventually exact. -/
theorem eventually_iteratedDeriv_compactCutoff_eq (f : ℝ → ℂ) (j : ℕ) (x : ℝ) :
    ∀ᶠ N : ℕ in atTop, iteratedDeriv j (compactCutoff N f) x = iteratedDeriv j f x := by
  obtain ⟨N, hN⟩ := exists_nat_gt |x|
  filter_upwards [eventually_ge_atTop N] with M hM
  exact (compactCutoff_eventuallyEq (by
    have hNM : (N : ℝ) ≤ M := by exact_mod_cast hM
    linarith) f).iteratedDeriv_eq j

/-- The exact finite Leibniz majorant, independent of the cutoff radius. -/
def cutoffDerivativeMajorant (f : ℝ → ℂ) (j : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (j + 1),
    (j.choose i : ℝ) * cutoffDerivativeBound i * ‖iteratedDeriv (j - i) f x‖

theorem cutoffDerivativeMajorant_nonneg (f : ℝ → ℂ) (j : ℕ) (x : ℝ) :
    0 ≤ cutoffDerivativeMajorant f j x := by
  unfold cutoffDerivativeMajorant
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (cutoffDerivativeBound_nonneg _))
    (norm_nonneg _)

theorem norm_iteratedDeriv_compactCutoff_le {f : ℝ → ℂ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (N j : ℕ) (x : ℝ) :
    ‖iteratedDeriv j (compactCutoff N f) x‖ ≤ cutoffDerivativeMajorant f j x := by
  have hj : (j : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞) :=
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl j).le
  unfold compactCutoff
  rw [iteratedDeriv_mul ((smoothCutoff_contDiff N).of_le hj).contDiffAt
    (hf.of_le hj).contDiffAt]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  simp only [norm_mul, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (norm_iteratedDeriv_smoothCutoff_le N i x)
      (Nat.cast_nonneg _)) (norm_nonneg _)

end RiemannResearch.Analysis
