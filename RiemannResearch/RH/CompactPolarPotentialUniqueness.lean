import RiemannResearch.RH.CompactPolarPotential
import RiemannResearch.RH.ArithmeticReturnDerivatives
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Abel

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Uniqueness of the compact pole-cancellation potential

Two integrating factors reduce the homogeneous equation to two functions
with zero derivative. Their values below the support force both constants
to vanish. This is a spatial proof, independent of a Fourier inversion axiom.
-/

noncomputable section
open MeasureTheory.BilateralLaplace

namespace RiemannResearch.RH

/-- A smooth homogeneous solution vanishing on a lower half-line is zero. -/
theorem eq_zero_of_poleCancellationOperator_zero {w : ℝ → ℂ} {a : ℝ}
    (hw : ContDiff ℝ (↑(⊤ : ℕ∞)) w) (ha : ∀ y < a, w y = 0)
    (hL : ∀ y, poleCancellationOperator w y = 0) : w = 0 := by
  have hw' : ContDiff ℝ (↑(⊤ : ℕ∞)) (deriv w) := by
    simpa only [Function.iterate_succ_apply, Function.iterate_zero_apply] using
      ContDiff.iterate_deriv 1 hw
  have hd := hw.differentiable (by simp)
  have hd' := hw'.differentiable (by simp)
  have hdd (y : ℝ) : deriv (deriv w) y = (1/4 : ℂ) * w y := by
    have h := sub_eq_zero.mp (hL y)
    simpa only [Complex.real_smul, Complex.ofReal_div,
      Complex.ofReal_one, Complex.ofReal_ofNat] using h
  let F : ℝ → ℂ := fun y => kernel (1/2) y * (deriv w y + (1/2 : ℂ) * w y)
  have hF (y : ℝ) : HasDerivAt F 0 y := by
    have h := (hasDerivAt_kernel_spatial (1/2) y).mul
      (((hd' y).hasDerivAt).add ((hd y).hasDerivAt.const_mul (1/2 : ℂ)))
    convert h using 1 <;> first | rfl | skip
    simp only [Pi.add_apply]
    rw [hdd]
    ring
  have hFa : F (a-1) = 0 := by
    simp only [F, ha (a-1) (by linarith),
      deriv_zero_below_of_zero_below ha (a-1) (by linarith), mul_zero, add_zero]
  have hFzero (y : ℝ) : F y = 0 :=
    (is_const_of_deriv_eq_zero (fun x => (hF x).differentiableAt)
      (fun x => (hF x).deriv) y (a-1)).trans hFa
  have hfirst (y : ℝ) : deriv w y + (1/2 : ℂ) * w y = 0 := by
    exact (mul_eq_zero.mp (hFzero y)).resolve_left (Complex.exp_ne_zero _)
  let G : ℝ → ℂ := fun y => kernel (-1/2) y * w y
  have hG (y : ℝ) : HasDerivAt G 0 y := by
    have h := (hasDerivAt_kernel_spatial (-1/2) y).mul ((hd y).hasDerivAt)
    convert h using 1 <;> first | rfl | skip
    calc
      (0 : ℂ) = kernel (-1/2) y * (deriv w y + (1/2 : ℂ) * w y) := by
        rw [hfirst, mul_zero]
      _ = _ := by ring
  have hGa : G (a-1) = 0 := by simp only [G, ha (a-1) (by linarith), mul_zero]
  funext y
  have hGy := (is_const_of_deriv_eq_zero (fun x => (hG x).differentiableAt)
    (fun x => (hG x).deriv) y (a-1)).trans hGa
  exact (mul_eq_zero.mp hGy).resolve_left (Complex.exp_ne_zero _)

/-- The actual second-order operator commutes with subtraction on smooth tests. -/
theorem poleCancellationOperator_sub_of_contDiff {u v : ℝ → ℂ}
    (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u) (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v) :
    poleCancellationOperator (u-v) = poleCancellationOperator u - poleCancellationOperator v := by
  have hd : deriv (u-v) = deriv u - deriv v := by
    funext y
    exact deriv_sub ((hu.differentiable (by simp)) y) ((hv.differentiable (by simp)) y)
  have hu' : ContDiff ℝ (↑(⊤ : ℕ∞)) (deriv u) := by
    simpa only [Function.iterate_succ_apply, Function.iterate_zero_apply] using
      ContDiff.iterate_deriv 1 hu
  have hv' : ContDiff ℝ (↑(⊤ : ℕ∞)) (deriv v) := by
    simpa only [Function.iterate_succ_apply, Function.iterate_zero_apply] using
      ContDiff.iterate_deriv 1 hv
  have hd2 : deriv (deriv (u-v)) = deriv (deriv u) - deriv (deriv v) := by
    rw [hd]
    funext y
    exact deriv_sub ((hu'.differentiable (by simp)) y) ((hv'.differentiable (by simp)) y)
  funext y
  simp only [poleCancellationOperator, hd2, Pi.sub_apply, smul_sub]
  abel

/-- Uniqueness needs only a lower support bound, rather than two-sided compactness. -/
theorem poleCancellationOperator_injective_of_zero_below {u v : ℝ → ℂ} {a : ℝ}
    (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u) (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (hua : ∀ y < a, u y = 0) (hva : ∀ y < a, v y = 0)
    (hL : poleCancellationOperator u = poleCancellationOperator v) : u = v := by
  have h : u-v = 0 := eq_zero_of_poleCancellationOperator_zero (a := a) (hu.sub hv)
    (fun y hy => by simp only [Pi.sub_apply, hua y hy, hva y hy, sub_self])
    (fun y => by
      rw [poleCancellationOperator_sub_of_contDiff hu hv, hL]
      simp)
  exact sub_eq_zero.mp h

/-- Existence and uniqueness of the actual smooth potential in the original support interval. -/
theorem existsUnique_compact_smooth_polarPotential {f : ℝ → ℂ} {a b : ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (ha : ∀ y < a, f y = 0) (hb : ∀ y > b, f y = 0)
    (h0 : centeredTransform f 0 = 0) (h1 : centeredTransform f 1 = 0) :
    ∃! v : ℝ → ℂ, ContDiff ℝ (↑(⊤ : ℕ∞)) v ∧
      tsupport v ⊆ Set.Icc a b ∧ poleCancellationOperator v = f := by
  refine ⟨compactPolarPotential a b f,
    ⟨compactPolarPotential_contDiff hf a b, compactPolarPotential_tsupport ha hb h0 h1,
      poleCancellationOperator_compactPolarPotential hf.continuous a b⟩, ?_⟩
  intro v hv
  apply poleCancellationOperator_injective_of_zero_below hv.1
    (compactPolarPotential_contDiff hf a b) (a := a)
  · intro y hy
    by_contra hne
    have hs : y ∈ tsupport v := subset_closure hne
    exact (not_le_of_gt hy) (hv.2.1 hs).1
  · exact fun y hy => compactPolarPotential_zero_below ha hy
  · exact hv.2.2.trans (poleCancellationOperator_compactPolarPotential hf.continuous a b).symm

end RiemannResearch.RH
