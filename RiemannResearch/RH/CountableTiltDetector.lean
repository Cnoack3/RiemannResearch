import RiemannResearch.Analysis.CountableLaplaceDetector
import RiemannResearch.RH.PoleCancellationTransform
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic.NormNum

/-!
# A compact detector annihilating the two poles

Source: user-provided countable-tilt argument in RH_Lean_Continuation_2026-09-09.zip.
This applies the general compact detector to the concrete operator D²−1/4.
It detects a specified countable set excluding 0 and 1, not an entire open strip.
-/

noncomputable section
open MeasureTheory RiemannResearch.Analysis
open scoped Topology
namespace RiemannResearch.RH

/-- One genuine smooth compact pole-annihilating test detects a prescribed
countable set disjoint from the two poles. No growth estimate is asserted. -/
theorem exists_smooth_compact_pole_annihilating_countable_detector
    {S : Set ℂ} (hS : S.Countable)
    (hSp : ∀ s ∈ S, s ≠ 0 ∧ s ≠ 1) :
    ∃ f : ℝ → ℂ, ContDiff ℝ (↑(⊤ : ℕ∞)) f ∧ HasCompactSupport f ∧
      f ≠ 0 ∧ BilateralLaplace.centeredTransform f 0 = 0 ∧
      BilateralLaplace.centeredTransform f 1 = 0 ∧
      ∀ s ∈ S, BilateralLaplace.centeredTransform f s ≠ 0 := by
  obtain ⟨v, hv, hvc, hd⟩ :=
    exists_smooth_compact_countable_detector (hS.insert (1 / 2))
  have hv' : ContDiff ℝ (↑(⊤ : ℕ∞)) (deriv v) := by
    simpa only [Function.iterate_succ_apply, Function.iterate_zero_apply] using
      ContDiff.iterate_deriv 1 hv
  have hv'' : ContDiff ℝ (↑(⊤ : ℕ∞)) (deriv (deriv v)) := by
    simpa only [Function.iterate_succ_apply, Function.iterate_zero_apply] using
      ContDiff.iterate_deriv 2 hv
  have ht (s : ℂ) :
      BilateralLaplace.centeredTransform (RiemannResearch.RH.poleCancellationOperator v) s =
        s * (s - 1) * BilateralLaplace.centeredTransform v s := by
    exact BilateralLaplace.centeredTransform_poleCancellationOperator
      (BilateralLaplace.hasExponentialMoments_of_compactSupport hv.continuous hvc)
      (BilateralLaplace.hasExponentialMoments_of_compactSupport hv'.continuous hvc.deriv)
      (BilateralLaplace.hasExponentialMoments_of_compactSupport hv''.continuous hvc.deriv.deriv)
      (hv.differentiable (by simp)) (hv'.differentiable (by simp)) s
  have hsmul : HasCompactSupport (fun y : ℝ => (1 / 4 : ℝ) • v y) :=
    hvc.smul_left (f := fun _ : ℝ => (1 / 4 : ℝ))
  have hfc : HasCompactSupport (RiemannResearch.RH.poleCancellationOperator v) := by
    unfold RiemannResearch.RH.poleCancellationOperator
    exact hvc.deriv.deriv.sub hsmul
  have hhalf :
      BilateralLaplace.centeredTransform (RiemannResearch.RH.poleCancellationOperator v)
        (1 / 2) ≠ 0 := by
    rw [ht]
    exact mul_ne_zero (by norm_num) (hd _ (Set.mem_insert _ _))
  have hfn : RiemannResearch.RH.poleCancellationOperator v ≠ 0 := by
    intro he
    apply hhalf
    simp [he, BilateralLaplace.centeredTransform, BilateralLaplace.transform]
  refine ⟨RiemannResearch.RH.poleCancellationOperator v,
    RiemannResearch.RH.poleCancellationOperator_contDiff hv, hfc, hfn,
    by simp [ht], by simp [ht], ?_⟩
  intro s hs
  rw [ht]
  exact mul_ne_zero (mul_ne_zero (hSp s hs).1 (sub_ne_zero.mpr (hSp s hs).2))
    (hd s (Set.mem_insert_of_mem _ hs))

end RiemannResearch.RH
