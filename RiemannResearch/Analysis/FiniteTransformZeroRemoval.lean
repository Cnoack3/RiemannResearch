import RiemannResearch.Analysis.SmoothZeroRemoval
import Mathlib.Analysis.Analytic.Order

/-!
# Removing an arbitrary finite transform multiplicity

The actual integral zero-removal operator is iterated until its transform is
nonzero at a specified point. Every other transform zero is preserved.
The intended consumer is a smooth test isolating one actual zeta zero in the
complete Weil pairing. No zero simplicity or RH assumption is used.
-/

open MeasureTheory
open scoped Topology

namespace RiemannResearch.Analysis

noncomputable section
set_option backward.isDefEq.respectTransparency false

private theorem analyticAt_smoothTransform {f : ℝ → ℂ}
    (hf : SmoothSuperexponentialDecay f) (z : ℂ) :
    AnalyticAt ℂ (BilateralLaplace.centeredTransform f) z :=
  hf.decay.analyticAt_centeredTransform hf.1.continuous z

theorem exists_transform_zero_removed_of_order (k : ℕ) {f : ℝ → ℂ}
    (hf : SmoothSuperexponentialDecay f) (z : ℂ)
    (horder : analyticOrderAt (BilateralLaplace.centeredTransform f) z = k) :
    ∃ g : ℝ → ℂ, SmoothSuperexponentialDecay g ∧
      BilateralLaplace.centeredTransform g z ≠ 0 ∧
      ∀ w : ℂ, w ≠ z → BilateralLaplace.centeredTransform f w = 0 →
        BilateralLaplace.centeredTransform g w = 0 := by
  induction k generalizing f with
  | zero =>
      refine ⟨f, hf, ?_, fun _ _ hw => hw⟩
      exact (analyticAt_smoothTransform hf z).analyticOrderAt_eq_zero.mp (by simpa using horder)
  | succ k ih =>
      have hfz : BilateralLaplace.centeredTransform f z = 0 := by
        apply (analyticAt_smoothTransform hf z).analyticOrderAt_ne_zero.mp
        rw [horder]
        simp
      let g : ℝ → ℂ := removeTransformZero f z
      have hg : SmoothSuperexponentialDecay g := hf.removeTransformZero hfz
      have hfactor : BilateralLaplace.centeredTransform f =
          (fun s : ℂ => s - z) * BilateralLaplace.centeredTransform g := by
        funext s
        exact (removeTransformZero_properties hf.decay hf.1.continuous hfz).2.2 s
      have hlin : analyticOrderAt (fun s : ℂ => s - z) z = 1 := by
        apply (show AnalyticAt ℂ (fun s : ℂ => s - z) z by fun_prop).analyticOrderAt_eq_natCast.mpr
        refine ⟨fun _ : ℂ => (1 : ℂ), analyticAt_const, one_ne_zero, ?_⟩
        exact Filter.Eventually.of_forall (fun s => by simp)
      have ho : ((k + 1 : ℕ) : ℕ∞) = 1 +
          analyticOrderAt (BilateralLaplace.centeredTransform g) z := by
        rw [← horder, hfactor,
          analyticOrderAt_mul (by fun_prop) (analyticAt_smoothTransform hg z),
          hlin]
      have hgo : analyticOrderAt (BilateralLaplace.centeredTransform g) z = k := by
        cases he : analyticOrderAt (BilateralLaplace.centeredTransform g) z with
        | top => simp [he] at ho
        | coe j =>
            rw [he] at ho
            have hj : j = k := by
              have hj' : k + 1 = 1 + j := by exact_mod_cast ho
              omega
            simp [hj]
      obtain ⟨h, hh, hhz, hzeros⟩ := ih hg hgo
      refine ⟨h, hh, hhz, fun w hwz hw => hzeros w hwz ?_⟩
      exact centeredTransform_removeTransformZero_zero_of_ne
        hf.decay hf.1.continuous hfz hw hwz

/-- Finite-order zero removal is an existence theorem for actual spatial
tests; the isolated value is a conclusion rather than an input witness. -/
theorem exists_transform_zero_removed {f : ℝ → ℂ}
    (hf : SmoothSuperexponentialDecay f) (z : ℂ)
    (hfinite : analyticOrderAt (BilateralLaplace.centeredTransform f) z ≠ ⊤) :
    ∃ g : ℝ → ℂ, SmoothSuperexponentialDecay g ∧
      BilateralLaplace.centeredTransform g z ≠ 0 ∧
      ∀ w : ℂ, w ≠ z → BilateralLaplace.centeredTransform f w = 0 →
        BilateralLaplace.centeredTransform g w = 0 := by
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hfinite
  exact exists_transform_zero_removed_of_order k hf z hk.symm

end
end RiemannResearch.Analysis
