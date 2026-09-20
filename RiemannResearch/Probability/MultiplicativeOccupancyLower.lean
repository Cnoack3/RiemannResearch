import RiemannResearch.Probability.MultiplicativeOccupancy
import Mathlib.Algebra.BigOperators.Fin

/-!
# A uniform first-site lower bound for damped occupation products

Source: user-provided damped DPP criterion, 2026-09-20. At damping weight 1/2,
a persistent first-site hole creates a fixed relative excess above the full
occupation benchmark, uniformly in the size of the finite observation window.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace RiemannResearch.Probability.Occupancy

theorem product_first_site_lower (m : ℕ) (a : Fin (m + 1) → ℝ)
    (ha : ∀ i, 0 < a i ∧ a i < 1) (ha0 : a 0 = 1 / 2)
    (x : Fin (m + 1) → Bool) :
    benchmark a * (if x 0 = false then 2 else 1) ≤ product a x := by
  have h := (product_bounds (fun i : Fin m => a i.succ)
    (fun i => ha i.succ) (fun i => x i.succ)).2.1
  unfold benchmark product at h ⊢
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ, ha0]
  cases hx : x 0 <;> simp only [Bool.false_eq_true, Bool.true_eq_false,
    ↓reduceIte] <;> nlinarith

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem integral_product_first_site_lower (m : ℕ) (a : Fin (m + 1) → ℝ)
    (ha : ∀ i, 0 < a i ∧ a i < 1) (ha0 : a 0 = 1 / 2)
    (f : Ω → Fin (m + 1) → Bool) (hf : Measurable f) :
    benchmark a * (1 + μ.real {ω | f ω 0 = false}) ≤
      ∫ ω, product a (f ω) ∂μ := by
  let A : Set Ω := {ω | f ω 0 = false}
  have hA : MeasurableSet A :=
    (measurableSet_singleton false).preimage ((measurable_pi_apply 0).comp hf)
  have hintA : Integrable (A.indicator (1 : Ω → ℝ)) μ :=
    (integrable_const (1 : ℝ)).indicator hA
  have hl : Integrable (fun ω => benchmark a * (1 + A.indicator (1 : Ω → ℝ) ω)) μ :=
    ((integrable_const (1 : ℝ)).add hintA).const_mul _
  have hle : (fun ω => benchmark a * (1 + A.indicator (1 : Ω → ℝ) ω)) ≤
      (fun ω => product a (f ω)) := by
    intro ω
    have h := product_first_site_lower m a ha ha0 (f ω)
    by_cases hx : f ω 0 = false <;> simpa [A, hx, show (1 : ℝ) + 1 = 2 by norm_num] using h
  have hi := integral_mono hl (product_integrable μ a ha f hf) hle
  rw [integral_const_mul, integral_add (integrable_const (1 : ℝ)) hintA,
    integral_const, probReal_univ, one_smul, integral_indicator_one hA] at hi
  exact hi

end RiemannResearch.Probability.Occupancy
