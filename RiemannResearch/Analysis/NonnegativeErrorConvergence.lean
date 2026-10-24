import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.Order.Basic

/-! Nonnegative complete error budgets along arbitrary filters. -/

open Filter
open scoped Topology
namespace RiemannResearch.Analysis.NonnegativeErrorConvergence

theorem norm_zero_iff_square {α H : Type*} {l : Filter α}
    [NormedAddCommGroup H] (f : α → H) :
    Tendsto (fun i => ‖f i‖) l (𝓝 0) ↔
      Tendsto (fun i => ‖f i‖ ^ 2) l (𝓝 0) := by
  constructor
  · intro h
    simpa only [zero_pow (by decide : 2 ≠ 0)] using h.pow 2
  · intro h
    have hs := Real.continuous_sqrt.continuousAt.tendsto.comp h
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), Real.sqrt_zero] using hs

theorem nonnegative_add_zero_iff {α : Type*} {l : Filter α}
    (f g : α → ℝ) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i) :
    Tendsto (fun i => f i + g i) l (𝓝 0) ↔
      Tendsto f l (𝓝 0) ∧ Tendsto g l (𝓝 0) := by
  constructor
  · intro h
    exact ⟨squeeze_zero hf (fun i => le_add_of_nonneg_right (hg i)) h,
      squeeze_zero hg (fun i => le_add_of_nonneg_left (hf i)) h⟩
  · rintro ⟨h₁, h₂⟩
    simpa only [add_zero] using h₁.add h₂

end RiemannResearch.Analysis.NonnegativeErrorConvergence
