import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Exact Gram sums for absolutely summable real Hilbert families

Source: continuation of the user-provided
DyadicAllScaleConvergenceVerification20260910(2).md, September 10, 2026.
The proof uses continuous linear functionals and absolute convergence.
Every signed off-diagonal pairing remains in the product-index sum.
-/

namespace RiemannResearch.Analysis
noncomputable section

variable {ι κ E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem summable_norm_inner_product_of_summable_norm
    (f : ι → E) (g : κ → E)
    (hf : Summable (fun i => ‖f i‖)) (hg : Summable (fun j => ‖g j‖)) :
    Summable (fun p : ι × κ => ‖inner ℝ (f p.1) (g p.2)‖) := by
  have hf' : Summable (fun i => ‖‖f i‖‖) := by simpa only [norm_norm] using hf
  have hg' : Summable (fun j => ‖‖g j‖‖) := by simpa only [norm_norm] using hg
  have hm := summable_mul_of_summable_norm hf' hg'
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun p => norm_inner_le_norm (f p.1) (g p.2)) hm

theorem inner_tsum_eq_tsum_product [CompleteSpace E]
    (f : ι → E) (g : κ → E)
    (hf : Summable (fun i => ‖f i‖)) (hg : Summable (fun j => ‖g j‖)) :
    inner ℝ (∑' i, f i) (∑' j, g j) =
      ∑' p : ι × κ, inner ℝ (f p.1) (g p.2) := by
  have hs := (summable_norm_inner_product_of_summable_norm f g hf hg).of_norm
  rw [hs.tsum_prod]
  calc
    _ = inner ℝ (∑' j, g j) (∑' i, f i) := real_inner_comm _ _
    _ = ∑' i, inner ℝ (∑' j, g j) (f i) :=
      (innerSL ℝ (∑' j, g j)).map_tsum hf.of_norm
    _ = ∑' i, ∑' j, inner ℝ (f i) (g j) := by
      apply tsum_congr
      intro i
      rw [real_inner_comm]
      exact (innerSL ℝ (f i)).map_tsum hg.of_norm

theorem norm_sq_tsum_eq_tsum_gram [CompleteSpace E]
    (f : ι → E) (hf : Summable (fun i => ‖f i‖)) :
    ‖∑' i, f i‖ ^ 2 = ∑' p : ι × ι, inner ℝ (f p.1) (f p.2) := by
  rw [← real_inner_self_eq_norm_sq]
  exact inner_tsum_eq_tsum_product f f hf hf

end
end RiemannResearch.Analysis
