import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Finite signed head pairings and squared head energy

Source: user-requested fourth Ramanujan transfer program, 23 October 2026.
These elementary finite-sequence statements are independent of arithmetic
and are shared by the complete Hilbert head/tail applications.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.SequenceHeadTail

def headPair (N : ℕ) (f g : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, f n * g n

def headSquare (N : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, (f n) ^ 2

theorem headSquare_nonneg (N : ℕ) (f : ℕ → ℝ) : 0 ≤ headSquare N f :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem headPair_sq_le (N : ℕ) (f g : ℕ → ℝ) :
    (headPair N f g) ^ 2 ≤ headSquare N f * headSquare N g :=
  Finset.sum_mul_sq_le_sq_mul_sq (Finset.range N) f g

theorem headPair_tendsto_zero {α : Type*} {l : Filter α}
    (N : ℕ) (r : ℕ → ℝ) (e : α → ℕ → ℝ)
    (he : ∀ n, Tendsto (fun i => e i n) l (𝓝 0)) :
    Tendsto (fun i => headPair N r (e i)) l (𝓝 0) := by
  induction N with
  | zero => simpa only [headPair, Finset.sum_range_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : α => (0 : ℝ)) l (𝓝 0))
  | succ N ih =>
      have h := ih.add ((he N).const_mul (r N))
      simpa only [headPair, Finset.sum_range_succ, mul_zero, add_zero] using h

end RiemannResearch.Analysis.SequenceHeadTail
