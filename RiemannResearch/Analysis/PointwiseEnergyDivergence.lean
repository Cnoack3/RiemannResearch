import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Order.Basic

/-!
# Divergence of nonnegative energies under pointwise convergence

Source: the finite-sum proof of Fatou's inequality, used in the September 14,
2026 arithmetic component analysis. No arithmetic hypotheses occur here.
-/
namespace RiemannResearch.Analysis
open scoped BigOperators Topology
open Filter
noncomputable section

/-- Discrete Fatou consequence stated as divergence of the whole energy.
The proof retains all finite coordinates before comparing with the full sum. -/
theorem total_nonnegative_energy_tendsto_atTop
    (E : ℕ → ℕ → ℝ) (e : ℕ → ℝ)
    (hE : ∀ j n, 0 ≤ E j n) (he : ∀ n, 0 ≤ e n)
    (hs : ∀ j, Summable (E j))
    (hp : ∀ n, Tendsto (fun j => E j n) atTop (𝓝 (e n)))
    (hn : ¬ Summable e) :
    Tendsto (fun j => ∑' n : ℕ, E j n) atTop atTop := by
  classical
  apply tendsto_atTop.2
  intro C
  have hex : ∃ s : Finset ℕ, C < ∑ n ∈ s, e n := by
    by_contra! hb
    exact hn (summable_of_sum_le he hb)
  obtain ⟨s, hsC⟩ := hex
  have ht : Tendsto (fun j => ∑ n ∈ s, E j n) atTop (𝓝 (∑ n ∈ s, e n)) := by
    apply tendsto_finsetSum
    intro n _
    exact hp n
  have hlarge : ∀ᶠ j in atTop, C < ∑ n ∈ s, E j n :=
    (tendsto_order.1 ht).1 C hsC
  filter_upwards [hlarge] with j hj
  exact hj.le.trans ((hs j).sum_le_tsum s (fun n _ => hE j n))

end
end RiemannResearch.Analysis
