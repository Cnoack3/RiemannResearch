import RiemannResearch.RH.ParetoGibbsEnergy

/-!
# Positivity of the complete Gibbs operator

The finite beta-integral Gram positivity is extended to every vector of the
actual weighted Hilbert space. Absolute convergence of the full product form
justifies passage to cofinal finite squares. No spectral theorem is assumed.
-/

open scoped BigOperators
open Filter
namespace RiemannResearch.RH.Pareto
noncomputable section

private theorem finite_square_cofinal :
    Tendsto (fun s : Finset ℕ => s ×ˢ s) atTop atTop := by
  apply tendsto_atTop.2
  intro t
  filter_upwards [eventually_ge_atTop (t.image Prod.fst ∪ t.image Prod.snd)] with s hs
  intro p hp
  apply Finset.mem_product.mpr
  constructor
  · exact hs (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩))
  · exact hs (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩))

/-- Positivity of the actual full operator form for every weighted H vector. -/
theorem gibbsAction_pairing_nonneg {f : ℕ → ℝ}
    (hf : Summable (fun n => paretoWeight n * f n ^ 2)) :
    0 ≤ ∑' n, paretoWeight n * (f n * gibbsAction f n) := by
  rw [← gibbs_cross_tsum hf hf]
  have hsum := (gibbs_cross_summable hf hf).hasSum
  change Tendsto (fun t : Finset (ℕ × ℕ) =>
    ∑ p ∈ t, geometricKernel p.1 p.2 * (f p.1 * f p.2)) atTop
      (nhds (∑' p : ℕ × ℕ, geometricKernel p.1 p.2 * (f p.1 * f p.2))) at hsum
  have hlimit := hsum.comp finite_square_cofinal
  apply ge_of_tendsto hlimit
  apply Eventually.of_forall
  intro s
  change 0 ≤ ∑ p ∈ s ×ˢ s, geometricKernel p.1 p.2 * (f p.1 * f p.2)
  calc
    0 ≤ ∑ n ∈ s, ∑ m ∈ s, f n * f m * geometricKernel n m :=
      geometricKernel_positive_semidefinite s f
    _ = _ := by
      rw [Finset.sum_product]
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro m hm
      ring

end
end RiemannResearch.RH.Pareto
