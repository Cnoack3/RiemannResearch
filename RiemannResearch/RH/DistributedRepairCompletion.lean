import RiemannResearch.RH.FiniteBoundaryRepairObstruction

/-!
# Exact error accounting for distributed root repairs

The full error is split into the uniform-share floor, every signed-share
fluctuation, every adjacent-pair square remainder, and the entire unselected
tail.  No summand of the full error is discarded in the identity.
-/

namespace RiemannResearch.RH.DistributedRepair

open scoped BigOperators
open OneBoundaryRepair PositiveSeedCone

noncomputable section

def selectedCoordinates (s : Finset ℕ) : Finset ℕ :=
  s.biUnion (fun T => {T - 2, T - 1})

theorem adjacent_error_completion_at_endpoint (F : ℕ → ℝ) (T : ℕ)
    (ρ : ℝ) (hT : 1 < T)
    (hjump : F T - F (T - 1) = -(T : ℝ) * ρ / 3) :
    weightedError F (T - 2) + weightedError F (T - 1) =
      ρ ^ 2 / 18 + adjacentRemainder F (T - 2) := by
  have ht2 : T - 2 + 2 = T := by omega
  have ht1 : T - 2 + 1 = T - 1 := by omega
  have htc : ((T - 2 : ℕ) : ℝ) + 2 = (T : ℝ) := by exact_mod_cast ht2
  have hTR : (T : ℝ) ≠ 0 := by exact_mod_cast (show T ≠ 0 by omega)
  have h := adjacent_error_completion F (T - 2)
  rw [ht2, ht1, htc, hjump] at h
  have he : (-(T : ℝ) * ρ / 3) ^ 2 / (2 * (T : ℝ) ^ 2) = ρ ^ 2 / 18 := by
    field_simp
    ring
  rwa [he] at h

/-- The exact full infinite error, with all four nonnegative contributions. -/
theorem fullError_distributed_completion (F : ℕ → ℝ) (s : Finset ℕ)
    (ρ : ℕ → ℝ) (hs : s.Nonempty) (hT : ∀ T ∈ s, 1 < T)
    (hdisjoint : ∀ T ∈ s, ∀ U ∈ s, T ≠ U →
      Disjoint ({T - 2, T - 1} : Finset ℕ) {U - 2, U - 1})
    (hρ : ∑ T ∈ s, ρ T = 1)
    (hjump : ∀ T ∈ s, F T - F (T - 1) = -(T : ℝ) * ρ T / 3)
    (hsum : Summable (weightedError F)) :
    (∑' k : ℕ, weightedError F k) =
      1 / (18 * (s.card : ℝ)) +
      (∑ T ∈ s, (ρ T - 1 / (s.card : ℝ)) ^ 2) / 18 +
      (∑ T ∈ s, adjacentRemainder F (T - 2)) +
      ∑' k : {k : ℕ // k ∉ selectedCoordinates s}, weightedError F k := by
  classical
  have hselected : (∑ k ∈ selectedCoordinates s, weightedError F k) =
      (∑ T ∈ s, (ρ T) ^ 2) / 18 +
        ∑ T ∈ s, adjacentRemainder F (T - 2) := by
    unfold selectedCoordinates
    rw [Finset.sum_biUnion hdisjoint]
    have heach :
        (∑ T ∈ s, ∑ k ∈ ({T - 2, T - 1} : Finset ℕ), weightedError F k) =
        ∑ T ∈ s, ((ρ T) ^ 2 / 18 + adjacentRemainder F (T - 2)) := by
      apply Finset.sum_congr rfl
      intro T hTs
      have hne : T - 2 ≠ T - 1 := by have := hT T hTs; omega
      simp only [Finset.sum_pair hne]
      exact adjacent_error_completion_at_endpoint F T (ρ T) (hT T hTs) (hjump T hTs)
    rw [heach, Finset.sum_add_distrib, ← Finset.sum_div]
  have hshare := FiniteRepairTriangular.signed_share_square_completion s ρ hs hρ
  have hsplit := hsum.sum_add_tsum_subtype_compl (selectedCoordinates s)
  rw [hselected, hshare] at hsplit
  rw [← hsplit]
  ring

theorem fullError_distributed_lower (F : ℕ → ℝ) (s : Finset ℕ)
    (ρ : ℕ → ℝ) (hs : s.Nonempty) (hT : ∀ T ∈ s, 1 < T)
    (hdisjoint : ∀ T ∈ s, ∀ U ∈ s, T ≠ U →
      Disjoint ({T - 2, T - 1} : Finset ℕ) {U - 2, U - 1})
    (hρ : ∑ T ∈ s, ρ T = 1)
    (hjump : ∀ T ∈ s, F T - F (T - 1) = -(T : ℝ) * ρ T / 3)
    (hsum : Summable (weightedError F)) :
    1 / (18 * (s.card : ℝ)) ≤ ∑' k : ℕ, weightedError F k := by
  rw [fullError_distributed_completion F s ρ hs hT hdisjoint hρ hjump hsum]
  have hfluc : 0 ≤ (∑ T ∈ s, (ρ T - 1 / (s.card : ℝ)) ^ 2) / 18 := by positivity
  have hrem : 0 ≤ ∑ T ∈ s, adjacentRemainder F (T - 2) :=
    Finset.sum_nonneg (fun T _ => adjacentRemainder_nonneg F (T - 2))
  have htail : 0 ≤ ∑' k : {k : ℕ // k ∉ selectedCoordinates s}, weightedError F k :=
    tsum_nonneg (fun k => weightedError_nonneg F k)
  linarith

end
end RiemannResearch.RH.DistributedRepair
