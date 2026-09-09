import RiemannResearch.RH.ParetoClosedRepairTails
import RiemannResearch.RH.ParetoHeadMeanEnergy

/-!
# Sharp mean-zero arithmetic pivot energy

Source: user-provided `ParetoCovarianceRepairReport_Advanced_2026-09-08.md`,
Section 4.4. These are identities in the complete Pareto Hilbert space.
The anchor is physical coordinate i+1 because the Gibbs index starts at zero.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
noncomputable section

theorem closedRepairTail_mean_zero (f : ℕ → ThresholdHilbert)
    (hm : ∀ i, inner ℝ (f i) hilbertOne = 0)
    (i : ℕ) (x : ThresholdHilbert) (hx : x ∈ closedRepairTail f i) :
    inner ℝ x hilbertOne = 0 := by
  have hone : hilbertOne ∈ (repairTailSpan f i)ᗮ := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨j, hj, rfl⟩ := hy
        exact hm j
    | zero => simp
    | add a b ha hb iha ihb => simp [inner_add_left, iha, ihb]
    | smul c a ha ih => simp [real_inner_smul_left, ih]
  rw [real_inner_comm]
  exact hx _ hone

theorem infiniteRepairPivot_mean_zero (f : ℕ → ThresholdHilbert)
    (hm : ∀ i, inner ℝ (f i) hilbertOne = 0) (i : ℕ) :
    inner ℝ (infiniteRepairPivot f i) hilbertOne = 0 :=
  closedRepairTail_mean_zero f hm i _ (infiniteRepairPivot_mem f i)

/-- The mean-zero unit-anchor repair has exact squared minimum 1/(i+1)^2,
plus the complete orthogonal tail remainder. -/
theorem pareto_mean_zero_unit_anchor_energy (x : ThresholdHilbert) (i : ℕ)
    (hh : ∀ k < i, hilbertGibbsPhysical x k = 0)
    (ha : hilbertGibbsPhysical x i = -1)
    (hm : inner ℝ x hilbertOne = 0) :
    ‖x‖^2 = 1 / ((i : ℝ)+1)^2 + ‖x - paretoHeadMeanMinimizer (i+1) x‖^2 := by
  have hsum (g : ℕ → ℝ) (hzero : ∀ k < i, g k = 0) :
      (∑ k ∈ Finset.range (i+1), g k) = g i := by
    rw [Finset.sum_range_succ]
    have hz : (∑ k ∈ Finset.range i, g k) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      exact hzero k (Finset.mem_range.mp hk)
    rw [hz, zero_add]
  have hs : (∑ k ∈ Finset.range (i+1),
      paretoWeight k * hilbertGibbsPhysical x k^2) = paretoWeight i := by
    rw [hsum _ (by intro k hk; rw [hh k hk]; ring), ha]
    ring
  have hmhead : paretoHeadMean (i+1) x = -paretoWeight i := by
    unfold paretoHeadMean
    rw [hsum _ (by intro k hk; rw [hh k hk, mul_zero]), ha]
    ring
  have hcost : paretoWeight i + (((i+1 : ℕ) : ℝ)+1) * (0 - -paretoWeight i)^2 =
      1 / ((i : ℝ)+1)^2 := by
    unfold paretoWeight
    push_cast
    have h1 : (i : ℝ)+1 ≠ 0 := by positivity
    have h2 : (i : ℝ)+2 ≠ 0 := by positivity
    field_simp
    ring
  rw [paretoHeadMean_energy_identity (i+1) x, hs, hmhead, hm, hcost]

theorem pareto_mean_zero_unit_anchor_lower (x : ThresholdHilbert) (i : ℕ)
    (hh : ∀ k < i, hilbertGibbsPhysical x k = 0)
    (ha : hilbertGibbsPhysical x i = -1)
    (hm : inner ℝ x hilbertOne = 0) : 1 / ((i : ℝ)+1)^2 ≤ ‖x‖^2 := by
  rw [pareto_mean_zero_unit_anchor_energy x i hh ha hm]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- The sharp mean constraint improves the single-coordinate bound on every
actual infinite arithmetic pivot. -/
theorem infiniteRepairPivot_sharp_lower (f : ℕ → ThresholdHilbert)
    (htri : ∀ i k, k < i → hilbertGibbsPhysical (f i) k = 0)
    (hm : ∀ i, inner ℝ (f i) hilbertOne = 0)
    (i : ℕ) (ha : hilbertGibbsPhysical (f i) i = -1) :
    1 / ((i : ℝ)+1)^2 ≤ ‖infiniteRepairPivot f i‖^2 := by
  apply pareto_mean_zero_unit_anchor_lower _ i
  · intro k hk
    rw [infiniteRepairPivot_head f htri i k (le_of_lt hk), htri i k hk]
  · rw [infiniteRepairPivot_head f htri i i le_rfl, ha]
  · exact infiniteRepairPivot_mean_zero f hm i

/-- Sparse arithmetic indexing is allowed: p is the physical anchor index,
whereas i is the position of the repair in its enumeration. -/
theorem infiniteRepairPivot_sharp_lower_at_anchor (f : ℕ → ThresholdHilbert)
    (hm : ∀ j, inner ℝ (f j) hilbertOne = 0)
    (i p : ℕ)
    (hhead : ∀ k < p, hilbertGibbsPhysical (f i) k = 0)
    (ha : hilbertGibbsPhysical (f i) p = -1)
    (hfuture : ∀ j, i < j → ∀ k ≤ p, hilbertGibbsPhysical (f j) k = 0) :
    1 / ((p : ℝ)+1)^2 ≤ ‖infiniteRepairPivot f i‖^2 := by
  apply pareto_mean_zero_unit_anchor_lower _ p
  · intro k hk
    rw [infiniteRepairPivot_anchor f i k (fun j hj => hfuture j hj k (le_of_lt hk)),
      hhead k hk]
  · rw [infiniteRepairPivot_anchor f i p (fun j hj => hfuture j hj p le_rfl), ha]
  · exact infiniteRepairPivot_mean_zero f hm i

end
end RiemannResearch.RH.Pareto
