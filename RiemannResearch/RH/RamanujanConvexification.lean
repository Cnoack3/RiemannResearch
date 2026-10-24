import RiemannResearch.Analysis.HilbertTailConvexification
import RiemannResearch.RH.RamanujanWeakConvergence

/-!
# Finite convexification of bounded pointwise Ramanujan approximants

Source: user-requested fifth Ramanujan transfer program, 24 October 2026.
Every filter-large tail of a bounded physically pointwise convergent family
contains finite convex combinations arbitrarily close in the full P or Q norm.
For legal packet families, each combination is represented by one finite
packet coefficient array at a common cutoff containing every chosen stage.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.RamanujanConvexification
open Pareto ZetaTwoHilbert QRamanujanPackets
open RamanujanTrialConvergence RamanujanWeakConvergence
open RiemannResearch.Analysis.HilbertTailConvexification

theorem pareto_tail_convex_approx
    {α : Type*} {l : Filter α} [NeBot l]
    (F : α → ThresholdHilbert) (x : ThresholdHilbert)
    (hpoint : ∀ k : ℕ, 0 < k →
      Tendsto (fun i => hilbertSequence (F i) k) l (𝓝 (hilbertSequence x k)))
    (C : ℝ) (hbound : ∀ᶠ i in l, ‖F i‖ ^ 2 ≤ C)
    (s : Set α) (hs : s ∈ l) (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (w : Fin n → ℝ) (j : Fin n → α),
      (∀ k, 0 ≤ w k) ∧ (∑ k, w k) = 1 ∧ (∀ k, j k ∈ s) ∧
        ‖(∑ k, w k • F (j k)) - x‖ < ε :=
  exists_finite_tail_combination F x
    (pareto_innerWeak_of_bounded_pointwise F x hpoint C hbound) s hs ε hε

theorem q_tail_convex_approx
    {α : Type*} {l : Filter α} [NeBot l]
    (F : α → QHilbert) (x : QHilbert)
    (hpoint : ∀ k : ℕ, 0 < k →
      Tendsto (fun i => qSequence (F i) k) l (𝓝 (qSequence x k)))
    (C : ℝ) (hbound : ∀ᶠ i in l, ‖F i‖ ^ 2 ≤ C)
    (s : Set α) (hs : s ∈ l) (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (w : Fin n → ℝ) (j : Fin n → α),
      (∀ k, 0 ≤ w k) ∧ (∑ k, w k) = 1 ∧ (∀ k, j k ∈ s) ∧
        ‖(∑ k, w k • F (j k)) - x‖ < ε :=
  exists_finite_tail_combination F x
    (q_innerWeak_of_bounded_pointwise F x hpoint C hbound) s hs ε hε

/-- Convexification produces an actual finite Pareto packet coefficient array. -/
theorem pareto_packet_tail_convex_approx
    {α : Type*} {l : Filter α} [NeBot l]
    (N : α → ℕ) (a : ∀ i, Fin (N i) → ℝ) (x : ThresholdHilbert)
    (hpoint : ∀ k : ℕ, 0 < k →
      Tendsto (fun i => hilbertSequence (paretoTrial (N i) (a i)) k)
        l (𝓝 (hilbertSequence x k)))
    (C : ℝ) (hbound : ∀ᶠ i in l, ‖paretoTrial (N i) (a i)‖ ^ 2 ≤ C)
    (s : Set α) (hs : s ∈ l) (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (w : Fin n → ℝ) (j : Fin n → α) (M : ℕ) (b : Fin M → ℝ),
      (∀ k, 0 ≤ w k) ∧ (∑ k, w k) = 1 ∧ (∀ k, j k ∈ s) ∧
        (∀ k, N (j k) ≤ M) ∧
        paretoTrial M b = ∑ k, w k • paretoTrial (N (j k)) (a (j k)) ∧
        ‖paretoTrial M b - x‖ < ε := by
  obtain ⟨n, w, j, hw, hsum, hj, hclose⟩ := pareto_tail_convex_approx
    (fun i => paretoTrial (N i) (a i)) x hpoint C hbound s hs ε hε
  obtain ⟨M, b, hM, hb⟩ := finite_partial_synthesis_common_stage
    (fun k => ramanujanPacketHilbert (k + 2)) (fun k => N (j k))
    (fun k => a (j k)) w
  change paretoTrial M b = ∑ k, w k • paretoTrial (N (j k)) (a (j k)) at hb
  exact ⟨n, w, j, M, b, hw, hsum, hj, hM, hb, by simpa only [hb] using hclose⟩

/-- The same finite construction is legal in the actual Q dictionary and norm. -/
theorem q_packet_tail_convex_approx
    {α : Type*} {l : Filter α} [NeBot l]
    (N : α → ℕ) (a : ∀ i, Fin (N i) → ℝ) (x : QHilbert)
    (hpoint : ∀ k : ℕ, 0 < k →
      Tendsto (fun i => qSequence (qTrial (N i) (a i)) k) l (𝓝 (qSequence x k)))
    (C : ℝ) (hbound : ∀ᶠ i in l, ‖qTrial (N i) (a i)‖ ^ 2 ≤ C)
    (s : Set α) (hs : s ∈ l) (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (w : Fin n → ℝ) (j : Fin n → α) (M : ℕ) (b : Fin M → ℝ),
      (∀ k, 0 ≤ w k) ∧ (∑ k, w k) = 1 ∧ (∀ k, j k ∈ s) ∧
        (∀ k, N (j k) ≤ M) ∧
        qTrial M b = ∑ k, w k • qTrial (N (j k)) (a (j k)) ∧
        ‖qTrial M b - x‖ < ε := by
  obtain ⟨n, w, j, hw, hsum, hj, hclose⟩ := q_tail_convex_approx
    (fun i => qTrial (N i) (a i)) x hpoint C hbound s hs ε hε
  obtain ⟨M, b, hM, hb⟩ := finite_partial_synthesis_common_stage
    (fun k => qRamanujanPacket (k + 2)) (fun k => N (j k))
    (fun k => a (j k)) w
  change qTrial M b = ∑ k, w k • qTrial (N (j k)) (a (j k)) at hb
  exact ⟨n, w, j, M, b, hw, hsum, hj, hM, hb, by simpa only [hb] using hclose⟩

end RiemannResearch.RH.RamanujanConvexification
