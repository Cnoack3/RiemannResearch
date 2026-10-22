import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Circle
import Mathlib.Topology.Algebra.Group.SubmonoidClosure
import Mathlib.Tactic.Linarith

/-!
# Zero persistence and finite phase recurrence

Source: user-provided argument, RH_CRT_Packet_Research_2026-09-09.md,
Section 9.2. Only zero existence, rather than the full multiplicity-counting
Rouche theorem, is needed. Here the inverse maximum-modulus principle gives
the required persistence lemma directly. Compact-group recurrence supplies
arbitrarily large simultaneous phase returns.
-/

namespace RiemannResearch.Analysis
open Set Filter Metric
open scoped Topology

/-- A holomorphic function whose center norm is strictly smaller than its
positive boundary lower bound has a zero in the open disk. -/
theorem exists_zero_in_ball_of_boundary_lower {g : ℂ → ℂ} {c : ℂ} {r δ : ℝ}
    (hr : 0 < r) (hδ : 0 < δ) (hg : DiffContOnCl ℂ g (ball c r))
    (hboundary : ∀ z ∈ sphere c r, δ ≤ ‖g z‖) (hcenter : ‖g c‖ < δ) :
    ∃ z ∈ ball c r, g z = 0 := by
  by_contra hnone
  have hzero : ∀ z ∈ ball c r, g z ≠ 0 := by
    intro z hz hgz
    exact hnone ⟨z, hz, hgz⟩
  have hclosed : ∀ z ∈ closure (ball c r), g z ≠ 0 := by
    intro z hz
    have hdist : dist z c ≤ r := closure_ball_subset_closedBall hz
    rcases lt_or_eq_of_le hdist with hlt | heq
    · exact hzero z hlt
    · have hb := hboundary z heq
      intro hgz
      rw [hgz, norm_zero] at hb
      exact (not_le_of_gt hδ) hb
  have hinv : DiffContOnCl ℂ (fun z => (g z)⁻¹) (ball c r) := hg.inv hclosed
  have hbound : ∀ z ∈ frontier (ball c r), ‖(g z)⁻¹‖ ≤ δ⁻¹ := by
    intro z hz
    have hb := hboundary z (frontier_ball_subset_sphere hz)
    have hp : 0 < ‖g z‖ := lt_of_lt_of_le hδ hb
    rw [norm_inv]
    exact (inv_le_inv₀ hp hδ).2 hb
  have hc : c ∈ closure (ball c r) := subset_closure (mem_ball_self hr)
  have hi := Complex.norm_le_of_forall_mem_frontier_norm_le
    (isBounded_ball : Bornology.IsBounded (ball c r)) hinv hbound hc
  rw [norm_inv] at hi
  have hgc : 0 < ‖g c‖ := norm_pos_iff.mpr (hclosed c hc)
  have hcontra : δ ≤ ‖g c‖ := (inv_le_inv₀ hgc hδ).1 hi
  exact (not_le_of_gt hcenter) hcontra

/-- A perturbation retains a zero when its boundary error and center value
are each smaller than half a positive boundary lower bound of the reference.
All differences remain in the premise; no probabilistic independence occurs. -/
theorem exists_zero_in_ball_of_uniform_perturbation {f g : ℂ → ℂ}
    {c : ℂ} {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ)
    (hg : DiffContOnCl ℂ g (ball c r))
    (hf : ∀ z ∈ sphere c r, δ ≤ ‖f z‖)
    (herror : ∀ z ∈ sphere c r, ‖g z - f z‖ < δ / 2)
    (hcenter : ‖g c‖ < δ / 2) :
    ∃ z ∈ ball c r, g z = 0 := by
  apply exists_zero_in_ball_of_boundary_lower hr (by linarith : 0 < δ / 2) hg
    (fun z hz => ?_) hcenter
  have he := herror z hz
  have hnorm := norm_sub_norm_le (f z) (g z)
  rw [norm_sub_rev] at hnorm
  linarith [hf z hz]

/-- Arbitrarily late simultaneous return of any finite collection of circle
phases. The product is compact, so the statement has no irrationality premise. -/
theorem finite_circle_phases_return {ι : Type*} [Fintype ι]
    (z : ι → Circle) (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ n : ℕ, N < n ∧ ∀ i, dist ((z i) ^ n) 1 < ε := by
  let U : Set (ι → Circle) := ⋂ i, {p | dist (p i) 1 < ε}
  have hU : IsOpen U := by
    apply isOpen_iInter_of_finite
    intro i
    exact isOpen_lt ((continuous_apply i).dist continuous_const) continuous_const
  have hone : (1 : ι → Circle) ∈ U := by simp [U, hε]
  have hfreq := (mapClusterPt_one_atTop_pow z).frequently (hU.mem_nhds hone)
  obtain ⟨n, hn, hmem⟩ := frequently_atTop'.1 hfreq N
  refine ⟨n, hn, ?_⟩
  intro i
  have hi := Set.mem_iInter.mp (show z ^ n ∈ U from hmem) i
  change dist ((z ^ n) i) 1 < ε at hi
  simpa only [Pi.pow_apply] using hi

end RiemannResearch.Analysis
