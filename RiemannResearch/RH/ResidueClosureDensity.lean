import RiemannResearch.RH.ArgumentDoublingGenerators
import RiemannResearch.RH.ParetoExactHeadClosure

/-!
# Density of the closed residue span

Source: user-provided CRT/orbit and odd-carry Markdown arguments (2026-09-20).

The residue closure contains the constant if and only if it is the whole
Pareto Hilbert space. All point vectors are differences of two scaled floor
dilations of the constant. This upgrades the existing odd carry reduction
to an exact density criterion without assuming an RH converse.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto.CoefficientStabilization

private theorem scaled_dilation_one_sequence (m : ℕ) (hm : 0 < m) (k : ℕ) :
    hilbertSequence (((m : ℝ)⁻¹) • hilbertDilation m hm hilbertOne) k =
      if m ≤ k then 1 else 0 := by
  rw [hilbertSequence_smul, hilbertDilation_sequence, hilbertOne_sequence]
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  by_cases hmk : m ≤ k
  · have hdiv : k / m ≠ 0 := Nat.ne_of_gt (Nat.div_pos hmk hm)
    simp [dilation, zeroAnchor, hmk, hdiv, hm0]
  · have hdiv : k / m = 0 := Nat.div_eq_of_lt (by omega)
    simp [dilation, zeroAnchor, hmk, hdiv]

theorem paretoPoint_eq_scaled_dilation_difference (n : ℕ) :
    paretoPointHilbert n =
      (((n + 1 : ℕ) : ℝ)⁻¹) • hilbertDilation (n + 1) (by omega) hilbertOne -
      (((n + 2 : ℕ) : ℝ)⁻¹) • hilbertDilation (n + 2) (by omega) hilbertOne := by
  apply hilbertSequence_injective
  funext k
  change hilbertSequence (paretoPointHilbert n) k = hilbertSequenceLinear (_ - _) k
  rw [map_sub]
  change hilbertSequence (paretoPointHilbert n) k =
    hilbertSequence ((((n + 1 : ℕ) : ℝ)⁻¹) • hilbertDilation (n + 1) (by omega) hilbertOne) k -
    hilbertSequence ((((n + 2 : ℕ) : ℝ)⁻¹) • hilbertDilation (n + 2) (by omega) hilbertOne) k
  rw [hilbertSequence_paretoPoint, scaled_dilation_one_sequence, scaled_dilation_one_sequence]
  by_cases hkn : k = n + 1
  · subst k
    simp [paretoPointSequence]
  · by_cases hlt : k < n + 1
    · have h1 : ¬ n + 1 ≤ k := by omega
      have h2 : ¬ n + 2 ≤ k := by omega
      simp [paretoPointSequence, hkn, h1, h2]
    · have h1 : n + 1 ≤ k := by omega
      have h2 : n + 2 ≤ k := by omega
      simp [paretoPointSequence, hkn, h1, h2]

theorem closedSpace_eq_top_iff_one_mem :
    closedSpace = ⊤ ↔ hilbertOne ∈ closedSpace := by
  constructor
  · intro h
    rw [h]
    trivial
  · intro h
    have hp (n : ℕ) : paretoPointHilbert n ∈ closedSpace := by
      rw [paretoPoint_eq_scaled_dilation_difference]
      exact closedSpace.sub_mem
        (closedSpace.smul_mem _ (closedSpace_dilation h (n + 1) (by omega)))
        (closedSpace.smul_mem _ (closedSpace_dilation h (n + 2) (by omega)))
    have hspan : Submodule.span ℝ (Set.range paretoPointHilbert) ≤ closedSpace := by
      apply Submodule.span_le.mpr
      rintro x ⟨n, rfl⟩
      exact hp n
    have hc : IsClosed (closedSpace : Set ThresholdHilbert) :=
      Submodule.isClosed_topologicalClosure _
    have ht := (Submodule.span ℝ (Set.range paretoPointHilbert)).topologicalClosure_minimal hspan hc
    rw [paretoPoint_span_dense] at ht
    exact top_unique ht

theorem odd_carry_iff_closedSpace_eq_top :
    (∀ d : ℕ, ∀ hd : 3 ≤ d, Odd d → doublingCarryHilbert d (by omega) ∈ closedSpace) ↔
      closedSpace = ⊤ := by
  constructor
  · intro h
    exact closedSpace_eq_top_iff_one_mem.mpr
      (hilbertOne_mem_of_argumentDoubling (argumentDoublingInvariant_iff_odd_carry.mpr h))
  · intro h d hd ho
    rw [h]
    trivial

end RiemannResearch.RH.Pareto.CoefficientStabilization
