/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.FiniteTwoSeedHeadMean
import RiemannResearch.RH.ParetoLegalApproximationClosure

/-!
# Continuous finite-head repair by actual two-seed vectors

Source: independently developed from the user-provided exact-head energy
problem, 14 September 2026. The established triangular interpolation supplies
a finite family of actual legal vectors. Their continuous coefficient maps
give a bounded right inverse for each fixed head. Its norm may depend on the
head length; no uniform or subpolynomial estimate for that norm is asserted.

The main consequence is density in each exact finite-head fiber: passing from
finite legal vectors to their Hilbert closure leaves the constrained infimum
unchanged. Exact interpolation is retained during the approximation.
-/

open scoped BigOperators

namespace RiemannResearch.RH.Pareto.FiniteTwoSeedCompletion

noncomputable section

private theorem seeds_positive : ∀ a ∈ ({2, 3} : Set ℕ), 0 < a := by
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl <;> omega

theorem exists_hilbert_head_basis (N i : ℕ) :
    ∃ f : ThresholdHilbert, hilbertSequence f ∈ budgetSpan N ∧
      ∀ k, 0 < k → k ≤ N →
        hilbertSequence f k = if k = i + 1 then 1 else 0 := by
  obtain ⟨g, hg, hhead⟩ := exists_head
    (fun k => if k = i + 1 then (1 : ℝ) else 0) N
  obtain ⟨f, hf, hseq⟩ := legalSeedSpan_exists_hilbert
    ({2, 3} : Set ℕ) seeds_positive (budgetSpan_le_legal N hg)
  exact ⟨f, hseq.symm ▸ hg, by simpa only [hseq] using hhead⟩

/-- A genuine finite legal interpolant for a single physical head coordinate. -/
def hilbertHeadBasis (N i : ℕ) : ThresholdHilbert :=
  Classical.choose (exists_hilbert_head_basis N i)

theorem hilbertHeadBasis_mem (N i : ℕ) :
    hilbertSequence (hilbertHeadBasis N i) ∈ budgetSpan N :=
  (Classical.choose_spec (exists_hilbert_head_basis N i)).1

theorem hilbertHeadBasis_coordinate (N i k : ℕ) (hk : 0 < k) (hkN : k ≤ N) :
    hilbertSequence (hilbertHeadBasis N i) k = if k = i + 1 then 1 else 0 :=
  (Classical.choose_spec (exists_hilbert_head_basis N i)).2 k hk hkN

/-- The bounded evaluation at positive physical coordinate `i+1`. -/
def physicalEvaluation (i : ℕ) : ThresholdHilbert →L[ℝ] ℝ :=
  (1 / Real.sqrt (paretoWeight i)) • lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 i

@[simp] theorem physicalEvaluation_apply (i : ℕ) (f : ThresholdHilbert) :
    physicalEvaluation i f = hilbertSequence f (i + 1) := by
  change (1 / Real.sqrt (paretoWeight i)) * f i =
    f i / Real.sqrt (paretoWeight i)
  ring

/-- Continuous finite-budget right inverse for restriction to the first `N` coordinates. -/
def hilbertHeadRepair (N : ℕ) : ThresholdHilbert →L[ℝ] ThresholdHilbert :=
  ∑ i ∈ Finset.range N, (physicalEvaluation i).smulRight (hilbertHeadBasis N i)

theorem hilbertHeadRepair_apply (N : ℕ) (f : ThresholdHilbert) :
    hilbertHeadRepair N f =
      ∑ i ∈ Finset.range N, hilbertSequence f (i + 1) • hilbertHeadBasis N i := by
  simp [hilbertHeadRepair]

theorem hilbertHeadRepair_mem (N : ℕ) (f : ThresholdHilbert) :
    hilbertSequence (hilbertHeadRepair N f) ∈ budgetSpan N := by
  rw [hilbertHeadRepair_apply]
  change hilbertSequenceLinear (∑ i ∈ Finset.range N,
    hilbertSequence f (i + 1) • hilbertHeadBasis N i) ∈ budgetSpan N
  rw [map_sum]
  apply (budgetSpan N).sum_mem
  intro i hi
  rw [map_smul]
  exact (budgetSpan N).smul_mem _ (hilbertHeadBasis_mem N i)

theorem hilbertHeadRepair_coordinate (N : ℕ) (f : ThresholdHilbert)
    (k : ℕ) (hk : k < N) :
    hilbertSequence (hilbertHeadRepair N f) (k + 1) = hilbertSequence f (k + 1) := by
  rw [hilbertHeadRepair_apply]
  change hilbertSequenceLinear (∑ i ∈ Finset.range N,
    hilbertSequence f (i + 1) • hilbertHeadBasis N i) (k + 1) = _
  rw [map_sum]
  simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
  change (∑ i ∈ Finset.range N, hilbertSequence f (i + 1) *
    hilbertSequence (hilbertHeadBasis N i) (k + 1)) = _
  simp_rw [hilbertHeadBasis_coordinate N _ (k + 1) (by omega) (by omega)]
  simp [mul_ite, hk]

/-- Every closure vector can be approximated while its finite head is fixed exactly. -/
theorem exists_legal_near_with_same_head
    {f : ThresholdHilbert} (hf : f ∈ hilbertLegalClosure ({2, 3} : Set ℕ))
    (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ThresholdHilbert, g ∈ hilbertLegalSubspace ({2, 3} : Set ℕ) ∧
      (∀ k, 0 < k → k ≤ N → hilbertSequence g k = hilbertSequence f k) ∧
      ‖f - g‖ < ε := by
  let L := hilbertHeadRepair N
  have hL : 0 < 1 + ‖L‖ := by positivity
  have hδ : 0 < ε / (1 + ‖L‖) := div_pos hε hL
  have hf' : f ∈ closure (hilbertLegalSubspace ({2, 3} : Set ℕ) : Set ThresholdHilbert) := hf
  obtain ⟨g, hg, hdist⟩ := Metric.mem_closure_iff.mp hf' _ hδ
  let q := g + L (f - g)
  have hq : q ∈ hilbertLegalSubspace ({2, 3} : Set ℕ) := by
    apply (hilbertLegalSubspace ({2, 3} : Set ℕ)).add_mem hg
    exact budgetSpan_le_legal N (hilbertHeadRepair_mem N (f - g))
  refine ⟨q, hq, ?_, ?_⟩
  · intro k hk hkN
    cases k with
    | zero => omega
    | succ k =>
        have hh := hilbertHeadRepair_coordinate N (f - g) k (by omega)
        change hilbertSequence (g + hilbertHeadRepair N (f - g)) (k + 1) = _
        rw [hilbertSequence_add, Pi.add_apply, hh]
        change hilbertSequenceLinear g (k + 1) +
          hilbertSequenceLinear (f - g) (k + 1) = _
        rw [map_sub]
        simp [hilbertSequenceLinear]
  · have he : f - q = (f - g) - L (f - g) := by dsimp [q]; abel
    rw [he]
    have hb := L.le_opNorm (f - g)
    have hd : ‖f - g‖ < ε / (1 + ‖L‖) := by simpa only [dist_eq_norm] using hdist
    have hsmall : (1 + ‖L‖) * ‖f - g‖ < ε := by
      have := (lt_div_iff₀ hL).mp hd
      nlinarith
    calc
      _ ≤ ‖f - g‖ + ‖L (f - g)‖ := norm_sub_le _ _
      _ ≤ ‖f - g‖ + ‖L‖ * ‖f - g‖ := add_le_add le_rfl hb
      _ < ε := by nlinarith

end

end RiemannResearch.RH.Pareto.FiniteTwoSeedCompletion
