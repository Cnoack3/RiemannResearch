import RiemannResearch.RH.ConditionalFiniteMatrixMinimum
/-!
# Finite-conductor exhaustion of the conditional-mean minimum

Source: user-provided
`Conditional_IID_Cesaro_Mathematical_Completion_2026-09-17.md`,
equation (11.5), and its finite-support proof expanded in the conversation.
The actual finite matrix minima decrease to the unrestricted legal infimum.
The existing normalized inverse formula identifies these same minima with
the manuscript's normalized coordinates. No RH hypothesis, uniform energy
bound, or quantitative convergence rate is used.
-/

open scoped BigOperators Topology
open Filter
noncomputable section
namespace RiemannResearch.RH.Pareto
open Probability.ConditionalIID
/-- Every legal finite combination fits in a finite arithmetic dictionary. -/
theorem legal_mem_finiteResidueSubspace {f : ℕ → ℝ}
    (hf : f ∈ legalSeedSpan (Set.Ici 1)) :
    ∃ D, f ∈ finiteResidueSubspace D := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, ha, m, hm, rfl⟩ := hf
    have ha0 : 0 < a := ha
    have he : dilation m (residue a) = residue (m * a) - residue m := by
      funext n
      exact residue_mul_floor m a n
    refine ⟨max (m * a) m, ?_⟩
    rw [he]
    exact (finiteResidueSubspace _).sub_mem
      (residue_mem_finiteResidueSubspace (Nat.mul_pos hm ha0) (le_max_left _ _))
      (residue_mem_finiteResidueSubspace hm (le_max_right _ _))
  | zero => exact ⟨0, (finiteResidueSubspace 0).zero_mem⟩
  | add f g hf hg ihf ihg =>
    obtain ⟨D, hD⟩ := ihf
    obtain ⟨E, hE⟩ := ihg
    exact ⟨max D E, (finiteResidueSubspace _).add_mem
      (finiteResidueSubspace_mono (le_max_left _ _) hD)
      (finiteResidueSubspace_mono (le_max_right _ _) hE)⟩
  | smul c f hf ih =>
    obtain ⟨D, hD⟩ := ih
    exact ⟨D, (finiteResidueSubspace D).smul_mem c hD⟩

namespace ConditionalFiniteMinimum
/-- Recover actual coefficient arrays from finite-dictionary membership. -/
theorem exists_synthesis_of_mem_finite {D : ℕ} {f : ℕ → ℝ}
    (hf : f ∈ finiteResidueSubspace D) :
    ∃ c, synthesis D c = f := by
  classical
  rw [finiteResidueSubspace_eq_span_range] at hf
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hf
  refine ⟨c, ?_⟩
  funext n
  simpa only [synthesis, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using congrFun hc n

/-- Exact ordinary heads impose the concrete conditional-mean matrix constraint. -/
theorem headMatrix_eq_one_of_synthesis_head (N D : ℕ)
    (c : Finset.Icc 2 D → ℝ) (hc : synthesis D c ∈ conditionalHeadClass N) :
    (A N D).mulVec c = fun _ => 1 := by
  funext i
  have h := cesaro_eq_one_of_exact_head N hc.2 (i.1 + 1)
    (Nat.succ_pos _) (Nat.succ_le_of_lt i.2)
  change cesaro (fun n => ∑ d : Finset.Icc 2 D, c d * residue d.1 n) (i.1 + 1) = 1 at h
  rw [cesaro_finsetCombination] at h
  simpa only [A, conditionalResidueHeadMatrix, Matrix.mulVec, dotProduct, mul_comm] using h

/-- The attained matrix minimum bounds every feasible finite-dictionary witness. -/
theorem fullValue_le_of_mem_finite (N D : ℕ) (hND : N + 1 ≤ D)
    {f : ℕ → ℝ} (hf : f ∈ conditionalHeadClass N)
    (hD : f ∈ finiteResidueSubspace D) :
    fullValue N D hND ≤ conditionalMeanSquare f := by
  obtain ⟨c, rfl⟩ := exists_synthesis_of_mem_finite hD
  exact (fullValue_isLeast N D hND).2
    ⟨c, headMatrix_eq_one_of_synthesis_head N D c hf, rfl⟩

/-- Enlarging the conductor budget cannot increase the attained minimum. -/
theorem fullValue_antitone (N D E : ℕ) (hND : N + 1 ≤ D) (hDE : D ≤ E) :
    fullValue N E (hND.trans hDE) ≤ fullValue N D hND := by
  obtain ⟨c, hc, hE⟩ := (fullValue_isLeast N D hND).1
  rw [← hE]
  exact fullValue_le_of_mem_finite N E (hND.trans hDE)
    (synthesis_headClass N D c hc)
    (finiteResidueSubspace_mono hDE (synthesis_mem_finite D c))


/-- Every finite-conductor minimum lies above the unrestricted infimum,
and finite support supplies the converse greatest-lower-bound property. -/
theorem conditionalHeadMinimum_isGLB_fullValue (N : ℕ) :
    IsGLB (Set.range (fun D : {D : ℕ // N + 1 ≤ D} =>
      fullValue N D.1 D.2)) (conditionalHeadMinimum N) := by
  constructor
  · rintro _ ⟨D, rfl⟩
    exact conditionalHeadMinimum_le_fullValue N D.1 D.2
  · intro b hb
    apply le_csInf (conditionalHeadEnergies_nonempty N)
    rintro E ⟨f, hf, rfl⟩
    obtain ⟨D, hD⟩ := legal_mem_finiteResidueSubspace hf.1
    let d : {D : ℕ // N + 1 ≤ D} := ⟨max (N + 1) D, le_max_left _ _⟩
    have hb' : b ≤ fullValue N d.1 d.2 := hb (Set.mem_range_self d)
    exact hb'.trans (fullValue_le_of_mem_finite N d.1 d.2 hf
      (finiteResidueSubspace_mono (le_max_right _ _) hD))

/-- Equation (11.5), infimum over all admissible conductor budgets. -/
theorem conditionalHeadMinimum_eq_iInf_fullValue (N : ℕ) :
    conditionalHeadMinimum N =
      ⨅ D : {D : ℕ // N + 1 ≤ D}, fullValue N D.1 D.2 :=
  ((conditionalHeadMinimum_isGLB_fullValue N).csInf_eq
    ⟨_, ⟨⟨N + 1, le_rfl⟩, rfl⟩⟩).symm

/-- Equation (11.5), convergence through all budgets N+1, N+2, ...
No uniform-in-N estimate or convergence rate is assumed. -/
theorem tendsto_fullValue_conditionalHeadMinimum (N : ℕ) :
    Tendsto (fun k : ℕ => fullValue N (N + 1 + k) (by omega))
      atTop (𝓝 (conditionalHeadMinimum N)) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [] with k
    exact ha.trans_le (conditionalHeadMinimum_le_fullValue N (N + 1 + k) (by omega))
  · intro b hb
    obtain ⟨f, hf, hE⟩ := exists_head_energy_lt N
      (b - conditionalHeadMinimum N) (sub_pos.mpr hb)
    obtain ⟨D, hD⟩ := legal_mem_finiteResidueSubspace hf.1
    filter_upwards [eventually_ge_atTop D] with k hk
    have hle := fullValue_le_of_mem_finite N (N + 1 + k) (by omega) hf
      (finiteResidueSubspace_mono (show D ≤ N + 1 + k by omega) hD)
    linarith

end ConditionalFiniteMinimum
end RiemannResearch.RH.Pareto
