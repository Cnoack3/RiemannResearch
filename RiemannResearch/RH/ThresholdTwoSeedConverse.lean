import RiemannResearch.RH.ThresholdHilbertCocycle
import RiemannResearch.RH.GibbsLegalSeed

/-!
# The algebraic and operator part of the two-seed converse

Source: Christian Noack, RH_Two_Seed_Threshold.tex, September 8, 2026,
Section 4, proof of the main threshold theorem (statement and proof strategy).

This file proves the precise conditional converse from two analytic inputs:
full positive-residue density, and constancy of the common adjoint fixed
vectors for 2 and 3. Neither analytic input is proved or asserted here.
-/

namespace RiemannResearch.RH.Pareto
noncomputable section

/-- Full residue density and common-fixed-vector rigidity imply full
two-seed density. The finite mean-one legal vector eliminates constants. -/
theorem twoSeed_legalClosure_eq_top_of_full_density_of_joint_fixed_constants
    (hfull : hilbertLegalClosure {n : ℕ | 0 < n} = ⊤)
    (hrigid : ∀ h : ThresholdHilbert,
      hilbertDilationAdjoint 2 (by norm_num) h = h →
      hilbertDilationAdjoint 3 (by norm_num) h = h →
      ∃ c : ℝ, h = c • hilbertOne) :
    hilbertLegalClosure {2, 3} = ⊤ := by
  let V := hilbertLegalClosure {2, 3}
  have hV : IsClosed (V : Set ThresholdHilbert) :=
    (hilbertLegalSubspace {2, 3}).isClosed_topologicalClosure
  have : CompleteSpace V := inferInstance
  apply Submodule.orthogonal_eq_bot_iff.mp
  apply le_antisymm
  · intro h hh
    change h = 0
    have h2 := adjoint_fixed_of_legal_orthogonal_of_full_density
      {2, 3} (a := 2) (by simp) (by norm_num) hfull hh
    have h3 := adjoint_fixed_of_legal_orthogonal_of_full_density
      {2, 3} (a := 3) (by simp) (by norm_num) hfull hh
    obtain ⟨c, hc⟩ := hrigid h h2 h3
    have hi : initialLegalMeanOne ∈ V :=
      (hilbertLegalSubspace {2, 3}).le_topologicalClosure initialLegalMeanOne_legal
    have ho := (V.mem_orthogonal h).mp hh initialLegalMeanOne hi
    rw [hc, real_inner_smul_right, initialLegalMeanOne_mean, mul_one] at ho
    rw [hc, ho, zero_smul]
  · exact bot_le

/-- The requested two-seed target follows once the two analytic inputs in
the preceding theorem have been established. -/
theorem hilbertOne_mem_twoSeed_of_full_density_of_joint_fixed_constants
    (hfull : hilbertLegalClosure {n : ℕ | 0 < n} = ⊤)
    (hrigid : ∀ h : ThresholdHilbert,
      hilbertDilationAdjoint 2 (by norm_num) h = h →
      hilbertDilationAdjoint 3 (by norm_num) h = h →
      ∃ c : ℝ, h = c • hilbertOne) :
    hilbertOne ∈ hilbertLegalClosure {2, 3} := by
  rw [twoSeed_legalClosure_eq_top_of_full_density_of_joint_fixed_constants hfull hrigid]
  trivial

end
end RiemannResearch.RH.Pareto
