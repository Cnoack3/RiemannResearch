import RiemannResearch.RH.ThresholdJointAdjointRigidity

/-!
# Two-seed annihilator defects embed into two full annihilators

Source: RH_Minimal_Seeds_Canonical_Basis_and_Arithmetic_Charge_20260914.md,
Section 2. The statement is unconditional; no RH or density hypothesis is used.
-/

namespace RiemannResearch.RH.Pareto
noncomputable section

/-- The two adjoint defects of a two-seed annihilator belong to the full
residue annihilator. -/
def twoSeedAnnihilatorDefects
    (h : (hilbertLegalClosure {2, 3})ᗮ) :
    (hilbertLegalClosure {n : ℕ | 0 < n})ᗮ ×
      (hilbertLegalClosure {n : ℕ | 0 < n})ᗮ :=
  (⟨hilbertDilationAdjoint 2 (by norm_num) h - h,
      adjoint_sub_mem_full_orthogonal {2, 3} (by simp) (by norm_num) h.property⟩,
   ⟨hilbertDilationAdjoint 3 (by norm_num) h - h,
      adjoint_sub_mem_full_orthogonal {2, 3} (by simp) (by norm_num) h.property⟩)

/-- Joint fixed vectors in the two-seed annihilator vanish. -/
theorem twoSeed_annihilator_joint_fixed_eq_zero {h : ThresholdHilbert}
    (hh : h ∈ (hilbertLegalClosure {2, 3})ᗮ)
    (h2 : hilbertDilationAdjoint 2 (by norm_num) h = h)
    (h3 : hilbertDilationAdjoint 3 (by norm_num) h = h) : h = 0 := by
  obtain ⟨c, hc⟩ := (hilbertDilationAdjoint_two_three_fixed_iff h).mp ⟨h2, h3⟩
  have hi : initialLegalMeanOne ∈ hilbertLegalClosure {2, 3} :=
    (hilbertLegalSubspace {2, 3}).le_topologicalClosure initialLegalMeanOne_legal
  have ho := ((hilbertLegalClosure {2, 3}).mem_orthogonal h).mp hh
    initialLegalMeanOne hi
  rw [hc, real_inner_smul_right, initialLegalMeanOne_mean, mul_one] at ho
  rw [hc, ho, zero_smul]

/-- The pair of adjoint defects determines every two-seed annihilator uniquely. -/
theorem twoSeedAnnihilatorDefects_injective :
    Function.Injective twoSeedAnnihilatorDefects := by
  intro h k he
  have he2 := congrArg (fun p => (p.1 : ThresholdHilbert)) he
  have he3 := congrArg (fun p => (p.2 : ThresholdHilbert)) he
  change hilbertDilationAdjoint 2 _ h - h = hilbertDilationAdjoint 2 _ k - k at he2
  change hilbertDilationAdjoint 3 _ h - h = hilbertDilationAdjoint 3 _ k - k at he3
  have hz : (h : ThresholdHilbert) - k = 0 :=
    twoSeed_annihilator_joint_fixed_eq_zero
      ((hilbertLegalClosure {2, 3})ᗮ.sub_mem h.property k.property)
      (by rw [map_sub]; exact sub_eq_sub_iff_sub_eq_sub.mp he2)
      (by rw [map_sub]; exact sub_eq_sub_iff_sub_eq_sub.mp he3)
  exact Subtype.ext (sub_eq_zero.mp hz)

end
end RiemannResearch.RH.Pareto
