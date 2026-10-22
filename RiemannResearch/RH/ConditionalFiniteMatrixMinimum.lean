import RiemannResearch.RH.ConditionalResidueHeadMatrix
import RiemannResearch.LinearAlgebra.FiniteConstrainedMatrixMinimum
import RiemannResearch.LinearAlgebra.FiniteConstrainedMatrixInverse

/-!
# The exact finite arithmetic constrained minimum

Source: `ArithmeticVariationalProof.md`, Section 6, and the user-provided
conditional-iid completion, equations (11.3)--(11.4). Positivity and full
row rank are discharged by the actual residue theorems. The inverse maps
are constructed, not assumed. `fullValue` is exactly
`1ᵀ (A G⁻¹ Aᵀ)⁻¹ 1`; `tailValue` uses `T` in place of `G`.
-/

noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
namespace RiemannResearch.RH.Pareto.ConditionalFiniteMinimum
open Probability.ConditionalIID
open RiemannResearch.LinearAlgebra.FiniteConstrainedMatrix

def G (D : ℕ) := conditionalResidueGramMatrix (Finset.Icc 2 D)
def T (N D : ℕ) := conditionalResidueTailMatrix N (Finset.Icc 2 D)
def A (N D : ℕ) := conditionalResidueHeadMatrix N (Finset.Icc 2 D)
def synthesis (D : ℕ) (c : Finset.Icc 2 D → ℝ) : ℕ → ℝ :=
  fun n => ∑ i : Finset.Icc 2 D, c i * residue i.1 n

theorem G_posDef (D : ℕ) : (G D).PosDef :=
  conditionalResidueGramMatrix_posDef _ (fun _ h => (Finset.mem_Icc.mp h).1)

theorem T_posDef (N D : ℕ) : (T N D).PosDef :=
  conditionalResidueTailMatrix_posDef _ _ (fun _ h => (Finset.mem_Icc.mp h).1)

theorem A_surjective (N D : ℕ) (hND : N + 1 ≤ D) : Function.Surjective (A N D).mulVec :=
  conditionalResidueHeadMatrix_surjective N D hND

def fullValue (N D : ℕ) (hND : N + 1 ≤ D) : ℝ :=
  dotProduct (fun _ : Fin N => (1 : ℝ))
    (multiplier (G D) (G_posDef D) (A N D) (A_surjective N D hND) (fun _ => 1))

def tailValue (N D : ℕ) (hND : N + 1 ≤ D) : ℝ :=
  dotProduct (fun _ : Fin N => (1 : ℝ))
    (multiplier (T N D) (T_posDef N D) (A N D) (A_surjective N D hND) (fun _ => 1))

theorem fullValue_eq_inverseMatrix (N D : ℕ) (hND : N + 1 ≤ D) :
    fullValue N D hND = dotProduct (fun _ : Fin N => (1 : ℝ))
      ((A N D * (G D)⁻¹ * (A N D).transpose)⁻¹.mulVec (fun _ => 1)) := by
  unfold fullValue
  rw [multiplier_eq_inverse_matrix]

theorem tailValue_eq_inverseMatrix (N D : ℕ) (hND : N + 1 ≤ D) :
    tailValue N D hND = dotProduct (fun _ : Fin N => (1 : ℝ))
      ((A N D * (T N D)⁻¹ * (A N D).transpose)⁻¹.mulVec (fun _ => 1)) := by
  unfold tailValue
  rw [multiplier_eq_inverse_matrix]

theorem G_quadratic (D : ℕ) (c : Finset.Icc 2 D → ℝ) :
    dotProduct c ((G D).mulVec c) = conditionalMeanSquare (synthesis D c) :=
  conditionalResidueGramMatrix_quadratic _ (fun _ h => (Finset.mem_Icc.mp h).1) c

theorem T_quadratic (N D : ℕ) (c : Finset.Icc 2 D → ℝ) :
    dotProduct c ((T N D).mulVec c) = conditionalMeanTailSquare N (synthesis D c) :=
  conditionalResidueTailMatrix_quadratic _ _ (fun _ h => (Finset.mem_Icc.mp h).1) c

theorem synthesis_mem_finite (D : ℕ) (c : Finset.Icc 2 D → ℝ) :
    synthesis D c ∈ finiteResidueSubspace D := by
  rw [finiteResidueSubspace_eq_span_range]
  have h : (∑ i : Finset.Icc 2 D, c i • residue i.1) ∈
      Submodule.span ℝ (Set.range (fun i : Finset.Icc 2 D => residue i.1)) := by
    apply Submodule.sum_mem
    intro i _
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨i, rfl⟩
  have he : synthesis D c = ∑ i : Finset.Icc 2 D, c i • residue i.1 := by
    funext n
    simp only [synthesis, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [he]
  exact h

theorem synthesis_headClass (N D : ℕ) (c : Finset.Icc 2 D → ℝ)
    (hc : (A N D).mulVec c = fun _ => 1) : synthesis D c ∈ conditionalHeadClass N := by
  refine ⟨finiteResidueSubspace_le_full_legal D (synthesis_mem_finite D c), ?_⟩
  have hmean (t : ℕ) (ht : 0 < t) (htN : t ≤ N) : cesaro (synthesis D c) t = 1 := by
    let i : Fin N := ⟨t - 1, by omega⟩
    have h := congrFun hc i
    have he : t - 1 + 1 = t := by omega
    change cesaro (fun n => ∑ i : Finset.Icc 2 D, c i * residue i.1 n) t = 1
    rw [cesaro_finsetCombination]
    simpa only [A, conditionalResidueHeadMatrix, Matrix.mulVec, dotProduct,
      i, he, mul_comm] using h
  intro n hn hnN
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hn)
  rw [cesaro_recover (synthesis D c) k, hmean (k + 1) (Nat.succ_pos _) hnN]
  by_cases hk : k = 0
  · simp [hk]
  · rw [hmean k (Nat.pos_of_ne_zero hk) (by omega)]
    push_cast
    ring

/-- The inverse formula is attained among the actual finite arithmetic witnesses. -/
theorem fullValue_isLeast (N D : ℕ) (hND : N + 1 ≤ D) :
    IsLeast {E : ℝ | ∃ c : Finset.Icc 2 D → ℝ,
      (A N D).mulVec c = (fun _ => 1) ∧ conditionalMeanSquare (synthesis D c) = E}
      (fullValue N D hND) := by
  have h := inverseCompressed_isLeast (G D) (G_posDef D) (A N D)
    (A_surjective N D hND) (fun _ => 1)
  simp_rw [G_quadratic] at h
  exact h

theorem tailValue_isLeast (N D : ℕ) (hND : N + 1 ≤ D) :
    IsLeast {E : ℝ | ∃ c : Finset.Icc 2 D → ℝ,
      (A N D).mulVec c = (fun _ => 1) ∧ conditionalMeanTailSquare N (synthesis D c) = E}
      (tailValue N D hND) := by
  have h := inverseCompressed_isLeast (T N D) (T_posDef N D) (A N D)
    (A_surjective N D hND) (fun _ => 1)
  simp_rw [T_quadratic] at h
  exact h

/-- Equation (11.4): exact compulsory head plus the actual inverse-tail minimum. -/
theorem fullValue_eq_head_add_tailValue (N D : ℕ) (hND : N + 1 ≤ D) :
    fullValue N D hND = (N : ℝ) / ((N : ℝ) + 2) + tailValue N D hND := by
  obtain ⟨cG, hcG, hEG⟩ := (fullValue_isLeast N D hND).1
  obtain ⟨cT, hcT, hET⟩ := (tailValue_isLeast N D hND).1
  have hGle := (fullValue_isLeast N D hND).2 ⟨cT, hcT, rfl⟩
  have hTle := (tailValue_isLeast N D hND).2 ⟨cG, hcG, rfl⟩
  have hsplitG := conditionalMeanSquare_exact_head_split N (synthesis_headClass N D cG hcG)
  have hsplitT := conditionalMeanSquare_exact_head_split N (synthesis_headClass N D cT hcT)
  change conditionalMeanSquare (synthesis D cG) =
    (N : ℝ) / ((N : ℝ) + 2) + conditionalMeanTailSquare N (synthesis D cG) at hsplitG
  change conditionalMeanSquare (synthesis D cT) =
    (N : ℝ) / ((N : ℝ) + 2) + conditionalMeanTailSquare N (synthesis D cT) at hsplitT
  linarith

theorem fullValue_gt_head_mass (N D : ℕ) (hN : 0 < N) (hND : N + 1 ≤ D) :
    (N : ℝ) / ((N : ℝ) + 2) < fullValue N D hND := by
  obtain ⟨c, hc, hE⟩ := (fullValue_isLeast N D hND).1
  rw [← hE]
  exact conditionalMeanSquare_gt_head_mass N hN (synthesis_headClass N D c hc)

theorem conditionalHeadMinimum_le_fullValue (N D : ℕ) (hND : N + 1 ≤ D) :
    conditionalHeadMinimum N ≤ fullValue N D hND := by
  obtain ⟨c, hc, hE⟩ := (fullValue_isLeast N D hND).1
  rw [← hE]
  exact conditionalHeadMinimum_le N (synthesis_headClass N D c hc)

end RiemannResearch.RH.Pareto.ConditionalFiniteMinimum
