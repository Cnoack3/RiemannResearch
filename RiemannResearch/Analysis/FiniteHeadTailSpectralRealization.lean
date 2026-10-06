/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FiniteHilbertGramProjection
import RiemannResearch.Analysis.FiniteSpectralBudget
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Positive finite head-tail spectral realization

The finite spectrum is constructed from A.adjoint.comp A; neither spectral
existence nor eigenvalue positivity is a new hypothesis. The remaining
structural inputs are an isometric head embedding J, its actual full-tail
map A, orthogonality of their ranges, and a target supported in the head.

In the actual Pareto application, E is compactHead N (finiteSpace (N-1)),
J is its inclusion, and A is the tail of the inverse head restriction.
Head restriction is injective by the existing compact coefficient duals.
The literal application and actual projection identities are constructed in
RH/ParetoActualHeadSpectrum.lean. The complete arithmetic source-moment
provider remains open.

Source: user-provided full-conductor continuation and its requested
improvement; see RH/GreenParetoGitHubAdvance20261006.md.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.FiniteHeadTailSpectralRealization

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Actual positive relative tail operator on the finite head space. -/
def relativeTail (A : E →L[ℝ] H) : E →ₗ[ℝ] E :=
  (A.adjoint.comp A).toLinearMap

theorem relativeTail_isSymmetric (A : E →L[ℝ] H) :
    (relativeTail A).IsSymmetric := by
  intro x y
  change inner ℝ (A.adjoint (A x)) y = inner ℝ x (A.adjoint (A y))
  rw [A.adjoint_inner_left, A.adjoint_inner_right]

/-- Mathlib supplies the complete actual finite eigenbasis. -/
def eigenBasis (A : E →L[ℝ] H) :
    OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E :=
  (relativeTail_isSymmetric A).eigenvectorBasis rfl

def eigenvalue (A : E →L[ℝ] H) : Fin (Module.finrank ℝ E) → ℝ :=
  (relativeTail_isSymmetric A).eigenvalues rfl

theorem eigenBasis_apply (A : E →L[ℝ] H) (i : Fin (Module.finrank ℝ E)) :
    relativeTail A (eigenBasis A i) = eigenvalue A i • eigenBasis A i :=
  (relativeTail_isSymmetric A).apply_eigenvectorBasis rfl i

/-- All complete physical-tail Gram entries are diagonalized, not truncated. -/
theorem tail_basis_inner (A : E →L[ℝ] H)
    (i j : Fin (Module.finrank ℝ E)) :
    inner ℝ (A (eigenBasis A i)) (A (eigenBasis A j)) =
      if i = j then eigenvalue A i else 0 := by
  calc
    _ = inner ℝ (eigenBasis A i) (relativeTail A (eigenBasis A j)) :=
      (A.adjoint_inner_right (eigenBasis A i) (A (eigenBasis A j))).symm
    _ = eigenvalue A j * inner ℝ (eigenBasis A i) (eigenBasis A j) := by
      rw [eigenBasis_apply, real_inner_smul_right]
    _ = _ := by
      rw [orthonormal_iff_ite.mp (eigenBasis A).orthonormal]
      by_cases hij : i = j <;> simp [hij]

/-- Spectral positivity is proved from the actual tail norms. -/
theorem eigenvalue_nonneg (A : E →L[ℝ] H) (i : Fin (Module.finrank ℝ E)) :
    0 ≤ eigenvalue A i := by
  have h := tail_basis_inner A i i
  rw [if_pos rfl, real_inner_self_eq_norm_sq] at h
  exact h ▸ sq_nonneg ‖A (eigenBasis A i)‖

theorem head_basis_orthonormal (J : E →ₗᵢ[ℝ] H) (A : E →L[ℝ] H) :
    Orthonormal ℝ (fun i => J (eigenBasis A i)) := by
  apply orthonormal_iff_ite.mpr
  intro i j
  rw [J.inner_map_map]
  exact orthonormal_iff_ite.mp (eigenBasis A).orthonormal i j

section FiniteFrame

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def synthesize (f : ι → H) (c : ι → ℝ) : H := ∑ i, c i • f i

/-- Complete finite Gram energy of a genuinely diagonal family. -/
theorem diagonal_norm_sq (f : ι → H) (d c : ι → ℝ)
    (hdiag : ∀ i j, inner ℝ (f i) (f j) = if i = j then d i else 0) :
    ‖synthesize f c‖ ^ 2 = ∑ i, (c i)^2 * d i := by
  rw [← real_inner_self_eq_norm_sq]
  unfold synthesize
  simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro i hi
  simp [hdiag, pow_two, mul_assoc]

def frame (h t : ι → H) (i : ι) : H := h i + t i

theorem frame_inner (h t : ι → H) (lam : ι → ℝ)
    (hh : Orthonormal ℝ h)
    (ht : ∀ i j, inner ℝ (t i) (t j) = if i = j then lam i else 0)
    (hht : ∀ i j, inner ℝ (h i) (t j) = 0) (i j : ι) :
    inner ℝ (frame h t i) (frame h t j) =
      if i = j then 1 + lam i else 0 := by
  have hth : inner ℝ (t i) (h j) = 0 := by
    rw [real_inner_comm]
    exact hht j i
  simp only [frame, inner_add_left, inner_add_right,
    orthonormal_iff_ite.mp hh, ht, hht, hth, add_zero, zero_add]
  by_cases hij : i = j <;> simp [hij]

def source (h : ι → H) (v : H) (i : ι) : ℝ := inner ℝ (h i) v
def sourceWeight (h : ι → H) (v : H) (i : ι) : ℝ := (source h v i)^2
def headFit (h : ι → H) (v : H) : H := synthesize h (source h v)
def fullFit (h t : ι → H) (lam : ι → ℝ) (v : H) : H :=
  synthesize (frame h t) (fun i => source h v i / (1 + lam i))
def fittedHead (h : ι → H) (lam : ι → ℝ) (v : H) : H :=
  synthesize h (fun i => source h v i / (1 + lam i))
def fittedTail (h t : ι → H) (lam : ι → ℝ) (v : H) : H :=
  synthesize t (fun i => source h v i / (1 + lam i))

theorem fullFit_eq_head_add_tail (h t : ι → H) (lam : ι → ℝ) (v : H) :
    fullFit h t lam v = fittedHead h lam v + fittedTail h t lam v := by
  simp only [fullFit, fittedHead, fittedTail, synthesize, frame, smul_add]
  rw [Finset.sum_add_distrib]

/-- Complete actual tail energy equals the optimizerTail finite scalar API. -/
theorem fittedTail_norm_sq (h t : ι → H) (lam : ι → ℝ) (v : H)
    (ht : ∀ i j, inner ℝ (t i) (t j) = if i = j then lam i else 0) :
    ‖fittedTail h t lam v‖^2 =
      FiniteSpectralBudget.optimizerTail Finset.univ (sourceWeight h v) lam := by
  rw [fittedTail, diagonal_norm_sq t lam _ ht]
  unfold FiniteSpectralBudget.optimizerTail sourceWeight
  simp only [Finset.mem_univ, true_implies, Finset.sum_const_zero, div_pow]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Source mass is exactly the squared norm of the head projection. -/
theorem headFit_norm_sq (h : ι → H) (v : H) (hh : Orthonormal ℝ h) :
    ‖headFit h v‖^2 = FiniteSpectralBudget.mass Finset.univ (sourceWeight h v) := by
  rw [headFit, diagonal_norm_sq h (fun _ => 1) _
    (orthonormal_iff_ite.mp hh)]
  simp [FiniteSpectralBudget.mass, sourceWeight]

/-- The head displacement is the second complete nonnegative square. -/
theorem headDisplacement_norm_sq (h : ι → H) (lam : ι → ℝ) (v : H)
    (hh : Orthonormal ℝ h) (hlam : ∀ i, 0 ≤ lam i) :
    ‖fittedHead h lam v - headFit h v‖^2 =
      FiniteSpectralBudget.headDisplacement Finset.univ (sourceWeight h v) lam := by
  have heq : fittedHead h lam v - headFit h v =
      synthesize h (fun i => source h v i / (1 + lam i) - source h v i) := by
    simp only [fittedHead, headFit, synthesize, sub_smul]
    rw [Finset.sum_sub_distrib]
  rw [heq, diagonal_norm_sq h (fun _ => 1) _ (orthonormal_iff_ite.mp hh)]
  unfold FiniteSpectralBudget.headDisplacement sourceWeight
  simp only [Finset.mem_univ, true_implies, mul_one]
  apply Finset.sum_congr rfl
  intro i hi
  have hd : 1 + lam i ≠ 0 := ne_of_gt (by linarith [hlam i])
  field_simp [hd]
  ring

/-- Both complete correction squares realize the correction finite scalar API. -/
theorem correction_realization (h t : ι → H) (lam : ι → ℝ) (v : H)
    (hh : Orthonormal ℝ h)
    (ht : ∀ i j, inner ℝ (t i) (t j) = if i = j then lam i else 0)
    (hlam : ∀ i, 0 ≤ lam i) :
    ‖fittedHead h lam v - headFit h v‖^2 + ‖fittedTail h t lam v‖^2 =
      FiniteSpectralBudget.correction Finset.univ (sourceWeight h v) lam := by
  rw [headDisplacement_norm_sq h lam v hh hlam, fittedTail_norm_sq h t lam v ht]
  symm
  exact FiniteSpectralBudget.correction_eq_headDisplacement_add_optimizerTail
    Finset.univ (sourceWeight h v) lam (fun i _ => hlam i)

/-- Actual full normal equation at every diagonalized conductor combination. -/
theorem fullFit_normal (h t : ι → H) (lam : ι → ℝ) (v : H)
    (hh : Orthonormal ℝ h)
    (ht : ∀ i j, inner ℝ (t i) (t j) = if i = j then lam i else 0)
    (hht : ∀ i j, inner ℝ (h i) (t j) = 0)
    (hvt : ∀ i, inner ℝ v (t i) = 0)
    (hlam : ∀ i, 0 ≤ lam i) (j : ι) :
    inner ℝ (v - fullFit h t lam v) (frame h t j) = 0 := by
  have hv : inner ℝ v (frame h t j) = source h v j := by
    simp only [frame, inner_add_right, hvt j, add_zero, source]
    exact (real_inner_comm v (h j)).symm
  have hp : inner ℝ (fullFit h t lam v) (frame h t j) = source h v j := by
    unfold fullFit synthesize
    rw [sum_inner]
    simp only [real_inner_smul_left, frame_inner h t lam hh ht hht]
    have hd : 1 + lam j ≠ 0 := ne_of_gt (by linarith [hlam j])
    simp [mul_ite, hd]
  rw [inner_sub_left, hv, hp, sub_self]

/-- The displayed fit is the actual orthogonal projection onto its entire
finite legal span. No convergence or moment provider occurs in this theorem. -/
theorem fullFit_eq_projection (h t : ι → H) (lam : ι → ℝ) (v : H)
    (hh : Orthonormal ℝ h)
    (ht : ∀ i j, inner ℝ (t i) (t j) = if i = j then lam i else 0)
    (hht : ∀ i j, inner ℝ (h i) (t j) = 0)
    (hvt : ∀ i, inner ℝ v (t i) = 0)
    (hlam : ∀ i, 0 ≤ lam i) :
    fullFit h t lam v =
      (FiniteHilbertGram.synthesisSpan (frame h t)).starProjection v := by
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (FiniteHilbertGram.synthesis_mem (frame h t) _)
  intro z hz
  rw [FiniteHilbertGram.synthesisSpan, ← Fintype.range_linearCombination] at hz
  obtain ⟨c, rfl⟩ := hz
  change inner ℝ (v - fullFit h t lam v) (∑ i, c i • frame h t i) = 0
  rw [inner_sum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [real_inner_smul_right, fullFit_normal h t lam v hh ht hht hvt hlam i]
  simp

end FiniteFrame

/-- A complete finite spectrum is realized by the actual head inclusion and
complete tail map. Eigenvalue positivity and diagonalization are discharged,
rather than imposed as additional arithmetic hypotheses. -/
theorem spectralFrame_correction_realization
    (J : E →ₗᵢ[ℝ] H) (A : E →L[ℝ] H) (v : H) :
    ‖fittedHead (fun i => J (eigenBasis A i)) (eigenvalue A) v -
      headFit (fun i => J (eigenBasis A i)) v‖^2 +
      ‖fittedTail (fun i => J (eigenBasis A i))
        (fun i => A (eigenBasis A i)) (eigenvalue A) v‖^2 =
      FiniteSpectralBudget.correction Finset.univ
        (sourceWeight (fun i => J (eigenBasis A i)) v) (eigenvalue A) := by
  exact correction_realization _ _ _ v (head_basis_orthonormal J A)
    (tail_basis_inner A) (eigenvalue_nonneg A)

/-- With the actual orthogonal head/tail ranges and a compact target, the
spectral fit is the actual full-stage orthogonal projection. -/
theorem spectralFrame_fullFit_eq_projection
    (J : E →ₗᵢ[ℝ] H) (A : E →L[ℝ] H) (v : H)
    (hJA : ∀ x y : E, inner ℝ (J x) (A y) = 0)
    (hvA : ∀ x : E, inner ℝ v (A x) = 0) :
    fullFit (fun i => J (eigenBasis A i)) (fun i => A (eigenBasis A i))
      (eigenvalue A) v =
      (FiniteHilbertGram.synthesisSpan (fun i =>
        frame (fun i => J (eigenBasis A i)) (fun i => A (eigenBasis A i)) i)).starProjection v := by
  exact fullFit_eq_projection _ _ _ v (head_basis_orthonormal J A)
    (tail_basis_inner A) (fun i j => hJA _ _) (fun i => hvA _)
    (eigenvalue_nonneg A)

end RiemannResearch.Analysis.FiniteHeadTailSpectralRealization
