import RiemannResearch.Analysis.ShiftedLiftGram
import RiemannResearch.RH.QReciprocalCostEquivalence
import RiemannResearch.RH.QResidueTriangular
import Mathlib.Tactic.Abel

/-!
# Complete regularized finite-residue minimization

The target in the smoothed term is D x. The inverse Gram formula uses complete Hilbert inner products. Its exact quadratic and completion identities preserve all signs. No arithmetic bound on the minimum is assumed or proved by matrix inversion alone.

Research agenda: D_Residue_Density_PQ_Nyman_Beurling_2026-11-11.pdf, Section 9.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QReciprocalFiniteCost
open ZetaTwoHilbert QReciprocalMetric QReciprocalCostEquivalence
open RiemannResearch.Analysis
open FiniteHilbertGram
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def gram (a : ι → QHilbert) (α : ℝ) : Matrix ι ι ℝ :=
  gramMatrix (fun i => D (a i)) + α • gramMatrix a

def load (a : ι → QHilbert) (x : QHilbert) : ι → ℝ :=
  cross (fun i => D (a i)) (D x)

def coefficients (a : ι → QHilbert) (x : QHilbert) (α : ℝ) : ι → ℝ :=
  (gram a α)⁻¹.mulVec (load a x)

def minimizer (a : ι → QHilbert) (x : QHilbert) (α : ℝ) : QHilbert :=
  Fintype.linearCombination ℝ a (coefficients a x α)

private def shift : QHilbert →ₗ[ℝ] QHilbert := LinearMap.id - D.toLinearMap

private theorem difference_shift (v : QHilbert) : ShiftedLift.difference shift v = D v := by
  simp [ShiftedLift.difference, shift]

omit [Fintype ι] [DecidableEq ι] in
private theorem gram_bridge (a : ι → QHilbert) (α : ℝ) (hα : 0 ≤ α) :
    ShiftedLift.regularizedGram shift a (Real.sqrt α) = gram a α := by
  simp only [ShiftedLift.regularizedGram, difference_shift, Real.sq_sqrt hα, gram]

private theorem coefficients_bridge (a : ι → QHilbert) (x : QHilbert)
    (α : ℝ) (hα : 0 ≤ α) :
    ShiftedLift.regularizedCoefficients shift a (D x) (Real.sqrt α) =
      coefficients a x α := by
  simp only [ShiftedLift.regularizedCoefficients, gram_bridge a α hα,
    difference_shift, coefficients, load]

private theorem cost_bridge (x v : QHilbert) (α : ℝ) (hα : 0 ≤ α) :
    ShiftedLift.regularizedEnergy shift (D x) (Real.sqrt α) v = cost α x v := by
  simp only [ShiftedLift.regularizedEnergy, difference_shift, Real.sq_sqrt hα, cost, map_sub]

omit [Fintype ι] [DecidableEq ι] in
theorem gram_posDef [Finite ι] (a : ι → QHilbert) (ha : LinearIndependent ℝ a)
    (α : ℝ) (hα : 0 < α) : (gram a α).PosDef := by
  classical
  let := Fintype.ofFinite ι
  rw [← gram_bridge a α hα.le]
  exact ShiftedLift.regularizedGram_posDef shift ha _ (Real.sqrt_pos.mpr hα)

theorem minimizer_mem (a : ι → QHilbert) (x : QHilbert) (α : ℝ) :
    minimizer a x α ∈ synthesisSpan a := synthesis_mem a _

theorem minimizer_normal (a : ι → QHilbert) (ha : LinearIndependent ℝ a)
    (x : QHilbert) (α : ℝ) (hα : 0 < α) :
    ∀ w ∈ synthesisSpan a,
      inner ℝ (D (minimizer a x α - x)) (D w) +
        α * inner ℝ (minimizer a x α) w = 0 := by
  simpa only [difference_shift, coefficients_bridge a x α hα.le,
    Real.sq_sqrt hα.le, map_sub, minimizer] using
    ShiftedLift.regularizedCoefficients_normal shift ha (D x) (Real.sqrt α)
      (Real.sqrt_pos.mpr hα)

theorem cost_completion (a : ι → QHilbert) (ha : LinearIndependent ℝ a)
    (x v : QHilbert) (hv : v ∈ synthesisSpan a) (α : ℝ) (hα : 0 < α) :
    cost α x v = cost α x (minimizer a x α) +
      ‖D (v-minimizer a x α)‖ ^ 2 + α*‖v-minimizer a x α‖ ^ 2 := by
  have hn := minimizer_normal a ha x α hα
  have hn' : ∀ w ∈ synthesisSpan a,
      inner ℝ (ShiftedLift.difference shift (minimizer a x α) - D x)
        (ShiftedLift.difference shift w) +
        (Real.sqrt α)^2 * inner ℝ (minimizer a x α) w = 0 := by
    simpa only [difference_shift, Real.sq_sqrt hα.le, map_sub] using hn
  have h := ShiftedLift.regularizedEnergy_completion shift (D x) (Real.sqrt α)
    (synthesisSpan a) (minimizer a x α) v (minimizer_mem a x α) hv hn'
  simpa only [cost_bridge _ _ α hα.le, difference_shift, Real.sq_sqrt hα.le,
    add_assoc] using h

theorem minimum_value (a : ι → QHilbert) (ha : LinearIndependent ℝ a)
    (x : QHilbert) (α : ℝ) (hα : 0 < α) :
    cost α x (minimizer a x α) =
      ‖D x‖ ^ 2 - dotProduct (load a x) (coefficients a x α) := by
  have hn := minimizer_normal a ha x α hα
  have hn' : ∀ w ∈ synthesisSpan a,
      inner ℝ (ShiftedLift.difference shift (minimizer a x α)-D x)
        (ShiftedLift.difference shift w) +
        (Real.sqrt α)^2*inner ℝ (minimizer a x α) w = 0 := by
    simpa only [difference_shift, Real.sq_sqrt hα.le, map_sub] using hn
  have h := ShiftedLift.regularizedEnergy_eq_norm_sq_sub_pairing shift (D x)
    (Real.sqrt α) (synthesisSpan a) (minimizer a x α) (minimizer_mem a x α) hn'
  rw [cost_bridge _ _ α hα.le, difference_shift] at h
  rw [h]
  congr 1
  change inner ℝ (D (Fintype.linearCombination ℝ a (coefficients a x α))) (D x) = _
  simp only [Fintype.linearCombination_apply, map_sum, map_smul,
    sum_inner, real_inner_smul_left, load, cross, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem minimizer_le (a : ι → QHilbert) (ha : LinearIndependent ℝ a)
    (x v : QHilbert) (hv : v ∈ synthesisSpan a) (α : ℝ) (hα : 0 < α) :
    cost α x (minimizer a x α) ≤ cost α x v := by
  rw [cost_completion a ha x v hv α hα]
  nlinarith [sq_nonneg ‖D (v-minimizer a x α)‖,
    mul_nonneg hα.le (sq_nonneg ‖v-minimizer a x α‖)]

theorem minimizer_unique (a : ι → QHilbert) (ha : LinearIndependent ℝ a)
    (x v : QHilbert) (hv : v ∈ synthesisSpan a) (α : ℝ) (hα : 0 < α)
    (he : cost α x v = cost α x (minimizer a x α)) :
    v = minimizer a x α := by
  have h := cost_completion a ha x v hv α hα
  rw [he] at h
  have hm : α*‖v-minimizer a x α‖^2 = 0 := by
    nlinarith [sq_nonneg ‖D (v-minimizer a x α)‖,
      mul_nonneg hα.le (sq_nonneg ‖v-minimizer a x α‖)]
  have hs : ‖v-minimizer a x α‖^2 = 0 :=
    (mul_eq_zero.mp hm).resolve_left (ne_of_gt hα)
  have hz : ‖v-minimizer a x α‖ = 0 := by nlinarith only [hs]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)


theorem minimizer_mem_submodule (a : ι → QHilbert) (x : QHilbert) (α : ℝ)
    (S : Submodule ℝ QHilbert) (ha : ∀ i, a i ∈ S) :
    minimizer a x α ∈ S := by
  unfold minimizer
  rw [Fintype.linearCombination_apply]
  exact S.sum_mem (fun i _ => S.smul_mem _ (ha i))

theorem residue_minimizer_legal (d : ι → ℕ) (hd : ∀ i, 1 < d i)
    (x : QHilbert) (α : ℝ) :
    minimizer (fun i => qResidue (d i)) x α ∈ QFullResidueProjection.legalSpan := by
  apply minimizer_mem_submodule
  intro i
  apply Submodule.subset_span
  refine ⟨d i-2, ?_⟩
  have hi := hd i
  have he : d i-2+2 = d i := by omega
  change qResidue (d i-2+2) = qResidue (d i)
  rw [he]

omit [Fintype ι] [DecidableEq ι] in
theorem residue_gram_posDef [Finite ι] (d : ι → ℕ) (hd : ∀ i, 1 < d i)
    (hinj : Function.Injective d) (α : ℝ) (hα : 0 < α) :
    (gram (fun i => qResidue (d i)) α).PosDef :=
  gram_posDef _ (QResidueTriangular.qResidue_linearIndependent_injective d hd hinj) α hα

omit [DecidableEq ι] in
theorem cost_quadratic (a : ι → QHilbert) (x : QHilbert)
    (α : ℝ) (hα : 0 ≤ α) (c : ι → ℝ) :
    cost α x (Fintype.linearCombination ℝ a c) =
      ‖D x‖^2 - 2*dotProduct c (load a x) + dotProduct c ((gram a α).mulVec c) := by
  have hg := ShiftedLift.regularizedGram_quadratic shift a (Real.sqrt α) c
  simp only [gram_bridge a α hα, difference_shift, Real.sq_sqrt hα] at hg
  have hi : inner ℝ (D (Fintype.linearCombination ℝ a c)) (D x) =
      dotProduct c (load a x) := by
    simp only [Fintype.linearCombination_apply, map_sum, map_smul, sum_inner,
      real_inner_smul_left, load, cross, dotProduct]
  rw [cost, map_sub, norm_sub_sq_real, hi]
  nlinarith only [hg]

end RiemannResearch.RH.QReciprocalFiniteCost
