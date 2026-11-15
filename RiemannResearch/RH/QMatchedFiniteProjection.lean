/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QCovarianceInvertibility
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.MobiusCoefficientStabilization
import RiemannResearch.Analysis.FiniteHilbertGramMatrix
import RiemannResearch.Analysis.FiniteHilbertGramProjection
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Actual matched finite Q/P projections and their complete normal equations

Source: the reciprocal-head investigation, 7 November 2026, Sections 4--5.
At size N the actual dictionary is qResidue(2),...,qResidue(N+1).
All solution arrays are constructed from independent actual Hilbert vectors;
no normal-equation solution premise is left to the numerical caller.
-/

noncomputable section
open scoped BigOperators Matrix
namespace RiemannResearch.RH.QMatchedFiniteProjection
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer Pareto
open RiemannResearch.Analysis.FiniteHilbertGram

def qDictionary (N : ℕ) (i : Fin N) : QHilbert := qResidue (i.val + 2)

def pDictionary (N : ℕ) (i : Fin N) : ThresholdHilbert := toPareto (qDictionary N i)

theorem qDictionary_independent (N : ℕ) : LinearIndependent ℝ (qDictionary N) := by
  apply QCovarianceInvertibility.qResidue_linearIndependent (fun i : Fin N => i.val + 2)
  · intro i; omega
  · intro i j h
    change i.val + 2 = j.val + 2 at h
    apply Fin.ext
    omega

theorem pDictionary_independent (N : ℕ) : LinearIndependent ℝ (pDictionary N) := by
  have h := Pareto.CoefficientStabilization.residueAtom_linearIndependent.comp
    (fun i : Fin N => i.val) Fin.val_injective
  change LinearIndependent ℝ (fun i : Fin N => toPareto (qResidue (i.val + 2)))
  simpa only [toPareto_residueAtom, Function.comp_def] using h

abbrev qSpace (N : ℕ) : Submodule ℝ QHilbert := synthesisSpan (qDictionary N)

abbrev pSpace (N : ℕ) : Submodule ℝ ThresholdHilbert := synthesisSpan (pDictionary N)

def qCoefficients (N : ℕ) : Fin N → ℝ := inverseCoeff (qDictionary_independent N) qOne

def pCoefficients (N : ℕ) : Fin N → ℝ :=
  inverseCoeff (pDictionary_independent N) (toPareto qOne)

def qFit (N : ℕ) : QHilbert := Fintype.linearCombination ℝ (qDictionary N) (qCoefficients N)

def pFitPhysical (N : ℕ) : QHilbert :=
  Fintype.linearCombination ℝ (qDictionary N) (pCoefficients N)

theorem toPareto_synthesis (N : ℕ) (a : Fin N → ℝ) :
    toPareto (Fintype.linearCombination ℝ (qDictionary N) a) =
      Fintype.linearCombination ℝ (pDictionary N) a := by
  change toParetoLinear (Fintype.linearCombination ℝ (qDictionary N) a) = _
  simp only [Fintype.linearCombination_apply, map_sum, map_smul]
  rfl

theorem qFit_eq_projection (N : ℕ) : qFit N = (qSpace N).starProjection qOne :=
  synthesis_inverseCoeff_eq_projection (qDictionary_independent N) qOne

theorem pFit_eq_projection (N : ℕ) :
    toPareto (pFitPhysical N) = (pSpace N).starProjection (toPareto qOne) := by
  rw [pFitPhysical, toPareto_synthesis]
  exact synthesis_inverseCoeff_eq_projection (pDictionary_independent N) (toPareto qOne)

def rawGram (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => zetaTwo * inner ℝ (qDictionary N i) (qDictionary N j)

def rawMean (N : ℕ) (i : Fin N) : ℝ := zetaTwo * inner ℝ qOne (qDictionary N i)

def paretoGram (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => inner ℝ (pDictionary N i) (pDictionary N j)

def paretoMean (N : ℕ) (i : Fin N) : ℝ :=
  inner ℝ (toPareto qOne) (pDictionary N i)

theorem rawGram_posDef (N : ℕ) : (rawGram N).PosDef := by
  change (zetaTwo • gramMatrix (qDictionary N)).PosDef
  exact (gramMatrix_posDef (qDictionary_independent N)).smul zetaTwo_pos

def rawInverse (N : ℕ) : Matrix (Fin N) (Fin N) ℝ := (rawGram N)⁻¹

theorem rawInverse_normal (N : ℕ) (i j : Fin N) :
    (∑ k, rawGram N i k * rawInverse N k j) = if i = j then 1 else 0 := by
  have h := Matrix.mul_nonsing_inv (rawGram N)
    (isUnit_iff_ne_zero.mpr (ne_of_gt (rawGram_posDef N).det_pos))
  have hij := congrFun (congrFun h i) j
  simpa only [Matrix.mul_apply, Matrix.one_apply, rawInverse] using hij

theorem rawInverse_posDef (N : ℕ) : (rawInverse N).PosDef := (rawGram_posDef N).inv

theorem rawInverse_symmetric (N : ℕ) (i j : Fin N) :
    rawInverse N i j = rawInverse N j i := by
  have h := (rawInverse_posDef N).isHermitian
  change (rawInverse N)ᴴ = rawInverse N at h
  have hij := congrFun (congrFun h i) j
  simpa only [Matrix.conjTranspose_apply, star_trivial] using hij.symm

/-- Every actual Q orthogonal projection satisfies its complete raw normal system. -/
theorem raw_projection_normal (N : ℕ) (x : QHilbert) (i : Fin N) :
    (∑ j, rawGram N i j * inverseCoeff (qDictionary_independent N) x j) =
      zetaTwo * inner ℝ (qDictionary N i) x := by
  have hn := inverseCoeff_normal (qDictionary_independent N) x i
  change gram (qDictionary N) (inverseCoeff (qDictionary_independent N) x) i = _ at hn
  rw [gram_apply] at hn
  calc
    _ = zetaTwo * (∑ j, inner ℝ (qDictionary N i) (qDictionary N j) *
        inverseCoeff (qDictionary_independent N) x j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      unfold rawGram
      ring
    _ = _ := by rw [hn]; rfl

theorem qCoefficients_normal (N : ℕ) (i : Fin N) :
    (∑ j, rawGram N i j * qCoefficients N j) = rawMean N i := by
  rw [qCoefficients, raw_projection_normal, rawMean, real_inner_comm]

theorem pCoefficients_normal (N : ℕ) (i : Fin N) :
    (∑ j, paretoGram N i j * pCoefficients N j) = paretoMean N i := by
  have hn := inverseCoeff_normal (pDictionary_independent N) (toPareto qOne) i
  change gram (pDictionary N) (pCoefficients N) i = _ at hn
  rw [gram_apply] at hn
  change (∑ j, inner ℝ (pDictionary N i) (pDictionary N j) * pCoefficients N j) =
    inner ℝ (toPareto qOne) (pDictionary N i)
  rw [hn]
  exact real_inner_comm _ _

def displacementCoefficients (N : ℕ) (i : Fin N) : ℝ := qCoefficients N i - pCoefficients N i

def displacement (N : ℕ) : QHilbert := qFit N - pFitPhysical N

def reciprocalTarget (N : ℕ) : QHilbert := QShiftedReciprocal.B (displacement N)

def projectionCoefficients (N : ℕ) : Fin N → ℝ :=
  inverseCoeff (qDictionary_independent N) (reciprocalTarget N)

theorem displacement_synthesis (N : ℕ) :
    displacement N = Fintype.linearCombination ℝ (qDictionary N) (displacementCoefficients N) := by
  change Fintype.linearCombination ℝ (qDictionary N) (qCoefficients N) -
    Fintype.linearCombination ℝ (qDictionary N) (pCoefficients N) =
      Fintype.linearCombination ℝ (qDictionary N) (qCoefficients N - pCoefficients N)
  rw [map_sub]

theorem toPareto_displacement_synthesis (N : ℕ) :
    toPareto (displacement N) =
      Fintype.linearCombination ℝ (pDictionary N) (displacementCoefficients N) := by
  rw [displacement_synthesis, toPareto_synthesis]

theorem reciprocal_projection_synthesis (N : ℕ) :
    Fintype.linearCombination ℝ (qDictionary N) (projectionCoefficients N) =
      (qSpace N).starProjection (reciprocalTarget N) :=
  synthesis_inverseCoeff_eq_projection (qDictionary_independent N) (reciprocalTarget N)

/-- Exact normal system for projecting the actual reciprocal displacement.
The RHS is the complete signed (raw-Q Gram minus P Gram) action. -/
theorem projectionCoefficients_normal (N : ℕ) (i : Fin N) :
    (∑ j, rawGram N i j * projectionCoefficients N j) =
      ∑ j, (rawGram N i j - paretoGram N i j) * displacementCoefficients N j := by
  rw [projectionCoefficients, raw_projection_normal]
  have hm := QShiftedReciprocal.pareto_inner_identity (qDictionary N i) (displacement N)
  have hQ : zetaTwo * inner ℝ (qDictionary N i) (displacement N) =
      ∑ j, rawGram N i j * displacementCoefficients N j := by
    rw [displacement_synthesis]
    change zetaTwo * gram (qDictionary N) (displacementCoefficients N) i = _
    rw [gram_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    unfold rawGram
    ring
  have hP : inner ℝ (pDictionary N i) (toPareto (displacement N)) =
      ∑ j, paretoGram N i j * displacementCoefficients N j := by
    rw [toPareto_displacement_synthesis]
    change gram (pDictionary N) (displacementCoefficients N) i = _
    exact gram_apply _ _ _
  change inner ℝ (pDictionary N i) (toPareto (displacement N)) =
    zetaTwo * (inner ℝ (qDictionary N i) (displacement N) -
      inner ℝ (qDictionary N i) (reciprocalTarget N)) at hm
  calc
    _ = zetaTwo * inner ℝ (qDictionary N i) (displacement N) -
        inner ℝ (pDictionary N i) (toPareto (displacement N)) := by linarith
    _ = (∑ j, rawGram N i j * displacementCoefficients N j) -
        (∑ j, paretoGram N i j * displacementCoefficients N j) := by rw [hQ, hP]
    _ = _ := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      ring

private theorem scaled_dictionary_quadratic {ι : Type*} [Fintype ι]
    (v : ι → QHilbert) (c : ι → ℝ) :
    (∑ i, ∑ j, c i * (zetaTwo * inner ℝ (v i) (v j)) * c j) / zetaTwo =
      ‖Fintype.linearCombination ℝ v c‖ ^ 2 := by
  apply (div_eq_iff (ne_of_gt zetaTwo_pos)).mpr
  rw [gram_quadratic, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [gram_apply, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem rawGram_quadratic (N : ℕ) (c : Fin N → ℝ) :
    (∑ i, ∑ j, c i * rawGram N i j * c j) / zetaTwo =
      ‖Fintype.linearCombination ℝ (qDictionary N) c‖ ^ 2 :=
  scaled_dictionary_quadratic (qDictionary N) c

theorem paretoGram_quadratic (N : ℕ) (c : Fin N → ℝ) :
    (∑ i, ∑ j, c i * paretoGram N i j * c j) =
      ‖toPareto (Fintype.linearCombination ℝ (qDictionary N) c)‖ ^ 2 := by
  rw [toPareto_synthesis, gram_quadratic]
  apply Finset.sum_congr rfl
  intro i hi
  rw [gram_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  unfold paretoGram
  ring

def rawReciprocalGram (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => zetaTwo * inner ℝ (QShiftedReciprocal.B (qDictionary N i))
    (QShiftedReciprocal.B (qDictionary N j))

theorem reciprocalTarget_synthesis (N : ℕ) :
    reciprocalTarget N = Fintype.linearCombination ℝ
      (fun j => QShiftedReciprocal.B (qDictionary N j)) (displacementCoefficients N) := by
  rw [reciprocalTarget, displacement_synthesis]
  simp only [Fintype.linearCombination_apply, map_sum, map_smul]

theorem displacement_raw_norm (N : ℕ) :
    (∑ i, ∑ j, displacementCoefficients N i * rawGram N i j *
      displacementCoefficients N j) / zetaTwo = ‖displacement N‖ ^ 2 := by
  rw [rawGram_quadratic, displacement_synthesis]

theorem displacement_pareto_norm (N : ℕ) :
    (∑ i, ∑ j, displacementCoefficients N i * paretoGram N i j *
      displacementCoefficients N j) = ‖toPareto (displacement N)‖ ^ 2 := by
  rw [paretoGram_quadratic, displacement_synthesis]

theorem reciprocalTarget_raw_norm (N : ℕ) :
    (∑ i, ∑ j, displacementCoefficients N i * rawReciprocalGram N i j *
      displacementCoefficients N j) / zetaTwo = ‖reciprocalTarget N‖ ^ 2 := by
  rw [reciprocalTarget_synthesis]
  exact scaled_dictionary_quadratic (fun j => QShiftedReciprocal.B (qDictionary N j))
    (displacementCoefficients N)

def reciprocalCross (N : ℕ) (i : Fin N) : ℝ :=
  ∑ j, (rawGram N i j - paretoGram N i j) * displacementCoefficients N j

/-- The signed complete cross/projection pairing is its actual Q projection energy. -/
theorem projected_target_energy (N : ℕ) :
    (∑ i, reciprocalCross N i * projectionCoefficients N i) / zetaTwo =
      ‖(qSpace N).starProjection (reciprocalTarget N)‖ ^ 2 := by
  rw [← reciprocal_projection_synthesis, ← rawGram_quadratic]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  change (∑ j, (rawGram N i j - paretoGram N i j) * displacementCoefficients N j) *
      projectionCoefficients N i = _
  rw [← projectionCoefficients_normal N i, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem qSequence_synthesis (N : ℕ) (c : Fin N → ℝ) (k : ℕ) :
    qSequence (Fintype.linearCombination ℝ (qDictionary N) c) k =
      ∑ j, c j * ArithmeticCumulative.residueFraction (j.val + 2) k := by
  change qSequenceLinear (Fintype.linearCombination ℝ (qDictionary N) c) k = _
  simp only [Fintype.linearCombination_apply, map_sum, map_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  change (∑ j, c j * qSequence (qDictionary N j) k) = _
  simp only [qDictionary, qSequence_qResidue]

def residual (N : ℕ) : QHilbert := qOne - qFit N

theorem residual_physical (N k : ℕ) (hk : 0 < k) :
    qSequence (residual N) k =
      1 - ∑ j, qCoefficients N j * ArithmeticCumulative.residueFraction (j.val + 2) k := by
  change qSequenceLinear (qOne - qFit N) k = _
  rw [map_sub]
  change qSequence qOne k - qSequence (qFit N) k = _
  rw [qFit, qSequence_synthesis, qSequence_qOne]
  simp only [qOneSequence, if_neg (Nat.ne_of_gt hk)]

theorem reciprocalTarget_physical (N k : ℕ) :
    qSequence (reciprocalTarget N) k =
      (∑ j, displacementCoefficients N j * ArithmeticCumulative.residueFraction (j.val + 2) k) /
        ((k : ℝ) + 1) := by
  rw [reciprocalTarget, QShiftedReciprocal.qSequence_B,
    displacement_synthesis, qSequence_synthesis]

end RiemannResearch.RH.QMatchedFiniteProjection
