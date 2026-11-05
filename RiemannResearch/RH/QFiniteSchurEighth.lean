/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.FiniteGramCoercivity
import RiemannResearch.RH.QFiniteSchurForcingData
import RiemannResearch.RH.QFiniteEighthCentered
import RiemannResearch.RH.QSquarefreeSchurRepresentation
import Mathlib.Data.Matrix.Mul

/-! # The inverse Schur response in the aligned eighth-moment criterion

Source: the finite eighth-moment handoff and the complete screened representation
in QSquarefreeSchurRepresentation. The signed pairing uses the full Gram inverse.
The quadratic energy bound and the uniform input estimate lead to a sufficient
RH criterion involving only the actual signed response and the analytic premise.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QSquarefreeFiniteDisplacement
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoOptimizerStage QShiftedReciprocal
open QFiniteSupportDualCriterion QSquarefreeSchurCoercivity QSquarefreeSchurRepresentation
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.FiniteGramCoercivity RiemannResearch.Analysis.FiniteGramCapacity
open ArithmeticCumulative

/-- The matrix on the signed floor rows is the full screened stage Gram. -/
theorem projectedFiniteForcing_eq_schur (N H d0 : ℕ) (hH : 1 ≤ H)
    (ha : H < d0) (hN : d0 ≤ N + 1) (hs : Squarefree d0) :
    projectedFiniteForcing N H =
      Fintype.linearCombination ℝ (squarefreeSchurFamily N H d0)
        ((gramMatrix (squarefreeSchurFamily N H d0))⁻¹.mulVec
          (forcingSchurRHS H d0 (qOne - finitePFit N))) := by
  rw [projectedFiniteForcing, B_finiteHead_eq]
  exact stageProjection_finiteHead_eq_schur_inverseGram N H d0 hH ha hN hs _

/-- The signed inverse-Gram quadratic form equals the actual post-inverse energy. -/
theorem projectedFiniteForcing_inverse_quadratic (N H d0 : ℕ) (hH : 1 ≤ H)
    (ha : H < d0) (hN : d0 ≤ N + 1) (hs : Squarefree d0) :
    dotProduct (forcingSchurRHS H d0 (qOne - finitePFit N))
      ((gramMatrix (squarefreeSchurFamily N H d0))⁻¹.mulVec
        (forcingSchurRHS H d0 (qOne - finitePFit N))) =
      ‖projectedFiniteForcing N H‖^2 := by
  classical
  let v := squarefreeSchurFamily N H d0
  let b := forcingSchurRHS H d0 (qOne - finitePFit N)
  have hv : LinearIndependent ℝ v := squarefreeSchurFamily_linearIndependent N H d0 hH ha
  have he : projectedFiniteForcing N H =
      Fintype.linearCombination ℝ v ((gramMatrix v)⁻¹.mulVec b) :=
    projectedFiniteForcing_eq_schur N H d0 hH ha hN hs
  change dotProduct b ((gramMatrix v)⁻¹.mulVec b) = _
  simp only [he, gramMatrix_inverseSource hv, inverseSource_synthesis_energy hv]
  change (∑ i, b i * inverseSource hv b i) = ∑ i, inverseSource hv b i * b i
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

/-- The exact complete-Q input energy has a second Pareto weight at each site. -/
theorem finiteHead_B_pareto_energy (H : ℕ) (f : QHilbert) :
    zetaTwo * ‖finiteHead H (B f)‖^2 =
      ∑ k ∈ Finset.range (H + 1), weight k * (weight k * (qSequence f k) ^ 2) := by
  have he : inner ℝ (B f) (finiteHead H (B f)) = ‖finiteHead H (B f)‖^2 := by
    rw [← real_inner_self_eq_norm_sq, finiteHead_inner, finiteHead_idem]
  rw [← he, forcingSchurRHS_physical H f (B f)]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hz : k = 0
  · subst k
    simp [qSequence_zero]
  · have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hz
    have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
    rw [qSequence_B]
    simp only [weight]
    field_simp [hkR, hk1]

theorem projectedFiniteForcing_energy_le_head (N H : ℕ) :
    zetaTwo * ‖projectedFiniteForcing N H‖ ^ 2 ≤
      (1 / 2 : ℝ) * ∑ k ∈ Finset.range (H + 1),
        weight k * (qSequence (qOne - finitePFit N) k) ^ 2 := by
  let f := qOne - finitePFit N
  let z := finiteHead H (B f)
  have hp : ‖(stage N).starProjection z‖ ≤ ‖z‖ :=
    ((stage N).starProjection.le_opNorm z).trans (by
      simpa using mul_le_mul_of_nonneg_right (Submodule.starProjection_norm_le (stage N))
        (norm_nonneg z))
  have he : projectedFiniteForcing N H = (stage N).starProjection z := by
    rw [projectedFiniteForcing, B_finiteHead_eq]
  have hweight (k : ℕ) : weight k ≤ (1 / 2 : ℝ) := by
    by_cases hz : k = 0
    · simp [hz, weight]
    · have hkR : 1 ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
      apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
      nlinarith [sq_nonneg ((k : ℝ) - 1)]
  rw [he]
  calc
    _ ≤ zetaTwo * ‖z‖^2 :=
      mul_le_mul_of_nonneg_left ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hp)
        zetaTwo_pos.le
    _ = ∑ k ∈ Finset.range (H + 1), weight k * (weight k * (qSequence f k) ^ 2) :=
      finiteHead_B_pareto_energy H f
    _ ≤ (1 / 2 : ℝ) * ∑ k ∈ Finset.range (H + 1), weight k * (qSequence f k) ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_right (hweight k)
        (mul_nonneg (Pareto.positiveWeight_nonneg k) (sq_nonneg _)))

theorem projectedFiniteForcing_energy_le_half (N H : ℕ) :
    zetaTwo * ‖projectedFiniteForcing N H‖^2 ≤ 1 / 2 := by
  have h := mul_le_mul_of_nonneg_left
    (finite_pareto_energy_le N (Finset.range (H + 1))) (by norm_num : (0 : ℝ) ≤ 1/2)
  simpa only [mul_one] using (projectedFiniteForcing_energy_le_head N H).trans h

open ZetaTwoHilbert ZetaTwoProbability ZetaTwoOptimizerStage
open QFiniteSupportDualCriterion QShiftedReciprocal QSquarefreeSchurCoercivity
open QSquarefreeSchurRepresentation RiemannResearch.Analysis.FiniteHilbertGram

/-- The evaluation at a physical site, pulled back through the complete
inverse Schur Gram. This row depends only on the stage geometry. -/
def schurEvaluationRow (N T d0 n : ℕ) : Option (lowConductors T) → ℝ :=
  Matrix.vecMul (fun i => qSequence (squarefreeSchurFamily N T d0 i) n)
    (gramMatrix (squarefreeSchurFamily N T d0))⁻¹

/-- Exact output of any retained physical source, with its signed low and anchor entries. -/
theorem schur_head_pairing (N T d0 n : ℕ) (f : QHilbert)
    (hT : 1 ≤ T) (ha : T < d0) (hd : d0 ≤ N + 1) (hs : Squarefree d0) :
    qSequence ((stage N).starProjection (finiteHead T (B f))) n =
      dotProduct (schurEvaluationRow N T d0 n) (forcingSchurRHS T d0 f) := by
  let b := forcingSchurRHS T d0 f
  let G := gramMatrix (squarefreeSchurFamily N T d0)
  let e := fun i => qSequence (squarefreeSchurFamily N T d0 i) n
  change _ = dotProduct (Matrix.vecMul e G⁻¹) b
  rw [← Matrix.dotProduct_mulVec, physical_finiteHead_response_eq N T d0 hT ha hd hs]
  change (∑ i, (G⁻¹).mulVec b i * e i) = ∑ i, e i * (G⁻¹).mulVec b i
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- Both the ordinary and the centered matched forcing can use the same inverse rows. -/
theorem schur_head_row_bound (N T d0 n : ℕ) (f : QHilbert)
    (hT : 1 ≤ T) (ha : T < d0) (hd : d0 ≤ N + 1) (hs : Squarefree d0)
    (henergy : (∑ k ∈ Finset.range (T + 1),
      ArithmeticCumulative.weight k * (qSequence f k) ^ 2) ≤ 1) :
    (zetaTwo * qSequence ((stage N).starProjection (finiteHead T (B f))) n) ^ 2 ≤
      4 * ∑ i, (schurEvaluationRow N T d0 n i) ^ 2 := by
  let b := forcingSchurRHS T d0 f
  let e := schurEvaluationRow N T d0 n
  have he : zetaTwo * qSequence ((stage N).starProjection (finiteHead T (B f))) n =
      ∑ i, (zetaTwo * b i) * e i := by
    rw [schur_head_pairing N T d0 n f hT ha hd hs, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by dsimp only [b,e]; ring
  have hb : (∑ i, (zetaTwo * b i) ^ 2) ≤ 4 :=
    (forcingSchurRHS_energy_le T d0 ha f).trans (by linarith only [henergy])
  rw [he]
  exact (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => zetaTwo * b i) e).trans
    (mul_le_mul_of_nonneg_right hb (Finset.sum_nonneg (fun i _ => sq_nonneg (e i))))

theorem projectedFiniteForcing_schur_row_bound (N T d0 n : ℕ)
    (hT : 1 ≤ T) (ha : T < d0) (hd : d0 ≤ N + 1) (hs : Squarefree d0) :
    (zetaTwo * qSequence (projectedFiniteForcing N T) n) ^ 2 ≤
      4 * ∑ i, (schurEvaluationRow N T d0 n i) ^ 2 := by
  rw [projectedFiniteForcing, B_finiteHead_eq]
  exact schur_head_row_bound N T d0 n _ hT ha hd hs (finite_pareto_energy_le N _)

theorem shiftedHeadForcing_schur_row_bound (N T d0 n : ℕ)
    (hT : 1 ≤ T) (ha : T < d0) (hd : d0 ≤ N + 1) (hs : Squarefree d0) :
    (zetaTwo * qSequence (shiftedHeadForcing N T (tailCenter T)) n) ^ 2 ≤
      4 * ∑ i, (schurEvaluationRow N T d0 n i) ^ 2 := by
  rw [shiftedHeadForcing, affineForcing_finiteHead_eq_taper]
  exact schur_head_row_bound N T d0 n _ hT ha hd hs
    ((taperedHead_pareto_energy_le T _ _).trans (finite_pareto_energy_le N _))

/-- The aligned eighth-power statistic of the inverse evaluation rows. -/
def schurRowEighthHead (N T d0 : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), (∑ i, (schurEvaluationRow N T d0 n i) ^ 2) ^ 4 / (n : ℝ) ^ 2

theorem projectedFiniteForcing_eighth_le_schur_rows (N T d0 : ℕ)
    (hT : 1 ≤ T) (ha : T < d0) (hd : d0 ≤ N + 1) (hs : Squarefree d0) :
    zetaTwo ^ 8 * eighthHead (projectedFiniteForcing N T) N ≤
      4 ^ 4 * schurRowEighthHead N T d0 := by
  unfold eighthHead schurRowEighthHead
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n _
  rw [← mul_div_assoc, ← mul_div_assoc, Even.pow_abs (by decide : Even 8)]
  apply div_le_div_of_nonneg_right _ (sq_nonneg (n : ℝ))
  have h := pow_le_pow_left₀ (sq_nonneg _) (projectedFiniteForcing_schur_row_bound
    N T d0 n hT ha hd hs) 4
  simpa only [← pow_mul, mul_pow] using h

/-- The signed row statistic retains the actual low contrasts and the actual anchor. -/
def signedSchurEighthHead (N T d0 : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), |dotProduct (schurEvaluationRow N T d0 n)
    (forcingSchurRHS T d0 (qOne - finitePFit N))| ^ 8 / (n : ℝ) ^ 2

/-- The signed Schur statistic is exactly the aligned physical moment of the truncated fit. -/
theorem signedSchurEighthHead_eq (N T d0 : ℕ)
    (hT : 1 ≤ T) (ha : T < d0) (hd : d0 ≤ N + 1) (hs : Squarefree d0) :
    signedSchurEighthHead N T d0 = eighthHead (projectedFiniteForcing N T) N := by
  unfold signedSchurEighthHead eighthHead projectedFiniteForcing
  rw [B_finiteHead_eq]
  apply Finset.sum_congr rfl
  intro n _
  rw [schur_head_pairing N T d0 n _ hT ha hd hs]

/-- Exact cancellation in the inverse Schur response suffices at arbitrarily slow
diverging input cutoffs, keeping the physical output head equal to the stage. -/
theorem riemannHypothesis_of_cofinal_signed_schur (happrox : HasSubcriticalApproximation)
    (T : ℕ → ℕ) (hT : Tendsto T atTop atTop) (C : ℝ)
    (hr : ∃ᶠ N : ℕ in atTop, ∃ d0 : ℕ, 1 ≤ T N ∧ T N < d0 ∧ d0 ≤ N + 1 ∧
      Squarefree d0 ∧ signedSchurEighthHead N (T N) d0 ≤ C) : RiemannHypothesis := by
  apply riemannHypothesis_of_displacement_eighth happrox
  apply summable_eighth_of_frequent_diagonal (projectedFiniteForcing_tendsto T hT) C
  apply hr.mono
  rintro N ⟨d0, hpos, ha, hd, hs, hc⟩
  rwa [← signedSchurEighthHead_eq N (T N) d0 hpos ha hd hs]

end RiemannResearch.RH.QSquarefreeFiniteDisplacement
