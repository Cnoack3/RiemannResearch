/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QCovarianceInvertibility
import RiemannResearch.Analysis.FiniteGramScreenedCapacity
import RiemannResearch.Analysis.FiniteGramScreenedInverse
import RiemannResearch.Analysis.FiniteHilbertGramMatrix
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Exact screening for actual Q-residue covariance blocks

Source: user-provided prime-adjunction research agenda,
Q_Squarefree_Primorial_Cofinality_Verified_Results_and_Agenda_2026-10-16.md,
Sections 7--8. This module supplies its finite covariance identities and
coefficient corrections. The screened source remains signed. No lower growth
estimate, independence of residue classes, or capacity divergence is assumed.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QCovarianceScreening

open ZetaTwoHilbert QCovarianceInverse QCovarianceInvertibility
open RiemannResearch.Analysis FiniteHilbertGram FiniteHilbertConstraints FiniteGramCapacity
open RiemannResearch.LinearAlgebra.CenteredNormalEquations

variable {ι κ : Type*}

theorem covarianceMatrix_eq_gramMatrix (a : ι → ℕ) :
    residueCovarianceMatrix a = gramMatrix (centeredResidue a) := by
  ext i j
  change qCov a i j = inner ℝ (centeredResidue a i) (centeredResidue a j)
  symm
  unfold centeredResidue qCov qGram qMean
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, qOne_inner_self]
  rw [real_inner_comm (qResidue (a i)) qOne]
  ring

theorem covarianceInverseSource_eq_inverseSource [Fintype ι] [DecidableEq ι]
    (a : ι → ℕ)
    (ha : ∀ i, 1 < a i) (hia : Function.Injective a) :
    covarianceInverseSource a =
      inverseSource (centeredResidue_linearIndependent a ha hia) (qMean a) := by
  unfold covarianceInverseSource
  rw [covarianceMatrix_eq_gramMatrix, gramMatrix_inverseSource]

theorem covarianceInformation_eq_capacity [Fintype ι] [DecidableEq ι]
    (a : ι → ℕ)
    (ha : ∀ i, 1 < a i) (hia : Function.Injective a) :
    covarianceInformation a =
      capacity (centeredResidue_linearIndependent a ha hia) (qMean a) := by
  unfold covarianceInformation dot capacity
  rw [covarianceInverseSource_eq_inverseSource a ha hia]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

theorem qMean_sum (a : ι → ℕ) (b : κ → ℕ) :
    qMean (Sum.elim a b) = Sum.elim (qMean a) (qMean b) := by
  funext k
  cases k <;> rfl

theorem centeredResidue_sum (a : ι → ℕ) (b : κ → ℕ) :
    centeredResidue (Sum.elim a b) =
      Sum.elim (centeredResidue a) (centeredResidue b) := by
  funext k
  cases k <;> rfl

/-- The old/new block V consists of actual full-Q centered inner products. -/
def crossCovariance (a : ι → ℕ) (b : κ → ℕ) : Matrix ι κ ℝ :=
  fun i j => inner ℝ (centeredResidue a i) (centeredResidue b j)

/-- The actual old inverse-covariance action on a cross-covariance column. -/
def projectionCoefficients [Fintype ι] [DecidableEq ι]
    (a : ι → ℕ) (b : κ → ℕ) (j : κ) : ι → ℝ :=
  (residueCovarianceMatrix a)⁻¹.mulVec (fun i => crossCovariance a b i j)

def screenedResidue [Fintype ι]
    (a : ι → ℕ) (b : κ → ℕ)
    (ha : ∀ i, 1 < a i) (hia : Function.Injective a) : κ → QHilbert :=
  screened (centeredResidue_linearIndependent a ha hia) (centeredResidue b)

/-- R is the genuine Gram matrix of the screened centered packet. -/
def screenedCovariance [Fintype ι]
    (a : ι → ℕ) (b : κ → ℕ)
    (ha : ∀ i, 1 < a i) (hia : Function.Injective a) : Matrix κ κ ℝ :=
  gramMatrix (screenedResidue a b ha hia)

/-- Delta retains the signed subtraction beta - V^T C^{-1} b. -/
def screenedMean [Fintype ι]
    (a : ι → ℕ) (b : κ → ℕ)
    (ha : ∀ i, 1 < a i) (hia : Function.Injective a) : κ → ℝ :=
  screenedSource (centeredResidue_linearIndependent a ha hia)
    (centeredResidue b) (qMean a) (qMean b)

def screenedInverseSource [Fintype ι] [Fintype κ] [DecidableEq κ]
    (a : ι → ℕ) (b : κ → ℕ)
    (ha : ∀ i, 1 < a i) (hia : Function.Injective a) : κ → ℝ :=
  (screenedCovariance a b ha hia)⁻¹.mulVec (screenedMean a b ha hia)

theorem projectionCoefficients_eq_inverseCoeff [Fintype ι] [DecidableEq ι]
    (a : ι → ℕ) (b : κ → ℕ)
    (ha : ∀ i, 1 < a i) (hia : Function.Injective a) (j : κ) :
    projectionCoefficients a b j =
      inverseCoeff (centeredResidue_linearIndependent a ha hia) (centeredResidue b j) := by
  unfold projectionCoefficients
  rw [covarianceMatrix_eq_gramMatrix, gramMatrix_inverseSource]
  rfl

theorem screenedMean_entry [Fintype ι] [DecidableEq ι]
    (a : ι → ℕ) (b : κ → ℕ)
    (ha : ∀ i, 1 < a i) (hia : Function.Injective a) (j : κ) :
    screenedMean a b ha hia j =
      qMean b j - ∑ i, covarianceInverseSource a i * crossCovariance a b i j := by
  unfold screenedMean
  rw [screenedSource_eq, covarianceInverseSource_eq_inverseSource a ha hia]
  rfl

/-- Every mixed entry survives in the exact Schur complement. -/
theorem screenedCovariance_entry [Fintype ι] [DecidableEq ι]
    (a : ι → ℕ) (b : κ → ℕ)
    (ha : ∀ i, 1 < a i) (hia : Function.Injective a) (i j : κ) :
    screenedCovariance a b ha hia i j =
      qCov b i j - ∑ k, crossCovariance a b k i * projectionCoefficients a b j k := by
  have hbinner (s t : κ) :
      inner ℝ (centeredResidue b s) (centeredResidue b t) = qCov b s t :=
    (congrFun (congrFun (covarianceMatrix_eq_gramMatrix b) s) t).symm
  dsimp only [screenedCovariance, gramMatrix, screenedResidue, crossCovariance]
  rw [real_inner_comm, screened_gram_entry, hbinner]
  have hsym : qCov b j i = qCov b i j := by
    rw [← hbinner, ← hbinner, real_inner_comm]
  rw [hsym]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [projectionCoefficients_eq_inverseCoeff a b ha hia]
  exact mul_comm _ _

theorem screenedCovariance_eq_schur [Fintype ι] [DecidableEq ι]
    (a : ι → ℕ) (b : κ → ℕ)
    (ha : ∀ i, 1 < a i) (hia : Function.Injective a) :
    screenedCovariance a b ha hia =
      residueCovarianceMatrix b -
        (crossCovariance a b).transpose * (residueCovarianceMatrix a)⁻¹ *
          crossCovariance a b := by
  rw [Matrix.mul_assoc]
  ext i j
  rw [screenedCovariance_entry a b ha hia]
  rfl

theorem screenedMean_eq_sub [Fintype ι] [DecidableEq ι]
    (a : ι → ℕ) (b : κ → ℕ)
    (ha : ∀ i, 1 < a i) (hia : Function.Injective a) :
    screenedMean a b ha hia =
      qMean b - (crossCovariance a b).transpose.mulVec (covarianceInverseSource a) := by
  ext j
  rw [screenedMean_entry a b ha hia]
  simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

theorem combined_independent [Finite ι] [Finite κ]
    (a : ι → ℕ) (b : κ → ℕ)
    (ha : ∀ i, 1 < a i) (hb : ∀ j, 1 < b j)
    (hab : Function.Injective (Sum.elim a b)) :
    LinearIndependent ℝ (Sum.elim (centeredResidue a) (centeredResidue b)) := by
  let := Fintype.ofFinite ι
  let := Fintype.ofFinite κ
  have hd (k : ι ⊕ κ) : 1 < Sum.elim a b k := by
    cases k with
    | inl i => exact ha i
    | inr j => exact hb j
  simpa only [centeredResidue_sum] using
    centeredResidue_linearIndependent (Sum.elim a b) hd hab

theorem combined_covarianceInverseSource [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (a : ι → ℕ) (b : κ → ℕ)
    (ha : ∀ i, 1 < a i) (hb : ∀ j, 1 < b j)
    (hab : Function.Injective (Sum.elim a b)) :
    covarianceInverseSource (Sum.elim a b) =
      inverseSource (combined_independent a b ha hb hab) (Sum.elim (qMean a) (qMean b)) := by
  have hd (k : ι ⊕ κ) : 1 < Sum.elim a b k := by
    cases k with
    | inl i => exact ha i
    | inr j => exact hb j
  have hg : gramMatrix (Sum.elim (centeredResidue a) (centeredResidue b)) =
      residueCovarianceMatrix (Sum.elim a b) := by
    rw [covarianceMatrix_eq_gramMatrix, centeredResidue_sum]
  apply gram_injective (combined_independent a b ha hb hab)
  have hn : gram (Sum.elim (centeredResidue a) (centeredResidue b))
      (covarianceInverseSource (Sum.elim a b)) = qMean (Sum.elim a b) := by
    rw [← gramMatrix_mulVec, hg]
    funext k
    exact covarianceInverseSource_normal (Sum.elim a b) hd hab k
  rw [hn, qMean_sum]
  exact (funext (inverseSource_normal (combined_independent a b ha hb hab) _)).symm

theorem screened_independent [Fintype ι] [Finite κ]
    (a : ι → ℕ) (b : κ → ℕ)
    (ha : ∀ i, 1 < a i) (hia : Function.Injective a)
    (hb : ∀ j, 1 < b j) (hab : Function.Injective (Sum.elim a b)) :
    LinearIndependent ℝ (screenedResidue a b ha hia) := by
  let := Fintype.ofFinite κ
  exact screened_linearIndependent (centeredResidue_linearIndependent a ha hia)
    (centeredResidue b) (combined_independent a b ha hb hab)

theorem screenedCovariance_posDef [Fintype ι] [Finite κ]
    (a : ι → ℕ) (b : κ → ℕ)
    (ha : ∀ i, 1 < a i) (hia : Function.Injective a)
    (hb : ∀ j, 1 < b j) (hab : Function.Injective (Sum.elim a b)) :
    (screenedCovariance a b ha hia).PosDef := by
  let := Fintype.ofFinite κ
  exact gramMatrix_posDef (screened_independent a b ha hia hb hab)

theorem screenedInverseSource_eq_inverseSource [Fintype ι] [Fintype κ] [DecidableEq κ]
    (a : ι → ℕ) (b : κ → ℕ)
    (ha : ∀ i, 1 < a i) (hia : Function.Injective a)
    (hb : ∀ j, 1 < b j) (hab : Function.Injective (Sum.elim a b)) :
    screenedInverseSource a b ha hia =
      inverseSource (screened_independent a b ha hia hb hab) (screenedMean a b ha hia) :=
  gramMatrix_inverseSource (screened_independent a b ha hia hb hab) _

/-- The exact actual-Q packet gain delta^T R^{-1} delta. -/
theorem covarianceInformation_gain [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (a : ι → ℕ) (b : κ → ℕ)
    (ha : ∀ i, 1 < a i) (hia : Function.Injective a)
    (hb : ∀ j, 1 < b j) (hab : Function.Injective (Sum.elim a b)) :
    covarianceInformation (Sum.elim a b) - covarianceInformation a =
      dotProduct (screenedMean a b ha hia) (screenedInverseSource a b ha hia) := by
  have hd (k : ι ⊕ κ) : 1 < Sum.elim a b k := by
    cases k with
    | inl i => exact ha i
    | inr j => exact hb j
  let hu := centeredResidue_linearIndependent a ha hia
  let hall := combined_independent a b ha hb hab
  let hs := screened_independent a b ha hia hb hab
  have he : covarianceInformation (Sum.elim a b) =
      capacity hall (Sum.elim (qMean a) (qMean b)) := by
    simpa only [centeredResidue_sum, qMean_sum] using
      covarianceInformation_eq_capacity (Sum.elim a b) hd hab
  rw [he, covarianceInformation_eq_capacity a ha hia,
    capacity_screened_add hu (centeredResidue b) hs hall]
  change capacity hu (qMean a) + capacity hs (screenedMean a b ha hia) -
    capacity hu (qMean a) = _
  rw [add_sub_cancel_left, screenedInverseSource_eq_inverseSource a b ha hia hb hab]
  unfold capacity dotProduct
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

/-- Both blocks of C_new^{-1} b_new, with the complete old coefficient correction. -/
theorem covarianceInverseSource_blocks [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (a : ι → ℕ) (b : κ → ℕ)
    (ha : ∀ i, 1 < a i) (hia : Function.Injective a)
    (hb : ∀ j, 1 < b j) (hab : Function.Injective (Sum.elim a b)) :
    covarianceInverseSource (Sum.elim a b) =
      Sum.elim
        (fun i => covarianceInverseSource a i -
          ∑ j, screenedInverseSource a b ha hia j * projectionCoefficients a b j i)
        (screenedInverseSource a b ha hia) := by
  have hd (k : ι ⊕ κ) : 1 < Sum.elim a b k := by
    cases k with
    | inl i => exact ha i
    | inr j => exact hb j
  let hu := centeredResidue_linearIndependent a ha hia
  let hall := combined_independent a b ha hb hab
  let hs := screened_independent a b ha hia hb hab
  have he : covarianceInverseSource (Sum.elim a b) =
      inverseSource hall (Sum.elim (qMean a) (qMean b)) := by
    exact combined_covarianceInverseSource a b ha hb hab
  rw [he, inverseSource_screened_sum hu (centeredResidue b) hs hall]
  congr 1
  · ext i
    simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [covarianceInverseSource_eq_inverseSource a ha hia]
    simp only [screenedInverseSource_eq_inverseSource a b ha hia hb hab,
      projectionCoefficients_eq_inverseCoeff a b ha hia]
    rfl
  · exact (screenedInverseSource_eq_inverseSource a b ha hia hb hab).symm

/-- Actual least-squares coefficients use the corrected inverse source in both blocks. -/
theorem gramInverseSource_blocks [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (a : ι → ℕ) (b : κ → ℕ)
    (ha : ∀ i, 1 < a i) (hia : Function.Injective a)
    (hb : ∀ j, 1 < b j) (hab : Function.Injective (Sum.elim a b)) :
    (residueGramMatrix (Sum.elim a b))⁻¹.mulVec (qMean (Sum.elim a b)) =
      Sum.elim
        (fun i => (covarianceInverseSource a i -
          ∑ j, screenedInverseSource a b ha hia j * projectionCoefficients a b j i) /
            (1 + covarianceInformation (Sum.elim a b)))
        (fun j => screenedInverseSource a b ha hia j /
          (1 + covarianceInformation (Sum.elim a b))) := by
  have hd (k : ι ⊕ κ) : 1 < Sum.elim a b k := by
    cases k with
    | inl i => exact ha i
    | inr j => exact hb j
  rw [gramInverseSource_eq_normalized_covariance (Sum.elim a b) hd hab,
    covarianceInverseSource_blocks a b ha hia hb hab]
  funext k
  cases k <;> rfl

theorem crossCovariance_eq (a : ι → ℕ) (b : κ → ℕ) (i : ι) (j : κ) :
    crossCovariance a b i j =
      inner ℝ (qResidue (a i)) (qResidue (b j)) - qMean a i * qMean b j := by
  unfold crossCovariance centeredResidue qMean
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, qOne_inner_self]
  rw [real_inner_comm (qResidue (a i)) qOne]
  ring

theorem screenedMean_eq_raw_residual [Fintype ι] [DecidableEq ι]
    (a : ι → ℕ) (b : κ → ℕ)
    (ha : ∀ i, 1 < a i) (hia : Function.Injective a) (j : κ) :
    screenedMean a b ha hia j =
      (1 + covarianceInformation a) * qMean b j -
        inner ℝ (qSynthesis a (covarianceInverseSource a)) (qResidue (b j)) := by
  have hinner : inner ℝ (qSynthesis a (covarianceInverseSource a)) (qResidue (b j)) =
      ∑ i, covarianceInverseSource a i * inner ℝ (qResidue (a i)) (qResidue (b j)) := by
    change inner ℝ
      (Fintype.linearCombination ℝ (fun i => qResidue (a i)) (covarianceInverseSource a))
      (qResidue (b j)) = _
    rw [inner_synthesis_left]
  have hmass : (∑ i, covarianceInverseSource a i * (qMean a i * qMean b j)) =
      covarianceInformation a * qMean b j := by
    unfold covarianceInformation dot
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [screenedMean_entry a b ha hia, hinner]
  simp_rw [crossCovariance_eq, mul_sub]
  rw [Finset.sum_sub_distrib, hmass]
  ring

/-- The signed screened source is the exact correlation with the actual old residual. -/
theorem screenedMean_eq_residual_correlation [Fintype ι] [DecidableEq ι]
    (a : ι → ℕ) (b : κ → ℕ)
    (ha : ∀ i, 1 < a i) (hia : Function.Injective a) (j : κ) :
    screenedMean a b ha hia j =
      (1 + covarianceInformation a) *
        inner ℝ
          (qOne - qSynthesis a (fun i =>
            covarianceInverseSource a i / (1 + covarianceInformation a)))
          (qResidue (b j)) := by
  have hnonneg := qInformation_nonneg a (covarianceInverseSource a)
    (covarianceInverseSource_normal a ha hia)
  have hden : 1 + covarianceInformation a ≠ 0 := by
    change 0 ≤ covarianceInformation a at hnonneg
    linarith
  have hscaled :
      qSynthesis a (fun i => covarianceInverseSource a i / (1 + covarianceInformation a)) =
        (1 + covarianceInformation a)⁻¹ • qSynthesis a (covarianceInverseSource a) := by
    simp only [qSynthesis, div_eq_mul_inv, Finset.smul_sum, smul_smul]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_comm]
  rw [screenedMean_eq_raw_residual a b ha hia, inner_sub_left, hscaled,
    real_inner_smul_left]
  change (1 + covarianceInformation a) * qMean b j -
    inner ℝ (qSynthesis a (covarianceInverseSource a)) (qResidue (b j)) =
      (1 + covarianceInformation a) *
        (qMean b j - (1 + covarianceInformation a)⁻¹ *
          inner ℝ (qSynthesis a (covarianceInverseSource a)) (qResidue (b j)))
  field_simp [hden]

/-- A single screened column gives a quantitative lower bound for the full gain. -/
theorem screenedMean_sq_le_gain_mul_diagonal
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] (a : ι → ℕ) (b : κ → ℕ)
    (ha : ∀ i, 1 < a i) (hia : Function.Injective a)
    (hb : ∀ j, 1 < b j) (hab : Function.Injective (Sum.elim a b)) (j : κ) :
    screenedMean a b ha hia j ^ 2 ≤
      (covarianceInformation (Sum.elim a b) - covarianceInformation a) *
        screenedCovariance a b ha hia j j := by
  let hs := screened_independent a b ha hia hb hab
  have h := real_inner_mul_inner_self_le
    (screenedResidue a b ha hia j) (minimumVector hs (screenedMean a b ha hia))
  rw [minimumVector_observation, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq] at h
  rw [covarianceInformation_gain a b ha hia hb hab,
    screenedInverseSource_eq_inverseSource a b ha hia hb hab]
  have hc : dotProduct (screenedMean a b ha hia)
      (inverseSource hs (screenedMean a b ha hia)) =
      capacity hs (screenedMean a b ha hia) := by
    unfold dotProduct capacity
    apply Finset.sum_congr rfl
    intro k _
    exact mul_comm _ _
  rw [hc, capacity_eq_norm_sq]
  change _ ≤ _ * inner ℝ (screenedResidue a b ha hia j) (screenedResidue a b ha hia j)
  rw [real_inner_self_eq_norm_sq]
  nlinarith

/-- Relabeling a finite actual conductor family preserves its inverse source. -/
theorem covarianceInverseSource_comp_equiv
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (a : κ → ℕ) (ha : ∀ i, 1 < a i) (hia : Function.Injective a) :
    covarianceInverseSource (a ∘ e) = covarianceInverseSource a ∘ e := by
  have hnormal :
      (residueCovarianceMatrix (a ∘ e)).mulVec (covarianceInverseSource a ∘ e) =
        qMean (a ∘ e) := by
    funext i
    change (∑ j, qCov a (e i) (e j) * covarianceInverseSource a (e j)) = qMean a (e i)
    rw [e.sum_comp (fun j => qCov a (e i) j * covarianceInverseSource a j)]
    exact covarianceInverseSource_normal a ha hia (e i)
  have hdet : IsUnit (residueCovarianceMatrix (a ∘ e)).det :=
    isUnit_iff_ne_zero.mpr
      (ne_of_gt (qCov_posDef (a ∘ e) (fun i => ha (e i)) (hia.comp e.injective)).det_pos)
  change (residueCovarianceMatrix (a ∘ e))⁻¹.mulVec (qMean (a ∘ e)) = _
  rw [← hnormal, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]

/-- The capacity is an invariant of the actual finite family, independent of its labels. -/
theorem covarianceInformation_comp_equiv
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (a : κ → ℕ) (ha : ∀ i, 1 < a i) (hia : Function.Injective a) :
    covarianceInformation (a ∘ e) = covarianceInformation a := by
  unfold covarianceInformation dot
  rw [covarianceInverseSource_comp_equiv e a ha hia]
  exact e.sum_comp (fun i => qMean a i * covarianceInverseSource a i)

end RiemannResearch.RH.QCovarianceScreening
