import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import RiemannResearch.RH.QCovarianceInverse
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.Analysis.FiniteHilbertGramMatrix
import Mathlib.Data.Nat.Factorial.Basic
import Lean.Elab.Tactic.Omega

/-!
# Genuine inverse covariance matrices for distinct residue conductors

Source: the user's Q-residue Gram calculation; ordinary finite Gram theory.
Distinct conductors greater than one have independent residues and independent
centered residues. A common factorial multiple rules out a nonzero constant
finite synthesis. Therefore both actual matrices are positive definite.
The inverse formula below has no assumed covariance solvability hypothesis.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QCovarianceInvertibility
open RiemannResearch.LinearAlgebra.CenteredNormalEquations
open RiemannResearch.RH.QCovarianceInverse
open RiemannResearch.RH.ZetaTwoHilbert
open RiemannResearch.RH.ZetaTwoParetoTransfer
open RiemannResearch.RH.Pareto.CoefficientStabilization
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.RH.ArithmeticCumulative

variable {ι : Type*} [Fintype ι]

theorem qResidue_linearIndependent (d : ι → ℕ)
    (hd : ∀ i, 1 < d i) (hinj : Function.Injective d) :
    LinearIndependent ℝ (fun i => qResidue (d i)) := by
  classical
  have hinj' : Function.Injective (fun i => d i - 2) := by
    intro i j hij
    change d i - 2 = d j - 2 at hij
    apply hinj
    have hi := hd i
    have hj := hd j
    omega
  have hp := residueAtom_linearIndependent.comp (fun i => d i - 2) hinj'
  have hmap (i : ι) : toParetoLinear (qResidue (d i)) = residueAtom (d i - 2) := by
    change toPareto (qResidue (d i)) = _
    have hi : d i = (d i - 2) + 2 := by have h := hd i; omega
    nth_rw 1 [hi]
    exact toPareto_residueAtom _
  apply Fintype.linearIndependent_iff.mpr
  intro a ha
  apply Fintype.linearIndependent_iff.mp hp a
  have hm := congrArg toParetoLinear ha
  simpa only [map_sum, map_smul, map_zero, hmap, Function.comp_def] using hm

def centeredResidue (d : ι → ℕ) (i : ι) : QHilbert :=
  qResidue (d i) - qMean d i • qOne

theorem centered_synthesis (d : ι → ℕ) (a : ι → ℝ) :
    (∑ i, a i • centeredResidue d i) =
      qSynthesis d a - dot (qMean d) a • qOne := by
  simp only [centeredResidue, smul_sub, Finset.sum_sub_distrib, smul_smul,
    qSynthesis, dot]
  congr 1
  rw [Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_comm]

/-- A literal common-period coordinate forces any constant synthesis to zero. -/
theorem qSynthesis_eq_const_forces_zero (d : ι → ℕ) (hd : ∀ i, 1 < d i)
    (a : ι → ℝ) (m : ℝ) (he : qSynthesis d a = m • qOne) : m = 0 := by
  classical
  let M : ℕ := ∑ i, d i
  let L : ℕ := (M + 1).factorial
  have hL : 0 < L := Nat.factorial_pos _
  have hdL (i : ι) : d i ∣ L := by
    have hi : d i ≤ M := by
      exact Finset.single_le_sum (fun j _ => Nat.zero_le (d j)) (Finset.mem_univ i)
    exact Nat.dvd_factorial (by have h := hd i; omega) (by omega)
  have hz (i : ι) : qSequence (qResidue (d i)) L = 0 := by
    rw [qSequence_qResidue]
    simp [residueFraction, Nat.mod_eq_zero_of_dvd (hdL i)]
  have hs : qSequenceLinear (qSynthesis d a) L = 0 := by
    unfold qSynthesis
    rw [map_sum]
    simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
    change (∑ i, a i * qSequence (qResidue (d i)) L) = 0
    simp only [hz, mul_zero, Finset.sum_const_zero]
  have hone : qSequence qOne L = 1 := by
    rw [qSequence_qOne]
    simp [qOneSequence, Nat.ne_of_gt hL]
  rw [he, map_smul] at hs
  change m * qSequence qOne L = 0 at hs
  simpa only [hone, mul_one] using hs

theorem centeredResidue_linearIndependent (d : ι → ℕ)
    (hd : ∀ i, 1 < d i) (hinj : Function.Injective d) :
    LinearIndependent ℝ (centeredResidue d) := by
  apply Fintype.linearIndependent_iff.mpr
  intro a ha
  rw [centered_synthesis] at ha
  have he : qSynthesis d a = dot (qMean d) a • qOne := sub_eq_zero.mp ha
  have hm := qSynthesis_eq_const_forces_zero d hd a (dot (qMean d) a) he
  have hz : qSynthesis d a = 0 := by simpa only [hm, zero_smul] using he
  exact Fintype.linearIndependent_iff.mp (qResidue_linearIndependent d hd hinj) a hz

theorem centeredResidue_inner (d : ι → ℕ) (i j : ι) :
    inner ℝ (centeredResidue d i) (centeredResidue d j) = qCov d i j := by
  unfold centeredResidue qCov qGram
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, qOne_inner_self]
  have hi : inner ℝ (qResidue (d i)) qOne = qMean d i := by
    rw [real_inner_comm]
    rfl
  have hj : inner ℝ qOne (qResidue (d j)) = qMean d j := rfl
  simp only [hi, hj]
  ring

/-- Matrix wrappers ensure inverse notation denotes matrix inversion, not pointwise inversion. -/
def residueGramMatrix (d : ι → ℕ) : Matrix ι ι ℝ := qGram d

def residueCovarianceMatrix (d : ι → ℕ) : Matrix ι ι ℝ := qCov d

theorem qGram_posDef (d : ι → ℕ) (hd : ∀ i, 1 < d i)
    (hinj : Function.Injective d) : (residueGramMatrix d).PosDef :=
  gramMatrix_posDef (qResidue_linearIndependent d hd hinj)

theorem qCov_posDef (d : ι → ℕ) (hd : ∀ i, 1 < d i)
    (hinj : Function.Injective d) : (residueCovarianceMatrix d).PosDef := by
  have he : residueCovarianceMatrix d = gramMatrix (centeredResidue d) := by
    funext i j
    exact (centeredResidue_inner d i j).symm
  rw [he]
  exact gramMatrix_posDef (centeredResidue_linearIndependent d hd hinj)

variable [DecidableEq ι]

def covarianceInverseSource (d : ι → ℕ) : ι → ℝ :=
  (residueCovarianceMatrix d)⁻¹.mulVec (qMean d)

def covarianceInformation (d : ι → ℕ) : ℝ :=
  dot (qMean d) (covarianceInverseSource d)

theorem covarianceInverseSource_normal (d : ι → ℕ) (hd : ∀ i, 1 < d i)
    (hinj : Function.Injective d) (i : ι) :
    action (qCov d) (covarianceInverseSource d) i = qMean d i := by
  have hdet : IsUnit (residueCovarianceMatrix d).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt (qCov_posDef d hd hinj).det_pos)
  have hh : (residueCovarianceMatrix d).mulVec ((residueCovarianceMatrix d)⁻¹.mulVec (qMean d)) = qMean d := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  exact congrFun hh i

theorem qError_genuine_inverse (d : ι → ℕ) (hd : ∀ i, 1 < d i)
    (hinj : Function.Injective d) :
    ‖qOne - qSynthesis d
      (fun i => covarianceInverseSource d i / (1 + covarianceInformation d))‖^2 =
      1 / (1 + covarianceInformation d) :=
  qError_covariance_solution d (covarianceInverseSource d)
    (covarianceInverseSource_normal d hd hinj)

theorem gramInverseSource_eq_normalized_covariance (d : ι → ℕ)
    (hd : ∀ i, 1 < d i) (hinj : Function.Injective d) :
    (residueGramMatrix d)⁻¹.mulVec (qMean d) =
      fun i => covarianceInverseSource d i / (1 + covarianceInformation d) := by
  let c : ι → ℝ := fun i => covarianceInverseSource d i / (1 + covarianceInformation d)
  have hden : 1 + covarianceInformation d ≠ 0 := by
    have h := qInformation_nonneg d (covarianceInverseSource d)
      (covarianceInverseSource_normal d hd hinj)
    change 0 ≤ covarianceInformation d at h
    linarith
  have hc : (residueGramMatrix d).mulVec c = qMean d := by
    funext i
    change action (qGram d) c i = qMean d i
    rw [qGram_rankOne]
    exact normalized_normal_equations (qCov d) (qMean d) (covarianceInverseSource d)
      (covarianceInverseSource_normal d hd hinj) hden i
  have hdet : IsUnit (residueGramMatrix d).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt (qGram_posDef d hd hinj).det_pos)
  change (residueGramMatrix d)⁻¹.mulVec (qMean d) = c
  rw [← hc, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]

theorem gram_determinant_covariance_update (d : ι → ℕ)
    (hd : ∀ i, 1 < d i) (hinj : Function.Injective d) :
    (residueGramMatrix d).det = (residueCovarianceMatrix d).det * (1 + covarianceInformation d) := by
  have he : residueGramMatrix d = residueCovarianceMatrix d + Matrix.vecMulVec (qMean d) (qMean d) := by
    funext i j
    change qGram d i j = qCov d i j + qMean d i * qMean d j
    unfold qCov
    ring
  rw [he, Matrix.det_add_outer _
    (isUnit_iff_ne_zero.mpr (ne_of_gt (qCov_posDef d hd hinj).det_pos))]
  rfl

/-- The actual inverse covariance optimizer has the determinant-ratio error. -/
theorem qError_eq_determinant_ratio (d : ι → ℕ)
    (hd : ∀ i, 1 < d i) (hinj : Function.Injective d) :
    ‖qOne - qSynthesis d
      (fun i => covarianceInverseSource d i / (1 + covarianceInformation d))‖^2 =
      (residueCovarianceMatrix d).det / (residueGramMatrix d).det := by
  rw [qError_genuine_inverse d hd hinj, gram_determinant_covariance_update d hd hinj]
  have hdet : (residueCovarianceMatrix d).det ≠ 0 :=
    ne_of_gt (qCov_posDef d hd hinj).det_pos
  have hden : 1 + covarianceInformation d ≠ 0 := by
    have h := qInformation_nonneg d (covarianceInverseSource d)
      (covarianceInverseSource_normal d hd hinj)
    change 0 ≤ covarianceInformation d at h
    linarith
  field_simp [hdet, hden]

end RiemannResearch.RH.QCovarianceInvertibility
