import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.LinearAlgebra.CenteredNormalEquations
import Mathlib.Tactic.NthRewrite

/-!
# Centered normal equations for the actual zeta-two residue family

Source: the user's Q-residue Gram calculation. The weighted Hilbert-space
realization and residue vectors are the actual existing Q objects.
The covariance is positive semidefinite, and a covariance solution computes
the exact infinite Q error. This module itself does not assert nonsingularity
for arbitrary conductor lists; duplicates and conductor one are permitted.
The actual stage application and limit criterion belong in a sibling module.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.QCovarianceInverse

open RiemannResearch.LinearAlgebra.CenteredNormalEquations
variable {ι : Type*} [Fintype ι]

open RiemannResearch.RH.ZetaTwoHilbert

/-- Actual means under Q(n)=1/(zeta(2)n²). -/
def qMean (d : ι → ℕ) (i : ι) : ℝ := inner ℝ qOne (qResidue (d i))

def qGram (d : ι → ℕ) (i j : ι) : ℝ := inner ℝ (qResidue (d i)) (qResidue (d j))

def qCov (d : ι → ℕ) (i j : ι) : ℝ := qGram d i j - qMean d i * qMean d j

def qSynthesis (d : ι → ℕ) (c : ι → ℝ) : QHilbert :=
  ∑ i, c i • qResidue (d i)

theorem qGram_rankOne (d : ι → ℕ) : qGram d = rankOneAdd (qCov d) (qMean d) := by
  funext i j
  unfold qCov rankOneAdd
  ring

theorem qMean_synthesis (d : ι → ℕ) (c : ι → ℝ) :
    inner ℝ qOne (qSynthesis d c) = dot (qMean d) c := by
  simp only [qSynthesis, inner_sum, real_inner_smul_right, dot, qMean]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem qGram_synthesis (d : ι → ℕ) (c : ι → ℝ) (i : ι) :
    inner ℝ (qResidue (d i)) (qSynthesis d c) = action (qGram d) c i := by
  simp only [qSynthesis, inner_sum, real_inner_smul_right, action, qGram]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem qSynthesis_norm_sq (d : ι → ℕ) (c : ι → ℝ) :
    ‖qSynthesis d c‖^2 = quadratic (qGram d) c := by
  rw [← real_inner_self_eq_norm_sq]
  nth_rw 1 [qSynthesis]
  simp only [sum_inner, real_inner_smul_left, qGram_synthesis, quadratic, dot]

theorem qOne_inner_self : inner ℝ qOne qOne = 1 := by
  rw [real_inner_self_eq_norm_sq, qOne_norm_sq]

theorem qCov_symmetric (d : ι → ℕ) (i j : ι) : qCov d i j = qCov d j i := by
  unfold qCov qGram
  rw [real_inner_comm (qResidue (d i)) (qResidue (d j))]
  ring

/-- The finite covariance quadratic form is an actual squared Q norm. -/
theorem qCov_quadratic_eq_norm_sq (d : ι → ℕ) (c : ι → ℝ) :
    quadratic (qCov d) c =
      ‖qSynthesis d c - dot (qMean d) c • qOne‖^2 := by
  have hG := quadratic_rankOneAdd (qCov d) (qMean d) c
  rw [← qGram_rankOne] at hG
  have hcross : inner ℝ (qSynthesis d c) qOne = dot (qMean d) c := by
    rw [real_inner_comm]
    exact qMean_synthesis d c
  rw [norm_sub_sq_real, norm_smul, qOne_norm, mul_one,
    Real.norm_eq_abs, sq_abs, real_inner_smul_right, hcross, qSynthesis_norm_sq]
  nlinarith [hG]

theorem qCov_positiveSemidefinite (d : ι → ℕ) (c : ι → ℝ) :
    0 ≤ quadratic (qCov d) c := by
  rw [qCov_quadratic_eq_norm_sq]
  exact sq_nonneg _

theorem qInformation_nonneg (d : ι → ℕ) (u : ι → ℝ)
    (hu : ∀ i, action (qCov d) u i = qMean d i) :
    0 ≤ dot (qMean d) u :=
  information_nonneg (qCov d) (qMean d) u (qCov_positiveSemidefinite d) hu

/-- Actual squared Q error, with no finite truncation of the probability law. -/
theorem qError_eq (d : ι → ℕ) (c : ι → ℝ) :
    ‖qOne - qSynthesis d c‖^2 =
      1 - 2 * dot (qMean d) c + quadratic (qGram d) c := by
  rw [norm_sub_sq_real, qOne_norm_sq, qSynthesis_norm_sq, qMean_synthesis]
  <;> ring

/-- Normal equations turn the actual squared Q error into `1-bᵀc`. -/
theorem qError_gram_solution (d : ι → ℕ) (c : ι → ℝ)
    (hc : ∀ i, action (qGram d) c i = qMean d i) :
    ‖qOne - qSynthesis d c‖^2 = 1 - dot (qMean d) c := by
  have hquad : quadratic (qGram d) c = dot (qMean d) c := by
    unfold quadratic
    rw [show action (qGram d) c = qMean d from funext hc, dot_comm]
  rw [qError_eq, hquad]
  ring

/-- The centered solve computes the actual Q error exactly. -/
theorem qError_covariance_solution (d : ι → ℕ) (u : ι → ℝ)
    (hu : ∀ i, action (qCov d) u i = qMean d i) :
    ‖qOne - qSynthesis d (fun i => u i / (1 + dot (qMean d) u))‖^2 =
      1 / (1 + dot (qMean d) u) := by
  have hden : 1 + dot (qMean d) u ≠ 0 := by
    have h := qInformation_nonneg d u hu
    linarith
  let c : ι → ℝ := fun i => u i / (1 + dot (qMean d) u)
  have hc : action (qGram d) c = qMean d := by
    funext i
    rw [qGram_rankOne]
    exact normalized_normal_equations (qCov d) (qMean d) u hu hden i
  have hquad : quadratic (qGram d) c = dot (qMean d) c := by
    unfold quadratic
    rw [hc, dot_comm]
  change ‖qOne - qSynthesis d c‖^2 = _
  rw [qError_eq, hquad]
  have he := normalized_residual_energy (qMean d) u hden
  change 1 - dot (qMean d) c = _ at he
  linarith

end RiemannResearch.RH.QCovarianceInverse
