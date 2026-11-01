import RiemannResearch.Analysis.CesaroFiniteCalculus
import RiemannResearch.RH.ArithmeticCumulativeBasic
import RiemannResearch.RH.CesaroResidueMean
import RiemannResearch.RH.PrimePowerTwoTargetCriterion
import RiemannResearch.RH.QParityConditionalTarget
import RiemannResearch.RH.QSquarefreeDilationObstruction
import RiemannResearch.RH.QSquarefreeJumpDistance
import RiemannResearch.RH.SquarefreeRadicalDifference
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Cesàro averaging and the two squarefree restrictions

Source: the user's request of 1 November 2026 to compare Cesàro averaging
under P and Q, and in the squarefree setting. The concrete counterexample
and its assembly with the existing square-jump witness are developed here.

Squarefree conductors restrict the dictionary, retaining every physical
sample index. Cesàro averaging is defined for these inputs, but its output
need not remain in the original squarefree closure, even with constants.
The first residue atom gives an exact signed defect of 1/6 and a complete
orthogonal remainder, with positive separation in both probability norms.

Restricting sample indices to squarefree integers is different: ordinary
Cesàro averaging does not even descend to equality on those sample indices.
This is a method distinction, not a contradiction to the RH criterion for
Cesàro energies of squarefree legal input functions.
-/

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace RiemannResearch.RH.SquarefreeCesaroObstruction
open RiemannResearch.Probability.ConditionalIID
open ArithmeticCumulative ArithmeticCumulative.CesaroResidue
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer
open QSquarefreeJumpDistance SquarefreeRadicalDifference PrimePowerTarget

/-- The complete Q realization of the Cesàro mean of one residue atom. -/
def qCesaroResidue (d : ℕ) (hd : 0 < d) : QHilbert :=
  encodeQ (cesaro (residueFraction d))
    (boundedQ_square_summable _ (1 / 2) (by norm_num) (fun n => by
      rw [abs_of_nonneg (cesaro_residue_nonneg d n)]
      exact cesaro_residue_le_half d n hd))

@[simp] theorem qSequence_qCesaroResidue (d : ℕ) (hd : 0 < d) :
    qSequence (qCesaroResidue d hd) = cesaro (residueFraction d) :=
  qSequence_encodeQ _ _ (by simp [cesaro])

/-- The four-site defect is already nonzero for the squarefree conductor 2. -/
theorem qCesaroResidue_two_squareJump :
    squareJumpFunctional 2 (qCesaroResidue 2 (by decide)) = (1 / 6 : ℝ) := by
  rw [squareJumpFunctional_apply 2 (by decide)]
  simp only [qDifference, qSequence_qCesaroResidue]
  norm_num [cesaro_residue_exact 2 1 (by decide),
    cesaro_residue_exact 2 2 (by decide),
    cesaro_residue_exact 2 3 (by decide),
    cesaro_residue_exact 2 4 (by decide)]

/-- Complete exact Q error energy; the entire orthogonal remainder is retained. -/
theorem qCesaroResidue_two_error_energy_exact (f : QHilbert)
    (hf : f ∈ closureWithConstants) :
    ‖qCesaroResidue 2 (by decide) - f‖ ^ 2 = 1 / (1080 * zetaTwo) +
      ‖qCesaroResidue 2 (by decide) - f -
        (1 / (180 * zetaTwo)) • squareJumpWitness 2‖ ^ 2 := by
  have h := closureWithConstants_error_energy_exact 2 (by decide)
    (qCesaroResidue 2 (by decide)) f hf
  rw [qCesaroResidue_two_squareJump] at h
  change ‖qCesaroResidue 2 (by decide) - f‖ ^ 2 =
    (1 / 6 : ℝ) ^ 2 / (2 * zetaTwo * ((2 : ℝ) ^ 4 - 2 + 1)) +
      ‖qCesaroResidue 2 (by decide) - f -
        ((1 / 6 : ℝ) / (2 * zetaTwo * ((2 : ℝ) ^ 4 - 2 + 1))) •
          squareJumpWitness 2‖ ^ 2 at h
  have hD : 2 * zetaTwo * ((2 : ℝ) ^ 4 - 2 + 1) = 30 * zetaTwo := by ring
  have he1 : (1 / 6 : ℝ) ^ 2 / (30 * zetaTwo) = 1 / (1080 * zetaTwo) := by
    field_simp [ne_of_gt zetaTwo_pos]
    ring
  have he2 : (1 / 6 : ℝ) / (30 * zetaTwo) = 1 / (180 * zetaTwo) := by
    field_simp [ne_of_gt zetaTwo_pos]
    ring
  rwa [hD, he1, he2] at h

theorem qCesaroResidue_two_error_sq_lower_bound (f : QHilbert)
    (hf : f ∈ closureWithConstants) :
    1 / (1080 * zetaTwo) ≤ ‖qCesaroResidue 2 (by decide) - f‖ ^ 2 := by
  rw [qCesaroResidue_two_error_energy_exact f hf]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- Exact P change of measure retains both the orthogonal remainder and correction. -/
theorem qCesaroResidue_two_pareto_error_exact (f : QHilbert)
    (hf : f ∈ closureWithConstants) :
    ‖toPareto (qCesaroResidue 2 (by decide) - f)‖ ^ 2 =
      zetaTwo * (1 / (1080 * zetaTwo) +
        ‖qCesaroResidue 2 (by decide) - f -
          (1 / (180 * zetaTwo)) • squareJumpWitness 2‖ ^ 2) -
      zetaTwo * normCorrection (qCesaroResidue 2 (by decide) - f) := by
  rw [toPareto_norm_sq_exact, qCesaroResidue_two_error_energy_exact f hf]

/-- A positive full-P separation follows from the complete reverse norm comparison. -/
theorem qCesaroResidue_two_pareto_error_sq_lower_bound (f : QHilbert)
    (hf : f ∈ closureWithConstants) :
    (1 / 2160 : ℝ) ≤ ‖toPareto (qCesaroResidue 2 (by decide) - f)‖ ^ 2 := by
  have hq := mul_le_mul_of_nonneg_left
    (qCesaroResidue_two_error_sq_lower_bound f hf) zetaTwo_pos.le
  have hp := zetaTwo_mul_norm_sq_le_two_toPareto_norm_sq
    (qCesaroResidue 2 (by decide) - f)
  have hc : zetaTwo * (1 / (1080 * zetaTwo)) = (1 / 1080 : ℝ) := by
    field_simp [ne_of_gt zetaTwo_pos]
  rw [hc] at hq
  linarith

theorem qCesaroResidue_two_not_mem :
    qCesaroResidue 2 (by decide) ∉ closureWithConstants := by
  intro h
  have hz := squareJumpFunctional_zero_on_closureWithConstants 2 (by decide) h
  rw [qCesaroResidue_two_squareJump] at hz
  norm_num at hz

/-- The output cannot stay in the squarefree closure, even after adding constants. -/
theorem cesaro_not_preserve_squarefreeClosure :
    ¬ ∀ f : QHilbert, f ∈ ZetaTwoOptimizerStage.closure →
      ∃ g : QHilbert, g ∈ closureWithConstants ∧
        qSequence g = cesaro (qSequence f) := by
  intro h
  obtain ⟨g, hg, he⟩ := h (qResidue 2) QParityConditionalTarget.qResidue_two_mem_closure
  have hge : g = qCesaroResidue 2 (by decide) := by
    apply qSequence_injective
    rw [qSequence_qCesaroResidue]
    simpa only [qSequence_qResidue] using he
  exact qCesaroResidue_two_not_mem (hge ▸ hg)

/-- A pulse removed by conditioning the sample measure to squarefree integers. -/
def nonSquarefreePulse (n : ℕ) : ℝ := if n = 4 then 1 else 0

theorem nonSquarefreePulse_zero_on_squarefree (n : ℕ) (hn : Squarefree n) :
    nonSquarefreePulse n = 0 := by
  have h4 : ¬ Squarefree (4 : ℕ) := by decide
  have hn4 : n ≠ 4 := by intro h; exact h4 (h ▸ hn)
  simp [nonSquarefreePulse, hn4]

theorem cesaro_nonSquarefreePulse_five :
    cesaro nonSquarefreePulse 5 = (1 / 5 : ℝ) := by
  norm_num [cesaro, nonSquarefreePulse]

/-- Ordinary Cesàro is not well-defined on equality restricted to squarefree samples. -/
theorem cesaro_not_preserve_squarefree_sample_equality :
    ¬ ∀ f g : ℕ → ℝ, (∀ n, Squarefree n → f n = g n) →
      ∀ n, Squarefree n → cesaro f n = cesaro g n := by
  intro h
  have he := h nonSquarefreePulse (fun _ => 0)
    nonSquarefreePulse_zero_on_squarefree 5 ((by norm_num : Nat.Prime 5).squarefree)
  rw [cesaro_nonSquarefreePulse_five] at he
  norm_num [cesaro] at he

end RiemannResearch.RH.SquarefreeCesaroObstruction
