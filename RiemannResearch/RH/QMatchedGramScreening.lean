import RiemannResearch.Analysis.ProjectionPairingSplit
import RiemannResearch.Analysis.ResidueOscillation
import RiemannResearch.Analysis.FiniteHilbertGramMatrix
import RiemannResearch.RH.QMatchedOscillationKernel
import RiemannResearch.RH.QFullDivisorProjection
import RiemannResearch.RH.QFullCRTDisplacement
import RiemannResearch.RH.QFullDisplacement
import RiemannResearch.RH.QHilbertConvergence
import RiemannResearch.RH.QSquarefreeLatticePackets
import RiemannResearch.RH.QParetoClosedProjectionComparison
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.ZetaTwoParetoTransfer
import Mathlib.Tactic.Linarith

/-!
# Additional Gram screening for the actual matched displacement

Source: user-requested combination of CRT, reciprocal, displacement and
residue/zero Gram methods, 9 November 2026. The exact matched pairing comes
from QMatchedOscillationKernel. The added step is standard orthogonal
decomposition on an arbitrary test subspace U in the complete Pareto space.

The scalar captured pairing is signed. Cauchy--Schwarz is applied only to
the two remaining vectors. The resulting bound is never larger than the
original complete residual/kernel product. The fixed-modulus head criterion
is a conditional research reduction: its uniform split bound remains Open.
No density of a zero-test family, no GUE hypothesis, and no RH are assumed.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.QMatchedGramScreening
open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer
open QParetoClosedProjectionComparison QMatchedOscillationKernel
open RiemannResearch.Analysis.ProjectionPairingSplit
open RiemannResearch.Analysis.FiniteHilbertGram

variable (S : Submodule ℝ QHilbert) (T U : Submodule ℝ ThresholdHilbert)
variable [S.HasOrthogonalProjection] [T.HasOrthogonalProjection] [U.HasOrthogonalProjection]

/-- Computable after fixing a finite test space; all norms are complete. -/
def splitPairBudget (x : QHilbert) (n m : ℕ) : ℝ :=
  |inner ℝ (U.starProjection (toPareto (x - pFit T x)))
    (U.starProjection (screenedPairKernel S T n m))| +
  ‖toPareto (x - pFit T x) - U.starProjection (toPareto (x - pFit T x))‖ *
    ‖screenedPairKernel S T n m - U.starProjection (screenedPairKernel S T n m)‖

theorem splitPairBudget_le_original (x : QHilbert) (n m : ℕ) :
    splitPairBudget S T U x n m ≤
      ‖toPareto (x - pFit T x)‖ * ‖screenedPairKernel S T n m‖ :=
  split_bound_le_cauchy U _ _

variable (hsame : ∀ f : QHilbert, toPareto f ∈ T ↔ f ∈ S)
include hsame

/-- Exact signed contribution of the test space and the full remaining pairing. -/
theorem matched_pair_split (x : QHilbert) (n m : ℕ) :
    zetaTwo * (qSequence (qFit S x - pFit T x) n -
      qSequence (qFit S x - pFit T x) m) =
      inner ℝ (U.starProjection (toPareto (x - pFit T x)))
        (U.starProjection (screenedPairKernel S T n m)) +
      inner ℝ (toPareto (x - pFit T x) -
          U.starProjection (toPareto (x - pFit T x)))
        (screenedPairKernel S T n m -
          U.starProjection (screenedPairKernel S T n m)) := by
  rw [matched_pair_identity S T hsame]
  exact pairing_split U _ _

theorem matched_pair_split_bound (x : QHilbert) (n m : ℕ) :
    zetaTwo * |qSequence (qFit S x - pFit T x) n -
      qSequence (qFit S x - pFit T x) m| ≤ splitPairBudget S T U x n m := by
  have h := abs_pairing_le U (toPareto (x - pFit T x)) (screenedPairKernel S T n m)
  rw [← matched_pair_identity S T hsame x n m, abs_mul, abs_of_pos zetaTwo_pos] at h
  exact h

omit [U.HasOrthogonalProjection] in
/-- Literal inverse-Gram formula for the centered matched pairing. -/
theorem matched_pair_gram_remainder_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → ThresholdHilbert) (hv : LinearIndependent ℝ v) (x : QHilbert) (n m : ℕ) :
    let r := toPareto (x - pFit T x)
    let W := screenedPairKernel S T n m
    let G := gramMatrix v
    let b := cross v r
    let k := cross v W
    (zetaTwo * (qSequence (qFit S x - pFit T x) n -
      qSequence (qFit S x - pFit T x) m) - dotProduct b (G⁻¹.mulVec k)) ^ 2 ≤
      (‖r‖ ^ 2 - dotProduct b (G⁻¹.mulVec b)) *
      (‖W‖ ^ 2 - dotProduct k (G⁻¹.mulVec k)) := by
  dsimp only
  rw [matched_pair_identity S T hsame]
  exact gram_pairing_remainder_sq_le hv _ _

end RiemannResearch.RH.QMatchedGramScreening

namespace RiemannResearch.RH.QFullOscillationDual
open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer
open QMatchedGramScreening QParetoClosedProjectionComparison
open QFullDisplacement

/-- Conditional research reduction. It suffices to bound the split pair budget
on expanding heads at one fixed positive modulus. This hypothesis is no
stronger than the existing original kernel-product hypothesis. -/
theorem riemannHypothesis_of_head_split_pair_budget
    (R : ℕ → ℕ+) (hnest : ∀ i j, i ≤ j → (R i : ℕ) ∣ (R j : ℕ))
    (hcofinal : ∀ q : ℕ, 1 < q → ∃ j, q ∣ (R j : ℕ))
    (U : ℕ → Submodule ℝ ThresholdHilbert) [∀ j, (U j).HasOrthogonalProjection]
    (H : ℕ → ℕ) (hH : Tendsto H atTop atTop)
    (L : ℕ) (hL : 0 < L) (C : ℝ)
    (hb : ∀ j n m, 0 < n → 0 < m → n ≤ H j → m ≤ H j →
      n % L = m % L →
      splitPairBudget (QSquarefreeLatticePackets.divisorStage (R j : ℕ))
        (QFullDivisorProjection.paretoStage (R j)) (U j) qOne n m ≤ zetaTwo * C) :
    RiemannHypothesis := by
  apply QFullCRTDisplacement.riemannHypothesis_of_finite_residue_oscillation L hL C
  apply RiemannResearch.Analysis.ResidueOscillation.bound_of_expanding_head_limit
    (fun j n => qSequence (QFullDivisorProjection.displacement (R j)) n)
    _ L C H hH
  · intro n
    exact qSequence_tendsto_of_tendsto
      (QFullDivisorProjection.displacement_tendsto R hnest hcofinal) n
  · intro j n m hn hm hjn hjm hnm
    have h := matched_pair_split_bound
      (QSquarefreeLatticePackets.divisorStage (R j : ℕ))
      (QFullDivisorProjection.paretoStage (R j)) (U j)
      (QFullDivisorProjection.toPareto_mem_stage_iff (R j)) qOne n m
    have hbound := h.trans (hb j n m hn hm hjn hjm hnm)
    change zetaTwo * |qSequence (QFullDivisorProjection.displacement (R j)) n -
      qSequence (QFullDivisorProjection.displacement (R j)) m| ≤ zetaTwo * C at hbound
    nlinarith [zetaTwo_pos]

end RiemannResearch.RH.QFullOscillationDual
