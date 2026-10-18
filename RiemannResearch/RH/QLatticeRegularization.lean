/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.SquarefreeCumulantCoordinates
import RiemannResearch.Analysis.PrimitiveRegularization
import RiemannResearch.RH.ArithmeticCumulativeBasic
import RiemannResearch.RH.QPrimorialRegularization
import RiemannResearch.RH.QPhysicalDifference
import RiemannResearch.RH.QSquarefreePrimorialCofinality
import RiemannResearch.RH.ZetaTwoCRTSquarefreeConverse
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Lattice coordinates for complete primitive regularization

Source: the user's lattice, CRT and convolution-function proposal, 18 October 2026.
The finite squarefree cumulant coordinates use the terminology of T. Sinclair,
https://arxiv.org/abs/2606.10870, Section 4. The physical synthesis and strict
budget consumers are developed here, without a novelty claim.

Surjective coordinates preserve the exact achievable strict budgets. Three-prime
polynomial convolution coordinates preserve the same physical trial set and
closure. Pointwise products are a distinct operation: a four-site calculation
excludes g2*g3 from the period-six legal span. This does not exclude that product
from the full closed squarefree span.

The final correction certificate retains the complete primitive cross term.
Its arithmetic inequality is Open as a uniform provider for vanishing penalties;
no new unconditional RH conclusion is proved.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QLatticeRegularization
open ZetaTwoHilbert ZetaTwoProbability QPhysicalDifference
open QSquarefreePrimorialCofinality QPrimorialRegularization

theorem squarefree_constant_mem_iff_parametrized_budget
    (Param : ℕ → Type*) (synth : ∀ M, Param M → primorialStage M)
    (hsurj : ∀ M, Function.Surjective (synth M))
    (penalty : ℕ → ℝ) (hpos : ∀ N, 0 < penalty N)
    (hzero : Tendsto penalty atTop (𝓝 0)) :
    qOne ∈ qSquarefreeCRTSpan.topologicalClosure ↔
      ∀ N, ∃ M, N ≤ M ∧ ∃ c, objective (penalty N) (synth M c : QHilbert) < penalty N := by
  rw [squarefree_constant_mem_iff_strict_primorial_budget penalty hpos hzero]
  constructor
  · intro h N
    obtain ⟨M, hMN, hb⟩ := h N
    obtain ⟨c, hc⟩ := hsurj M (minimizer M (penalty N) (hpos N))
    exact ⟨M, hMN, c, by simpa only [hc, value] using hb⟩
  · intro h N
    obtain ⟨M, hMN, c, hb⟩ := h N
    exact ⟨M, hMN, (minimizer_le_trial M (penalty N) (hpos N)
      (synth M c) (synth M c).property).trans_lt hb⟩

theorem pointwise_product_not_six_stage :
    ¬ ∃ a b c : ℝ, ∀ n : ℕ,
      ArithmeticCumulative.residueFraction 2 n *
        ArithmeticCumulative.residueFraction 3 n =
      a * ArithmeticCumulative.residueFraction 2 n +
        b * ArithmeticCumulative.residueFraction 3 n +
          c * ArithmeticCumulative.residueFraction 6 n := by
  rintro ⟨a,b,c,h⟩
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  norm_num [ArithmeticCumulative.residueFraction] at h1 h2 h3 h4
  linarith

open RiemannResearch.Analysis.SquarefreeCumulantCoordinates
open RiemannResearch.Analysis.PrimitiveRegularization

/-- Physical synthesis of the seven nonempty three-prime subsets. -/
def threePrimeSynthesis (p q r : ℕ) (c : Coefficients3 ℝ) : QHilbert :=
  synthesize3
    ⟨qResidue p, qResidue q, qResidue r, qResidue (p * q),
      qResidue (p * r), qResidue (q * r), qResidue (p * q * r)⟩ c

/-- Every full three-prime convolution exponential gives exactly the original trial set. -/
theorem threePrime_exp_range (p q r : ℕ) :
    Set.range (fun c => threePrimeSynthesis p q r (squarefreeExp3 c)) =
      Set.range (threePrimeSynthesis p q r) :=
  range_squarefreeExp3_eq _

/-- Closure is unchanged, without an infinite-series or norm assumption. -/
theorem threePrime_exp_closure (p q r : ℕ) :
    closure (Set.range (fun c => threePrimeSynthesis p q r (squarefreeExp3 c))) =
      closure (Set.range (threePrimeSynthesis p q r)) := by
  rw [threePrime_exp_range]

/-- All unit-linear degree-three convolution functions preserve strict trial budgets. -/
theorem threePrime_function_budget_iff (p q r : ℕ) (t s lam : ℝ) :
    (∃ c, objective lam (threePrimeSynthesis p q r (triangular3 t s c)) < lam) ↔
      ∃ c, objective lam (threePrimeSynthesis p q r c) < lam :=
  exists_reparam_iff (threePrimeSynthesis p q r) _
    (triangularEquiv3 t s).surjective (fun u => objective lam u < lam)

/-- The complete signed correction certificate remains legal in its finite stage. -/
theorem strict_value_of_correction_certificate (M : ℕ) (lam : ℝ) (hlam : 0 < lam)
    (u v : QHilbert) (hu : u ∈ primorialStage M) (hv : v ∈ primorialStage M)
    (hq : 0 < ‖differenceCLM v‖ ^ 2 + lam * ‖v‖ ^ 2)
    (hcert : (objective lam u - lam) *
      (‖differenceCLM v‖ ^ 2 + lam * ‖v‖ ^ 2) <
      (inner ℝ (differenceCLM qOne - differenceCLM u) (differenceCLM v) -
        lam * inner ℝ u v) ^ 2) :
    value M lam hlam < lam := by
  obtain ⟨w, hw, hb⟩ := exists_strict_budget_of_correction_certificate
    differenceCLM.toLinearMap (primorialStage M) (differenceCLM qOne) lam u v hu hv hq hcert
  exact (minimizer_le_trial M lam hlam w hw).trans_lt hb

end RiemannResearch.RH.QLatticeRegularization
