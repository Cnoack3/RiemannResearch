import RiemannResearch.RH.QDensityMetric
import RiemannResearch.RH.QHilbertConvergence
import RiemannResearch.RH.QParetoEquivalence
import RiemannResearch.RH.ArithmeticCumulativeBasic
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ThresholdHilbertSpace
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Data.Nat.Squarefree
import Mathlib.Topology.Algebra.Module.ClosedSubmodule
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# A four-site obstruction to squarefree density-image approximation

Source: the user's squarefree-density claim. The proof uses the four-site
residue identity already formalized in QSquarefreeBoundary. Here its pullback
through the actual density B = dQ/dP detects the constant function.

Every family omitting conductor four has density-image closed span excluding
one. In particular, squarefree density images are not dense in L²(Q), and the
same physical vectors cannot approximate one in the Pareto norm. This does
not contradict approximation by the augmented family containing both g_k and
B g_k. No RH or cancellation hypothesis is assumed.
-/

noncomputable section
namespace RiemannResearch.RH.QDensitySquarefreeObstruction
open ZetaTwoHilbert ZetaTwoProbability QDensityMetric

/-- The four-coordinate obstruction pulled back through the density multiplier. -/
def densityFourSite : QHilbert →L[ℝ] ℝ :=
  ((1 : ℝ) / 2) • qEvalCLM 1 - ((2 : ℝ) / 3) • qEvalCLM 2 -
    ((3 : ℝ) / 4) • qEvalCLM 3 + ((4 : ℝ) / 5) • qEvalCLM 4

theorem densityFourSite_apply (f : QHilbert) :
    densityFourSite f = (1 : ℝ) / 2 * qSequence f 1 -
      (2 : ℝ) / 3 * qSequence f 2 - (3 : ℝ) / 4 * qSequence f 3 +
      (4 : ℝ) / 5 * qSequence f 4 := by
  simp [densityFourSite, qEvalCLM_apply]

/-- Exact signed identity before using any conductor restriction. -/
theorem densityFourSite_B (f : QHilbert) :
    densityFourSite (B f) = (1 / zetaTwo) *
      (qSequence f 1 - qSequence f 2 - qSequence f 3 + qSequence f 4) := by
  rw [densityFourSite_apply]
  simp only [qSequence_B]
  norm_num
  ring

/-- Conductor four is the only residue atom detected by this four-site test. -/
theorem densityFourSite_B_qResidue (k : ℕ) (hk : k ≠ 4) :
    densityFourSite (B (qResidue k)) = 0 := by
  rw [densityFourSite_B]
  simp only [qSequence_qResidue, ArithmeticCumulative.residueFraction]
  by_cases hsmall : k ≤ 4
  · interval_cases k <;> norm_num at *
  · have h1 : 1 < k := by omega
    have h2 : 2 < k := by omega
    have h3 : 3 < k := by omega
    have h4 : 4 < k := by omega
    rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2,
      Nat.mod_eq_of_lt h3, Nat.mod_eq_of_lt h4]
    norm_num only [Nat.cast_ofNat]
    ring

theorem densityFourSite_qOne : densityFourSite qOne = -(7 : ℝ) / 60 := by
  rw [densityFourSite_apply]
  simp only [qSequence_qOne]
  norm_num [qOneSequence]

/-- Finite span of density images, without adjoining the original residues. -/
def densitySpan (s : Set ℕ) : Submodule ℝ QHilbert :=
  Submodule.span ℝ {f | ∃ k, k ∈ s ∧ f = B (qResidue k)}

theorem densityFourSite_zero_on_closure {s : Set ℕ} (h4 : 4 ∉ s)
    {f : QHilbert} (hf : f ∈ (densitySpan s).topologicalClosure) :
    densityFourSite f = 0 := by
  have hle : densitySpan s ≤ densityFourSite.ker := by
    apply Submodule.span_le.mpr
    rintro f ⟨k, hk, rfl⟩
    change densityFourSite (B (qResidue k)) = 0
    exact densityFourSite_B_qResidue k (fun h => h4 (h ▸ hk))
  have hclosed := (densitySpan s).topologicalClosure_minimal hle
    densityFourSite.isClosed_ker
  exact hclosed hf

theorem one_not_mem_densityClosure_of_four_not_mem {s : Set ℕ} (h4 : 4 ∉ s) :
    qOne ∉ (densitySpan s).topologicalClosure := by
  intro h
  have hz := densityFourSite_zero_on_closure h4 h
  rw [densityFourSite_qOne] at hz
  norm_num at hz

theorem densityClosure_ne_top_of_four_not_mem {s : Set ℕ} (h4 : 4 ∉ s) :
    (densitySpan s).topologicalClosure ≠ ⊤ := by
  intro h
  apply one_not_mem_densityClosure_of_four_not_mem h4
  rw [h]
  trivial

theorem one_not_mem_squarefree_densityClosure :
    qOne ∉ (densitySpan {k : ℕ | Squarefree k}).topologicalClosure := by
  apply one_not_mem_densityClosure_of_four_not_mem
  intro h
  have hh := Nat.squarefree_iff_prime_squarefree.mp h 2 Nat.prime_two
  norm_num at hh

theorem squarefree_densityClosure_ne_top :
    (densitySpan {k : ℕ | Squarefree k}).topologicalClosure ≠ ⊤ := by
  intro h
  apply one_not_mem_squarefree_densityClosure
  rw [h]
  trivial

open Pareto ZetaTwoParetoTransfer QParetoEquivalence

/-- The same physical density images do not approximate one in the Pareto norm. -/
theorem pareto_one_not_mem_squarefree_densityClosure :
    hilbertOne ∉
      ((densitySpan {k : ℕ | Squarefree k}).map
        paretoEquiv.toLinearMap).topologicalClosure := by
  intro h
  apply one_not_mem_squarefree_densityClosure
  apply (mem_closure_map_iff (densitySpan {k : ℕ | Squarefree k}) qOne).mp
  simpa only [toPareto_qOne] using h

end RiemannResearch.RH.QDensitySquarefreeObstruction
