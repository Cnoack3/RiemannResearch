/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.SquarefreeMobiusProjection
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoOptimizerStage
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Unconditional atom series cannot represent the constant target

Source: the user's request to apply CRT simultaneously to all squarefree
atoms, 25 October 2026. The obstruction below is derived from the existing
continuous Mobius coefficient functionals and Mathlib's Euler/Erdos theorem
that the sum of prime reciprocals diverges.

`HasSum` here means convergence of the net over all finite subsets. It does
not describe ordered conditional series or stage-dependent finite coefficients.
This obstruction therefore does not refute squarefree closure membership.
-/

noncomputable section
open scoped Topology
namespace RiemannResearch.RH.QUnconditionalAtomSeries
open ZetaTwoHilbert SquarefreeMobiusProjection ArithmeticCumulative

/-- Any unconditional constant expansion has the uniquely forced Mobius coefficients. -/
theorem coefficient_eq_neg_moebius_of_hasSum (c : ℕ → ℝ)
    (hc : HasSum (fun j => c j • qResidue (j + 2)) qOne) (i : ℕ) :
    c i = -(ArithmeticFunction.moebius (i + 2) : ℝ) := by
  have h := (qCoefficientCLM (i + 2)).hasSum hc
  have hh : HasSum (fun j : ℕ => if j = i then c i else 0)
      (qCoefficientCLM (i + 2) qOne) := by
    convert h using 1
    funext j
    rw [map_smul, q_coordinate_biorthogonal]
    by_cases hij : j = i
    · subst j
      simp
    · simp [hij, Ne.symm hij]
  have he := (hasSum_ite_eq i (c i)).unique hh
  rwa [q_target_coordinate (i + 2) (by omega)] at he

private def firstSiteCLM : QHilbert →L[ℝ] ℝ :=
  (Real.sqrt (qWeight 0))⁻¹ • lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 0

private theorem firstSiteCLM_apply (f : QHilbert) :
    firstSiteCLM f = qSequence f 1 := by
  change (Real.sqrt (qWeight 0))⁻¹ * f 0 = qSequence f 1
  rw [qSequence_succ]
  simp only [div_eq_mul_inv, mul_comm]

/-- Even allowing every conductor, no unconditional atom sum is the constant. -/
theorem no_hasSum_qOne (c : ℕ → ℝ) :
    ¬ HasSum (fun j => c j • qResidue (j + 2)) qOne := by
  intro hc
  have hcoef := coefficient_eq_neg_moebius_of_hasSum c hc
  have hscalar := (firstSiteCLM.hasSum hc).summable
  have hinj : Function.Injective (fun p : Nat.Primes => p.val - 2) := by
    intro p q hpq
    change p.val - 2 = q.val - 2 at hpq
    apply Subtype.ext
    have hp := p.property.two_le
    have hq := q.property.two_le
    omega
  have hp := hscalar.comp_injective hinj
  have hpval (p : Nat.Primes) :
      firstSiteCLM (c (p.val - 2) • qResidue (p.val - 2 + 2)) =
        (1 : ℝ) / (p.val : ℝ) := by
    rw [map_smul, firstSiteCLM_apply, hcoef,
      Nat.sub_add_cancel p.property.two_le, qSequence_qResidue]
    simp [ArithmeticFunction.moebius_apply_prime p.property,
      residueFraction, Nat.mod_eq_of_lt p.property.one_lt]
  apply Nat.Primes.not_summable_one_div
  simpa only [Function.comp_def, hpval] using hp

/-- In particular the full masked squarefree family has no unconditional expansion of one. -/
theorem no_hasSum_squarefree_qOne (c : ℕ → ℝ) :
    ¬ HasSum (fun j => c j • ZetaTwoOptimizerStage.squarefreeAtom j) qOne := by
  intro hc
  let a : ℕ → ℝ := fun j => if Squarefree (j + 2) then c j else 0
  apply no_hasSum_qOne a
  convert hc using 1
  funext j
  by_cases hj : Squarefree (j + 2) <;>
    simp [a, ZetaTwoOptimizerStage.squarefreeAtom, hj]

/-- The same obstruction indexed directly by the squarefree conductors. -/
theorem no_hasSum_squarefree_subtype_qOne
    (c : {d : ℕ // 2 ≤ d ∧ Squarefree d} → ℝ) :
    ¬ HasSum (fun d => c d • qResidue d.val) qOne := by
  classical
  intro hc
  let a : ℕ → ℝ := fun i =>
    if h : Squarefree (i + 2) then c ⟨i + 2, by omega, h⟩ else 0
  let e : {d : ℕ // 2 ≤ d ∧ Squarefree d} → ℕ := fun d => d.val - 2
  have he : Function.Injective e := by
    intro d f hdf
    change d.val - 2 = f.val - 2 at hdf
    apply Subtype.ext
    have hd := d.property.1
    have hf := f.property.1
    omega
  apply no_hasSum_qOne a
  apply (he.hasSum_iff ?_).mp
  · convert hc using 1
    funext d
    dsimp only [Function.comp_def, e]
    have hd : d.val - 2 + 2 = d.val := Nat.sub_add_cancel d.property.1
    simp [a, hd, d.property.2]
  · intro i hi
    have hn : ¬Squarefree (i + 2) := by
      intro h
      apply hi
      exact ⟨⟨i + 2, by omega, h⟩, by simp [e]⟩
    simp [a, hn]

end RiemannResearch.RH.QUnconditionalAtomSeries
