/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QMobiusExactHead
import RiemannResearch.RH.QResidueHeadSpace
import RiemannResearch.RH.ZetaTwoParetoTransfer
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Primorial

/-!
# Concrete canonical competitors in finite squarefree primorial dictionaries

Source: the user's CRT/Pareto optimizer continuation, 28 October 2026.
The canonical Möbius witness supplies an actual feasible competitor whenever
its normalization conductor is squarefree. This includes every prime anchor.
The zero-head tangent is the actual intersection of the finite dictionary
with the physical head kernel, not an assumed abstract feasible space.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QSquarefreeCanonicalFeasibility
open ZetaTwoHilbert QSquarefreeLatticePackets QResidueHeadSpace
open ZetaTwoParetoTransfer

theorem exactHead_mem_primorialStage (H : ℕ) (hsf : Squarefree (H + 1)) :
    QMobiusExactHead.exactHead H ∈ divisorStage (primorial (H + 1)) := by
  have hres (d : ℕ) (hdH : d ≤ H + 1) (hs : Squarefree d) :
      qResidue d ∈ divisorStage (primorial (H + 1)) := by
    exact Submodule.subset_span
      ⟨d, dvd_trans hs.dvd_primorial (primorial_dvd_primorial hdH), rfl⟩
  unfold QMobiusExactHead.exactHead
  apply Submodule.add_mem
  · apply Submodule.neg_mem
    apply Submodule.sum_mem
    intro d hd
    by_cases hs : Squarefree d
    · exact Submodule.smul_mem _ _
        (hres d (by have := (Finset.mem_Icc.mp hd).2; omega) hs)
    · have hm : ArithmeticFunction.moebius d = 0 :=
        ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs
      simp only [hm, Int.cast_zero, zero_smul]
      exact Submodule.zero_mem _
  · exact Submodule.smul_mem _ _ (hres (H + 1) le_rfl hsf)

def tangent (H : ℕ) : Submodule ℝ QHilbert :=
  divisorStage (primorial (H + 1)) ⊓ headNull H

/-- The literal tangent is contained in a finite divisor dictionary. -/
instance tangent_finiteDimensional (H : ℕ) : FiniteDimensional ℝ (tangent H) := by
  let s := (primorial (H + 1)).divisors
  letI : FiniteDimensional ℝ (dictionary s) := by
    change FiniteDimensional ℝ (Submodule.span ℝ (Set.range fun d : s => qResidue (d : ℕ)))
    exact FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
  have hstage : divisorStage (primorial (H + 1)) ≤ dictionary s := by
    apply Submodule.span_le.mpr
    rintro f ⟨d, hd, rfl⟩
    exact Submodule.subset_span
      ⟨⟨d, Nat.mem_divisors.mpr ⟨hd, ne_of_gt (primorial_pos _)⟩⟩, rfl⟩
  exact Submodule.finiteDimensional_of_le
    (show tangent H ≤ dictionary s from fun f hf => hstage hf.1)

/-- The corresponding Pareto tangent is finite dimensional as the image of
the same finite-dimensional physical tangent. -/
instance pareto_tangent_finiteDimensional (H : ℕ) :
    FiniteDimensional ℝ ((tangent H).map toParetoLinear) := by
  let T : tangent H →ₗ[ℝ] ((tangent H).map toParetoLinear) :=
    { toFun := fun u => ⟨toParetoLinear u, ⟨(u : QHilbert), u.property, rfl⟩⟩
      map_add' := by
        intro u v
        apply Subtype.ext
        exact toParetoLinear.map_add (u : QHilbert) (v : QHilbert)
      map_smul' := by
        intro c u
        apply Subtype.ext
        exact toParetoLinear.map_smul c (u : QHilbert) }
  have hs : Function.Surjective T := by
    intro v
    obtain ⟨u, hu, he⟩ := v.property
    refine ⟨⟨u, hu⟩, ?_⟩
    apply Subtype.ext
    exact he
  exact FiniteDimensional.of_surjective T hs

theorem tangent_coordinates_zero (H : ℕ) (u : QHilbert) (hu : u ∈ tangent H)
    (n : ℕ) (hn : n < H) : u n = 0 := by
  have he := hu.2 (n + 1) (by omega) (by omega)
  rw [qSequence_succ] at he
  exact (div_eq_zero_iff.mp he).resolve_right
    (ne_of_gt (Real.sqrt_pos.mpr (qWeight_pos n)))

/-- Any two feasible vectors differ by the literal zero-head tangent. -/
theorem sub_mem_tangent (H : ℕ) (F G : QHilbert)
    (hF : F ∈ divisorStage (primorial (H + 1)))
    (hG : G ∈ divisorStage (primorial (H + 1)))
    (hFhead : ∀ n, 0 < n → n ≤ H → qSequence F n = 1)
    (hGhead : ∀ n, 0 < n → n ≤ H → qSequence G n = 1) :
    F - G ∈ tangent H := by
  refine ⟨Submodule.sub_mem _ hF hG, ?_⟩
  intro n hn hnH
  change qSequenceLinear (F - G) n = 0
  simp only [map_sub, Pi.sub_apply]
  change qSequence F n - qSequence G n = 0
  rw [hFhead n hn hnH, hGhead n hn hnH, sub_self]

/-- The explicit Möbius vector is a competitor for every feasible minimizer. -/
theorem exactHead_sub_mem_tangent (H : ℕ) (hsf : Squarefree (H + 1))
    (F : QHilbert) (hF : F ∈ divisorStage (primorial (H + 1)))
    (hFhead : ∀ n, 0 < n → n ≤ H → qSequence F n = 1) :
    QMobiusExactHead.exactHead H - F ∈ tangent H :=
  sub_mem_tangent H _ _ (exactHead_mem_primorialStage H hsf) hF
    (QMobiusExactHead.exactHead_exact H) hFhead

theorem prime_anchor_feasible (p : ℕ) (hp : Nat.Prime p) :
    QMobiusExactHead.exactHead (p - 1) ∈ divisorStage (primorial p) ∧
      ∀ n, 0 < n → n < p → qSequence (QMobiusExactHead.exactHead (p - 1)) n = 1 := by
  have he : p - 1 + 1 = p := by have := hp.two_le; omega
  constructor
  · simpa only [he] using
      exactHead_mem_primorialStage (p - 1) (he.symm ▸ hp.squarefree)
  · intro n hn hnp
    exact QMobiusExactHead.exactHead_exact (p - 1) n hn (by omega)

end RiemannResearch.RH.QSquarefreeCanonicalFeasibility
