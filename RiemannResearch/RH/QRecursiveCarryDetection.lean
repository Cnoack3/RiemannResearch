/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QCompositeCarryDetection
import RiemannResearch.RH.QCRTCarry

/-! # Composite charges of recursive, two-factor CRT carries

An actual floor carry joining a parent conductor to a new prime has two
possible composite charges. The finite tree formula collects both at once.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QRecursiveCarryDetection
open Pareto ZetaTwoHilbert ZetaTwoParetoTransfer QCompositeCarryDetection QCRTCarry

private theorem charge_apply (D : ℕ) (f : QHilbert) :
    ((mobiusDifferenceCLM D).comp toParetoCLM) f = mobiusDifference D (qSequence f) := by
  simp

/-- The new composite receives unit charge and the parent conductor loses
its signed CRT multiplier. The new prime is invisible at a composite D. -/
theorem charge_recursive_carry (D r p : ℕ) (u v t : ℤ)
    (hD : 1 < D) (hn : ¬D.Prime) (hr : 0 < r) (hp : p.Prime)
    (hcrt : (u : ℝ) * (p : ℝ) + (v : ℝ) * (r : ℝ) =
      1 + (t : ℝ) * (r : ℝ) * (p : ℝ)) :
    mobiusDifference D (qSequence (qCarry r p u v)) =
      (if D = r * p then 1 else 0) - (if D = r then (u : ℝ) else 0) := by
  classical
  let L := (mobiusDifferenceCLM D).comp toParetoCLM
  have he (f : QHilbert) : L f = mobiusDifference D (qSequence f) := charge_apply D f
  have hne : D ≠ p := fun h => hn (h.symm ▸ hp)
  rw [qCarry_eq_linear r p u v t hr hp.pos hcrt, ← he, map_sub, map_add, map_smul, map_smul]
  simp only [smul_eq_mul, he, charge_residue D r hD hr, charge_residue D p hD hp.pos,
    charge_residue D (r * p) hD (Nat.mul_pos hr hp.pos), if_neg hne, mul_zero, add_zero]
  split_ifs <;> ring

/-- For a finite set of recursive edges indexed by their distinct target
conductors, the residual charge is the edge weight at D minus the signed
weights of every child of D. No choice of branching or order is assumed. -/
theorem charge_recursive_carry_sum (D : ℕ) (hD : 1 < D) (hn : ¬D.Prime)
    (S : Finset ℕ) (r p : ℕ → ℕ) (u v t : ℕ → ℤ) (w : ℕ → ℝ)
    (hr : ∀ m ∈ S, 0 < r m) (hp : ∀ m ∈ S, (p m).Prime)
    (hm : ∀ m ∈ S, r m * p m = m)
    (hcrt : ∀ m ∈ S, (u m : ℝ) * (p m : ℝ) + (v m : ℝ) * (r m : ℝ) =
      1 + (t m : ℝ) * (r m : ℝ) * (p m : ℝ)) :
    mobiusDifference D (qSequence (∑ m ∈ S, w m • qCarry (r m) (p m) (u m) (v m))) =
      (if D ∈ S then w D else 0) - ∑ m ∈ S.filter (fun m => r m = D), w m * (u m : ℝ) := by
  classical
  let L := (mobiusDifferenceCLM D).comp toParetoCLM
  have he (f : QHilbert) : L f = mobiusDifference D (qSequence f) := charge_apply D f
  rw [← he, map_sum]
  simp only [map_smul, smul_eq_mul]
  calc
    _ = ∑ m ∈ S, ((if m = D then w D else 0) -
        (if r m = D then w m * (u m : ℝ) else 0)) := by
      apply Finset.sum_congr rfl
      intro m hmem
      rw [he, charge_recursive_carry D (r m) (p m) (u m) (v m) (t m) hD hn
        (hr m hmem) (hp m hmem) (hcrt m hmem), hm m hmem]
      by_cases h : m = D
      · subst m
        by_cases hj : r D = D
        · simp [hj, mul_sub]
        · simp [hj, Ne.symm hj]
      · by_cases hj : r m = D
        · simp [h, Ne.symm h, hj]
        · simp [h, Ne.symm h, hj, Ne.symm hj]
    _ = _ := by rw [Finset.sum_sub_distrib, Finset.sum_filter]; simp

end RiemannResearch.RH.QRecursiveCarryDetection
