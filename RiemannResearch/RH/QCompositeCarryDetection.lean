/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QPrimeCRTCarries
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.MobiusHilbertCoordinates

/-! # Detecting a composite CRT carry at its own conductor

The physical Möbius charge at a composite conductor kills every prime atom.
It evaluates to one on a prime CRT carry with that conductor and to zero on
every other carry. It also commutes with pointwise limits at fixed conductor.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.QCompositeCarryDetection
open Pareto ZetaTwoHilbert ZetaTwoParetoTransfer QPrimeCRTCarries

private theorem charge_apply (D : ℕ) (f : QHilbert) :
    ((mobiusDifferenceCLM D).comp toParetoCLM) f = mobiusDifference D (qSequence f) := by
  simp

/-- Sign convention for the physical Möbius charge of a residue atom. -/
theorem charge_residue (D m : ℕ) (hD : 1 < D) (hm : 0 < m) :
    mobiusDifference D (qSequence (qResidue m)) = if D = m then -1 else 0 := by
  have h := mobius_normalizedResidue D m hD hm
  simpa only [mobiusDifferenceCLM_apply, normalizedResidueHilbert_sequence, qSequence_qResidue]
    using h

/-- The composite charge detects precisely the carry's target conductor. -/
theorem charge_carry {ι : Type*} [Fintype ι] (D m : ℕ)
    (p : ι → ℕ) (a : ι → ℤ) (hD : 1 < D) (hn : ¬D.Prime) (hm : 0 < m)
    (hp : ∀ i, (p i).Prime) :
    mobiusDifference D (qSequence (carryVector m p a)) = if D = m then 1 else 0 := by
  classical
  let L := (mobiusDifferenceCLM D).comp toParetoCLM
  have he (f : QHilbert) : L f = mobiusDifference D (qSequence f) := charge_apply D f
  have hp0 (i : ι) : L (qResidue (p i)) = 0 := by
    have hne : D ≠ p i := fun ht => hn (ht.symm ▸ hp i)
    rw [he, charge_residue D (p i) hD (hp i).pos, if_neg hne]
  rw [← he, carryVector, map_sub, map_sum]
  simp only [map_smul, smul_eq_mul, hp0, mul_zero, Finset.sum_const_zero, zero_sub]
  rw [he, charge_residue D m hD hm]
  by_cases hd : D = m <;> simp [hd]

/-- Carry representatives and their integer coefficients may be chosen
independently at every conductor. -/
theorem charge_carry_sum (D : ℕ) (hD : 1 < D) (hn : ¬D.Prime)
    (S : Finset ℕ) (hm : ∀ m ∈ S, 0 < m) (c : ℕ → ℝ)
    (a : (m : ℕ) → m.primeFactors → ℤ) :
    mobiusDifference D (qSequence
      (∑ m ∈ S, c m • carryVector m (fun p : m.primeFactors => p.val) (a m))) =
        if D ∈ S then c D else 0 := by
  classical
  let L := (mobiusDifferenceCLM D).comp toParetoCLM
  have he (f : QHilbert) : L f = mobiusDifference D (qSequence f) := charge_apply D f
  rw [← he, map_sum]
  simp only [map_smul, smul_eq_mul]
  simp_rw [he]
  calc
    _ = ∑ m ∈ S, if m = D then c D else 0 := by
      apply Finset.sum_congr rfl
      intro m hmem
      rw [charge_carry D m _ (a m) hD hn (hm m hmem)
        (fun p => Nat.prime_of_mem_primeFactors p.property)]
      by_cases ht : D = m
      · subst m
        simp
      · simp [ht, Ne.symm ht]
    _ = _ := by simp

/-- Fixed-conductor detection requires convergence at only the finitely many
sites k and k-1 for k dividing the detecting conductor. -/
theorem charge_tendsto_of_sites (D : ℕ) (f : ℕ → ℕ → ℝ) (g : ℕ → ℝ)
    (h : ∀ k ∈ D.divisors, Tendsto (fun j => f j k) atTop (𝓝 (g k)) ∧
      Tendsto (fun j => f j (k - 1)) atTop (𝓝 (g (k - 1)))) :
    Tendsto (fun j => mobiusDifference D (f j)) atTop (𝓝 (mobiusDifference D g)) := by
  unfold mobiusDifference
  apply tendsto_finsetSum
  intro k hk
  exact ((h k hk).1.sub (h k hk).2).const_mul _

end RiemannResearch.RH.QCompositeCarryDetection
