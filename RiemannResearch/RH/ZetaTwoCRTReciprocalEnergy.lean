/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ZetaTwoPolygammaResidues
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ParetoCRTReciprocalEnergy

/-!
# Sharp inverse-square comparison for periodic CRT errors

Source: user-provided CRT squarefree-span formulation, 13 October 2026.
For positive representatives a ≤ L, the complete Q residue weight lies between
1/(ζ(2)a²) and 1/a². The finite reciprocal energy and the full Q energy
therefore have equivalent boundedness and zero-limit criteria. Every
progression, including the representative L, is retained.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.ZetaTwoProbability
open Pareto ZetaTwoHilbert

theorem residueSquareWeight_lower {L a : ℝ} (hL : 0 < L) (ha : 0 < a) :
    1 / (zetaTwo * a ^ 2) ≤ residuePowerWeight 0 L a := by
  simpa [residuePowerWeight] using (residuePowerWeight_summable 0 hL ha).le_tsum
    0 (fun j _ => by have := zetaTwo_pos; positivity)

theorem residueSquareWeight_upper {L a : ℝ} (ha : 0 < a) (haL : a ≤ L) :
    residuePowerWeight 0 L a ≤ 1 / a ^ 2 := by
  have hL : 0 < L := lt_of_lt_of_le ha haL
  have hs : Summable (fun j : ℕ => positiveQWeight (j + 1)) :=
    (summable_nat_add_iff 1).mpr positiveQWeight_summable
  have ht : (∑' j : ℕ, positiveQWeight (j + 1)) = 1 := by
    have h := positiveQWeight_summable.tsum_eq_zero_add
    rw [positiveQWeight_tsum] at h
    simpa [positiveQWeight] using h.symm
  calc
    residuePowerWeight 0 L a ≤
        ∑' j : ℕ, positiveQWeight (j + 1) / a ^ 2 := by
      apply Summable.tsum_le_tsum _ (residuePowerWeight_summable 0 hL ha)
        (hs.div_const (a ^ 2))
      intro j
      have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      have hb : 0 < a * ((j : ℝ) + 1) := by positivity
      have he : a * ((j : ℝ) + 1) ≤ a + (j : ℝ) * L := by nlinarith
      have hd : zetaTwo * (a * ((j : ℝ) + 1)) ^ 2 ≤
          zetaTwo * (a + (j : ℝ) * L) ^ 2 :=
        mul_le_mul_of_nonneg_left ((sq_le_sq₀ hb.le (by positivity)).2 he) zetaTwo_pos.le
      calc
        1 / (zetaTwo * (a + (j : ℝ) * L) ^ (0 + 2)) ≤
            1 / (zetaTwo * (a * ((j : ℝ) + 1)) ^ 2) :=
          one_div_le_one_div_of_le (mul_pos zetaTwo_pos (sq_pos_of_pos hb)) hd
        _ = positiveQWeight (j + 1) / a ^ 2 := by
          simp [positiveQWeight, Nat.cast_add, Nat.cast_one, mul_pow,
            div_eq_mul_inv, mul_comm, mul_left_comm]
    _ = 1 / a ^ 2 := by rw [tsum_div_const, ht]

theorem periodic_qEnergy_comparison (L : ℕ) (hL : 0 < L)
    (R : ℕ → ℝ) {C : ℝ} (hR : ∀ n, |R n| ≤ C)
    (hp : ∀ n, R (n + L) = R n) :
    crtReciprocalEnergy L R / zetaTwo ≤ inversePowerMean 0 (fun n => R n ^ 2) ∧
      inversePowerMean 0 (fun n => R n ^ 2) ≤ crtReciprocalEnergy L R := by
  have hC : 0 ≤ C := (abs_nonneg (R 0)).trans (hR 0)
  have hsq : ∀ n, |R n ^ 2| ≤ C ^ 2 := by
    intro n
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [abs_le.mp (hR n)]
  rw [periodic_inversePowerMean 0 L hL _ hsq (by intro n; rw [hp])]
  constructor
  · rw [crtReciprocalEnergy, Finset.sum_div]
    apply Finset.sum_le_sum
    intro a _
    have hw := residueSquareWeight_lower (by exact_mod_cast hL : (0 : ℝ) < L)
      (by positivity : (0 : ℝ) < (a.val : ℝ) + 1)
    have hh := mul_le_mul_of_nonneg_right hw (sq_nonneg (R (a.val + 1)))
    convert hh using 1 <;> push_cast <;> simp [div_eq_mul_inv, mul_inv] <;> ring
  · apply Finset.sum_le_sum
    intro a _
    have hw := residueSquareWeight_upper (L := (L : ℝ))
      (by positivity : (0 : ℝ) < (a.val : ℝ) + 1)
      (by exact_mod_cast (show a.val + 1 ≤ L from a.isLt))
    have hh := mul_le_mul_of_nonneg_right hw (sq_nonneg (R (a.val + 1)))
    convert hh using 1 <;> push_cast <;> ring

/-- The arithmetic expectation is exactly the norm in the actual Q realization. -/
theorem qNorm_eq_inversePowerMean (f : QHilbert) :
    ‖f‖ ^ 2 = inversePowerMean 0 (fun n => qSequence f n ^ 2) := by
  rw [qNorm_weighted_sq, (qSequence_square_summable f).tsum_eq_zero_add]
  simp only [qSequence_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add]
  unfold inversePowerMean
  apply tsum_congr
  intro k
  simp [positiveQWeight, div_eq_mul_inv, mul_comm]

theorem periodic_qNorm_comparison (L : ℕ) (hL : 0 < L)
    (f : QHilbert) {C : ℝ} (hf : ∀ n, |qSequence f n| ≤ C)
    (hp : ∀ n, qSequence f (n + L) = qSequence f n) :
    crtReciprocalEnergy L (qSequence f) / zetaTwo ≤ ‖f‖ ^ 2 ∧
      ‖f‖ ^ 2 ≤ crtReciprocalEnergy L (qSequence f) := by
  rw [qNorm_eq_inversePowerMean]
  exact periodic_qEnergy_comparison L hL _ hf hp

/-- Converse comparison: bounded finite energies and bounded full Q energies
are equivalent, uniformly even when the periods vary. -/
theorem periodic_qEnergy_bddAbove_iff (L : ℕ → ℕ) (R : ℕ → ℕ → ℝ)
    (hL : ∀ j, 0 < L j)
    (hR : ∀ j, ∃ C : ℝ, ∀ n, |R j n| ≤ C)
    (hp : ∀ j n, R j (n + L j) = R j n) :
    BddAbove (Set.range (fun j => inversePowerMean 0 (fun n => R j n ^ 2))) ↔
      BddAbove (Set.range (fun j => crtReciprocalEnergy (L j) (R j))) := by
  have hcmp (j) := periodic_qEnergy_comparison (L j) (hL j) (R j)
    (hR j).choose_spec (hp j)
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C * zetaTwo, ?_⟩
    rintro e ⟨j, rfl⟩
    exact (div_le_iff₀ zetaTwo_pos).mp ((hcmp j).1.trans (hC ⟨j, rfl⟩))
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    rintro e ⟨j, rfl⟩
    exact (hcmp j).2.trans (hC ⟨j, rfl⟩)

/-- The same sharp comparison also gives the converse for vanishing energies. -/
theorem periodic_qEnergy_tendsto_zero_iff (L : ℕ → ℕ) (R : ℕ → ℕ → ℝ)
    (hL : ∀ j, 0 < L j)
    (hR : ∀ j, ∃ C : ℝ, ∀ n, |R j n| ≤ C)
    (hp : ∀ j n, R j (n + L j) = R j n) :
    Filter.Tendsto (fun j => inversePowerMean 0 (fun n => R j n ^ 2))
      Filter.atTop (nhds 0) ↔
    Filter.Tendsto (fun j => crtReciprocalEnergy (L j) (R j))
      Filter.atTop (nhds 0) := by
  have hcmp (j) := periodic_qEnergy_comparison (L j) (hL j) (R j)
    (hR j).choose_spec (hp j)
  constructor
  · intro h
    have hz := h.mul_const zetaTwo
    simp only [zero_mul] at hz
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hz
      (fun j => crtReciprocalEnergy_nonneg _ _)
      (fun j => (div_le_iff₀ zetaTwo_pos).mp (hcmp j).1)
  · intro h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
      (fun j => (div_nonneg (crtReciprocalEnergy_nonneg _ _) zetaTwo_pos.le).trans
        (hcmp j).1)
      (fun j => (hcmp j).2)

end RiemannResearch.RH.ZetaTwoProbability

namespace RiemannResearch.RH.ZetaTwoProbability
open Pareto ZetaTwoHilbert
noncomputable section

/-- The anchor at zero is not an extra probability atom. -/
theorem qError_eq_inversePowerMean (f : QHilbert) :
    ‖qOne - f‖ ^ 2 = inversePowerMean 0 (fun n => (1 - qSequence f n) ^ 2) := by
  rw [qNorm_eq_inversePowerMean]
  unfold inversePowerMean
  apply tsum_congr
  intro n
  have hsub := congrFun (qSequenceLinear.map_sub qOne f) (n + 1)
  change qSequence (qOne - f) (n + 1) =
    qSequence qOne (n + 1) - qSequence f (n + 1) at hsub
  dsimp only
  rw [hsub, qSequence_qOne]
  simp [qOneSequence]

theorem periodic_qError_comparison (L : ℕ) (hL : 0 < L)
    (f : QHilbert) {C : ℝ} (hf : ∀ n, |qSequence f n| ≤ C)
    (hp : ∀ n, qSequence f (n + L) = qSequence f n) :
    crtReciprocalEnergy L (fun n => 1 - qSequence f n) / zetaTwo ≤ ‖qOne - f‖ ^ 2 ∧
      ‖qOne - f‖ ^ 2 ≤ crtReciprocalEnergy L (fun n => 1 - qSequence f n) := by
  rw [qError_eq_inversePowerMean]
  apply periodic_qEnergy_comparison L hL
  · intro n
    calc
      |1 - qSequence f n| ≤ 1 + |qSequence f n| := by
        simpa [sub_eq_add_neg] using abs_add_le (1 : ℝ) (-qSequence f n)
      _ ≤ 1 + C := add_le_add le_rfl (hf n)
  · intro n
    rw [hp]

end
end RiemannResearch.RH.ZetaTwoProbability
