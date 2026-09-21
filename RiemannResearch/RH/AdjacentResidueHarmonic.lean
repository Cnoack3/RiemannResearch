/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.NearbyDilationGram
import Mathlib.NumberTheory.Harmonic.Defs

/-!
# Sharp harmonic control of consecutive raw residue differences

Source: independently derived continuation, 2026-09-21, using the existing
nearby-dilation finite partition. For U_d=R_d-R_(d+1), the complete energy
lies between H_d-d/(d+1) and H_d. The remainder is the literal infinite tail.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto

def adjacentResidueDifference (d j : ℕ) : ℝ := residue d j - residue (d+1) j

theorem adjacentResidueDifference_eq_nearby (d j : ℕ) :
    adjacentResidueDifference d j = nearbyDilationPacket (fun k => (k : ℝ)) d j := by
  have h₁ := Nat.mod_add_div j d
  have h₂ := Nat.mod_add_div j (d+1)
  have h₁R : (j%d : ℕ) + (d:ℝ)*(j/d : ℕ) = (j:ℝ) := by exact_mod_cast h₁
  have h₂R : (j%(d+1) : ℕ) + ((d:ℝ)+1)*(j/(d+1) : ℕ) = (j:ℝ) := by
    exact_mod_cast h₂
  unfold adjacentResidueDifference residue nearbyDilationPacket
  linarith

theorem adjacentResidueDifference_abs_le (d j : ℕ) (hd : 0 < d) :
    |adjacentResidueDifference d j| ≤ (d : ℝ) := by
  have h₁ : ((j % d : ℕ) : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast (Nat.mod_lt j hd).le
  have h₂ : ((j % (d+1) : ℕ) : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast (Nat.le_of_lt_succ (Nat.mod_lt j (by omega)))
  unfold adjacentResidueDifference residue
  exact abs_le.mpr ⟨by linarith [(Nat.cast_nonneg (j%d) : (0:ℝ) ≤ (j%d : ℕ))],
    by linarith [(Nat.cast_nonneg (j%(d+1)) : (0:ℝ) ≤ (j%(d+1) : ℕ))]⟩

private theorem reciprocal_difference_sum (n : ℕ) :
    (∑ j ∈ Finset.range n, (1 / ((j:ℝ)+1) - 1 / ((j:ℝ)+2))) =
      1 - 1 / ((n:ℝ)+1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- Exact first-common-period energy: all jumps and plateaus are retained. -/
theorem adjacentResidueDifference_prefix (d : ℕ) (hd : 0 < d) :
    (∑ j ∈ Finset.range (d*(d+1)), positiveWeight j *
      (adjacentResidueDifference d j)^2) =
        (harmonic d : ℝ) - (d:ℝ)/((d:ℝ)+1) := by
  have he := nearbyDilationGram_prefix
    (φ := fun k => (k:ℝ)) (ψ := fun k => (k:ℝ)) (by norm_num) (by norm_num) d
  simp only [← adjacentResidueDifference_eq_nearby, ← pow_two] at he
  rw [he, ← Finset.sum_add_distrib]
  have ht (j : ℕ) :
      nearbyDilationJumpTerm (fun k => (k:ℝ)) (fun k => (k:ℝ)) d j +
        nearbyDilationPlateauTerm (fun k => (k:ℝ)) (fun k => (k:ℝ)) d j =
      1 / ((j:ℝ)+1) + (1/(d:ℝ))*
        (1/((j:ℝ)+1)-1/((j:ℝ)+2)-1) := by
    unfold nearbyDilationJumpTerm nearbyDilationPlateauTerm
    push_cast
    have hd0 : (d:ℝ) ≠ 0 := by positivity
    have hd1 : (d:ℝ)+1 ≠ 0 := by positivity
    have hj1 : (j:ℝ)+1 ≠ 0 := by positivity
    have hj2 : (j:ℝ)+2 ≠ 0 := by positivity
    field_simp
    <;> ring
  simp_rw [ht]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
    reciprocal_difference_sum]
  have hH : (∑ j ∈ Finset.range d, 1/((j:ℝ)+1)) = (harmonic d : ℝ) := by
    simp [harmonic, one_div]
  rw [hH]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have hd0 : (d:ℝ) ≠ 0 := by positivity
  have hd1 : (d:ℝ)+1 ≠ 0 := by positivity
  field_simp
  <;> ring

def adjacentResidueRemainder (d : ℕ) : ℝ :=
  ∑' j : ℕ, positiveWeight (j+d*(d+1)) *
    (adjacentResidueDifference d (j+d*(d+1)))^2

theorem adjacentResidueDifference_summable (d : ℕ) (hd : 0 < d) :
    Summable (fun j => positiveWeight j * (adjacentResidueDifference d j)^2) := by
  simpa only [pow_two] using weighted_summable_of_bounded
    (bounded_product (adjacentResidueDifference_abs_le d · hd)
      (adjacentResidueDifference_abs_le d · hd))

theorem adjacentResidueRemainder_nonneg (d : ℕ) : 0 ≤ adjacentResidueRemainder d := by
  apply tsum_nonneg
  intro j
  exact mul_nonneg (positiveWeight_nonneg _) (sq_nonneg _)

theorem adjacentResidueRemainder_le (d : ℕ) (hd : 0 < d) :
    adjacentResidueRemainder d ≤ (d:ℝ)/((d:ℝ)+1) := by
  let L := d*(d+1)
  have hL : 0 < L := Nat.mul_pos hd (by omega)
  have hs := (summable_nat_add_iff L).mpr (adjacentResidueDifference_summable d hd)
  have hw := (summable_nat_add_iff L).mpr positiveWeight_summable
  have hb (j : ℕ) : positiveWeight (j+L) *
      (adjacentResidueDifference d (j+L))^2 ≤ positiveWeight (j+L)*(d:ℝ)^2 := by
    apply mul_le_mul_of_nonneg_left _ (positiveWeight_nonneg _)
    have h := (sq_le_sq₀ (abs_nonneg _) (Nat.cast_nonneg d)).mpr
      (adjacentResidueDifference_abs_le d (j+L) hd)
    simpa only [sq_abs] using h
  calc
    adjacentResidueRemainder d ≤ ∑' j, positiveWeight (j+L)*(d:ℝ)^2 :=
      hs.tsum_le_tsum hb (hw.mul_right _)
    _ = (d:ℝ)/((d:ℝ)+1) := by
      rw [tsum_mul_right, positiveWeight_tail_tsum L hL]
      dsimp [L]
      push_cast
      have hd0 : (d:ℝ) ≠ 0 := by positivity
      have hd1 : (d:ℝ)+1 ≠ 0 := by positivity
      field_simp
      <;> ring

/-- Exact energy with an explicit nonnegative bounded remainder. -/
theorem adjacentResidueDifference_energy_exact (d : ℕ) (hd : 0 < d) :
    (∑' j, positiveWeight j * (adjacentResidueDifference d j)^2) =
      (harmonic d : ℝ) - (d:ℝ)/((d:ℝ)+1) + adjacentResidueRemainder d := by
  have h := (adjacentResidueDifference_summable d hd).sum_add_tsum_nat_add (d*(d+1))
  rw [adjacentResidueDifference_prefix d hd] at h
  exact h.symm

theorem adjacentResidueDifference_energy_lower (d : ℕ) (hd : 0 < d) :
    (harmonic d : ℝ) - (d:ℝ)/((d:ℝ)+1) ≤
      ∑' j, positiveWeight j * (adjacentResidueDifference d j)^2 := by
  rw [adjacentResidueDifference_energy_exact d hd]
  exact le_add_of_nonneg_right (adjacentResidueRemainder_nonneg d)

theorem adjacentResidueDifference_energy_upper (d : ℕ) (hd : 0 < d) :
    (∑' j, positiveWeight j * (adjacentResidueDifference d j)^2) ≤
      (harmonic d : ℝ) := by
  rw [adjacentResidueDifference_energy_exact d hd]
  linarith [adjacentResidueRemainder_le d hd]

end RiemannResearch.RH.Pareto
