/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.RH.QInfiniteRecursiveCarry
import Mathlib.Tactic

/-! # The exact probability weights of a normalized carry chain

Source: C. Noack, *Prime trees, fractional parts, and zeta zeros* (2026),
equations (8) and (9). The signed tail and residue representation hold for
every normalized Bézout chain; positivity needs positive, nonincreasing
weights. A chain starting at conductor two with weight one has total mass one.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.CRTCarryArithmetic.NormalizedCarryChain
open ArithmeticCumulative

variable (s : NormalizedCarryChain)

def edgeMass (k : ℕ) : ℝ :=
  2 * (s.w k / (s.D k : ℝ) - s.w (k + 1) / (s.D (k + 1) : ℝ))

private theorem reciprocalWeight_summable : Summable (fun k => s.w k / (s.D k : ℝ)) := by
  apply Summable.of_norm_bounded (summable_geometric_of_lt_one (by norm_num : 0 ≤ (1/2 : ℝ)) (by norm_num))
  intro k
  have hd : (2 : ℝ) ^ k ≤ (s.D k : ℝ) := by exact_mod_cast s.modulus_growth k
  rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (Nat.cast_nonneg (s.D k) : (0 : ℝ) ≤ s.D k),
    div_pow, one_pow]
  exact (div_le_div_of_nonneg_right (s.weight_bound k) (Nat.cast_nonneg _)).trans
    (one_div_le_one_div_of_le (by positivity) hd)

/-- Every signed tail telescopes, including its exact remaining mass. -/
theorem edgeMass_tail (K : ℕ) :
    HasSum (fun k => s.edgeMass (k + K)) (2 * (s.w K / (s.D K : ℝ))) := by
  let t (k : ℕ) := s.w (k + K) / (s.D (k + K) : ℝ)
  have ht : Summable t := (summable_nat_add_iff K).mpr s.reciprocalWeight_summable
  have hn : Summable (fun k => t (k + 1)) := (summable_nat_add_iff 1).mpr ht
  have h := (ht.hasSum.sub hn.hasSum).mul_left 2
  have he : 2 * ((∑' k, t k) - ∑' k, t (k+1)) = 2 * t 0 := by
    rw [ht.tsum_eq_zero_add]
    ring
  rw [he] at h
  have hi (k : ℕ) : k + 1 + K = k + K + 1 := by omega
  simpa only [t, edgeMass, hi, Nat.zero_add] using h

theorem edgeMass_total (hD : s.D 0 = 2) (hw : s.w 0 = 1) : HasSum s.edgeMass 1 := by
  have h := s.edgeMass_tail 0
  norm_num [hD, hw] at h
  exact h

theorem edgeMass_pos (hw : ∀ k, 0 < s.w k) (hmono : ∀ k, s.w (k+1) ≤ s.w k) (k : ℕ) :
    0 < s.edgeMass k := by
  have hD : 0 < s.D k :=
    (pow_pos (by decide : 0 < (2 : ℕ)) k).trans_le (s.modulus_growth k)
  have hlt : s.D k < s.D (k+1) := by
    rw [s.next]
    simpa using Nat.mul_lt_mul_of_pos_left (show 1 < s.p k from s.radix_ge k) hD
  have hDr : (0 : ℝ) < s.D k := by exact_mod_cast hD
  have hDnext : (s.D k : ℝ) < s.D (k+1) := by exact_mod_cast hlt
  unfold edgeMass
  exact mul_pos (by norm_num) (sub_pos.mpr ((div_lt_div_iff₀ (hDr.trans hDnext) hDr).mpr
    ((mul_le_mul_of_nonneg_right (hmono k) hDr.le).trans_lt
      (mul_lt_mul_of_pos_left hDnext (hw k)))))

/-- The signed integral of the least remainder under the edge masses. -/
theorem carrySum_eq_residue_average (n : ℕ) :
    (∑' k, s.carryTerm n k) =
      s.parentTerm n 0 - (1 / 2 : ℝ) * ∑' k, s.edgeMass k * ((n % s.p k : ℕ) : ℝ) := by
  have he (k : ℕ) : s.edgeMass k * ((n % s.p k : ℕ) : ℝ) = (-2 : ℝ) * s.primeTerm n k := by
    rw [s.primeTerm_eq]
    unfold edgeMass
    ring
  simp_rw [he]
  rw [tsum_mul_left, (s.infinite_carry_expansion n).2.2]
  ring

/-- The entire infinite carry signal takes value minus one at the physical
site two for any normalized chain beginning at two with all odd radices. -/
theorem carrySum_at_two (hD : s.D 0 = 2) (hw : s.w 0 = 1) (hp : ∀ k, 2 < s.p k) :
    (∑' k, s.carryTerm 2 k) = -1 := by
  rw [s.carrySum_eq_residue_average]
  have hmod (k : ℕ) : 2 % s.p k = 2 := Nat.mod_eq_of_lt (hp k)
  simp only [hmod, Nat.cast_ofNat, tsum_mul_right]
  rw [(s.edgeMass_total hD hw).tsum_eq]
  norm_num [parentTerm, residueFraction, hD, hw]

end RiemannResearch.RH.CRTCarryArithmetic.NormalizedCarryChain
