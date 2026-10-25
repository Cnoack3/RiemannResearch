/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Exact blocks of adjacent-conductor residue packets

Source: direct residue arithmetic from the user's signed-localization research
agenda. These finite formulas support the coefficient-response obstruction
described in ShrinkingHeadAndInverseResponse20261025.md. The complete L1 bound
and the infinite squarefree-pair argument in that note are not formalized here.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QAdjacentConductorPacket
open ZetaTwoHilbert

/-- Physical adjacent-conductor packet, with real rather than truncated subtraction. -/
def packet (d n : ℕ) : ℝ := ((n % d : ℕ) : ℝ) - ((n % (d + 1) : ℕ) : ℝ)

/-- Exact two-valued formula on each pre-period block. -/
theorem packet_block (d q r : ℕ) (hq : q ≤ d) (hr : r < d) :
    packet d (q * d + r) = if r < q then (q : ℝ) - d - 1 else (q : ℝ) := by
  have hmod : (q * d + r) % d = r := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt hr]
  unfold packet
  rw [hmod]
  by_cases hlt : r < q
  · rw [if_pos hlt]
    have hqpos : 1 ≤ q := by omega
    let s := d + 1 + r - q
    have hsplus : s + q = d + 1 + r := by
      dsimp [s]
      exact Nat.sub_add_cancel (by omega)
    have hslt : s < d + 1 := by omega
    have hdecomp : q * d + r = (q - 1) * (d + 1) + s := by
      calc
        q * d + r = ((q - 1) + 1) * d + r := by rw [Nat.sub_add_cancel hqpos]
        _ = (q - 1) * d + (d + r) := by ring
        _ = (q - 1) * d + ((q - 1) + s) := by congr 1; omega
        _ = (q - 1) * (d + 1) + s := by ring
    have hmod' : (q * d + r) % (d + 1) = s := by
      rw [hdecomp]
      simp [Nat.add_mod, Nat.mod_eq_of_lt hslt]
    rw [hmod']
    have hsR : (s : ℝ) + (q : ℝ) = (d : ℝ) + 1 + (r : ℝ) := by
      exact_mod_cast hsplus
    linarith
  · rw [if_neg hlt]
    have hqr : q ≤ r := by omega
    have hsplus : (r - q) + q = r := Nat.sub_add_cancel hqr
    have hslt : r - q < d + 1 := by omega
    have hdecomp : q * d + r = q * (d + 1) + (r - q) := by
      calc
        q * d + r = q * d + (q + (r - q)) := by congr 1; omega
        _ = q * (d + 1) + (r - q) := by ring
    have hmod' : (q * d + r) % (d + 1) = r - q := by
      rw [hdecomp]
      simp [Nat.add_mod, Nat.mod_eq_of_lt hslt]
    rw [hmod']
    have hsR : ((r - q : ℕ) : ℝ) + (q : ℝ) = (r : ℝ) := by
      exact_mod_cast hsplus
    linarith

/-- Below the first conductor the packet vanishes exactly. -/
theorem packet_eq_zero_of_lt (d n : ℕ) (hn : n < d) : packet d n = 0 := by
  simp [packet, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (show n < d + 1 by omega)]

/-- Its first nonzero physical site has size d. -/
theorem packet_first_site (d : ℕ) : packet d d = -(d : ℝ) := by
  simp [packet, Nat.mod_eq_of_lt (show d < d + 1 by omega)]

/-- Absolute block values, in a form suitable for exact summation. -/
theorem packet_block_abs (d q r : ℕ) (hq : q ≤ d) (hr : r < d) :
    |packet d (q * d + r)| =
      if r < q then (d : ℝ) + 1 - q else (q : ℝ) := by
  rw [packet_block d q r hq hr]
  by_cases h : r < q
  · rw [if_pos h, if_pos h, abs_of_nonpos]
    · ring
    · have hqR : (q : ℝ) ≤ d := by exact_mod_cast hq
      linarith
  · rw [if_neg h, if_neg h, abs_of_nonneg (Nat.cast_nonneg q)]

/-- Exact complete absolute sum on each pre-period block. -/
theorem packet_block_abs_sum (d q : ℕ) (hq : q ≤ d) :
    (∑ r ∈ Finset.range d, |packet d (q * d + r)|) =
      (q : ℝ) * (2 * (d : ℝ) + 1 - 2 * (q : ℝ)) := by
  have hdEq : q + (d - q) = d := by omega
  have hsplit := Finset.sum_range_add (fun r => |packet d (q * d + r)|) q (d - q)
  rw [hdEq] at hsplit
  have hlow : (∑ r ∈ Finset.range q, |packet d (q * d + r)|) =
      (q : ℝ) * ((d : ℝ) + 1 - q) := by
    calc
      _ = ∑ _r ∈ Finset.range q, ((d : ℝ) + 1 - q) := by
        apply Finset.sum_congr rfl
        intro r hr
        have hrq := Finset.mem_range.mp hr
        rw [packet_block_abs d q r hq (by omega), if_pos hrq]
      _ = _ := by simp; ring
  have hhigh : (∑ r ∈ Finset.range (d - q), |packet d (q * d + (q + r))|) =
      ((d - q : ℕ) : ℝ) * (q : ℝ) := by
    calc
      _ = ∑ _r ∈ Finset.range (d - q), (q : ℝ) := by
        apply Finset.sum_congr rfl
        intro r hr
        have hrd := Finset.mem_range.mp hr
        rw [packet_block_abs d q (q + r) hq (by omega), if_neg (by omega)]
      _ = _ := by simp
  rw [hsplit, hlow, hhigh, Nat.cast_sub hq]
  ring

/-- The unweighted absolute block mass has an explicit linear majorant. -/
theorem packet_block_abs_sum_le (d q : ℕ) (hq : q ≤ d) :
    (∑ r ∈ Finset.range d, |packet d (q * d + r)|) ≤
      2 * (q : ℝ) * (d : ℝ) := by
  rw [packet_block_abs_sum d q hq]
  by_cases hzero : q = 0
  · simp [hzero]
  · have hqR : (1 : ℝ) ≤ q := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hzero)
    nlinarith

/-- A complete physical bound, including the region beyond the pre-period blocks. -/
theorem packet_abs_le (d n : ℕ) (hd : 0 < d) : |packet d n| ≤ (d : ℝ) := by
  have ha : n % d ≤ d := (Nat.mod_lt n hd).le
  have hb : n % (d + 1) ≤ d := Nat.lt_succ_iff.mp (Nat.mod_lt n (Nat.succ_pos d))
  have haR : ((n % d : ℕ) : ℝ) ≤ d := by exact_mod_cast ha
  have hbR : ((n % (d + 1) : ℕ) : ℝ) ≤ d := by exact_mod_cast hb
  have han : (0 : ℝ) ≤ ((n % d : ℕ) : ℝ) := Nat.cast_nonneg _
  have hbn : (0 : ℝ) ≤ ((n % (d + 1) : ℕ) : ℝ) := Nat.cast_nonneg _
  unfold packet
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- A quantitative inverse-square L1 estimate on every pre-period block. -/
theorem packet_weighted_block_le (d q : ℕ) (hd : 0 < d) (hq0 : 0 < q)
    (hqd : q ≤ d) :
    (∑ r ∈ Finset.range d,
      |packet d (q * d + r)| / (((q * d + r : ℕ) : ℝ) ^ 2)) ≤
        2 / ((q : ℝ) * (d : ℝ)) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq0
  have hqdR : 0 < (q : ℝ) * (d : ℝ) := mul_pos hqR hdR
  calc
    _ ≤ ∑ r ∈ Finset.range d,
        |packet d (q * d + r)| / (((q : ℝ) * (d : ℝ)) ^ 2) := by
      apply Finset.sum_le_sum
      intro r hr
      apply div_le_div_of_nonneg_left (abs_nonneg _) (sq_pos_of_pos hqdR)
      have hn : (q : ℝ) * (d : ℝ) ≤ ((q * d + r : ℕ) : ℝ) := by
        push_cast
        exact le_add_of_nonneg_right (Nat.cast_nonneg r)
      nlinarith
    _ = (∑ r ∈ Finset.range d, |packet d (q * d + r)|) /
        (((q : ℝ) * (d : ℝ)) ^ 2) := by rw [Finset.sum_div]
    _ ≤ (2 * (q : ℝ) * (d : ℝ)) / (((q : ℝ) * (d : ℝ)) ^ 2) :=
      div_le_div_of_nonneg_right (packet_block_abs_sum_le d q hqd) (sq_nonneg _)
    _ = 2 / ((q : ℝ) * (d : ℝ)) := by
      field_simp [ne_of_gt hdR, ne_of_gt hqR]

/-- The packet equals the two-atom combination. It is squarefree-legal when both
conductors are squarefree. -/
theorem packet_eq_residue_combination (d n : ℕ) (hd : 0 < d) :
    packet d n =
      (d : ℝ) * qSequence (qResidue d) n -
      ((d + 1 : ℕ) : ℝ) * qSequence (qResidue (d + 1)) n := by
  rw [qSequence_qResidue, qSequence_qResidue]
  unfold packet ArithmeticCumulative.residueFraction
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hd1R : ((d + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [hdR, hd1R]

end RiemannResearch.RH.QAdjacentConductorPacket
