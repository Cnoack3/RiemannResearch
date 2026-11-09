/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QReciprocalMellinCriterion
import RiemannResearch.RH.QMellinWitness
import RiemannResearch.RH.QMellinTail
import RiemannResearch.RH.QFiniteSupportDualCriterion
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.Analysis.MellinDifferenceBounds
import RiemannResearch.Analysis.WeightedComplexPairing
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Sharp-power reciprocal Mellin head bound

Source: continuation of the user's reciprocal-density research agenda,
8 November 2026. The proof uses the already established physical Mellin
series and first-difference estimate. The signed finite sum and the exact
head/tail cross term precede all norm estimates. No arithmetic estimate for
a legal approximating family's complete norm is supplied.

-/

noncomputable section
open scoped BigOperators Topology

namespace RiemannResearch.RH.QReciprocalMellinSharpHead
open ZetaTwoHilbert ZetaTwoProbability QShiftedReciprocal
open QFiniteSupportDualCriterion QMellinTransfer QMellinWitness
open QReciprocalMellinCriterion
open RiemannResearch.Analysis.Cesaro
open RiemannResearch.Analysis.WeightedPairing

/-- Undoing the reciprocal multiplier only inside the finite signed Mellin head. -/
def reciprocalMellinCoeff (s : ℂ) (n : ℕ) : ℂ :=
  (((n : ℝ) + 2 : ℝ) : ℂ) * mellinFirst s (n + 1)

/-- Exact signed finite-head formula; every arithmetic sign is retained. -/
theorem qMellin_head_reciprocal_sum (H : ℕ) (f : QHilbert)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    s * qMellin (finiteHead H f) s =
      ∑ n ∈ Finset.range H,
        reciprocalMellinCoeff s n * (qSequence (B f) (n + 1) : ℂ) := by
  rw [← (qMellin_hasSum (finiteHead H f) s hs).tsum_eq]
  rw [tsum_eq_sum (s := Finset.range H) (by
    intro n hn
    have hHn : H ≤ n := by simp only [Finset.mem_range] at hn; omega
    rw [qSequence_succ, finiteHead_apply_eq_zero H f n hHn, zero_div,
      Complex.ofReal_zero, mul_zero])]
  apply Finset.sum_congr rfl
  intro n hn
  have hnH : n < H := Finset.mem_range.mp hn
  have hd : (((n : ℝ) + 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (by positivity : (0 : ℝ) < (n : ℝ) + 2))
  rw [qSequence_succ, finiteHead_apply_of_lt H f n hnH,
    reciprocalMellinCoeff, qSequence_succ, B_apply]
  simp only [Complex.ofReal_div]
  field_simp [hd]
  <;> ring

/-- The exact reciprocal coefficient energy in the physical Q normalization. -/
theorem reciprocalMellinCoeff_energy_eq (s : ℂ) (n : ℕ) :
    ‖reciprocalMellinCoeff s n‖ ^ 2 / qWeight n =
      zetaTwo * ((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 2) ^ 2 *
        ‖mellinFirst s (n + 1)‖ ^ 2 := by
  rw [reciprocalMellinCoeff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 2), mul_pow]
  simp only [qWeight, positiveQWeight, Nat.cast_add, Nat.cast_one,
    div_eq_mul_inv, one_mul, inv_inv]
  ring

/-- The reciprocal dual-energy term has exponent 2-2 Re(s), with explicit constant. -/
theorem reciprocalMellinCoeff_energy_le (s : ℂ) (hs : 0 < s.re) (n : ℕ) :
    ‖reciprocalMellinCoeff s n‖ ^ 2 / qWeight n ≤
      4 * zetaTwo * ‖s‖ ^ 2 * ((n : ℝ) + 1) ^ (2 - 2 * s.re) := by
  have hZ := zetaTwo_pos
  have hx : 0 < (n : ℝ) + 1 := by positivity
  have hfirst := mellinFirst_norm_le s hs (n + 1) (Nat.succ_pos n)
  simp only [Nat.cast_add, Nat.cast_one] at hfirst
  have hfirst2 := pow_le_pow_left₀ (norm_nonneg _) hfirst 2
  rw [mul_pow] at hfirst2
  have hden : ((n : ℝ) + 2) ^ 2 ≤ 4 * ((n : ℝ) + 1) ^ 2 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hp : (((n : ℝ) + 1) ^ (-s.re - 1)) ^ 2 =
      ((n : ℝ) + 1) ^ (-2 * s.re - 2) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hx.le]
    congr 1
    ring
  have hpower : ((n : ℝ) + 1) ^ 4 * ((n : ℝ) + 1) ^ (-2 * s.re - 2) =
      ((n : ℝ) + 1) ^ (2 - 2 * s.re) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hx]
    congr 1
    norm_num
    <;> ring
  rw [reciprocalMellinCoeff_energy_eq]
  calc
    _ ≤ zetaTwo * ((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 2) ^ 2 *
        (‖s‖ ^ 2 * (((n : ℝ) + 1) ^ (-s.re - 1)) ^ 2) :=
      mul_le_mul_of_nonneg_left hfirst2 (by positivity)
    _ ≤ zetaTwo * ((n : ℝ) + 1) ^ 2 * (4 * ((n : ℝ) + 1) ^ 2) *
        (‖s‖ ^ 2 * (((n : ℝ) + 1) ^ (-s.re - 1)) ^ 2) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hden (by positivity)) (by positivity)
    _ = (4 * zetaTwo * ‖s‖ ^ 2) *
        (((n : ℝ) + 1) ^ 4 * ((n : ℝ) + 1) ^ (-2 * s.re - 2)) := by
      rw [hp]
      ring
    _ = _ := by rw [hpower]

/-- Full signed head energy is bounded without replacing Q by a periodic law. -/
theorem reciprocalMellinCoeff_head_energy_le
    (s : ℂ) (hs : 0 < s.re) (hs1 : s.re ≤ 1)
    (H : ℕ) (hH : 1 ≤ H) :
    (∑ n ∈ Finset.range H, ‖reciprocalMellinCoeff s n‖ ^ 2 / qWeight n) ≤
      4 * zetaTwo * ‖s‖ ^ 2 * (H : ℝ) ^ (3 - 2 * s.re) := by
  have hZ := zetaTwo_pos
  have hHR : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hconst : 0 ≤ 4 * zetaTwo * ‖s‖ ^ 2 := by positivity
  have he : (H : ℝ) * (H : ℝ) ^ (2 - 2 * s.re) =
      (H : ℝ) ^ (3 - 2 * s.re) := by
    nth_rewrite 1 [← Real.rpow_one (H : ℝ)]
    rw [← Real.rpow_add hHR]
    congr 1
    ring
  calc
    _ ≤ ∑ n ∈ Finset.range H, 4 * zetaTwo * ‖s‖ ^ 2 * (H : ℝ) ^ (2 - 2 * s.re) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnH : (n : ℝ) + 1 ≤ H := by
        exact_mod_cast Nat.succ_le_iff.mpr (Finset.mem_range.mp hn)
      exact (reciprocalMellinCoeff_energy_le s hs n).trans
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (by positivity) hnH (by linarith)) hconst)
    _ = (4 * zetaTwo * ‖s‖ ^ 2) * ((H : ℝ) * (H : ℝ) ^ (2 - 2 * s.re)) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    _ = _ := by rw [he]

/-- The sharp head power is 3-2 Re(s), improving the crude quadratic inverse-head cost. -/
theorem qMellin_head_norm_sq_le_reciprocal
    (f : QHilbert) (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s.re ≤ 1)
    (H : ℕ) (hH : 1 ≤ H) :
    ‖qMellin (finiteHead H f) s‖ ^ 2 ≤
      4 * zetaTwo * (H : ℝ) ^ (3 - 2 * s.re) * ‖B f‖ ^ 2 := by
  have hZ := zetaTwo_pos
  have hs0 : s ≠ 0 := by intro he; norm_num [he] at hs
  have hsn : 0 < ‖s‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hs0)
  have hcs := finite_pairing_norm_sq_le qWeight qWeight_pos
    (reciprocalMellinCoeff s) (fun n => (qSequence (B f) (n + 1) : ℂ)) (Finset.range H)
  rw [← qMellin_head_reciprocal_sum H f s hs] at hcs
  have henergy : (∑ n ∈ Finset.range H,
      qWeight n * ‖(qSequence (B f) (n + 1) : ℂ)‖ ^ 2) ≤ ‖B f‖ ^ 2 := by
    simp_rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, qWeight, qSequence_weighted_square]
    rw [qNorm_sq]
    exact Summable.sum_le_tsum (Finset.range H) (fun n _ => sq_nonneg _)
      (qCoordinate_square_summable (B f))
  have henergy0 : 0 ≤ ∑ n ∈ Finset.range H,
      qWeight n * ‖(qSequence (B f) (n + 1) : ℂ)‖ ^ 2 := by
    apply Finset.sum_nonneg
    intro n _
    exact mul_nonneg (qWeight_pos n).le (sq_nonneg _)
  have hb := hcs.trans (mul_le_mul
    (reciprocalMellinCoeff_head_energy_le s (by linarith) hs1 H hH)
    henergy henergy0 (by positivity))
  rw [norm_mul, mul_pow] at hb
  apply (mul_le_mul_iff_right₀ hsn).mp
  convert hb using 1 <;> ring

/-- Exact energy decomposition, retaining the signed Mellin head/tail cross term. -/
theorem qMellin_head_tail_energy_identity (H : ℕ) (f : QHilbert)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    ‖qMellin f s‖ ^ 2 = ‖qMellin (finiteHead H f) s‖ ^ 2 +
      ‖qMellin (f - finiteHead H f) s‖ ^ 2 +
      2 * inner ℝ (qMellin (finiteHead H f) s) (qMellin (f - finiteHead H f) s) := by
  rw [qMellin_head_tail_identity H f s hs]
  simpa only [add_assoc, add_comm, add_left_comm] using
    norm_add_sq_real (qMellin (finiteHead H f) s)
      (qMellin (f - finiteHead H f) s)

/-- Quantitative two-energy estimate with the entire unsmoothed physical tail retained. -/
theorem qMellin_norm_sq_le_sharp_reciprocal_split
    (f : QHilbert) (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s.re ≤ 1)
    (H : ℕ) (hH : 1 ≤ H) :
    ‖qMellin f s‖ ^ 2 ≤
      8 * zetaTwo * (H : ℝ) ^ (3 - 2 * s.re) * ‖B f‖ ^ 2 +
      (2 * zetaTwo / (2 * s.re - 1)) * (H : ℝ) ^ (1 - 2 * s.re) *
        ‖f - finiteHead H f‖ ^ 2 := by
  let h := finiteHead H f
  let t := f - h
  have htzero : ∀ k ≤ H, qSequence t k = 0 := by
    intro k hk
    cases k with
    | zero => exact qSequence_zero t
    | succ n =>
      have hn : n < H := by omega
      change (f n - finiteHead H f n) / Real.sqrt (qWeight n) = 0
      rw [finiteHead_apply_of_lt H f n hn, sub_self, zero_div]
  have hh := qMellin_head_norm_sq_le_reciprocal f s hs hs1 H hH
  have ht := qMellin_norm_sq_le_of_head_zero t s hs H hH htzero
  have htri : ‖qMellin f s‖ ≤ ‖qMellin h s‖ + ‖qMellin t s‖ := by
    rw [qMellin_head_tail_identity H f s hs]
    exact norm_add_le _ _
  have htri2 := pow_le_pow_left₀ (norm_nonneg _) htri 2
  have hsum : (‖qMellin h s‖ + ‖qMellin t s‖) ^ 2 ≤
      2 * (‖qMellin h s‖ ^ 2 + ‖qMellin t s‖ ^ 2) := by
    nlinarith [sq_nonneg (‖qMellin h s‖ - ‖qMellin t s‖)]
  calc
    _ ≤ 2 * (‖qMellin h s‖ ^ 2 + ‖qMellin t s‖ ^ 2) := htri2.trans hsum
    _ ≤ 2 * (4 * zetaTwo * (H : ℝ) ^ (3 - 2 * s.re) * ‖B f‖ ^ 2 +
        zetaTwo * ‖t‖ ^ 2 * ((H : ℝ) ^ (1 - 2 * s.re) / (2 * s.re - 1))) := by
      nlinarith only [hh, ht]
    _ = _ := by dsimp [t, h]; ring

/-- A finite complete-energy certificate excludes a zero with the sharper head power. -/
theorem zeta_ne_zero_of_sharp_reciprocal_budget
    (v : QHilbert) (hv : v ∈ QFullResidueProjection.legalSpan)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s.re < 1)
    (H : ℕ) (hH : 1 ≤ H)
    (hbudget : 8 * zetaTwo * (H : ℝ) ^ (3 - 2 * s.re) * ‖B (qOne - v)‖ ^ 2 +
      (2 * zetaTwo / (2 * s.re - 1)) * (H : ℝ) ^ (1 - 2 * s.re) *
        ‖(qOne - v) - finiteHead H (qOne - v)‖ ^ 2 < ‖(1 : ℂ) / s‖ ^ 2) :
    riemannZeta s ≠ 0 := by
  intro hz
  have hsne : s ≠ 1 := by intro he; norm_num [he] at hs1
  have hm : qMellin (qOne - v) s = 1 / s := by
    change qMellinContinuous s hs (qOne - v) = _
    rw [map_sub]
    change qMellin qOne s - qMellin v s = _
    rw [qMellin_one s hs, qMellin_legalSpan_zero v hv s hs hsne hz, sub_zero]
  have hb := qMellin_norm_sq_le_sharp_reciprocal_split (qOne - v) s hs hs1.le H hH
  rw [hm] at hb
  exact (not_lt_of_ge hb) hbudget

end RiemannResearch.RH.QReciprocalMellinSharpHead
