/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QMellinTail
import RiemannResearch.RH.QFiniteSupportDualCriterion
import RiemannResearch.RH.QReciprocalFiniteHead
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.QFullResidueProjection
import RiemannResearch.RH.RiemannHypothesisRightHalfStrip
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Reciprocal error and subpower energy imply RH

Source: user-provided Reciprocal_Density_CRT_Nyman_Beurling_2026-11-08.pdf,
Sections 8 and 10, and the continuation discussion of 8 November 2026.
The argument uses the existing physical Mellin tail estimate and zeta-zero
annihilation. The analytic inequality is unconditional; the final arithmetic
norm-growth and reciprocal-error budgets remain explicit Open providers.

No arithmetic growth provider is asserted by this module.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.QReciprocalMellinCriterion
open ZetaTwoHilbert ZetaTwoProbability QShiftedReciprocal
open QFiniteSupportDualCriterion QMellinTransfer QReciprocalFiniteHead

/-- The exact linear decomposition precedes the following norm estimate. -/
theorem qMellin_head_tail_identity (N : ℕ) (f : QHilbert)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    qMellin f s = qMellin (finiteHead N f) s +
      qMellin (f - finiteHead N f) s := by
  change qMellinContinuous s hs f = qMellinContinuous s hs (finiteHead N f) +
    qMellinContinuous s hs (f - finiteHead N f)
  rw [map_sub]
  ring

/-- A complete-norm estimate retaining both reciprocal head error and the
entire unsmoothed tail. Its head factor is deliberately elementary. -/
theorem qMellin_norm_sq_le_reciprocal_split
    (f : QHilbert) (s : ℂ) (hs : (1 / 2 : ℝ) < s.re)
    (N : ℕ) (hN : 1 ≤ N) :
    ‖qMellin f s‖ ^ 2 ≤ (2 * zetaTwo / (2 * s.re - 1)) *
      (((N : ℝ) + 1) ^ 2 * ‖B f‖ ^ 2 +
        (N : ℝ) ^ (1 - 2 * s.re) * ‖f‖ ^ 2) := by
  let h := finiteHead N f
  let t := f - h
  have hd : 0 < 2 * s.re - 1 := by linarith
  have htzero : ∀ k ≤ N, qSequence t k = 0 := by
    intro k hk
    cases k with
    | zero => exact qSequence_zero t
    | succ n =>
      have hn : n < N := by omega
      change (f n - finiteHead N f n) / Real.sqrt (qWeight n) = 0
      rw [finiteHead_apply_of_lt N f n hn, sub_self, zero_div]
  have htailnorm : ‖t‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    have he := finiteHead_norm_sq_split N f
    change ‖f‖ ^ 2 = ‖h‖ ^ 2 + ‖t‖ ^ 2 at he
    nlinarith [sq_nonneg ‖h‖]
  have hh := qMellin_norm_sq_le h s hs
  have hh' : ‖qMellin h s‖ ^ 2 ≤
      zetaTwo * (((N : ℝ) + 1) ^ 2 * ‖B f‖ ^ 2) / (2 * s.re - 1) :=
    hh.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (finiteHead_norm_sq_le_reciprocal N f) zetaTwo_pos.le) hd.le)
  have ht := qMellin_norm_sq_le_of_head_zero t s hs N hN htzero
  have ht' : ‖qMellin t s‖ ^ 2 ≤ zetaTwo * ‖f‖ ^ 2 *
      ((N : ℝ) ^ (1 - 2 * s.re) / (2 * s.re - 1)) :=
    ht.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left htailnorm zetaTwo_pos.le) (by positivity))
  have htri : ‖qMellin f s‖ ≤ ‖qMellin h s‖ + ‖qMellin t s‖ := by
    rw [qMellin_head_tail_identity N f s hs]
    exact norm_add_le _ _
  have htri2 := pow_le_pow_left₀ (norm_nonneg _) htri 2
  have hsum : (‖qMellin h s‖ + ‖qMellin t s‖) ^ 2 ≤
      2 * (‖qMellin h s‖ ^ 2 + ‖qMellin t s‖ ^ 2) := by
    nlinarith [sq_nonneg (‖qMellin h s‖ - ‖qMellin t s‖)]
  calc
    _ ≤ 2 * (‖qMellin h s‖ ^ 2 + ‖qMellin t s‖ ^ 2) := htri2.trans hsum
    _ ≤ 2 * (zetaTwo * (((N : ℝ) + 1) ^ 2 * ‖B f‖ ^ 2) / (2 * s.re - 1) +
        zetaTwo * ‖f‖ ^ 2 * ((N : ℝ) ^ (1 - 2 * s.re) / (2 * s.re - 1))) := by
      nlinarith only [hh', ht']
    _ = _ := by ring

/-- Every finite full-conductor legal vector has the actual zero signature. -/
theorem qMellin_legalSpan_zero (v : QHilbert)
    (hv : v ∈ QFullResidueProjection.legalSpan)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) : qMellin v s = 0 := by
  have hle : QFullResidueProjection.legalSpan ≤ (qMellinContinuous s hs).ker := by
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    change qMellin (qResidue (i + 2)) s = 0
    exact qMellin_residue_zero (i + 2) (by omega) s (by linarith) hs1 hz
  exact hle hv

/-- One finite reciprocal/full-energy certificate excludes a zero at s.
Both energies are complete Q energies, not truncated numerical sums. -/
theorem zeta_ne_zero_of_reciprocal_budget
    (v : QHilbert) (hv : v ∈ QFullResidueProjection.legalSpan)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (N : ℕ) (hN : 1 ≤ N)
    (hbudget : (2 * zetaTwo / (2 * s.re - 1)) *
      (((N : ℝ) + 1) ^ 2 * ‖B (qOne - v)‖ ^ 2 +
        (N : ℝ) ^ (1 - 2 * s.re) * ‖qOne - v‖ ^ 2) < ‖(1 : ℂ) / s‖ ^ 2) :
    riemannZeta s ≠ 0 := by
  intro hz
  have hm : qMellin (qOne - v) s = 1 / s := by
    change qMellinContinuous s hs (qOne - v) = _
    rw [map_sub]
    change qMellin qOne s - qMellin v s = _
    rw [qMellin_one s hs, qMellin_legalSpan_zero v hv s hs hs1 hz, sub_zero]
  have hb := qMellin_norm_sq_le_reciprocal_split (qOne - v) s hs N hN
  rw [hm] at hb
  exact (not_lt_of_ge hb) hbudget

/-- Conditional RH criterion with an arbitrary moving physical head.
The full reciprocal error and full residual energy remain explicit budgets. -/
theorem riemannHypothesis_of_variable_head_subpower_residual
    (v : ℕ → QHilbert) (hv : ∀ j, v j ∈ QFullResidueProjection.legalSpan)
    (H : ℕ → ℕ) (hH : ∀ j, 1 ≤ H j)
    (herr : Tendsto (fun j => ((H j : ℝ) + 1) ^ 2 * ‖B (qOne - v j)‖ ^ 2)
      atTop (𝓝 0))
    (hgrowth : ∀ a : ℝ, 0 < a → Tendsto
      (fun j => (H j : ℝ) ^ (-a) * ‖qOne - v j‖ ^ 2) atTop (𝓝 0)) :
    RiemannHypothesis := by
  apply RiemannResearch.RH.riemannHypothesis_iff_right_half_strip_zero_free.mpr
  intro s hs hs1 hz
  have hs0 : s ≠ 0 := by intro he; norm_num [he] at hs
  have hsne : s ≠ 1 := by intro he; norm_num [he] at hs1
  have hm (j : ℕ) : qMellin (qOne - v j) s = 1 / s := by
    change qMellinContinuous s hs (qOne - v j) = _
    rw [map_sub]
    change qMellin qOne s - qMellin (v j) s = _
    rw [qMellin_one s hs, qMellin_legalSpan_zero (v j) (hv j) s hs hsne hz, sub_zero]
  have htail := hgrowth (2 * s.re - 1) (by linarith)
  have ht : Tendsto (fun j => (2 * zetaTwo / (2 * s.re - 1)) *
      (((H j : ℝ) + 1) ^ 2 * ‖B (qOne - v j)‖ ^ 2 +
        (H j : ℝ) ^ (1 - 2 * s.re) * ‖qOne - v j‖ ^ 2)) atTop (𝓝 0) := by
    have he : -(2 * s.re - 1) = 1 - 2 * s.re := by ring
    simpa only [he, add_zero, mul_zero] using
      (herr.add htail).const_mul (2 * zetaTwo / (2 * s.re - 1))
  have hp : 0 < ‖(1 : ℂ) / s‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (div_ne_zero one_ne_zero hs0))
  obtain ⟨j, hj⟩ := (ht.eventually (gt_mem_nhds hp)).exists
  have hb := qMellin_norm_sq_le_reciprocal_split (qOne - v j) s hs (H j) (hH j)
  rw [hm j] at hb
  exact (not_lt_of_ge hb) hj

/-- Variable-head formulation allowing subpower growth of the legal norm.
In particular H_j=floor(sqrt j) is compatible with reciprocal error O(1/j). -/
theorem riemannHypothesis_of_variable_head_subpower_norm
    (v : ℕ → QHilbert) (hv : ∀ j, v j ∈ QFullResidueProjection.legalSpan)
    (H : ℕ → ℕ) (hH : ∀ j, 1 ≤ H j) (hHtop : Tendsto H atTop atTop)
    (herr : Tendsto (fun j => ((H j : ℝ) + 1) ^ 2 * ‖B (qOne - v j)‖ ^ 2)
      atTop (𝓝 0))
    (hgrowth : ∀ a : ℝ, 0 < a → Tendsto
      (fun j => (H j : ℝ) ^ (-a) * ‖v j‖ ^ 2) atTop (𝓝 0)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_variable_head_subpower_residual v hv H hH herr
  intro a ha
  have hbase : Tendsto (fun j : ℕ => (H j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hHtop
  have hp : Tendsto (fun j : ℕ => (H j : ℝ) ^ (-a)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop ha).comp hbase
  have hu : Tendsto (fun j =>
      2 * (H j : ℝ) ^ (-a) + 2 * ((H j : ℝ) ^ (-a) * ‖v j‖ ^ 2))
      atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using (hp.const_mul 2).add ((hgrowth a ha).const_mul 2)
  apply squeeze_zero (fun j => by positivity) ?_ hu
  intro j
  have htri : ‖qOne - v j‖ ≤ 1 + ‖v j‖ := by
    simpa only [qOne_norm] using norm_sub_le qOne (v j)
  have htri2 := pow_le_pow_left₀ (norm_nonneg _) htri 2
  have hsq : ‖qOne - v j‖ ^ 2 ≤ 2 + 2 * ‖v j‖ ^ 2 := by
    nlinarith [sq_nonneg (1 - ‖v j‖)]
  have h := mul_le_mul_of_nonneg_left hsq (Real.rpow_nonneg (Nat.cast_nonneg (H j)) (-a))
  nlinarith only [h]

/-- Cofinal simultaneous smallness is enough: no full-sequence limit or
uniform complete-norm bound is assumed. -/
theorem riemannHypothesis_of_cofinal_variable_head_budget
    (v : ℕ → QHilbert) (hv : ∀ j, v j ∈ QFullResidueProjection.legalSpan)
    (H : ℕ → ℕ) (hH : ∀ j, 1 ≤ H j)
    (hbudget : ∀ a : ℝ, 0 < a → ∀ c : ℝ, 0 < c → ∀ N : ℕ,
      ∃ j : ℕ, N ≤ j ∧
        ((H j : ℝ) + 1) ^ 2 * ‖B (qOne - v j)‖ ^ 2 +
          (H j : ℝ) ^ (-a) * ‖qOne - v j‖ ^ 2 < c) :
    RiemannHypothesis := by
  apply RiemannResearch.RH.riemannHypothesis_iff_right_half_strip_zero_free.mpr
  intro s hs hs1 hz
  have hs0 : s ≠ 0 := by intro he; norm_num [he] at hs
  have hsne : s ≠ 1 := by intro he; norm_num [he] at hs1
  let C : ℝ := 2 * zetaTwo / (2 * s.re - 1)
  have hC : 0 < C := by
    dsimp [C]
    exact div_pos (mul_pos (by norm_num) zetaTwo_pos) (by linarith)
  have hp : 0 < ‖(1 : ℂ) / s‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (div_ne_zero one_ne_zero hs0))
  obtain ⟨j, _hj, hsmall⟩ := hbudget (2 * s.re - 1) (by linarith)
    (‖(1 : ℂ) / s‖ ^ 2 / C) (div_pos hp hC) 0
  have hm : qMellin (qOne - v j) s = 1 / s := by
    change qMellinContinuous s hs (qOne - v j) = _
    rw [map_sub]
    change qMellin qOne s - qMellin (v j) s = _
    rw [qMellin_one s hs, qMellin_legalSpan_zero (v j) (hv j) s hs hsne hz, sub_zero]
  have hb := qMellin_norm_sq_le_reciprocal_split (qOne - v j) s hs (H j) (hH j)
  rw [hm] at hb
  have he : -(2 * s.re - 1) = 1 - 2 * s.re := by ring
  rw [he] at hsmall
  have hmul := (lt_div_iff₀ hC).mp hsmall
  change ‖(1 : ℂ) / s‖ ^ 2 ≤ C * _ at hb
  nlinarith only [hb, hmul]

/-- An explicit reciprocal O(1/j) rate together with subpower complete
energy implies actual Mathlib RH. The proof uses stage j=j(j+2), so the
original denominator stage j+1 is exactly (j+1)^2; no floor estimates occur.
The complete energy hypothesis remains the unresolved arithmetic provider. -/
theorem riemannHypothesis_of_reciprocal_rate_subpower_norm
    (U : ℕ → QHilbert) (hU : ∀ k, U k ∈ QFullResidueProjection.legalSpan)
    (C : ℝ)
    (herr : ∀ k, ‖B (qOne - U k)‖ ≤ C / ((k : ℝ) + 1))
    (hgrowth : ∀ a : ℝ, 0 < a → Tendsto
      (fun (k : ℕ) => ((k : ℝ) + 1) ^ (-a) * ‖U k‖ ^ 2) atTop (𝓝 0)) :
    RiemannHypothesis := by
  let stage : ℕ → ℕ := fun j => j * (j + 2)
  have hstage : Tendsto stage atTop atTop := by
    have hle (j : ℕ) : j ≤ stage j := by
      dsimp [stage]
      nlinarith [Nat.zero_le j]
    exact tendsto_atTop_mono hle tendsto_id
  have hstage_sq (j : ℕ) : (stage j : ℝ) + 1 = ((j : ℝ) + 1) ^ 2 := by
    dsimp [stage]
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
    ring
  have hhead : Tendsto (fun j : ℕ => j + 1) atTop atTop :=
    tendsto_atTop_mono (fun j : ℕ => show j ≤ j + 1 by omega) tendsto_id
  have hbase : Tendsto (fun j : ℕ => (j : ℝ) + 1) atTop atTop := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_natCast_atTop_atTop.comp hhead :
        Tendsto (fun j : ℕ => ((j + 1 : ℕ) : ℝ)) atTop atTop)
  have hi : Tendsto (fun j : ℕ => ((j : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hbase
  have hupper : Tendsto (fun j : ℕ => 4 * C ^ 2 / ((j : ℝ) + 1) ^ 2)
      atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, inv_pow, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      mul_zero] using (hi.pow 2).const_mul (4 * C ^ 2)
  have hR : Tendsto (fun j : ℕ => ((j : ℝ) + 2) ^ 2 *
      ‖B (qOne - U (stage j))‖ ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero (fun j => by positivity) ?_ hupper
    intro j
    have hx : 0 < (j : ℝ) + 1 := by positivity
    have he := herr (stage j)
    rw [hstage_sq j] at he
    have he2 := pow_le_pow_left₀ (norm_nonneg _) he 2
    have hhead_le : (j : ℝ) + 2 ≤ 2 * ((j : ℝ) + 1) := by
      linarith [Nat.cast_nonneg (α := ℝ) j]
    have hhead2 := pow_le_pow_left₀ (by positivity : 0 ≤ (j : ℝ) + 2) hhead_le 2
    have hhead2' : ((j : ℝ) + 2) ^ 2 ≤ 4 * ((j : ℝ) + 1) ^ 2 := by
      nlinarith only [hhead2]
    calc
      _ ≤ ((j : ℝ) + 2) ^ 2 * (C / ((j : ℝ) + 1) ^ 2) ^ 2 :=
        mul_le_mul_of_nonneg_left he2 (sq_nonneg _)
      _ ≤ (4 * ((j : ℝ) + 1) ^ 2) * (C / ((j : ℝ) + 1) ^ 2) ^ 2 :=
        mul_le_mul_of_nonneg_right hhead2' (sq_nonneg _)
      _ = _ := by field_simp [ne_of_gt hx]
  have hG (a : ℝ) (ha : 0 < a) : Tendsto
      (fun (j : ℕ) => ((j : ℝ) + 1) ^ (-a) * ‖U (stage j)‖ ^ 2) atTop (𝓝 0) := by
    have he (j : ℕ) : ((stage j : ℝ) + 1) ^ (-(a / 2)) =
        ((j : ℝ) + 1) ^ (-a) := by
      rw [hstage_sq j, ← Real.rpow_two,
        ← Real.rpow_mul (by positivity : 0 ≤ (j : ℝ) + 1)]
      congr 1
      ring
    simpa only [Function.comp_def, he] using (hgrowth (a / 2) (by linarith)).comp hstage
  apply riemannHypothesis_of_variable_head_subpower_norm
    (fun j => U (stage j)) (fun j => hU (stage j))
    (fun j => j + 1) (fun j => by omega) hhead
  · simpa only [Nat.cast_add, Nat.cast_one,
      show ∀ j : ℕ, (j : ℝ) + 1 + 1 = (j : ℝ) + 2 by intro j; ring] using hR
  · intro a ha
    simpa only [Nat.cast_add, Nat.cast_one] using hG a ha

end RiemannResearch.RH.QReciprocalMellinCriterion
