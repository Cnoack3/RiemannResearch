/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSquarefreeAffineHead
import RiemannResearch.RH.QSquarefreeConstrainedMinimum
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.NumberTheory.PrimeNumberTheorem.MobiusReciprocal
import RiemannResearch.RH.QSquarefreeBlockBalance
import RiemannResearch.RH.QSquarefreeSublinearHeads
import RiemannResearch.RH.QConductorCoefficientMass
import RiemannResearch.RH.QMobiusExactHead
import RiemannResearch.RH.CanonicalMobiusPNT
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Sublinear energy of actual squarefree affine head minima

Source: continuation of the user's LCM cost/gain question, 19 October 2026.
This reuses the established PNT-based canonical exact-head estimate and the
complete-Q conductor bound from QConductorCoefficientMass. Replacing the
canonical anchor by a nearby legal squarefree anchor costs o(H). Thus the
actual constrained minima, and their signed cumulative cost minus gain, are
o(H). This does not prove boundedness or RH.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QSquarefreeAffineEnergy
open ZetaTwoHilbert ZetaTwoProbability QSquarefreeAffineHead QSquarefreeHeadSchedule
open QSquarefreeBlockBalance

private theorem sub_norm_sq_le (x y : QHilbert) :
    ‖x - y‖^2 ≤ 2 * ‖x‖^2 + 2 * ‖y‖^2 := by
  have h := mul_self_le_mul_self (norm_nonneg (x - y)) (norm_sub_le x y)
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

private theorem scaled_atom_energy (d : ℕ) (hd : 2 ≤ d) (a : ℝ) :
    ‖((d : ℝ) * a) • qResidue d‖^2 ≤ (2 / zetaTwo) * (d : ℝ) * a^2 := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  calc
    _ = ((d : ℝ) * a)^2 * ‖qResidue d‖^2 := by
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    _ ≤ ((d : ℝ) * a)^2 * (2 / (zetaTwo * (d : ℝ))) :=
      mul_le_mul_of_nonneg_left (qResidue_norm_sq_le_two_div d hd) (sq_nonneg _)
    _ = _ := by field_simp [hdR, ne_of_gt zetaTwo_pos]

/-- A quantitative complete-Q comparison with the existing canonical family. -/
theorem baseline_error_le (H r : ℕ) (hH : 0 < H) (hr : H < r) (hr2 : r ≤ 2 * H) :
    ‖qOne - baseline H r‖^2 ≤
      2 * ‖qOne - QMobiusExactHead.exactHead H‖^2 +
        (32 / zetaTwo) * (H : ℝ) * (Pareto.mobiusReciprocalSum H)^2 := by
  let m := Pareto.mobiusReciprocalSum H
  let A := ((r : ℝ) * m) • qResidue r
  let B := (((H + 1 : ℕ) : ℝ) * m) • qResidue (H + 1)
  have hZ := zetaTwo_pos
  have ha := scaled_atom_energy r (by omega) m
  have hb := scaled_atom_energy (H + 1) (by omega) m
  have hd := sub_norm_sq_le A B
  have hR : (r : ℝ) ≤ 2 * (H : ℝ) := by exact_mod_cast hr2
  have hH1 : ((H + 1 : ℕ) : ℝ) ≤ 2 * (H : ℝ) := by
    push_cast
    have : (1 : ℝ) ≤ H := by exact_mod_cast hH
    linarith
  have hm : 0 ≤ (2 / zetaTwo) * m^2 := by positivity
  have hsum := mul_le_mul_of_nonneg_right (add_le_add hR hH1) hm
  have hdiff : ‖A - B‖^2 ≤ (16 / zetaTwo) * (H : ℝ) * m^2 := by
    change ‖A‖^2 ≤ _ at ha
    change ‖B‖^2 ≤ _ at hb
    calc
      _ ≤ 2 * ‖A‖^2 + 2 * ‖B‖^2 := hd
      _ ≤ 2 * ((2 / zetaTwo) * (r : ℝ) * m^2) +
          2 * ((2 / zetaTwo) * ((H + 1 : ℕ) : ℝ) * m^2) :=
        add_le_add (mul_le_mul_of_nonneg_left ha (by norm_num))
          (mul_le_mul_of_nonneg_left hb (by norm_num))
      _ = 2 * (((r : ℝ) + ((H + 1 : ℕ) : ℝ)) * ((2 / zetaTwo) * m^2)) := by ring
      _ ≤ 2 * ((2 * (H : ℝ) + 2 * (H : ℝ)) * ((2 / zetaTwo) * m^2)) :=
        mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ = _ := by ring
  have heq : qOne - baseline H r =
      (qOne - QMobiusExactHead.exactHead H) - (A - B) := by
    dsimp [baseline, QMobiusExactHead.exactHead, QSquarefreeConstrainedMinimum.mobiusSeed,
      A, B, m]
    abel
  rw [heq]
  have he := sub_norm_sq_le (qOne - QMobiusExactHead.exactHead H) (A - B)
  change _ ≤ 2 * ‖qOne - QMobiusExactHead.exactHead H‖^2 +
    (32 / zetaTwo) * (H : ℝ) * m^2
  calc
    _ ≤ 2 * ‖qOne - QMobiusExactHead.exactHead H‖^2 + 2 * ‖A - B‖^2 := he
    _ ≤ 2 * ‖qOne - QMobiusExactHead.exactHead H‖^2 +
        2 * ((16 / zetaTwo) * (H : ℝ) * m^2) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hdiff (by norm_num))
    _ = _ := by ring

theorem energy_le_canonical (s : Schedule) (i : ℕ) :
    energy s i ≤ 2 * ‖qOne - QMobiusExactHead.exactHead (i + 1)‖^2 +
      (32 / zetaTwo) * (i + 1 : ℝ) * (Pareto.mobiusReciprocalSum (i + 1))^2 := by
  have hm := minimumError_le (i + 1) (s.period i) (s.anchor i) (Nat.succ_pos i)
    (s.positive i) (s.anchor_mem i) (s.anchor_gt i) (s.small i)
    (baseline (i + 1) (s.anchor i))
    (baseline_mem_divisorStage (i + 1) (s.period i) (s.anchor i)
      (Nat.mem_divisors.mp (Finset.mem_filter.mp (s.anchor_mem i)).1).1 (s.small i))
    (baseline_head (i + 1) (s.anchor i) (s.anchor_gt i))
  simpa only [energy, Nat.cast_add, Nat.cast_one] using
    hm.trans (baseline_error_le (i + 1) (s.anchor i) (Nat.succ_pos i)
      (s.anchor_gt i) (s.anchor_le i))

/-- Unconditional o(H), retaining all physical sites, for the actual minima. -/
theorem energy_sublinear (s : Schedule) :
    Tendsto (fun i => energy s i / (i + 1 : ℝ)) atTop (𝓝 0) := by
  have hshift : Tendsto (fun i : ℕ => i + 1) atTop atTop := tendsto_add_atTop_nat 1
  have hc := QSquarefreeSublinearHeads.exactHead_error_sublinear.comp hshift
  have hm := (Pareto.mobiusReciprocalSum_tendsto_zero.comp hshift).pow 2
  have hu := (hc.const_mul 2).add (hm.const_mul (32 / zetaTwo))
  simp only [Function.comp_def, Nat.cast_add, Nat.cast_one,
    zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] at hu
  apply squeeze_zero (fun i => div_nonneg (sq_nonneg _) (by positivity)) ?_ hu
  intro i
  have he := div_le_div_of_nonneg_right (energy_le_canonical s i)
    (by positivity : (0 : ℝ) ≤ (i + 1 : ℝ))
  have hn : (i + 1 : ℝ) ≠ 0 := by positivity
  calc
    _ ≤ (2 * ‖qOne - QMobiusExactHead.exactHead (i + 1)‖^2 +
        (32 / zetaTwo) * (i + 1 : ℝ) * (Pareto.mobiusReciprocalSum (i + 1))^2) /
        (i + 1 : ℝ) := he
    _ = _ := by field_simp [hn]

theorem signed_balance_sublinear (s : Schedule) :
    Tendsto (fun N =>
      (∑ i ∈ Finset.range N, (cost s i - gain s i)) / (N + 1 : ℝ))
      atTop (𝓝 0) := by
  have hc : Tendsto (fun N : ℕ => energy s 0 / (N + 1 : ℝ)) atTop (𝓝 0) := by
    have h := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (tendsto_add_atTop_nat 1)
    simpa only [Function.comp_def, mul_zero, Nat.cast_add, Nat.cast_one,
      div_eq_mul_inv, one_mul]
      using h.const_mul (energy s 0)
  have h := (energy_sublinear s).sub hc
  simp only [sub_zero] at h
  apply h.congr'
  exact Eventually.of_forall fun N => by
    dsimp only
    rw [← sub_div]
    have he := signed_balance_eq s N
    congr 1
    linarith

end RiemannResearch.RH.QSquarefreeAffineEnergy
