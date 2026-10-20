/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ThresholdHilbertMean
import RiemannResearch.RH.ThresholdHilbertDilation
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Complete prime-power counting targets

Source: the ordinary argument in `PrimePowerTargetsResearch20261020.md`.
The construction here uses the contraction equation F(n)=F(n/p)+1_{p≤n}.
It supplies an actual Hilbert vector before making any closure hypothesis.
All bases p>1 are allowed; primality is not needed in this module.
-/

noncomputable section
open scoped BigOperators Topology
namespace RiemannResearch.RH.PrimePowerTarget
open Pareto

def unscaledDilation (p : ℕ) (hp : 0 < p) :
    ThresholdHilbert →L[ℝ] ThresholdHilbert :=
  (1 / (p : ℝ)) • hilbertDilationContinuous p hp

theorem unscaledDilation_norm (p : ℕ) (hp : 0 < p) (f : ThresholdHilbert) :
    ‖unscaledDilation p hp f‖ = Real.sqrt (p : ℝ) / p * ‖f‖ := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  change ‖(1 / (p : ℝ)) • hilbertDilation p hp f‖ = _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), hilbertDilation_norm]
  ring

theorem unscaledDilation_norm_sq (p : ℕ) (hp : 0 < p) (f : ThresholdHilbert) :
    ‖unscaledDilation p hp f‖ ^ 2 = ‖f‖ ^ 2 / p := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  rw [unscaledDilation_norm, mul_pow, div_pow, Real.sq_sqrt hpR.le]
  field_simp

def targetMap (p : ℕ) (hp : 0 < p) (f : ThresholdHilbert) : ThresholdHilbert :=
  unscaledDilation p hp (f + hilbertOne)

def contractionFactor (p : ℕ) : NNReal :=
  ⟨Real.sqrt (p : ℝ) / p, by positivity⟩

theorem targetMap_contracting (p : ℕ) (hp : 1 < p) :
    ContractingWith (contractionFactor p) (targetMap p (by omega)) := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have hpR0 : (0 : ℝ) < p := by linarith
  constructor
  · change Real.sqrt (p : ℝ) / p < 1
    apply (div_lt_iff₀ hpR0).2
    have hs := Real.sq_sqrt hpR0.le
    have hn := Real.sqrt_nonneg (p : ℝ)
    nlinarith
  · apply LipschitzWith.of_dist_le_mul
    intro f g
    rw [dist_eq_norm, dist_eq_norm]
    change ‖unscaledDilation p _ (f + hilbertOne) -
      unscaledDilation p _ (g + hilbertOne)‖ ≤ _
    rw [← map_sub, add_sub_add_right_eq_sub, unscaledDilation_norm]
    exact le_rfl

def paretoTarget (p : ℕ) (hp : 1 < p) : ThresholdHilbert :=
  ContractingWith.fixedPoint (targetMap p (by omega)) (targetMap_contracting p hp)

theorem paretoTarget_fixed (p : ℕ) (hp : 1 < p) :
    unscaledDilation p (by omega) (paretoTarget p hp + hilbertOne) =
      paretoTarget p hp :=
  (targetMap_contracting p hp).fixedPoint_isFixedPt

theorem unscaledDilation_sequence (p : ℕ) (hp : 0 < p)
    (f : ThresholdHilbert) (n : ℕ) :
    hilbertSequence (unscaledDilation p hp f) n = hilbertSequence f (n / p) := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  change hilbertSequence ((1 / (p : ℝ)) • hilbertDilation p hp f) n = _
  rw [hilbertSequence_smul, hilbertDilation_sequence]
  simp [dilation, hpR]

theorem paretoTarget_sequence_rec (p : ℕ) (hp : 1 < p) (n : ℕ) :
    hilbertSequence (paretoTarget p hp) n =
      hilbertSequence (paretoTarget p hp) (n / p) +
        (if n / p = 0 then 0 else 1) := by
  conv_lhs => rw [← paretoTarget_fixed p hp]
  rw [unscaledDilation_sequence, hilbertSequence_add, hilbertOne_sequence]
  rfl

theorem paretoTarget_sequence (p : ℕ) (hp : 1 < p) (n : ℕ) :
    hilbertSequence (paretoTarget p hp) n = (Nat.log p n : ℝ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      simp
    · have hn0 : 0 < n := Nat.pos_of_ne_zero hn
      have hdiv : n / p < n := Nat.div_lt_self hn0 hp
      rw [paretoTarget_sequence_rec, ih (n / p) hdiv]
      by_cases hnp : n < p
      · simp [Nat.div_eq_of_lt hnp, Nat.log_of_lt hnp]
      · have hpn : p ≤ n := Nat.le_of_not_gt hnp
        have hd : 0 < n / p := Nat.div_pos hpn (by omega)
        have hl : 0 < Nat.log p n := Nat.log_pos hp hpn
        rw [if_neg (by omega), Nat.log_div_base]
        push_cast [Nat.cast_sub (by omega : 1 ≤ Nat.log p n)]
        ring

theorem paretoTarget_mean (p : ℕ) (hp : 1 < p) :
    inner ℝ (paretoTarget p hp) hilbertOne = 1 / ((p : ℝ) - 1) := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have h := congrArg (fun f : ThresholdHilbert => inner ℝ f hilbertOne)
    (paretoTarget_fixed p hp)
  change inner ℝ ((1 / (p : ℝ)) •
    hilbertDilation p (by omega) (paretoTarget p hp + hilbertOne)) hilbertOne = _ at h
  rw [real_inner_smul_left, hilbert_inner_one, hilbertDilation_mean,
    ← hilbert_inner_one, inner_add_left, real_inner_self_eq_norm_sq,
    hilbertOne_norm_sq] at h
  apply (eq_div_iff (by linarith : (p : ℝ) - 1 ≠ 0)).2
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  field_simp [hp0] at h
  nlinarith

theorem paretoTarget_norm_sq (p : ℕ) (hp : 1 < p) :
    ‖paretoTarget p hp‖ ^ 2 = ((p : ℝ) + 1) / ((p : ℝ) - 1) ^ 2 := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have h := congrArg (fun f : ThresholdHilbert => ‖f‖ ^ 2) (paretoTarget_fixed p hp)
  rw [unscaledDilation_norm_sq, norm_add_sq_real,
    hilbertOne_norm_sq, paretoTarget_mean] at h
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  field_simp [hp0, hp1] at h ⊢
  nlinarith

end RiemannResearch.RH.PrimePowerTarget
