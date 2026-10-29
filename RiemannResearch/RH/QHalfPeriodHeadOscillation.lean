/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSquarefreeLatticePackets
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Forced half-period oscillation of exact-head residue combinations

Source: the user-provided minimum-energy research agenda, 28 October 2026,
and finite-stage exploration in this session. The identities below are
elementary residue calculations. They hold for every period twice an odd
integer; squarefree even periods are a special case.

The signed identities obstruct global range bounds, not complete-Q
energy bounds: the forced oscillation occurs near half the period.
-/

noncomputable section
namespace RiemannResearch.RH.QHalfPeriodHeadOscillation
open ZetaTwoHilbert ArithmeticCumulative QSquarefreeLatticePackets

private theorem half_residue_bound (m d : ℕ) (hd : 0 < d) (hdiv : d ∣ 2 * m) :
    2 * (m % d) ≤ d := by
  have hdivr : d ∣ 2 * (m % d) := by
    apply Nat.dvd_of_mod_eq_zero
    simpa only [Nat.mul_mod, Nat.mod_mod] using Nat.mod_eq_zero_of_dvd hdiv
  obtain ⟨k, hk⟩ := hdivr
  have hr := Nat.mod_lt m hd
  have hklt : k < 2 := by
    by_contra hnot
    have htwo : 2 ≤ k := by omega
    have hmul := Nat.mul_le_mul_left d htwo
    omega
  interval_cases k <;> simp_all <;> omega

theorem half_shift_no_wrap (m d a : ℕ) (hd : 0 < d)
    (hdiv : d ∣ 2 * m) (ha : 2 * a < d) :
    residueFraction d (m + a) - residueFraction d m = (a : ℝ) / (d : ℝ) := by
  have hr := half_residue_bound m d hd hdiv
  have hsum : m % d + a < d := by omega
  have hmod : (m + a) % d = m % d + a := by
    calc
      (m + a) % d = (m % d + a) % d := by
        simp only [Nat.add_mod, Nat.mod_mod]
      _ = m % d + a := Nat.mod_eq_of_lt hsum
  simp only [residueFraction, hmod, Nat.cast_add]
  ring

private theorem residue_shift_four (m d : ℕ) (hm : m % 2 = 1)
    (hd : 1 < d) (hdiv : d ∣ 2 * m) :
    residueFraction d (m + 4) - residueFraction d m =
      residueFraction d 4 + 2 * residueFraction d 1 - residueFraction d 3 -
        residueFraction d 5 + residueFraction d 6 := by
  by_cases hlarge : 8 < d
  · rw [half_shift_no_wrap m d 4 (by omega) hdiv (by omega)]
    simp only [residueFraction, Nat.mod_eq_of_lt (show 4 < d by omega),
      Nat.mod_eq_of_lt (show 1 < d by omega),
      Nat.mod_eq_of_lt (show 3 < d by omega),
      Nat.mod_eq_of_lt (show 5 < d by omega),
      Nat.mod_eq_of_lt (show 6 < d by omega)]
    norm_num <;> ring
  · have hsmall : d ≤ 8 := by omega
    have hmod := Nat.mod_eq_zero_of_dvd hdiv
    have hr : m % d = if d % 2 = 0 then d / 2 else 0 := by
      interval_cases d <;> norm_num at hmod ⊢ <;> omega
    have hs : (m + 4) % d = ((if d % 2 = 0 then d / 2 else 0) + 4) % d := by
      simpa only [Nat.add_mod, Nat.mod_mod] using
        congrArg (fun r : ℕ => (r + 4) % d) hr
    simp only [residueFraction, hs, hr]
    interval_cases d <;> norm_num at hmod ⊢ <;> omega

private theorem residue_shift_eight (m d : ℕ) (hm : m % 2 = 1)
    (hd : 1 < d) (hdiv : d ∣ 2 * m) :
    residueFraction d (m + 8) - residueFraction d m =
      residueFraction d 8 + 4 * residueFraction d 1 - 2 * residueFraction d 2 -
      residueFraction d 5 - residueFraction d 7 - residueFraction d 9 -
      residueFraction d 13 + residueFraction d 4 + residueFraction d 6 +
      residueFraction d 10 + residueFraction d 14 := by
  by_cases hlarge : 16 < d
  · rw [half_shift_no_wrap m d 8 (by omega) hdiv (by omega)]
    simp only [residueFraction, Nat.mod_eq_of_lt (show 8 < d by omega),
      Nat.mod_eq_of_lt (show 1 < d by omega), Nat.mod_eq_of_lt (show 2 < d by omega),
      Nat.mod_eq_of_lt (show 5 < d by omega), Nat.mod_eq_of_lt (show 7 < d by omega),
      Nat.mod_eq_of_lt (show 9 < d by omega), Nat.mod_eq_of_lt (show 13 < d by omega),
      Nat.mod_eq_of_lt (show 4 < d by omega), Nat.mod_eq_of_lt (show 6 < d by omega),
      Nat.mod_eq_of_lt (show 10 < d by omega), Nat.mod_eq_of_lt (show 14 < d by omega)]
    norm_num <;> ring
  · have hsmall : d ≤ 16 := by omega
    have hmod := Nat.mod_eq_zero_of_dvd hdiv
    have hr : m % d = if d % 2 = 0 then d / 2 else 0 := by
      interval_cases d <;> norm_num at hmod ⊢ <;> omega
    have hs : (m + 8) % d = ((if d % 2 = 0 then d / 2 else 0) + 8) % d := by
      simpa only [Nat.add_mod, Nat.mod_mod] using
        congrArg (fun r : ℕ => (r + 8) % d) hr
    simp only [residueFraction, hs, hr]
    interval_cases d <;> norm_num at hmod ⊢ <;> omega

/-- The full signed identity behind the head-six range obstruction. -/
theorem half_period_four_identity (m : ℕ) (hm : m % 2 = 1)
    (f : QHilbert) (hf : f ∈ divisorStage (2 * m)) :
    qSequence f (m + 4) - qSequence f m =
      qSequence f 4 + 2 * qSequence f 1 - qSequence f 3 -
        qSequence f 5 + qSequence f 6 := by
  let ev (n : ℕ) : (ℕ → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj n
  let T : (ℕ → ℝ) →ₗ[ℝ] ℝ :=
    ev (m + 4) - ev m - ev 4 -
      (2 : ℝ) • ev 1 + ev 3 + ev 5 -
      ev 6
  let ell := T.comp qSequenceLinear
  have hle : divisorStage (2 * m) ≤ ell.ker := by
    apply Submodule.span_le.mpr
    rintro x ⟨d, hdiv, rfl⟩
    by_cases hd1 : d = 1
    · rw [hd1, qResidue_one]
      exact ell.ker.zero_mem
    · have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdiv (by omega)
      change qSequence (qResidue d) (m + 4) - qSequence (qResidue d) m -
        qSequence (qResidue d) 4 - 2 * qSequence (qResidue d) 1 +
        qSequence (qResidue d) 3 + qSequence (qResidue d) 5 -
        qSequence (qResidue d) 6 = 0
      simp only [qSequence_qResidue]
      have he := residue_shift_four m d hm (by omega) hdiv
      linarith
  have he := hle hf
  change qSequence f (m + 4) - qSequence f m - qSequence f 4 -
    2 * qSequence f 1 + qSequence f 3 + qSequence f 5 - qSequence f 6 = 0 at he
  linarith

/-- The full signed identity behind the head-fourteen range obstruction. -/
theorem half_period_eight_identity (m : ℕ) (hm : m % 2 = 1)
    (f : QHilbert) (hf : f ∈ divisorStage (2 * m)) :
    qSequence f (m + 8) - qSequence f m =
      qSequence f 8 + 4 * qSequence f 1 - 2 * qSequence f 2 -
      qSequence f 5 - qSequence f 7 - qSequence f 9 - qSequence f 13 +
      qSequence f 4 + qSequence f 6 + qSequence f 10 + qSequence f 14 := by
  let ev (n : ℕ) : (ℕ → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj n
  let T : (ℕ → ℝ) →ₗ[ℝ] ℝ :=
    ev (m + 8) - ev m - ev 8 -
      (4 : ℝ) • ev 1 + (2 : ℝ) • ev 2 +
      ev 5 + ev 7 + ev 9 + ev 13 -
      ev 4 - ev 6 - ev 10 - ev 14
  let ell := T.comp qSequenceLinear
  have hle : divisorStage (2 * m) ≤ ell.ker := by
    apply Submodule.span_le.mpr
    rintro x ⟨d, hdiv, rfl⟩
    by_cases hd1 : d = 1
    · rw [hd1, qResidue_one]
      exact ell.ker.zero_mem
    · have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdiv (by omega)
      change qSequence (qResidue d) (m + 8) - qSequence (qResidue d) m -
        qSequence (qResidue d) 8 - 4 * qSequence (qResidue d) 1 +
        2 * qSequence (qResidue d) 2 + qSequence (qResidue d) 5 +
        qSequence (qResidue d) 7 + qSequence (qResidue d) 9 +
        qSequence (qResidue d) 13 - qSequence (qResidue d) 4 -
        qSequence (qResidue d) 6 - qSequence (qResidue d) 10 -
        qSequence (qResidue d) 14 = 0
      simp only [qSequence_qResidue]
      have he := residue_shift_eight m d hm (by omega) hdiv
      linarith
  have he := hle hf
  change qSequence f (m + 8) - qSequence f m - qSequence f 8 -
    4 * qSequence f 1 + 2 * qSequence f 2 + qSequence f 5 + qSequence f 7 +
    qSequence f 9 + qSequence f 13 - qSequence f 4 - qSequence f 6 -
    qSequence f 10 - qSequence f 14 = 0 at he
  linarith

theorem exact_head_six_half_period_increment (m : ℕ) (hm : m % 2 = 1)
    (f : QHilbert) (hf : f ∈ divisorStage (2 * m))
    (hh : ∀ n, 0 < n → n ≤ 6 → qSequence f n = 1) :
    qSequence f (m + 4) = qSequence f m + 2 := by
  have he := half_period_four_identity m hm f hf
  rw [hh 4 (by norm_num) (by norm_num), hh 1 (by norm_num) (by norm_num),
    hh 3 (by norm_num) (by norm_num), hh 5 (by norm_num) (by norm_num),
    hh 6 (by norm_num) (by norm_num)] at he
  linarith

theorem exact_head_fourteen_half_period_increment (m : ℕ) (hm : m % 2 = 1)
    (f : QHilbert) (hf : f ∈ divisorStage (2 * m))
    (hh : ∀ n, 0 < n → n ≤ 14 → qSequence f n = 1) :
    qSequence f (m + 8) = qSequence f m + 3 := by
  have he := half_period_eight_identity m hm f hf
  rw [hh 8 (by norm_num) (by norm_num), hh 1 (by norm_num) (by norm_num),
    hh 2 (by norm_num) (by norm_num), hh 5 (by norm_num) (by norm_num),
    hh 7 (by norm_num) (by norm_num), hh 9 (by norm_num) (by norm_num),
    hh 13 (by norm_num) (by norm_num), hh 4 (by norm_num) (by norm_num),
    hh 6 (by norm_num) (by norm_num), hh 10 (by norm_num) (by norm_num),
    hh 14 (by norm_num) (by norm_num)] at he
  linarith

theorem no_unit_interval_exact_head_six (m : ℕ) (hm : m % 2 = 1)
    (f : QHilbert) (hf : f ∈ divisorStage (2 * m))
    (hh : ∀ n, 0 < n → n ≤ 6 → qSequence f n = 1) :
    ¬ (∀ n, 0 ≤ qSequence f n ∧ qSequence f n ≤ 1) := by
  intro hb
  have he := exact_head_six_half_period_increment m hm f hf hh
  have hlo := (hb m).1
  have hhi := (hb (m + 4)).2
  linarith

theorem no_abs_one_exact_head_fourteen (m : ℕ) (hm : m % 2 = 1)
    (f : QHilbert) (hf : f ∈ divisorStage (2 * m))
    (hh : ∀ n, 0 < n → n ≤ 14 → qSequence f n = 1) :
    ¬ (∀ n, |qSequence f n| ≤ 1) := by
  intro hb
  have he := exact_head_fourteen_half_period_increment m hm f hf hh
  have hlo := (abs_le.mp (hb m)).1
  have hhi := (abs_le.mp (hb (m + 8))).2
  linarith

private theorem squarefree_odd_half_extension (L : ℕ) (hsf : Squarefree L) :
    ∃ m : ℕ, m % 2 = 1 ∧ L ∣ 2 * m := by
  by_cases h2 : 2 ∣ L
  · have hnot4 : ¬ 4 ∣ L := by
      intro h4
      have hp := hsf.pow_dvd_of_pow_dvd
        (show (2 : ℕ) ^ 2 ∣ L by simpa using h4)
      norm_num at hp
    have hmod2 := Nat.mod_eq_zero_of_dvd h2
    have hdiv := Nat.mod_add_div L 2
    have heq : 2 * (L / 2) = L := by omega
    have hm : (L / 2) % 2 = 1 := by
      by_contra hnot
      have hm0 : (L / 2) % 2 = 0 := by omega
      have hmod4 : L % 4 = 0 := by omega
      exact hnot4 (Nat.dvd_of_mod_eq_zero hmod4)
    refine ⟨L / 2, hm, ?_⟩
    rw [heq]
  · have hm : L % 2 = 1 := by
      have hmod : L % 2 ≠ 0 := by
        intro h
        exact h2 (Nat.dvd_of_mod_eq_zero h)
      omega
    exact ⟨L, hm, ⟨2, by omega⟩⟩

/-- Enlarging a squarefree period cannot rescue the nonnegative unit-range
construction once six exact coordinates are required. -/
theorem squarefree_stage_no_unit_interval_exact_head_six (L : ℕ)
    (hsf : Squarefree L) (f : QHilbert) (hf : f ∈ divisorStage L)
    (hh : ∀ n, 0 < n → n ≤ 6 → qSequence f n = 1) :
    ¬ (∀ n, 0 ≤ qSequence f n ∧ qSequence f n ≤ 1) := by
  obtain ⟨m, hm, hdiv⟩ := squarefree_odd_half_extension L hsf
  exact no_unit_interval_exact_head_six m hm f (divisorStage_mono hdiv hf) hh

/-- Even allowing negative values does not permit the fixed amplitude one
once fourteen exact coordinates are required. This is not an energy obstruction. -/
theorem squarefree_stage_no_abs_one_exact_head_fourteen (L : ℕ)
    (hsf : Squarefree L) (f : QHilbert) (hf : f ∈ divisorStage L)
    (hh : ∀ n, 0 < n → n ≤ 14 → qSequence f n = 1) :
    ¬ (∀ n, |qSequence f n| ≤ 1) := by
  obtain ⟨m, hm, hdiv⟩ := squarefree_odd_half_extension L hsf
  exact no_abs_one_exact_head_fourteen m hm f (divisorStage_mono hdiv hf) hh

end RiemannResearch.RH.QHalfPeriodHeadOscillation
