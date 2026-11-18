/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualZeroCountUpper
import RiemannResearch.Analysis.ActualZeroDensityWindow
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# An unconditional thin-strip Ingham profile

The powers of T and log T are the profile in Chourasiya--Simonic,
https://arxiv.org/html/2507.15184v2, Corollary 1. The theorem below covers
only the explicitly stated shrinking strip. It follows from the already
proved total-zero count, with actual analytic multiplicities, and does
not assume or prove the global Ingham estimate.

The exact logarithmic comparison records the boundary of the range in
which this total-count argument suffices.
-/

noncomputable section
open Set
namespace RiemannResearch.Analysis.ActualZeroOrdinate

/-- Exact comparison with the log-power profile of Chourasiya--Simonic. -/
theorem height_log_le_ingham_profile_iff {T σ : ℝ} (hT : 1 < T) (hσ : σ < 2) :
    T * Real.log T ≤
        T ^ (3 * (1-σ) / (2-σ)) * (Real.log T) ^ ((7-5*σ) / (2-σ)) ↔
      (σ-1 / 2) * (2*Real.log T + 4*Real.log (Real.log T)) ≤
        3*Real.log (Real.log T) := by
  have hT0 : 0 < T := by linarith
  have hL : 0 < Real.log T := Real.log_pos hT
  have hd : 0 < 2-σ := by linarith
  have he : Real.log T * (3*(1-σ)/(2-σ)) +
      Real.log (Real.log T) * ((7-5*σ)/(2-σ)) -
      (Real.log T + Real.log (Real.log T)) =
      (3*Real.log (Real.log T) -
        (σ-1 / 2)*(2*Real.log T+4*Real.log (Real.log T)))/(2-σ) := by
    field_simp [hd.ne']
    ring
  have hb : T * Real.log T =
      Real.exp (Real.log T + Real.log (Real.log T)) := by
    rw [Real.exp_add, Real.exp_log hT0, Real.exp_log hL]
  rw [hb, Real.rpow_def_of_pos hT0, Real.rpow_def_of_pos hL,
    ← Real.exp_add, Real.exp_le_exp]
  constructor
  · intro h
    have hn : 0 ≤ (3*Real.log (Real.log T) -
        (σ-1 / 2)*(2*Real.log T+4*Real.log (Real.log T)))/(2-σ) := by
      linarith
    have hn' := (le_div_iff₀ hd).mp hn
    linarith
  · intro h
    have hn : 0 ≤ (3*Real.log (Real.log T) -
        (σ-1 / 2)*(2*Real.log T+4*Real.log (Real.log T)))/(2-σ) :=
      div_nonneg (by linarith) hd.le
    linarith

/-- An unconditional actual-zero estimate on a logarithmically shrinking strip.
The total count alone suffices throughout this strip. -/
theorem exists_ingham_profile_on_thin_strip :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 9 ≤ T → ∀ σ ∈ Icc (1 / 2 : ℝ) 1,
      (σ-1 / 2) * (2*Real.log T + 4*Real.log (Real.log T)) ≤
        3*Real.log (Real.log T) →
      rightInclusiveCount T σ ≤
        C * T ^ (3*(1-σ)/(2-σ)) * (Real.log T) ^ ((7-5*σ)/(2-σ)) := by
  obtain ⟨C,hC,hcount⟩ := exists_count_le_height_log
  refine ⟨C,hC,?_⟩
  intro T hT σ hσ hstrip
  have hb := (height_log_le_ingham_profile_iff (show 1 < T by linarith)
    (show σ < 2 by linarith [hσ.2])).mpr hstrip
  calc
    _ ≤ (Zeta23.Ncount 0 T : ℝ) := rightInclusiveCount_le_count T σ
    _ ≤ C * T * Real.log T := hcount T hT
    _ ≤ C * T ^ (3*(1-σ)/(2-σ)) * (Real.log T) ^ ((7-5*σ)/(2-σ)) := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb hC.le

end RiemannResearch.Analysis.ActualZeroOrdinate
