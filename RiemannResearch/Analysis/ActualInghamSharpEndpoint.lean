/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualInghamSharpRightMoment
import RiemannResearch.Analysis.ActualInghamGabrielEndpoints
import RiemannResearch.Analysis.ActualMobiusLCMTransport
import RiemannResearch.Analysis.MobiusLCMTotientExpansion
import RiemannResearch.NumberTheory.PrimeNumberTheorem.CoprimeMobiusHarmonicMean

/-!
# The unconditional one-log moving right edge

The prime-by-prime change of measure transports the fixed harmonic estimate
to the moving line. The signed Dirichlet mean-square theorem then gives the
one-logarithm order in Chourasiya and Simonič, arXiv:2507.15184, Lemma 6.
The constants here are qualitative and the interval may start at any height.
-/
noncomputable section
open MeasureTheory Complex Set
open scoped BigOperators

namespace RiemannResearch.Analysis.InghamMollifier

/-- A single bounded lcm form works uniformly for all cutoffs on the moving line. -/
theorem exists_moving_lcm_form_bound {b : ℝ} (hb : 0 ≤ b) :
    ∃ B : ℝ, 0 < B ∧ ∀ X : ℕ, 2 ≤ X →
      truncatedMobiusLCMForm X (1 + b / Real.log X) ≤ B := by
  obtain ⟨K, hK, h⟩ := exists_truncatedMobiusLCMForm_one_bound
  refine ⟨Real.exp (4 * b) * K, mul_pos (Real.exp_pos _) hK, ?_⟩
  intro X hX
  exact (truncatedMobiusLCMForm_moving_le hX hb).trans
    (mul_le_mul_of_nonneg_left (h X) (Real.exp_pos _).le)

/-- Sharp I3 for the actual Möbius mollifier on every translated interval.
The positive constant depends only on the fixed distance parameter δ. -/
theorem exists_actual_moving_right_error_moment_log_one {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {X : ℕ}, 2 ≤ X → ∀ {H T : ℝ}, H ≤ T →
      (∫ t in H..T, ‖riemannZeta (((1 + δ / Real.log X : ℝ) : ℂ) + I*t) *
        mollifier X (((1 + δ / Real.log X : ℝ) : ℂ) + I*t) - 1‖ ^ 2) ≤
        C * (1 + (T - H) / X) * (1 + Real.log X) := by
  obtain ⟨B, hB, hform⟩ := exists_moving_lcm_form_bound (b := 2*δ) (by positivity)
  refine ⟨52 * B * (1 + 1 / (2*δ)), by positivity, ?_⟩
  intro X hX H T hHT
  have hx : (1 : ℝ) < X := by exact_mod_cast hX
  have hx0 := lt_trans zero_lt_one hx
  have hl := (Real.log_pos hx).le
  let L := (T - H) / X
  have hL : 0 ≤ L := div_nonneg (sub_nonneg.mpr hHT) hx0.le
  have hh := actual_moving_right_error_moment_le_of_lcm hδ hB.le hX hHT (hform X hX)
  have hlen : L + 52 ≤ 52 * (1 + L) := by linarith
  have hrate : 1 + Real.log X / (2*δ) ≤ (1 + 1/(2*δ)) * (1 + Real.log X) := by
    rw [div_eq_mul_inv, one_div]
    nlinarith [(inv_pos.mpr (by positivity : 0 < 2*δ)).le]
  calc
    _ ≤ (L + 52) * ((1 + Real.log X / (2*δ))*B - 1) := hh
    _ ≤ (L + 52) * ((1 + Real.log X / (2*δ))*B) := by
      apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ ≤ (52 * (1 + L)) * (((1 + 1/(2*δ)) * (1 + Real.log X)) * B) := by
      apply mul_le_mul hlen (mul_le_mul_of_nonneg_right hrate hB.le)
        (mul_nonneg (by positivity) hB.le) (by positivity)
    _ = _ := by dsimp [L]; ring

/-- The literal one-log form, uniformly for every cutoff at least two. -/
theorem exists_actual_moving_right_error_moment_le_log {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {X : ℕ}, 2 ≤ X → ∀ {H T : ℝ}, H ≤ T →
      (∫ t in H..T, ‖riemannZeta (((1 + δ / Real.log X : ℝ) : ℂ) + I*t) *
        mollifier X (((1 + δ / Real.log X : ℝ) : ℂ) + I*t) - 1‖ ^ 2) ≤
        C * (1 + (T - H) / X) * Real.log X := by
  obtain ⟨C, hC, h⟩ := exists_actual_moving_right_error_moment_log_one hδ
  have htwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  refine ⟨C * (1 + 1 / Real.log 2), by positivity, ?_⟩
  intro X hX H T hHT
  have hx : (2 : ℝ) ≤ X := by exact_mod_cast hX
  have hl := Real.log_le_log (by norm_num : (0:ℝ) < 2) hx
  have hone : 1 ≤ Real.log (X : ℝ) / Real.log 2 := (one_le_div htwo).mpr hl
  have hlog : 1 + Real.log X ≤ (1 + 1 / Real.log 2) * Real.log X := by
    rw [div_eq_mul_inv] at hone
    rw [one_div]
    nlinarith
  have hv : 0 ≤ (T-H) / (X : ℝ) := div_nonneg (sub_nonneg.mpr hHT) (Nat.cast_nonneg X)
  apply (h hX hHT).trans
  calc
    _ ≤ (C * (1+(T-H)/X)) * ((1+1/Real.log 2) * Real.log X) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = _ := by ring

/-- The actual right-hand Gaussian budget inherits precisely one logarithm.
The constant depends only on δ and the height integral has its complete tail. -/
theorem exists_actual_gabriel_right_endpoint_log_one {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {X : ℕ}, 2 ≤ X → ∀ {T a : ℝ}, 0 ≤ T → 0 ≤ a →
      let β := 1 + δ / Real.log (X : ℝ)
      let f := fun t : ℝ => ‖riemannZeta ((β : ℂ) + I*t) *
        mollifier X ((β : ℂ) + I*t) - 1‖ ^ 2
      IntegrableOn (fun u : ℝ => Real.exp (-u) * ∫ t in 0..T*a*Real.sqrt u, f t) (Ioi 0) ∧
      gabrielEndpoint f T a ≤ C * Real.log X * (1 + (T*a/X) * Real.Gamma (3/2)) := by
  obtain ⟨C, hC, h⟩ := exists_actual_moving_right_error_moment_le_log hδ
  refine ⟨C, hC, ?_⟩
  intro X hX T a hT ha
  dsimp only
  have hx : (1 : ℝ) < X := by exact_mod_cast hX
  have hβ : 1 < 1 + δ / Real.log (X : ℝ) := by linarith [div_pos hδ (Real.log_pos hx)]
  have hc := (vertical_error_continuous X hβ.ne').pow 2
  simp only [mollifiedError, mul_comm _ I] at hc
  let K := C * Real.log X
  have hm := gabrielEndpoint_of_affine hc (fun t => sq_nonneg _) hT ha
    (A := K) (B := K / X) (fun U hU => by
      have hu := h hX (H := 0) (T := U) hU
      rw [sub_zero] at hu
      refine hu.trans_eq ?_
      dsimp [K]
      ring)
  refine ⟨hm.1, hm.2.trans_eq ?_⟩
  dsimp [K]
  ring

/--
info: 'RiemannResearch.Analysis.InghamMollifier.exists_actual_moving_right_error_moment_log_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_actual_moving_right_error_moment_log_one

end RiemannResearch.Analysis.InghamMollifier
