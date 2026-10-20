/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QPrimePowerPrimorial
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Exact legal two-stage prime-power interpolation

Source: user-provided RH/CRT continuation agenda, 20 October 2026, Priority 3,
for the drift-cancelling construction. The complete norm identities and the
fixed-first-cutoff divergence consequence are developed here. Exact finite
head interpolation does not provide a uniform complete-Q energy bound.
-/

noncomputable section
open scoped BigOperators Topology
open Filter
namespace RiemannResearch.RH.QPrimePowerSieve
open ZetaTwoHilbert ZetaTwoProbability QSquarefreeLatticePackets
open RiemannResearch.Analysis

/-- The actual two-stage synthesis, with the full denominator retained. -/
def twoStageVector (x y : ℕ) : QHilbert :=
  (finitePrimeProduct x - finitePrimeProduct y)⁻¹ •
    (finitePrimeProduct x • primePowerTwoVector y -
      finitePrimeProduct y • primePowerTwoVector x)

theorem twoStageVector_mem_squarefreeSpan (x y : ℕ) :
    twoStageVector x y ∈ qSquarefreeCRTSpan := by
  exact qSquarefreeCRTSpan.smul_mem _
    (qSquarefreeCRTSpan.sub_mem
      (qSquarefreeCRTSpan.smul_mem _ (primePowerTwoVector_mem_squarefreeSpan y))
      (qSquarefreeCRTSpan.smul_mem _ (primePowerTwoVector_mem_squarefreeSpan x)))

theorem twoStageVector_mem_divisorStage (x y : ℕ)
    (hxy : primorial x ∣ primorial y) :
    twoStageVector x y ∈ divisorStage (primorial y) := by
  exact (divisorStage (primorial y)).smul_mem _
    ((divisorStage (primorial y)).sub_mem
      ((divisorStage (primorial y)).smul_mem _
        (sieveVector_mem_divisorStage (primorial y) 2))
      ((divisorStage (primorial y)).smul_mem _
        (divisorStage_mono hxy (sieveVector_mem_divisorStage (primorial x) 2))))

theorem qSequence_twoStageVector (x y n : ℕ) :
    qSequence (twoStageVector x y) n =
      (finitePrimeProduct x * qSequence (primePowerTwoVector y) n -
        finitePrimeProduct y * qSequence (primePowerTwoVector x) n) /
          (finitePrimeProduct x - finitePrimeProduct y) := by
  change qSequenceLinear ((_ : ℝ) • (_ - _)) n = _
  simp only [map_smul, map_sub, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  change (finitePrimeProduct x - finitePrimeProduct y)⁻¹ *
    (finitePrimeProduct x * qSequence (primePowerTwoVector y) n -
      finitePrimeProduct y * qSequence (primePowerTwoVector x) n) = _
  ring

/-- Both arithmetic drifts cancel on the whole common physical head. -/
theorem qSequence_twoStageVector_head (x y n : ℕ) (hx : 2 ≤ x)
    (hxy : x ≤ y) (hn : n ≤ x)
    (hgap : finitePrimeProduct x ≠ finitePrimeProduct y) :
    qSequence (twoStageVector x y) n = (Nat.log 2 n : ℝ) := by
  rw [qSequence_twoStageVector,
    qSequence_primePowerTwoVector_head y n (hx.trans hxy) (hn.trans hxy),
    qSequence_primePowerTwoVector_head x n hx hn]
  apply (div_eq_iff (sub_ne_zero.mpr hgap)).mpr
  ring

/-- The complete signed Gram expression, including the cross term. -/
theorem twoStageVector_norm_sq_exact (x y : ℕ) :
    ‖twoStageVector x y‖ ^ 2 =
      (finitePrimeProduct x ^ 2 * ‖primePowerTwoVector y‖ ^ 2 +
        finitePrimeProduct y ^ 2 * ‖primePowerTwoVector x‖ ^ 2 -
        2 * finitePrimeProduct x * finitePrimeProduct y *
          inner ℝ (primePowerTwoVector y) (primePowerTwoVector x)) /
        (finitePrimeProduct x - finitePrimeProduct y) ^ 2 := by
  rw [twoStageVector, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    norm_sub_sq_real]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_smul_left, real_inner_smul_right, inv_pow, div_eq_mul_inv]
  ring

/-- Exact extrapolation cost: the nonnegative displacement term is retained. -/
theorem twoStageVector_norm_sq_correction (x y : ℕ)
    (hgap : finitePrimeProduct x ≠ finitePrimeProduct y) :
    ‖twoStageVector x y‖ ^ 2 =
      (finitePrimeProduct x * ‖primePowerTwoVector y‖ ^ 2 -
        finitePrimeProduct y * ‖primePowerTwoVector x‖ ^ 2) /
          (finitePrimeProduct x - finitePrimeProduct y) +
      finitePrimeProduct x * finitePrimeProduct y /
        (finitePrimeProduct x - finitePrimeProduct y) ^ 2 *
          ‖primePowerTwoVector y - primePowerTwoVector x‖ ^ 2 := by
  rw [twoStageVector_norm_sq_exact, norm_sub_sq_real]
  field_simp [sub_ne_zero.mpr hgap]
  ring

/-- The second raw vector is a convex combination of the extrapolant and first vector. -/
theorem twoStageVector_balance (x y : ℕ)
    (hgap : finitePrimeProduct x ≠ finitePrimeProduct y) :
    finitePrimeProduct x • primePowerTwoVector y =
      (finitePrimeProduct x - finitePrimeProduct y) • twoStageVector x y +
        finitePrimeProduct y • primePowerTwoVector x := by
  rw [twoStageVector, smul_smul,
    mul_inv_cancel₀ (sub_ne_zero.mpr hgap), one_smul]
  abel

/-- Cancelling the drift cannot erase raw growth while the first cutoff is fixed. -/
theorem twoStageVector_norm_lower (x y : ℕ)
    (hgap : finitePrimeProduct y < finitePrimeProduct x) :
    ‖primePowerTwoVector y‖ - ‖primePowerTwoVector x‖ ≤ ‖twoStageVector x y‖ := by
  have ha := finitePrimeProduct_pos x
  have hb := (finitePrimeProduct_pos y).le
  have hd : 0 ≤ finitePrimeProduct x - finitePrimeProduct y := sub_nonneg.mpr hgap.le
  have he := congrArg norm (twoStageVector_balance x y (ne_of_gt hgap))
  have ht := norm_add_le
    ((finitePrimeProduct x - finitePrimeProduct y) • twoStageVector x y)
    (finitePrimeProduct y • primePowerTwoVector x)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha] at he
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hd, abs_of_nonneg hb] at ht
  rw [← he] at ht
  have htx := mul_nonneg hb (norm_nonneg (twoStageVector x y))
  have hax := mul_nonneg hd (norm_nonneg (primePowerTwoVector x))
  nlinarith

/-- All sufficiently late second cutoffs have a nonzero interpolation denominator. -/
theorem eventually_twoStage_gap (x : ℕ) :
    ∀ᶠ y : ℕ in atTop, finitePrimeProduct y < finitePrimeProduct x :=
  finitePrimeProduct_tendsto_zero.eventually
    (eventually_lt_nhds (finitePrimeProduct_pos x))

/-- Even the exact-head-corrected legal family diverges when its first stage is fixed. -/
theorem twoStageVector_norm_tendsto_atTop (x : ℕ) :
    Tendsto (fun y : ℕ => ‖twoStageVector x y‖) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_twoStage_gap x,
    primePowerTwoVector_norm_tendsto_atTop.eventually
      (eventually_ge_atTop (b + ‖primePowerTwoVector x‖))] with y hgap hy
  have h := twoStageVector_norm_lower x y hgap
  linarith

/-- The exact-head correction preserves the raw pointwise target. -/
theorem twoStageVector_pointwise (x n : ℕ) :
    Tendsto (fun y => qSequence (twoStageVector x y) n) atTop
      (𝓝 (Nat.log 2 n : ℝ)) := by
  have ht : Tendsto (fun y : ℕ =>
      (finitePrimeProduct x * qSequence (primePowerTwoVector y) n -
        finitePrimeProduct y * qSequence (primePowerTwoVector x) n) /
        (finitePrimeProduct x - finitePrimeProduct y)) atTop
      (𝓝 ((finitePrimeProduct x * (Nat.log 2 n : ℝ) -
        0 * qSequence (primePowerTwoVector x) n) / (finitePrimeProduct x - 0))) :=
    ((tendsto_const_nhds.mul (primePowerTwoVector_pointwise n)).sub
    (finitePrimeProduct_tendsto_zero.mul_const
      (qSequence (primePowerTwoVector x) n))).div
    (tendsto_const_nhds.sub finitePrimeProduct_tendsto_zero)
    (by simpa using ne_of_gt (finitePrimeProduct_pos x))
  have hs : (finitePrimeProduct x * (Nat.log 2 n : ℝ) -
      0 * qSequence (primePowerTwoVector x) n) /
      (finitePrimeProduct x - 0) = (Nat.log 2 n : ℝ) := by
    simp [ne_of_gt (finitePrimeProduct_pos x)]
  rw [hs] at ht
  simpa only [qSequence_twoStageVector] using ht

/-- Every finite logarithmic head has an actual finite squarefree legal interpolant.
This asserts feasibility only and imposes no energy bound. -/
theorem exists_squarefree_logarithmic_head (x : ℕ) :
    ∃ f : QHilbert, f ∈ qSquarefreeCRTSpan ∧
      ∀ n, n ≤ x → qSequence f n = (Nat.log 2 n : ℝ) := by
  obtain ⟨y, hgap, hxy⟩ :=
    ((eventually_twoStage_gap (max 2 x)).and (eventually_ge_atTop (max 2 x))).exists
  refine ⟨twoStageVector (max 2 x) y,
    twoStageVector_mem_squarefreeSpan (max 2 x) y, ?_⟩
  intro n hn
  exact qSequence_twoStageVector_head (max 2 x) y n (le_max_left 2 x) hxy
    (hn.trans (le_max_right 2 x)) (ne_of_gt hgap)

end RiemannResearch.RH.QPrimePowerSieve
