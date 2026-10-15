/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.CanonicalMobiusMovingCovariance
import RiemannResearch.RH.CanonicalMobiusStretchedEnergy
import RiemannResearch.Analysis.StretchedExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# An explicit growing cutoff for complete covariance columns

Source: user-requested moving-test investigation, 15 October 2026.
The existing unconditional stretched Mertens provider implies a normalized
residual-energy ceiling D / (6 + log N)^2. Hence
K_N = floor(sqrt(6 + log N)) + 1 tends to infinity and makes the entire
initial covariance column energy tend to zero. Signed coefficient vectors
with bounded squared mass, including convex weights, inherit pairing decay.
The arithmetic constants and starting index are existential, not numerical.
No norm convergence or bounded cofinal-average energy is asserted.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false
namespace RiemannResearch.RH.Pareto.MovingCovariance
open RiemannResearch.Analysis
def logScale (N : ℕ) : ℝ := 6 + Real.log (N : ℝ)

theorem logScale_tendsto : Tendsto logScale atTop atTop :=
  tendsto_atTop_add_const_left atTop 6
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

theorem logScale_square_div_tendsto :
    Tendsto (fun N => logScale N ^ 2 / (N : ℝ)) atTop (𝓝 0) := by
  have h0 := tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
  have h1 := (Real.tendsto_pow_log_div_pow_atTop 1 1 (by norm_num : (0 : ℝ) < 1)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have h2 := (Real.tendsto_pow_log_div_pow_atTop 1 2 (by norm_num : (0 : ℝ) < 1)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  simp only [Function.comp_def, Real.rpow_one, Real.rpow_two] at h1 h2
  have ht := ((h0.const_mul 36).add (h1.const_mul 12)).add h2
  simp only [mul_zero, zero_add] at ht
  convert ht using 1
  ext N
  unfold logScale
  ring

theorem energyRate_eventual_log_square :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ N in atTop,
      energyRate N ≤ D / logScale N ^ 2 := by
  obtain ⟨a, ha, C, hC, he⟩ := canonicalMobiusResidual_eventual_stretched_energy
  obtain ⟨B, hB, hBbound⟩ := stretchedExp_le_inverse_square a (1 / 11) ha (by norm_num)
  refine ⟨8 + C * B, by positivity, ?_⟩
  have hp := logScale_square_div_tendsto.eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [he, hp, eventually_ge_atTop (1 : ℕ)] with N heN hpN hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hL : 6 ≤ logScale N := by
    have hlog := Real.log_nonneg (show (1 : ℝ) ≤ N by exact_mod_cast hN)
    dsimp [logScale]
    linarith
  have hL0 : 0 < logScale N := by linarith
  have hLsq : logScale N ^ 2 ≤ (N : ℝ) + 1 := by
    have hp' := (div_lt_iff₀ hNR).mp hpN
    linarith
  have hx : Real.exp (-a * logProductPower (1 / 11) (logScale N)) ≤
      B / logScale N ^ 2 := by
    calc
      _ ≤ Real.exp (-a * (logScale N) ^ (1 / 11 : ℝ)) := by
        apply Real.exp_le_exp.mpr
        have hl := logProductPower_lower (1 / 11) (by norm_num) hL
        nlinarith
      _ ≤ _ := hBbound _ (by linarith)
  have h8 : 8 / ((N : ℝ) + 1) ≤ 8 / logScale N ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hL0) hLsq
  have hmain : energyRate N ≤ 8 / ((N : ℝ) + 1) +
      C * Real.exp (-a * logProductPower (1 / 11) (logScale N)) := by
    unfold energyRate residual
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) + 1)).mpr
    calc
      _ ≤ 8 + C * (N : ℝ) *
          Real.exp (-a * logProductPower (1 / 11) (logScale N)) := heN
      _ ≤ _ := by
        rw [add_mul, div_mul_cancel₀ _ (by positivity : (N : ℝ) + 1 ≠ 0)]
        nlinarith [mul_nonneg hC
          (Real.exp_pos (-a * logProductPower (1 / 11) (logScale N))).le]
  calc
    energyRate N ≤ 8 / ((N : ℝ) + 1) +
        C * Real.exp (-a * logProductPower (1 / 11) (logScale N)) := hmain
    _ ≤ 8 / logScale N ^ 2 + C * (B / logScale N ^ 2) :=
      add_le_add h8 (mul_le_mul_of_nonneg_left hx hC)
    _ = _ := by ring

def explicitCutoff (N : ℕ) : ℕ := ⌊Real.sqrt (logScale N)⌋₊ + 1

theorem explicitCutoff_pos (N : ℕ) : 0 < explicitCutoff N := Nat.succ_pos _

theorem explicitCutoff_tendsto : Tendsto explicitCutoff atTop atTop := by
  exact (tendsto_add_atTop_nat 1).comp
    (tendsto_nat_floor_atTop.comp (Real.tendsto_sqrt_atTop.comp logScale_tendsto))

theorem explicitCutoff_budget_tendsto :
    Tendsto (fun N => (explicitCutoff N : ℝ) *
      (1 + 2 * (explicitCutoff N : ℝ)) ^ 2 * energyRate N) atTop (𝓝 0) := by
  obtain ⟨D, hD, hbound⟩ := energyRate_eventual_log_square
  have hroot := Real.tendsto_sqrt_atTop.comp logScale_tendsto
  have hlim : Tendsto (fun N => 50 * D / Real.sqrt (logScale N)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hroot
  apply squeeze_zero' (Eventually.of_forall (fun N => by
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
      (energyRate_nonneg N))) _ hlim
  filter_upwards [hbound, logScale_tendsto.eventually (eventually_ge_atTop (1 : ℝ))]
    with N hb hL
  have hL0 : 0 < logScale N := by linarith
  have hs0 : 0 < Real.sqrt (logScale N) := Real.sqrt_pos.mpr hL0
  have hs1 : 1 ≤ Real.sqrt (logScale N) := by
    nlinarith [Real.sq_sqrt hL0.le]
  have hK : (explicitCutoff N : ℝ) ≤ 2 * Real.sqrt (logScale N) := by
    have hf := Nat.floor_le (Real.sqrt_nonneg (logScale N))
    dsimp [explicitCutoff]
    push_cast
    linarith
  have hterm : (1 + 2 * (explicitCutoff N : ℝ)) ^ 2 ≤ 25 * logScale N := by
    have hu : 1 + 2 * (explicitCutoff N : ℝ) ≤ 5 * Real.sqrt (logScale N) := by
      linarith
    have hsq := (sq_le_sq₀ (by positivity : 0 ≤ 1 + 2 * (explicitCutoff N : ℝ))
      (by positivity : 0 ≤ 5 * Real.sqrt (logScale N))).mpr hu
    nlinarith [Real.sq_sqrt hL0.le]
  calc
    _ ≤ (2 * Real.sqrt (logScale N) * (25 * logScale N)) * energyRate N := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hK hterm (sq_nonneg _) (by positivity)) (energyRate_nonneg N)
    _ ≤ (2 * Real.sqrt (logScale N) * (25 * logScale N)) * (D / logScale N ^ 2) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = 50 * D / Real.sqrt (logScale N) := by
      apply (eq_div_iff hs0.ne').mpr
      calc
        _ = 50 * D * (Real.sqrt (logScale N)) ^ 2 / logScale N := by
          field_simp; ring
        _ = 50 * D := by
          rw [Real.sq_sqrt hL0.le]
          field_simp

theorem explicitCutoff_blockEnergy_tendsto :
    Tendsto (fun N => blockEnergy (explicitCutoff N) N) atTop (𝓝 0) :=
  blockEnergy_tendsto explicitCutoff explicitCutoff_budget_tendsto

theorem explicitCutoff_pair_budget_tendsto :
    Tendsto (fun N => (1 + 2 * (explicitCutoff N : ℝ)) ^ 2 * energyRate N)
      atTop (𝓝 0) := by
  apply squeeze_zero (fun N => mul_nonneg (sq_nonneg _) (energyRate_nonneg N)) _
    explicitCutoff_budget_tendsto
  intro N
  have hK : (1 : ℝ) ≤ explicitCutoff N := by exact_mod_cast explicitCutoff_pos N
  have hp : 0 ≤ (1 + 2 * (explicitCutoff N : ℝ)) ^ 2 * energyRate N :=
    mul_nonneg (sq_nonneg _) (energyRate_nonneg N)
  nlinarith

theorem explicitCutoff_covariance_tendsto :
    Tendsto (fun N => inner ℝ (residual (explicitCutoff N)) (residual N))
      atTop (𝓝 0) :=
  moving_canonical_tendsto explicitCutoff explicitCutoff_pos explicitCutoff_pair_budget_tendsto

/-- A concrete cofinal schedule, with its actual moving-test budget. -/
theorem exists_growing_canonical_tests :
    ∃ K : ℕ → ℕ, Tendsto K atTop atTop ∧ (∀ N, 0 < K N) ∧
      Tendsto (fun N => (1 + 2 * (K N : ℝ)) ^ 2 * energyRate N) atTop (𝓝 0) ∧
      Tendsto (fun N => inner ℝ (residual (K N)) (residual N)) atTop (𝓝 0) :=
  ⟨explicitCutoff, explicitCutoff_tendsto, explicitCutoff_pos,
    explicitCutoff_pair_budget_tendsto, explicitCutoff_covariance_tendsto⟩

theorem explicitCutoff_signed_block_tendsto
    (a : ℕ → ℕ → ℝ) (B : ℝ)
    (hB : ∀ N, (∑ k ∈ Finset.range (explicitCutoff N), a N k ^ 2) ≤ B) :
    Tendsto (fun N => inner ℝ (blockAverage (explicitCutoff N) (a N)) (residual N))
      atTop (𝓝 0) :=
  blockAverage_tendsto _ a B hB explicitCutoff_blockEnergy_tendsto

theorem explicitCutoff_convex_block_tendsto
    (a : ℕ → ℕ → ℝ)
    (ha : ∀ N k, k ∈ Finset.range (explicitCutoff N) → 0 ≤ a N k)
    (hsum : ∀ N, ∑ k ∈ Finset.range (explicitCutoff N), a N k = 1) :
    Tendsto (fun N => inner ℝ (blockAverage (explicitCutoff N) (a N)) (residual N))
      atTop (𝓝 0) :=
  explicitCutoff_signed_block_tendsto a 1
    (fun N => convex_coefficients_sq_le_one _ _ (ha N) (hsum N))
end RiemannResearch.RH.Pareto.MovingCovariance
