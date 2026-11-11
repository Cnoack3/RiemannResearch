/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.ShortIntervalVariance
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-! # Complete finite model transfer for prime-window energies

The application is a finite Ramanujan or truncated divisor-sum model.
The mixed term and the square of the actual model error are both retained.
The finite empirical Gram identity keeps every pair of model coefficients;
no Haar orthogonality on a different sample space is substituted.

Source: Goldston--Yildirim, Higher correlations of divisor sums related to
primes II, https://arxiv.org/abs/math/0412366, for the use of finite divisor
approximations and mixed correlations. The finite identities below are
proved directly and do not instantiate analytic estimates from that paper.
-/

noncomputable section
open scoped BigOperators
open Finset
namespace RiemannResearch.Analysis.ShortIntervalModelTransfer
open ShortIntervalVariance

def windowSum (a : ℕ → ℝ) (H x : ℕ) : ℝ :=
  ∑ j ∈ range H, a (x + j + 2)

def energy (a : ℕ → ℝ) (N H : ℕ) : ℝ :=
  ∑ x ∈ range N, (windowSum a H x) ^ 2

def pairing (a b : ℕ → ℝ) (N H : ℕ) : ℝ :=
  ∑ x ∈ range N, windowSum a H x * windowSum b H x

theorem energy_nonneg (a : ℕ → ℝ) (N H : ℕ) : 0 ≤ energy a N H :=
  sum_nonneg (fun _ _ => sq_nonneg _)

theorem windowSum_sub (a b : ℕ → ℝ) (H x : ℕ) :
    windowSum (fun n => a n - b n) H x = windowSum a H x - windowSum b H x := by
  simp [windowSum, sum_sub_distrib]

theorem energy_transfer_exact (a b : ℕ → ℝ) (N H : ℕ) :
    energy a N H = energy b N H +
      2 * pairing b (fun n => a n - b n) N H + energy (fun n => a n - b n) N H := by
  unfold energy pairing
  simp only [windowSum_sub, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro x hx
  ring

theorem energy_variational_exact (a b : ℕ → ℝ) (N H : ℕ) :
    energy a N H = 2 * pairing a b N H - energy b N H +
      energy (fun n => a n - b n) N H := by
  unfold energy pairing
  simp only [windowSum_sub, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro x hx
  ring

theorem energy_variational_lower (a b : ℕ → ℝ) (N H : ℕ) :
    2 * pairing a b N H - energy b N H ≤ energy a N H := by
  rw [energy_variational_exact a b]
  linarith [energy_nonneg (fun n => a n - b n) N H]

theorem centeredVariance_model_exact (b : ℕ → ℝ) (N H : ℕ) :
    centeredVariance N H = energy b N H +
      2 * pairing b (fun n => centeredMangoldt n - b n) N H +
      energy (fun n => centeredMangoldt n - b n) N H :=
  energy_transfer_exact centeredMangoldt b N H

/-- An unconditional lower bound for the actual centered von Mangoldt variance. -/
theorem centeredVariance_model_lower (b : ℕ → ℝ) (N H : ℕ) :
    2 * pairing centeredMangoldt b N H - energy b N H ≤ centeredVariance N H :=
  energy_variational_lower centeredMangoldt b N H

/-- A Young estimate is taken only after the exact signed identity is recorded. -/
theorem energy_transfer_abs_le (a b : ℕ → ℝ) (N H : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    |energy a N H - energy b N H| ≤
      δ * energy b N H + (1 + δ⁻¹) * energy (fun n => a n - b n) N H := by
  have point (u v : ℝ) : |(u + v)^2 - u^2| ≤ δ * u^2 + (1 + δ⁻¹) * v^2 := by
    have hplus := sq_nonneg (δ * u + v)
    have hminus := sq_nonneg (δ * u - v)
    have h1 : 2 * u * v ≤ δ * u^2 + δ⁻¹ * v^2 := by
      apply (mul_le_mul_iff_right₀ hδ).mp
      field_simp
      nlinarith
    have h2 : -(2 * u * v) ≤ δ * u^2 + δ⁻¹ * v^2 := by
      apply (mul_le_mul_iff_right₀ hδ).mp
      field_simp
      nlinarith
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg v]
  unfold energy
  rw [← sum_sub_distrib]
  calc
    _ ≤ ∑ x ∈ range N, |(windowSum a H x)^2 - (windowSum b H x)^2| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ x ∈ range N, (δ * (windowSum b H x)^2 +
        (1 + δ⁻¹) * (windowSum (fun n => a n - b n) H x)^2) := by
      apply sum_le_sum
      intro x hx
      simpa only [windowSum_sub, add_sub_cancel] using
        point (windowSum b H x) (windowSum a H x - windowSum b H x)
    _ = _ := by rw [sum_add_distrib, ← mul_sum, ← mul_sum]

def finiteModel {ι : Type*} (s : Finset ι) (c : ι → ℝ) (v : ι → ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ r ∈ s, c r * v r n

theorem finiteModel_window {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (v : ι → ℕ → ℝ) (H x : ℕ) :
    windowSum (finiteModel s c v) H x = ∑ r ∈ s, c r * windowSum (v r) H x := by
  unfold windowSum finiteModel
  rw [sum_comm]
  simp only [mul_sum]

/-- Every empirical off-diagonal Gram entry is retained. -/
theorem finiteModel_energy_gram {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (v : ι → ℕ → ℝ) (N H : ℕ) :
    energy (finiteModel s c v) N H =
      ∑ r ∈ s, ∑ t ∈ s, c r * c t * pairing (v r) (v t) N H := by
  unfold energy
  simp only [finiteModel_window, pow_two, sum_mul, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro r hr
  rw [sum_comm]
  apply sum_congr rfl
  intro t ht
  unfold pairing
  rw [mul_sum]
  apply sum_congr rfl
  intro x hx
  ring

end RiemannResearch.Analysis.ShortIntervalModelTransfer
