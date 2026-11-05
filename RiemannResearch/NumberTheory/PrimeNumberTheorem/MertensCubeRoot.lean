/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.NumberTheory.PrimeNumberTheorem.MertensPrimeErrorTransfer
import RiemannResearch.NumberTheory.PrimeNumberTheorem.Quantitative.ClassicalStrongPNT

/-!
# Transferring the classical prime number theorem to the ordinary Mertens function

The finite Möbius–von Mangoldt identity and the uniform tail recurrence are in
`MertensStretchedDecay`. This specialization retains the square-root prime-error
exponent throughout that recurrence. For the use of a prime error to bound a
Möbius sum, see Ramaré and Zuniga Alterman, *From explicit estimates for the
primes to explicit estimates for the Möbius function II*, §2,
https://doi.org/10.7169/facm/250121-19-5 .
-/
noncomputable section
open Filter Asymptotics
open scoped Topology
namespace RiemannResearch.NumberTheory.PrimeNumberTheorem
open RiemannResearch.Analysis

/-- A square-root prime error yields a cube-root logarithmic-product bound for
`M`, globally in the real cutoff. -/
theorem M_cubeRoot_logProduct_of_strongPNT
    (hPrime : ∃ a > 0, (Chebyshev.psi - id) =O[atTop]
      fun x : ℝ => x * Real.exp (-a * (Real.log x) ^ (1 / 2 : ℝ))) :
    ∃ d > 0, ∃ B ≥ 0, ∀ x : ℝ, 1 ≤ x →
      |M x| ≤ B * x * Real.exp (-d * logProductPower (1 / 3) (6 + Real.log x)) := by
  obtain ⟨a, ha, h⟩ := hPrime
  let d := a ^ (1 / (1 + (1 / 2 : ℝ))) / 2
  have hp := Real.rpow_pos_of_pos ha (1 / (1 + (1 / 2 : ℝ)))
  have hd : 0 < d := half_pos hp
  refine ⟨d, hd, ?_⟩
  have hM := M_logProduct_global_of_chebyshev_bigO (1 / 2) a d (by norm_num)
    (by norm_num) ha hd (half_lt_self hp) h
  norm_num at hM ⊢
  exact hM

/-- The imported classical prime number theorem supplies the only arithmetic
input to the cube-root transfer. -/
theorem M_cubeRoot_logProduct :
    ∃ d > 0, ∃ B ≥ 0, ∀ x : ℝ, 1 ≤ x →
      |M x| ≤ B * x * Real.exp (-d * logProductPower (1 / 3) (6 + Real.log x)) :=
  M_cubeRoot_logProduct_of_strongPNT Quantitative.ClassicalRegion.StrongPNT

/-- Below the cube-root exponent every fixed exponential coefficient is
admissible, with eventual prefactor one. This includes the former exponent `1/11`. -/
theorem M_logProduct_eventually_of_lt_one_third (β A : ℝ) (hβ : 0 ≤ β)
    (hβ' : β < 1 / 3) :
    ∀ᶠ x : ℝ in atTop, |M x| ≤ x * Real.exp (-A * logProductPower β (6 + Real.log x)) := by
  obtain ⟨d, hd, B, hB, hM⟩ := M_cubeRoot_logProduct
  have hs : Tendsto (fun x : ℝ => 6 + Real.log x) atTop atTop :=
    tendsto_atTop_add_const_left atTop 6 Real.tendsto_log_atTop
  have hg := ((tendsto_logProductPower_atTop (1 / 3 - β) (sub_pos.mpr hβ')).comp hs).eventually
    (eventually_ge_atTop ((A + B) / d))
  filter_upwards [hg, eventually_ge_atTop (1 : ℝ)] with x hg hx
  let s := 6 + Real.log x
  have hs6 : 6 ≤ s := by dsimp [s]; linarith [Real.log_nonneg hx]
  have hbase : 1 ≤ s * Real.log s := one_le_mul_of_one_le_of_one_le (by linarith) (one_le_log_of_six_le hs6)
  have hp : 1 ≤ logProductPower β s := Real.one_le_rpow hbase hβ
  have he : logProductPower (1 / 3 - β) s * logProductPower β s = logProductPower (1 / 3) s := by
    simp only [logProductPower, ← Real.rpow_add (zero_lt_one.trans_le hbase), sub_add_cancel]
  change (A + B) / d ≤ logProductPower (1 / 3 - β) s at hg
  have hrate := mul_le_mul_of_nonneg_right ((div_le_iff₀ hd).mp hg) (zero_le_one.trans hp)
  have hB' := le_mul_of_one_le_right hB hp
  have hsum : B - d * logProductPower (1 / 3) s ≤ -A * logProductPower β s := by
    nlinarith only [hrate, hB', congrArg (fun z : ℝ => d*z) he]
  calc
    |M x| ≤ B * x * Real.exp (-d * logProductPower (1 / 3) s) := hM x hx
    _ ≤ Real.exp B * x * Real.exp (-d * logProductPower (1 / 3) s) := by
      gcongr
      linarith [Real.add_one_le_exp B]
    _ = x * Real.exp (B - d * logProductPower (1 / 3) s) := by
      rw [show B - d * logProductPower (1 / 3) s = B + (-d * logProductPower (1 / 3) s) by ring,
        Real.exp_add]
      ring
    _ ≤ x * Real.exp (-A * logProductPower β s) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsum) (zero_le_one.trans hx)

end RiemannResearch.NumberTheory.PrimeNumberTheorem
