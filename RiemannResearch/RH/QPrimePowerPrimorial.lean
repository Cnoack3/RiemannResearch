/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QPrimePowerSieve
import RiemannResearch.Analysis.FinitePrimeProductBounds
import RiemannResearch.Analysis.PrimeProductDyadicGrowth
import RiemannResearch.Analysis.PrimeProductHeadGrowth
import Mathlib.NumberTheory.Primorial
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# The actual primorial gcd-two sieve

Source: the user-directed RH/CRT continuation of 20 October 2026. The
finite prime-product estimates are reused from `FinitePrimeProductBounds`;
the earlier `PrimeSievePointEnergy` concerns a different first-coordinate
sieve. Here the coefficient vector selects the gcd class two, whose
pointwise target is the count of positive powers of two.
-/

noncomputable section
open scoped BigOperators Topology
open Filter
namespace RiemannResearch.RH.QPrimePowerSieve
open ZetaTwoHilbert ZetaTwoProbability
open RiemannResearch.Analysis

/-- Removing the single factor two from a squarefree even number preserves totient. -/
theorem totient_div_two_of_squarefree (L : ℕ) (hsf : Squarefree L)
    (h2 : 2 ∣ L) : Nat.totient (L / 2) = Nat.totient L := by
  have he : 2 * (L / 2) = L := Nat.mul_div_cancel' h2
  have hs : Squarefree (2 * (L / 2)) := he.symm ▸ hsf
  have hc : Nat.Coprime 2 (L / 2) := Nat.coprime_of_squarefree_mul hs
  have ht := Nat.totient_mul hc
  rw [he, Nat.totient_two, one_mul] at ht
  exact ht.symm

/-- The exact gcd-two slope is the ordinary finite Euler product. -/
theorem sieveSlope_primorial_two (H : ℕ) (hH : 2 ≤ H) :
    sieveSlope (primorial H) 2 = finitePrimeProduct H := by
  have h2 : 2 ∣ primorial H := Nat.prime_two.dvd_primorial_iff.mpr hH
  have h2mem : 2 ∈ (primorial H).divisors :=
    Nat.mem_divisors.mpr ⟨h2, primorial_ne_zero H⟩
  rw [sieveSlope_eq_totient _ _ (primorial_pos H) h2mem,
    totient_div_two_of_squarefree _ (squarefree_primorial H) h2]
  have ht : ((primorial H).totient : ℝ) = (primorial H : ℝ) *
      finitePrimeProduct H := by
    have ht := congrArg (fun q : ℚ => (q : ℝ))
      (Nat.totient_eq_mul_prod_factors (primorial H))
    push_cast at ht
    rw [primeFactors_primorial] at ht
    simpa only [finitePrimeProduct, Nat.primesLE, Nat.succ_eq_add_one,
      one_div] using ht
  rw [ht]
  have hL : (primorial H : ℝ) ≠ 0 := by exact_mod_cast primorial_ne_zero H
  field_simp

/-- No existential coefficient choice: this is the actual finite primorial synthesis. -/
def primePowerTwoVector (H : ℕ) : QHilbert := sieveVector (primorial H) 2

theorem primePowerTwoVector_mem_squarefreeSpan (H : ℕ) :
    primePowerTwoVector H ∈ qSquarefreeCRTSpan :=
  sieveVector_mem_squarefreeSpan _ _ (primorial_pos H) (squarefree_primorial H)

theorem qSequence_primePowerTwoVector (H n : ℕ) (hH : 2 ≤ H) :
    qSequence (primePowerTwoVector H) n =
      sieveCount (primorial H) 2 n - finitePrimeProduct H * (n : ℝ) := by
  rw [primePowerTwoVector, qSequence_sieveVector _ _ _ (primorial_pos H),
    sieveSlope_primorial_two H hH]

/-- The complete finite head is exactly the logarithmic target plus its signed drift. -/
theorem qSequence_primePowerTwoVector_head (H n : ℕ) (hH : 2 ≤ H) (hnH : n ≤ H) :
    qSequence (primePowerTwoVector H) n =
      (Nat.log 2 n : ℝ) - finitePrimeProduct H * (n : ℝ) := by
  have hc : ∀ q : ℕ, q.Prime → q ≤ H → q ∣ primorial H := by
    intro q hq hqH
    exact hq.dvd_primorial_iff.mpr hqH
  simpa only [primePowerTwoVector, sieveSlope_primorial_two H hH] using
    qSequence_sieveVector_head (primorial H) 2 H n (primorial_pos H)
      Nat.prime_two (squarefree_primorial H)
      (Nat.prime_two.dvd_primorial_iff.mpr hH) hc hnH

/-- Pointwise convergence follows from the exact head and Euler's prime-product decay. -/
theorem primePowerTwoVector_pointwise (n : ℕ) :
    Tendsto (fun H => qSequence (primePowerTwoVector H) n) atTop
      (𝓝 (Nat.log 2 n : ℝ)) := by
  have ht : Tendsto (fun H => (Nat.log 2 n : ℝ) - finitePrimeProduct H * (n : ℝ))
      atTop (𝓝 (Nat.log 2 n : ℝ)) := by
    simpa only [zero_mul, sub_zero] using
      tendsto_const_nhds.sub (finitePrimeProduct_tendsto_zero.mul_const (n : ℝ))
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (max 2 n)] with H hH
  exact (qSequence_primePowerTwoVector_head H n
    ((le_max_left 2 n).trans hH) ((le_max_right 2 n).trans hH)).symm

/-- A complete-Q bound with all arithmetic providers concretely discharged. -/
theorem primePowerTwoVector_norm_lower (H : ℕ) (hH : 2 ≤ H) :
    finitePrimeProduct H ^ 2 * (H : ℝ) / (2 * zetaTwo) -
      (Nat.log 2 H : ℝ) ^ 2 ≤ ‖primePowerTwoVector H‖ ^ 2 := by
  have hc : ∀ q : ℕ, q.Prime → q ≤ H → q ∣ primorial H := by
    intro q hq hqH
    exact hq.dvd_primorial_iff.mpr hqH
  simpa only [primePowerTwoVector, sieveSlope_primorial_two H hH] using
    sieveVector_norm_lower (primorial H) 2 H (primorial_pos H) Nat.prime_two hc

/-- The concrete dyadic subsequence escapes every complete-Q norm bound. -/
theorem primePowerTwoVector_dyadic_norm_sq_tendsto_atTop :
    Tendsto (fun m : ℕ => ‖primePowerTwoVector (64 ^ m)‖ ^ 2) atTop atTop := by
  have hg := finitePrimeProduct_dyadic_head_tendsto_atTop zetaTwo zetaTwo_pos
  apply tendsto_atTop.2
  intro b
  filter_upwards [hg.eventually (eventually_ge_atTop b), eventually_ge_atTop 1]
    with m hm hm1
  have h64 : 2 ≤ 64 ^ m := by
    have hpow : 64 ^ 1 ≤ 64 ^ m := Nat.pow_le_pow_right (by decide) hm1
    norm_num at hpow
    omega
  have hlog : Nat.log 2 (64 ^ m) = 6 * m := by
    have he : (64 : ℕ) ^ m = 2 ^ (6 * m) := by
      rw [pow_mul]
      norm_num
    rw [he, Nat.log_pow (by decide : 1 < 2)]
  have hn := primePowerTwoVector_norm_lower (64 ^ m) h64
  rw [hlog] at hn
  push_cast at hm hn
  exact hm.trans hn

/-- Hence the complete Q norms of this actual legal subsequence tend to infinity. -/
theorem primePowerTwoVector_dyadic_norm_tendsto_atTop :
    Tendsto (fun m : ℕ => ‖primePowerTwoVector (64 ^ m)‖) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [primePowerTwoVector_dyadic_norm_sq_tendsto_atTop.eventually
    (eventually_ge_atTop ((max b 0) ^ 2))] with m hm
  have hn : 0 ≤ ‖primePowerTwoVector (64 ^ m)‖ := norm_nonneg _
  have hmax : 0 ≤ max b 0 := le_max_right _ _
  have hs : max b 0 ≤ ‖primePowerTwoVector (64 ^ m)‖ :=
    (sq_le_sq₀ hmax hn).mp hm
  exact (le_max_left b 0).trans hs

/-- Every sufficiently large cutoff has large norm, not only the dyadic subsequence. -/
theorem primePowerTwoVector_norm_sq_tendsto_atTop :
    Tendsto (fun H : ℕ => ‖primePowerTwoVector H‖ ^ 2) atTop atTop := by
  have hg := finitePrimeProduct_head_tendsto_atTop zetaTwo zetaTwo_pos
  apply tendsto_atTop.2
  intro b
  filter_upwards [hg.eventually (eventually_ge_atTop b), eventually_ge_atTop 2]
    with H hH hH2
  exact hH.trans (primePowerTwoVector_norm_lower H hH2)

/-- The unsmoothed gcd-two prime sieve diverges in the complete Q norm. -/
theorem primePowerTwoVector_norm_tendsto_atTop :
    Tendsto (fun H : ℕ => ‖primePowerTwoVector H‖) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [primePowerTwoVector_norm_sq_tendsto_atTop.eventually
    (eventually_ge_atTop ((max b 0) ^ 2))] with H hH
  have hn : 0 ≤ ‖primePowerTwoVector H‖ := norm_nonneg _
  have hmax : 0 ≤ max b 0 := le_max_right _ _
  have hs : max b 0 ≤ ‖primePowerTwoVector H‖ := (sq_le_sq₀ hmax hn).mp hH
  exact (le_max_left b 0).trans hs

end RiemannResearch.RH.QPrimePowerSieve
