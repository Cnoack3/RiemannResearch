/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.SqrtPrimeErrorBarrier
import RiemannResearch.NumberTheory.PrimeNumberTheorem.MertensStretchedFloor

noncomputable section
open Filter Asymptotics
open scoped Topology
namespace RiemannResearch.NumberTheory.PrimeNumberTheorem
open RiemannResearch.Analysis

/-- A global error for the Chebyshev remainder with coefficient `c` gives every
Mertens coefficient strictly below `c^(1/(1+α))`.  The exponent `β` is
specified by `(1-β)α=β`; the full range here is `0<α<1`. -/
theorem M_logProduct_global_of_prime_error_at_rate (α β c D d : ℝ)
    (hβ : 0 < β) (hβ2 : 2 * β < 1) (hα : (1 - β) * α = β)
    (hc : 0 < c) (hD : 0 ≤ D) (hd : 0 < d)
    (hdc : d < c ^ (1 / (1 + α)))
    (hR : ∀ u : ℝ, 1 ≤ u → |R u| ≤ D * u * Real.exp (-c * (Real.log u) ^ α) /
      (1 + Real.log u) ^ 2) :
    ∃ B ≥ 0, ∀ x : ℝ, 1 ≤ x →
      |M x| ≤ B * x * Real.exp (-d * logProductPower β (6 + Real.log x)) := by
  have ha : 0 ≤ α := by
    by_contra! h
    have hbad := mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ 1 - β) h.le
    linarith only [hbad, hα, hβ]
  let K := 13 + 7 * Real.log (2 : ℝ)
  have hK : 0 ≤ K := by
    dsimp [K]
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    positivity
  obtain ⟨B, hB, hTail⟩ := stretched_envelope_bound_at_rate mertensTailEnvelope α β c D K d
    hβ hβ2 hα hD hK hd hc hdc mertensTailEnvelope_nonneg mertensTailEnvelope_le_one
    (mertensTailEnvelope_stretched_recurrence_rpow α ha c D hc.le hD hR)
  have hNat : ∀ᶠ N : ℕ in atTop, |M (N : ℝ)| ≤ B * N *
      Real.exp (-d * logProductPower β (6 + Real.log (N : ℝ))) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hN0 : 0 < (N : ℝ) := by linarith
    have he := mertensTailEnvelope_nat_bound (Real.log (N : ℝ)) N (by rw [Real.exp_log hN0])
    have hm := (div_le_iff₀ hN0).mp (he.trans (hTail _ (Real.log_nonneg hN1)))
    simpa only [add_comm (Real.log (N : ℝ)) 6, mul_assoc, mul_left_comm, mul_comm] using hm
  obtain ⟨X, hX⟩ := eventually_atTop.mp
    ((M_stretched_loglog_eventually_nat_iff_real β d B hβ.le hβ2 hd.le hB).1 hNat)
  let X' := max 1 X
  let A := Real.exp (d * logProductPower β (6 + Real.log X'))
  refine ⟨max B A, hB.trans (le_max_left _ _), fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  by_cases hxX : X ≤ x
  · exact (hX x hxX).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hx0.le) (Real.exp_pos _).le)
  · have hxX' : x ≤ X' := (lt_of_not_ge hxX).le.trans (le_max_right _ _)
    have hlog := Real.log_le_log hx0 hxX'
    have hp := logProductPower_mono β hβ.le
      (by linarith [Real.log_nonneg hx] : 1 ≤ 6 + Real.log x)
      (by linarith only [hlog] : 6 + Real.log x ≤ 6 + Real.log X')
    have hw : 1 ≤ A * Real.exp (-d * logProductPower β (6 + Real.log x)) := by
      dsimp only [A]
      rw [← Real.exp_add]
      apply Real.one_le_exp_iff.mpr
      linarith only [mul_le_mul_of_nonneg_left hp hd.le]
    have hm : |M x| ≤ x := by
      calc
        |M x| = |M (⌊x⌋₊ : ℝ)| := by simp [M]
        _ ≤ (⌊x⌋₊ : ℝ) := M_nat_abs_le_self _
        _ ≤ _ := Nat.floor_le hx0.le
    calc
      _ ≤ x := hm
      _ ≤ x * (A * Real.exp (-d * logProductPower β (6+Real.log x))) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hw hx0.le
      _ = A * x * Real.exp (-d * logProductPower β (6+Real.log x)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hx0.le)
        (Real.exp_pos _).le

/-- A Chebyshev error `O(x exp(-a (log x)^α))` for any `0 < α < 1`
gives every ordinary Mertens coefficient `d < a^(1/(1+α))` at exponent
`α/(1+α)`, globally for real `x ≥ 1`. -/
theorem M_logProduct_global_of_chebyshev_bigO (α a d : ℝ)
    (hα : 0 < α) (hα1 : α < 1) (ha : 0 < a) (hd : 0 < d)
    (hda : d < a ^ (1 / (1 + α)))
    (hPrime : (Chebyshev.psi - id) =O[atTop]
      fun x : ℝ => x * Real.exp (-a * (Real.log x) ^ α)) :
    ∃ B ≥ 0, ∀ x : ℝ, 1 ≤ x → |M x| ≤ B * x * Real.exp
      (-d * logProductPower (α / (1 + α)) (6 + Real.log x)) := by
  have hp : 0 < 1 + α := by linarith
  have hroot (b : ℝ) (hb : 0 < b) : (b ^ (1 / (1 + α))) ^ (1 + α) = b := by
    rw [← Real.rpow_mul hb.le, one_div_mul_cancel hp.ne', Real.rpow_one]
  have hpow := (Real.rpow_lt_rpow_iff hd.le (Real.rpow_pos_of_pos ha _).le hp).2 hda
  rw [hroot a ha] at hpow
  obtain ⟨c, hdc, hca⟩ := exists_between hpow
  have hc := (Real.rpow_pos_of_pos hd (1 + α)).trans hdc
  have hrate : d < c ^ (1 / (1 + α)) :=
    (Real.rpow_lt_rpow_iff hd.le (Real.rpow_pos_of_pos hc _).le hp).1 (by rwa [hroot c hc])
  obtain ⟨D, hD, hR⟩ := R_stretched_squareLog_bound_at_rate α a c hα hc hca hPrime
  refine M_logProduct_global_of_prime_error_at_rate α (α/(1+α)) c D d (div_pos hα hp) ?_ ?_
    hc hD.le hd hrate hR
  · rw [← mul_div_assoc, div_lt_one hp]; linarith
  · field_simp [hp.ne'] <;> ring

end RiemannResearch.NumberTheory.PrimeNumberTheorem
