import RiemannResearch.RH.CanonicalMobiusPNT
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Reciprocal Möbius square-log rate from finite cutoff bounds

The arithmetic cutoff estimate is explicit in the hypotheses. No quantitative
arithmetic premise is discharged by the elementary limiting arguments below.
Source: the cutoff argument developed for HardyEndpointFormalization20260924.md;
the rate is composed with an unconditional provider in MobiusQuantitativeRate.
-/

noncomputable section
open Filter Real
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto

theorem eventually_loglog_bound_of_cutoff_bound (f : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hcut : ∀ᶠ N : ℕ in atTop, ∀ K : ℕ, 0 < K →
      |f N| ≤ 1/(K : ℝ) + 1/((N : ℝ)*K) +
        C*((harmonic K : ℝ)+1)/Real.log N) :
    ∀ᶠ N : ℕ in atTop,
      |f N| ≤ (2+2*C)*(1+Real.log (Real.log N+1))/Real.log N := by
  filter_upwards [hcut, eventually_ge_atTop (3 : ℕ)] with N hNcut hN
  have hNr : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hL : 0 < Real.log (N : ℝ) := Real.log_pos hNr
  let K : ℕ := ⌊Real.log (N : ℝ)⌋₊+1
  have hK : 0 < K := by dsimp [K]; omega
  have hKlow : Real.log (N : ℝ) < (K : ℝ) := by
    simpa only [K, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one (Real.log (N : ℝ))
  have hKhi : (K : ℝ) ≤ Real.log (N : ℝ)+1 := by
    dsimp [K]
    push_cast
    linarith [Nat.floor_le hL.le]
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hH : (harmonic K : ℝ) ≤ 1+Real.log (Real.log (N : ℝ)+1) := by
    exact (harmonic_le_one_add_log K).trans
      (by linarith [Real.log_le_log hKr hKhi])
  have h1 : 1/(K : ℝ) ≤ 1/Real.log N :=
    one_div_le_one_div_of_le hL hKlow.le
  have hNK : (K : ℝ) ≤ (N : ℝ)*K := by nlinarith
  have h2 : 1/((N : ℝ)*K) ≤ 1/Real.log N :=
    (one_div_le_one_div_of_le hKr hNK).trans h1
  have h3 : C*((harmonic K : ℝ)+1)/Real.log N ≤
      C*(2+Real.log (Real.log (N : ℝ)+1))/Real.log N := by
    apply div_le_div_of_nonneg_right _ hL.le
    exact mul_le_mul_of_nonneg_left (by linarith) hC
  have hq : 0 ≤ Real.log (Real.log (N : ℝ)+1) :=
    Real.log_nonneg (by linarith)
  have hp := hNcut K hK
  have hlast : 1/Real.log (N : ℝ) + 1/Real.log (N : ℝ) +
      C*(2+Real.log (Real.log (N : ℝ)+1))/Real.log N ≤
      (2+2*C)*(1+Real.log (Real.log (N : ℝ)+1))/Real.log N := by
    calc
      _ = (2+C*(2+Real.log (Real.log (N : ℝ)+1)))/Real.log N := by ring
      _ ≤ _ := (div_le_div_iff_of_pos_right hL).2 (by nlinarith)
  linarith

theorem tendsto_one_add_log_sq_div :
    Tendsto (fun x : ℝ => (1+Real.log x)^2/x) atTop (𝓝 0) := by
  have h2 := Real.tendsto_pow_log_div_pow_atTop 1 2 (by norm_num : (0 : ℝ) < 1)
  have h1 := Real.tendsto_pow_log_div_pow_atTop 1 1 (by norm_num : (0 : ℝ) < 1)
  simp only [Real.rpow_one, Real.rpow_two, pow_one] at h1 h2
  have h0 : Tendsto (fun x : ℝ => 1/x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have h := h0.add ((h1.const_mul 2).add h2)
  convert h using 1 <;> solve | (ext x; ring) | norm_num

theorem square_mul_log_tendsto_zero_of_loglog_bound (f : ℕ → ℝ) (B : ℝ)
    (hB : 0 ≤ B)
    (hb : ∀ᶠ N : ℕ in atTop,
      |f N| ≤ B*(1+Real.log (Real.log N+1))/Real.log N) :
    Tendsto (fun N : ℕ => (f N)^2 * Real.log N) atTop (𝓝 0) := by
  have hL : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hLp : Tendsto (fun N : ℕ => Real.log (N : ℝ)+1) atTop atTop :=
    tendsto_atTop_mono (fun N => by linarith) hL
  have hlim := (tendsto_one_add_log_sq_div.comp hLp).const_mul (2*B^2)
  simp only [Function.comp_def, mul_zero] at hlim
  apply squeeze_zero'
    (by filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
        exact mul_nonneg (sq_nonneg _) (Real.log_nonneg (by exact_mod_cast hN)))
    _ hlim
  filter_upwards [hb, hL.eventually (eventually_ge_atTop (1 : ℝ))] with N hN hL1
  have hL0 : 0 < Real.log (N : ℝ) := by linarith
  have hLp0 : 0 < Real.log (N : ℝ)+1 := by linarith
  have hq : 0 ≤ 1+Real.log (Real.log (N : ℝ)+1) := by
    linarith [Real.log_nonneg (show 1 ≤ Real.log (N : ℝ)+1 by linarith)]
  have hsq : (f N)^2 ≤
      (B*(1+Real.log (Real.log (N : ℝ)+1))/Real.log N)^2 := by
    simpa only [← sq, sq_abs] using mul_self_le_mul_self (abs_nonneg (f N)) hN
  have hmul := mul_le_mul_of_nonneg_right hsq hL0.le
  have he :
      (B*(1+Real.log (Real.log (N : ℝ)+1))/Real.log N)^2 * Real.log N =
      B^2*(1+Real.log (Real.log (N : ℝ)+1))^2/Real.log N := by
    field_simp [hL0.ne'] <;> ring
  change (f N)^2 * Real.log N ≤
    2*B^2*((1+Real.log (Real.log (N : ℝ)+1))^2/(Real.log N+1))
  calc
    _ ≤ B^2*(1+Real.log (Real.log (N : ℝ)+1))^2/Real.log N := by
      simpa only [he] using hmul
    _ ≤ (2*B^2*(1+Real.log (Real.log (N : ℝ)+1))^2)/(Real.log N+1) := by
      apply (div_le_div_iff₀ hL0 hLp0).2
      nlinarith [mul_nonneg (sq_nonneg B)
        (sq_nonneg (1+Real.log (Real.log (N : ℝ)+1)))]
    _ = _ := by ring

theorem square_mul_log_tendsto_zero_of_cutoff_bound (f : ℕ → ℝ) (C : ℝ)
    (hC : 0 ≤ C)
    (hcut : ∀ᶠ N : ℕ in atTop, ∀ K : ℕ, 0 < K →
      |f N| ≤ 1/(K : ℝ) + 1/((N : ℝ)*K) +
        C*((harmonic K : ℝ)+1)/Real.log N) :
    Tendsto (fun N : ℕ => (f N)^2 * Real.log N) atTop (𝓝 0) :=
  square_mul_log_tendsto_zero_of_loglog_bound f (2+2*C) (by positivity)
    (eventually_loglog_bound_of_cutoff_bound f C hC hcut)

/-- The exact logarithmic factor occurring in the raw endpoint correction
also tends to zero under the square-log rate. -/
theorem square_mul_log_succ_add_half_tendsto_zero (f : ℕ → ℝ)
    (hlog : Tendsto (fun N : ℕ => (f N)^2 * Real.log N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (f N)^2 *
      (Real.log ((N : ℝ)+1) + 1/2)) atTop (𝓝 0) := by
  have hL : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsq : Tendsto (fun N : ℕ => (f N)^2) atTop (𝓝 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall (fun N => sq_nonneg (f N)))
      (by filter_upwards [hL.eventually (eventually_ge_atTop (1 : ℝ))] with N hN
          nlinarith [sq_nonneg (f N)]) hlog
  have hlim := hlog.add (hsq.const_mul (3/2 : ℝ))
  simp only [mul_zero, zero_add] at hlim
  apply squeeze_zero'
    (by filter_upwards [] with N
        apply mul_nonneg (sq_nonneg _)
        have := Real.log_nonneg (show 1 ≤ (N : ℝ)+1 by
          have := Nat.cast_nonneg (α := ℝ) N
          linarith)
        linarith)
    _ hlim
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hbound : Real.log ((N : ℝ)+1) ≤ Real.log (N : ℝ)+1 := by
    have hl := Real.log_le_log (show 0 < (N : ℝ)+1 by positivity)
      (show (N : ℝ)+1 ≤ 2*(N : ℝ) by linarith)
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hN0.ne'] at hl
    have h2 : Real.log (2 : ℝ) ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at this
      exact this
    linarith
  nlinarith [mul_nonneg (sq_nonneg (f N)) (show
    0 ≤ Real.log (N : ℝ)+1-Real.log ((N : ℝ)+1) by linarith)]

end RiemannResearch.RH.Pareto
