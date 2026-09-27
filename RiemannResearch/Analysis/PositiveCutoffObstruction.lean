/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.PowerLogProfileObstruction

/-!
# Necessary conditions on positive recurrence certificates

Source: the explicit recurrence audited in `RH/MertensStretchedContinuation20260927.md`.
These are restrictions on termwise positive supersolution/contraction certificates,
not lower bounds for the Mertens function. The forcing prefactor 1/T is retained.
The actual signed identity and signed Abel cancellation remain outside this obstruction.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.Analysis

/-- The tenth root identity used to eliminate a nonnegative cutoff. -/
theorem cutoff_tenth_root_pow (L : ℝ) (hL : 0 ≤ L) :
    (L ^ ((1 : ℝ) / 10)) ^ 10 = L := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hL]
  norm_num

/-- Exact algebraic obstruction, retaining the additive logarithmic slack in
the forcing budget. This is a restriction on a positive certificate. -/
theorem positive_cutoff_exact_algebraic_obstruction
    (p c L κ s q T : ℝ)
    (hp : 0 ≤ p) (hc : 0 ≤ c) (hL : 0 ≤ L) (hκ : 0 ≤ κ)
    (hdeficit : 0 ≤ p - s)
    (hforce : p ≤ c * L ^ ((1 : ℝ) / 10) + s)
    (hshift : κ * p * L ≤ T * q) :
    κ * p * (p - s) ^ 10 ≤ c ^ 10 * T * q := by
  have hr : 0 ≤ L ^ ((1 : ℝ) / 10) := Real.rpow_nonneg hL _
  have hroot : p - s ≤ c * L ^ ((1 : ℝ) / 10) := by linarith
  have hpow : (p - s) ^ 10 ≤ c ^ 10 * L := by
    calc
      (p - s) ^ 10 ≤ (c * L ^ ((1 : ℝ) / 10)) ^ 10 :=
        pow_le_pow_left₀ hdeficit hroot 10
      _ = c ^ 10 * L := by rw [mul_pow, cutoff_tenth_root_pow L hL]
  calc
    κ * p * (p - s) ^ 10 ≤ κ * p * (c ^ 10 * L) :=
      mul_le_mul_of_nonneg_left hpow (mul_nonneg hκ hp)
    _ = c ^ 10 * (κ * p * L) := by ring
    _ ≤ c ^ 10 * (T * q) :=
      mul_le_mul_of_nonneg_left hshift (pow_nonneg hc _)
    _ = c ^ 10 * T * q := by ring

/-- Once the logarithmic forcing slack uses at most half the trial exponent,
positive forcing absorption and a regular lower shift force the eleventh-power
budget. No hypothesis on an arithmetic envelope occurs in this theorem. -/
theorem positive_cutoff_algebraic_obstruction
    (p c L κ s q T : ℝ)
    (hp : 0 ≤ p) (_hc : 0 ≤ c) (hL : 0 ≤ L) (hκ : 0 ≤ κ)
    (hforce : p ≤ c * L ^ ((1 : ℝ) / 10) + s)
    (hslack : 2 * s ≤ p)
    (hshift : κ * p * L ≤ T * q) :
    κ * p ^ 11 ≤ (2 * c) ^ 10 * T * q := by
  have hroot : p ≤ (2 * c) * L ^ ((1 : ℝ) / 10) := by linarith
  have hpow : p ^ 10 ≤ (2 * c) ^ 10 * L := by
    calc
      p ^ 10 ≤ ((2 * c) * L ^ ((1 : ℝ) / 10)) ^ 10 :=
        pow_le_pow_left₀ hp hroot 10
      _ = (2 * c) ^ 10 * L := by rw [mul_pow, cutoff_tenth_root_pow L hL]
  calc
    κ * p ^ 11 = κ * p * p ^ 10 := by ring
    _ ≤ κ * p * ((2 * c) ^ 10 * L) :=
      mul_le_mul_of_nonneg_left hpow (mul_nonneg hκ hp)
    _ = (2 * c) ^ 10 * (κ * p * L) := by ring
    _ ≤ (2 * c) ^ 10 * (T * q) :=
      mul_le_mul_of_nonneg_left hshift (by positivity)
    _ = (2 * c) ^ 10 * T * q := by ring

/-- Logarithmic budgets forced by an operational positive-cutoff certificate.
`delta` is the trial profile loss across the delay. The forcing term has retained
its factor `1/T`: discarding this factor would incorrectly remove `log T` from
the necessary forcing budget. -/
theorem positive_cutoff_certificate_log_budgets
    (p c L K T H delta : ℝ) (hT : 0 < T) (hH : 0 < H)
    (hA : 1 ≤ 3 * L + K)
    (hforcing : Real.exp (p - c * L ^ ((1 : ℝ) / 10)) / T ≤ H)
    (hcontraction : (3 * L + K) * Real.exp delta / T ≤ 1) :
    p ≤ c * L ^ ((1 : ℝ) / 10) + Real.log T + Real.log H ∧
      delta ≤ Real.log T := by
  constructor
  · have hf : Real.exp (p - c * L ^ ((1 : ℝ) / 10)) ≤ H * T :=
      (div_le_iff₀ hT).mp hforcing
    have hlog : p - c * L ^ ((1 : ℝ) / 10) ≤ Real.log T + Real.log H := by
      apply Real.exp_le_exp.mp
      calc
        Real.exp (p - c * L ^ ((1 : ℝ) / 10)) ≤ H * T := hf
        _ = Real.exp (Real.log T + Real.log H) := by
          rw [Real.exp_add, Real.exp_log hT, Real.exp_log hH]
          ring
    linarith
  · have ha : (3 * L + K) * Real.exp delta ≤ T := by
      simpa only [one_mul] using (div_le_iff₀ hT).mp hcontraction
    apply Real.exp_le_exp.mp
    calc
      Real.exp delta ≤ (3 * L + K) * Real.exp delta := by
        nlinarith [Real.exp_pos delta]
      _ ≤ T := ha
      _ = Real.exp (Real.log T) := (Real.exp_log hT).symm

/-- A concrete necessary eleventh-power budget for the existing positive
recurrence/cutoff framework. `hshift` is an explicit regular-profile lower bound,
not a consequence of positivity of the unknown arithmetic envelope. -/
theorem positive_cutoff_certificate_eleventh_power
    (p c L K T H delta κ : ℝ)
    (hp : 0 ≤ p) (hc : 0 ≤ c) (hL : 0 ≤ L) (hT : 0 < T)
    (hH : 0 < H) (hκ : 0 ≤ κ) (hA : 1 ≤ 3 * L + K)
    (hforcing : Real.exp (p - c * L ^ ((1 : ℝ) / 10)) / T ≤ H)
    (hcontraction : (3 * L + K) * Real.exp delta / T ≤ 1)
    (hslack : 2 * (Real.log T + Real.log H) ≤ p)
    (hshift : κ * p * L / T ≤ delta) :
    κ * p ^ 11 ≤ (2 * c) ^ 10 * T * Real.log T := by
  obtain ⟨hf, hd⟩ := positive_cutoff_certificate_log_budgets
    p c L K T H delta hT hH hA hforcing hcontraction
  apply positive_cutoff_algebraic_obstruction p c L κ
    (Real.log T + Real.log H) (Real.log T) T hp hc hL hκ
  · linarith
  · exact hslack
  · have h := (div_le_iff₀ hT).mp (hshift.trans hd)
    nlinarith

/- The following lemmas retain the complete finite logarithmic slack and
contraction coefficient. -/

/-- The exact finite logarithmic budgets of the positive certificate. -/
theorem positive_cutoff_certificate_sharp_log_budgets
    (p c L K T H delta : ℝ) (hT : 0 < T) (hH : 0 < H)
    (hA : 0 < 3 * L + K)
    (hforcing : Real.exp (p - c * L ^ ((1 : ℝ) / 10)) / T ≤ H)
    (hcontraction : (3 * L + K) * Real.exp delta / T ≤ 1) :
    p ≤ c * L ^ ((1 : ℝ) / 10) + Real.log (T * H) ∧
      delta ≤ Real.log (T / (3 * L + K)) := by
  constructor
  · have hf : Real.exp (p - c * L ^ ((1 : ℝ) / 10)) ≤ H * T :=
      (div_le_iff₀ hT).mp hforcing
    have hlog : p - c * L ^ ((1 : ℝ) / 10) ≤ Real.log (T * H) := by
      apply Real.exp_le_exp.mp
      calc
        Real.exp (p - c * L ^ ((1 : ℝ) / 10)) ≤ H * T := hf
        _ = Real.exp (Real.log (T * H)) := by
          rw [Real.exp_log (mul_pos hT hH)]
          ring
    linarith
  · have ha : (3 * L + K) * Real.exp delta ≤ T := by
      simpa only [one_mul] using (div_le_iff₀ hT).mp hcontraction
    apply (Real.le_log_iff_exp_le (div_pos hT hA)).mpr
    apply (le_div_iff₀ hA).mpr
    simpa only [mul_comm] using ha

/-- The strongest finite algebraic obstruction supplied by these separate
positive forcing and contraction budgets: both polynomial slack and the full
cutoff prefactor are retained. -/
theorem positive_cutoff_certificate_exact_deficit
    (p c L K T H delta κ : ℝ)
    (hp : 0 ≤ p) (hc : 0 ≤ c) (hL : 0 ≤ L) (hT : 0 < T)
    (hH : 0 < H) (hκ : 0 ≤ κ) (hA : 0 < 3 * L + K)
    (hforcing : Real.exp (p - c * L ^ ((1 : ℝ) / 10)) / T ≤ H)
    (hcontraction : (3 * L + K) * Real.exp delta / T ≤ 1)
    (hdeficit : 0 ≤ p - (Real.log (T * H)))
    (hshift : κ * p * L / T ≤ delta) :
    κ * p * (p - (Real.log (T * H))) ^ 10 ≤
      c ^ 10 * T * Real.log (T / (3 * L + K)) := by
  obtain ⟨hf, hd⟩ := positive_cutoff_certificate_sharp_log_budgets
    p c L K T H delta hT hH hA hforcing hcontraction
  apply positive_cutoff_exact_algebraic_obstruction p c L κ
    (Real.log (T * H)) (Real.log (T / (3 * L + K))) T hp hc hL hκ hdeficit
  · linarith
  · have h := (div_le_iff₀ hT).mp (hshift.trans hd)
    nlinarith



/-- The separate budgets follow from a positive supersolution certificate.
For a trial majorant `B * exp (-p)`, the recurrence's PNT source coefficient is
`J = 3 * D / B`; the omitted nonnegative source is `U = (3 / B) * exp (p-L)`.
The strict hypothesis `J>0` is essential for extracting a forcing restriction. -/
theorem positive_cutoff_budgets_of_supersolution
    (p c L K T delta J U : ℝ) (hT : 0 < T) (hJ : 0 < J)
    (hU : 0 ≤ U) (hA : 0 ≤ 3 * L + K)
    (hcertificate : ((3 * L + K) * Real.exp delta + U +
      J * Real.exp (p - c * L ^ ((1 : ℝ) / 10))) / T ≤ 1) :
    Real.exp (p - c * L ^ ((1 : ℝ) / 10)) / T ≤ 1 / J ∧
      (3 * L + K) * Real.exp delta / T ≤ 1 := by
  have hcert : (3 * L + K) * Real.exp delta + U +
      J * Real.exp (p - c * L ^ ((1 : ℝ) / 10)) ≤ T := by
    simpa only [one_mul] using (div_le_iff₀ hT).mp hcertificate
  have ha : 0 ≤ (3 * L + K) * Real.exp delta :=
    mul_nonneg hA (Real.exp_pos _).le
  have hj : 0 ≤ J * Real.exp (p - c * L ^ ((1 : ℝ) / 10)) :=
    mul_nonneg hJ.le (Real.exp_pos _).le
  constructor
  · apply (div_le_div_iff₀ hT hJ).mpr
    nlinarith
  · apply (div_le_iff₀ hT).mpr
    nlinarith

/-- The recurrence alone imposes no restriction on a decay profile: the zero
envelope satisfies it. Necessity statements must therefore concern the positive
supersolution certificate, rather than the unknown arithmetic envelope itself. -/
theorem zero_envelope_positive_recurrence (c D K : ℝ) (hD : 0 ≤ D)
    (T L : ℝ) (hT : 0 < T) :
    (0 : ℝ) ≤ ((3 * L + K) * 0 + 3 * Real.exp (-L) +
      3 * D * Real.exp (-c * L ^ ((1 : ℝ) / 10))) / T := by
  simp only [mul_zero, zero_add]
  positivity



/-- Necessity for regular trial envelopes certified by the positive recurrence.
The delayed argument must stay in the explicit regular-profile region, the normalized positive prime
forcing must remain bounded, and the delayed coefficient must be at most one.
These are hypotheses on a proof certificate, not on the actual Mertens error.
No monotonicity of the cutoff function is assumed. -/
theorem regular_trial_positive_cutoff_exponents_necessary
    (b β η c K H : ℝ) (L : ℝ → ℝ)
    (hb : 0 < b) (hβ : 0 < β) (hc : 0 ≤ c) (hH : 0 < H)
    (hregion : ∀ᶠ T : ℝ in atTop,
      1 < T - L T - Real.log 2 ∧
      2 * |η| ≤ β * Real.log (T - L T - Real.log 2))
    (hcert : ∀ᶠ T : ℝ in atTop,
      0 ≤ L T ∧ 1 ≤ 3 * L T + K ∧
      Real.exp (b * (T ^ β * (Real.log T) ^ η) -
        c * (L T) ^ ((1 : ℝ) / 10)) / T ≤ H ∧
      (3 * L T + K) * Real.exp
        (b * (T ^ β * (Real.log T) ^ η) -
          b * ((T - L T - Real.log 2) ^ β *
            (Real.log (T - L T - Real.log 2)) ^ η)) / T ≤ 1) :
    β ≤ (1 : ℝ) / 11 ∧ (β = (1 : ℝ) / 11 → η ≤ (1 : ℝ) / 11) := by
  let κ := β / (β + 2)
  have hκ : 0 < κ := by dsimp [κ]; positivity
  apply scaled_regular_profile_exponents_of_power_budget b β η
    ((2 * c) ^ 10 / κ) hb
  filter_upwards [hcert, eventually_gt_atTop (1 : ℝ), hregion,
    regular_profile_eventually_superlog b β η H hb hβ] with T hcert hT hregion hslack
  obtain ⟨hr, hs⟩ := hregion
  obtain ⟨hL, hA, hf, hcontract⟩ := hcert
  let r := T - L T - Real.log 2
  let p := b * (T ^ β * (Real.log T) ^ η)
  have hT0 : 0 < T := by linarith
  have hlogT : 0 < Real.log T := Real.log_pos hT
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hshift := regular_profile_lower_cutoff_shift b β η T (L T) r
    hb.le hβ hL hr rfl hs
  have hbudget := positive_cutoff_certificate_eleventh_power p c (L T) K T H
    (p - b * (r ^ β * (Real.log r) ^ η)) κ hp hc hL hT0 hH hκ.le hA
    hf hcontract hslack hshift
  have hh : p ^ 11 ≤ ((2 * c) ^ 10 * T * Real.log T) / κ := by
    apply (le_div_iff₀ hκ).mpr
    simpa only [mul_comm] using hbudget
  change p ^ 11 ≤ ((2 * c) ^ 10 / κ) * T * Real.log T
  convert hh using 1; ring

/-- A delayed argument tending to infinity automatically enters the regular
profile region required by the necessity theorem. -/
theorem regular_trial_positive_cutoff_exponents_of_delay_tendsto
    (b β η c K H : ℝ) (L : ℝ → ℝ)
    (hb : 0 < b) (hβ : 0 < β) (hc : 0 ≤ c) (hH : 0 < H)
    (hdelay : Tendsto (fun T => T - L T - Real.log 2) atTop atTop)
    (hcert : ∀ᶠ T : ℝ in atTop,
      0 ≤ L T ∧ 1 ≤ 3 * L T + K ∧
      Real.exp (b * (T ^ β * (Real.log T) ^ η) -
        c * (L T) ^ ((1 : ℝ) / 10)) / T ≤ H ∧
      (3 * L T + K) * Real.exp
        (b * (T ^ β * (Real.log T) ^ η) -
          b * ((T - L T - Real.log 2) ^ β *
            (Real.log (T - L T - Real.log 2)) ^ η)) / T ≤ 1) :
    β ≤ (1 : ℝ) / 11 ∧ (β = (1 : ℝ) / 11 → η ≤ (1 : ℝ) / 11) := by
  apply regular_trial_positive_cutoff_exponents_necessary b β η c K H L hb hβ hc hH
    ?_ hcert
  filter_upwards [hdelay.eventually (eventually_gt_atTop (1 : ℝ)),
    (Real.tendsto_log_atTop.comp hdelay).eventually
      (eventually_ge_atTop (2 * |η| / β))] with T hr hsize
  refine ⟨hr, ?_⟩
  have hh := (div_le_iff₀ hβ).mp hsize
  simpa only [Function.comp_apply, mul_comm] using hh

end RiemannResearch.Analysis
