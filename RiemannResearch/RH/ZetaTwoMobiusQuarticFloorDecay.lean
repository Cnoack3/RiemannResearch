import RiemannResearch.RH.ZetaTwoMobiusQuarticFloor
import RiemannResearch.NumberTheory.PrimeNumberTheorem.MertensAllLogPowers
import RiemannResearch.RH.MobiusReciprocalCutoff
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Unconditional logarithmic decay of the squarefree quartic floor

Source: user-provided exact optimizer cancellation manuscript, for the floor
consumer. The actual arithmetic provider is
`M_shiftedLog_all_nat_powers`; the finite reciprocal Möbius cutoff theorem
retains the complete signed summatory increments before estimating them.
No RH or optimizer cancellation hypothesis is used.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto.ZetaTwoMobiusFloor
open RiemannResearch.RH.Pareto
open RiemannResearch.RH.ZetaTwoProbability
open RiemannResearch.NumberTheory.PrimeNumberTheorem

private theorem shiftedLogPow_div_nat_tendsto_zero (p : ℕ) :
    Tendsto (fun N : ℕ => (6+Real.log (N : ℝ))^p/(N : ℝ)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hbase : Tendsto (fun N : ℕ => (Real.log (N : ℝ))^p/(N : ℝ)) atTop (𝓝 0) := by
    have h := Real.tendsto_pow_log_div_pow_atTop 1 (p : ℝ) (by norm_num : (0:ℝ) < 1)
    have hh := h.comp (tendsto_natCast_atTop_atTop :
      Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
    simpa only [Function.comp_def, Real.rpow_one, Real.rpow_natCast] using hh
  have hlim := hbase.const_mul ((2:ℝ)^p)
  simp only [mul_zero] at hlim
  apply squeeze_zero'
    (by filter_upwards [hlog.eventually (eventually_ge_atTop (6:ℝ))] with N hN
        exact div_nonneg (by positivity) (Nat.cast_nonneg _))
    _ hlim
  filter_upwards [hlog.eventually (eventually_ge_atTop (6:ℝ))] with N hN
  calc
    _ ≤ (2*Real.log (N:ℝ))^p/(N:ℝ) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact pow_le_pow_left₀ (by linarith) (by linarith) p
    _ = _ := by rw [mul_pow]; ring

private theorem inv_shiftedLog_tendsto_zero :
    Tendsto (fun N : ℕ => 1/(6+Real.log (N:ℝ))) atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hL : Tendsto (fun N : ℕ => 6+Real.log (N:ℝ)) atTop atTop :=
    tendsto_atTop_mono (fun N => by linarith) hlog
  exact tendsto_const_nhds.div_atTop hL

/-- Every fixed shifted logarithmic power of the reciprocal Möbius charge
vanishes unconditionally. The proof calls the established Mertens provider. -/
theorem mobiusReciprocalSum_abs_mul_shiftedLogPow_tendsto_zero (p : ℕ) :
    Tendsto (fun N : ℕ => |mobiusReciprocalSum N| * (6+Real.log (N:ℝ))^p)
      atTop (𝓝 0) := by
  obtain ⟨B, hB, hM⟩ := M_shiftedLog_all_nat_powers (p+2)
  have hlim : Tendsto (fun N : ℕ =>
      2*(6+Real.log (N:ℝ))^p/(N:ℝ) + B/(6+Real.log (N:ℝ))) atTop (𝓝 0) := by
    have h := ((shiftedLogPow_div_nat_tendsto_zero p).const_mul 2).add
      (inv_shiftedLog_tendsto_zero.const_mul B)
    convert h using 1 <;> first | (ext N; ring) | norm_num
  apply squeeze_zero'
    (by filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
        exact mul_nonneg (abs_nonneg _) (by
          apply pow_nonneg
          linarith [Real.log_nonneg (show (1:ℝ) ≤ N by exact_mod_cast hN)]))
    _ hlim
  filter_upwards [eventually_ge_atTop (2:ℕ)] with N hN
  have hNp : 0 < N := by omega
  have hNR : (0:ℝ) < N := by exact_mod_cast hNp
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  let L : ℝ := 6+Real.log (N:ℝ)
  have hL : 0 < L := by dsimp [L]; linarith [Real.log_nonneg hN1]
  have hLp : 0 < L^(p+2) := pow_pos hL _
  have hfreeze : ∀ y : ℝ, (N:ℝ) ≤ y → |M y| ≤ (B/L^(p+2))*y := by
    intro y hy
    have hy1 : 1 ≤ y := hN1.trans hy
    have hLy : L ≤ 6+Real.log y := by
      dsimp [L]
      linarith [Real.log_le_log hNR hy]
    have hp := pow_le_pow_left₀ hL.le hLy (p+2)
    have hh : |M y| * L^(p+2) ≤ B*y :=
      (mul_le_mul_of_nonneg_left hp (abs_nonneg _)).trans (hM y hy1)
    calc
      |M y| ≤ (B*y)/L^(p+2) := (le_div_iff₀ hLp).mpr hh
      _ = _ := by ring
  have hu := mobiusReciprocalSum_cutoff_bound_of_uniform_M_bound
    N N hNp hNp (B/L^(p+2)) (div_nonneg hB hLp.le) hfreeze
  have hH : (harmonic N : ℝ)+1 ≤ L := by
    have hh := harmonic_le_one_add_log N
    dsimp [L]
    linarith
  have hinv : 1/((N:ℝ)*(N:ℝ)) ≤ 1/(N:ℝ) := by
    exact one_div_le_one_div_of_le hNR (by nlinarith)
  have humajor : |mobiusReciprocalSum N| ≤ 2/(N:ℝ) + (B/L^(p+2))*L := by
    have hb := mul_le_mul_of_nonneg_left hH (div_nonneg hB hLp.le)
    calc
      |mobiusReciprocalSum N| ≤ 1/(N:ℝ) + 1/((N:ℝ)*(N:ℝ)) +
          (B/L^(p+2))*((harmonic N:ℝ)+1) := hu
      _ ≤ 1/(N:ℝ) + 1/(N:ℝ) + (B/L^(p+2))*L :=
        add_le_add (add_le_add le_rfl hinv) hb
      _ = _ := by ring
  have he : (2/(N:ℝ) + (B/L^(p+2))*L)*L^p =
      2*L^p/(N:ℝ)+B/L := by
    rw [show p+2 = p+1+1 by omega, pow_succ, pow_succ]
    field_simp [hL.ne', hNR.ne', pow_ne_zero p hL.ne']
  have hmul := mul_le_mul_of_nonneg_right humajor (pow_nonneg hL.le p)
  rw [he] at hmul
  simpa only [L] using hmul

/-- Full quartic trial energy has every fixed logarithmic saving. -/
theorem residual_quarticEnergy_mul_shiftedLogPow_tendsto_zero (p : ℕ) :
    Tendsto (fun N : ℕ => quarticEnergy (residual N) * (6+Real.log (N:ℝ))^p)
      atTop (𝓝 0) := by
  have hu := (mobiusReciprocalSum_abs_mul_shiftedLogPow_tendsto_zero p).mul
    mobiusReciprocalSum_tendsto_zero.abs
  have hu' : Tendsto (fun N : ℕ => (mobiusReciprocalSum N)^2 *
      (6+Real.log (N:ℝ))^p) atTop (𝓝 0) := by
    convert hu using 1 <;> first
      | (ext N; rw [← sq_abs]; ring)
      | norm_num
  have ht := (shiftedLogPow_div_nat_tendsto_zero p).const_mul (1/(3*zetaTwo))
  have hlim : Tendsto (fun N : ℕ => ((mobiusReciprocalSum N)^2 +
      1/(3*zetaTwo*(N:ℝ)))*(6+Real.log (N:ℝ))^p) atTop (𝓝 0) := by
    have hh := hu'.add ht
    convert hh using 1 <;> first
      | (ext N; simp only [div_eq_mul_inv, mul_inv_rev]; ring)
      | norm_num
  apply squeeze_zero'
    (by filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
        apply mul_nonneg
        · exact tsum_nonneg (quarticEnergyTerm_nonneg _)
        · apply pow_nonneg
          linarith [Real.log_nonneg (show (1:ℝ) ≤ N by exact_mod_cast hN)])
    _ hlim
  filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
  exact mul_le_mul_of_nonneg_right (residual_quarticEnergy_le N (by omega))
    (by apply pow_nonneg; linarith [Real.log_nonneg (show (1:ℝ) ≤ N by exact_mod_cast hN)])

/-- The actual squarefree variational floor has every fixed logarithmic saving. -/
theorem squarefreeQuarticFloor_mul_shiftedLogPow_tendsto_zero (p : ℕ) :
    Tendsto (fun N : ℕ => squarefreeQuarticFloor N * (6+Real.log (N:ℝ))^p)
      atTop (𝓝 0) := by
  apply squeeze_zero'
    (by filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
        exact mul_nonneg (squarefreeQuarticFloor_nonneg N) (by
          apply pow_nonneg
          linarith [Real.log_nonneg (show (1:ℝ) ≤ N by exact_mod_cast hN)]))
    _ (residual_quarticEnergy_mul_shiftedLogPow_tendsto_zero p)
  filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
  exact mul_le_mul_of_nonneg_right (squarefreeQuarticFloor_le_trialEnergy N) (by
    apply pow_nonneg
    linarith [Real.log_nonneg (show (1:ℝ) ≤ N by exact_mod_cast hN)])

theorem squarefreeQuarticFloor_tendsto_zero :
    Tendsto squarefreeQuarticFloor atTop (𝓝 0) := by
  simpa using squarefreeQuarticFloor_mul_shiftedLogPow_tendsto_zero 0

/-- The unconditional saving holds for every fixed real logarithmic exponent;
the statement makes no uniformity assertion in that exponent. -/
theorem squarefreeQuarticFloor_mul_shiftedLogRpow_tendsto_zero (a : ℝ) :
    Tendsto (fun N : ℕ => squarefreeQuarticFloor N *
      (6+Real.log (N:ℝ))^a) atTop (𝓝 0) := by
  obtain ⟨n, han⟩ := exists_nat_ge a
  apply squeeze_zero'
    (by filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
        apply mul_nonneg (squarefreeQuarticFloor_nonneg N)
        exact Real.rpow_nonneg (by
          linarith [Real.log_nonneg (show (1:ℝ) ≤ N by exact_mod_cast hN)]) _)
    _ (squarefreeQuarticFloor_mul_shiftedLogPow_tendsto_zero n)
  filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
  have hL : 1 ≤ 6+Real.log (N:ℝ) := by
    linarith [Real.log_nonneg (show (1:ℝ) ≤ N by exact_mod_cast hN)]
  have hp := Real.rpow_le_rpow_of_exponent_le hL han
  exact mul_le_mul_of_nonneg_left (by simpa only [Real.rpow_natCast] using hp)
    (squarefreeQuarticFloor_nonneg N)

/-- Conditional normalization transfer. The lower bound for the actual
inverse-square optimizer is explicitly required; it is not proved here. -/
theorem squarefreeQuarticFloor_normalized_tendsto_zero_of_log_lower
    (e : ℕ → ℝ) {c : ℝ} (hc : 0 < c)
    (he : ∀ᶠ N : ℕ in atTop, 0 < e N)
    (hlower : ∀ᶠ N : ℕ in atTop, c ≤ e N * (6 + Real.log (N : ℝ))) :
    Tendsto (fun N => squarefreeQuarticFloor N / e N) atTop (𝓝 0) := by
  have hlim := (squarefreeQuarticFloor_mul_shiftedLogPow_tendsto_zero 1).div_const c
  simp only [pow_one, zero_div] at hlim
  apply squeeze_zero'
    (by filter_upwards [he] with N hN
        exact div_nonneg (squarefreeQuarticFloor_nonneg N) hN.le)
    _ hlim
  filter_upwards [he, hlower] with N hN hl
  apply (div_le_div_iff₀ hN hc).mpr
  calc
    squarefreeQuarticFloor N * c ≤
        squarefreeQuarticFloor N * (e N * (6 + Real.log (N : ℝ))) :=
      mul_le_mul_of_nonneg_left hl (squarefreeQuarticFloor_nonneg N)
    _ = _ := by ring

end RiemannResearch.RH.Pareto.ZetaTwoMobiusFloor
