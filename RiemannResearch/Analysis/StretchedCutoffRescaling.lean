import RiemannResearch.Analysis.LogProductPowerBounds
/-!
# Fixed-cutoff rescaling of the logarithmic-product energy profile

Source: elementary estimates independently assembled for the user's
coefficient-mass obstruction, 28 September 2026. The RH consumer uses n/8 so
conductors up to four remain inside stage n. The rescaling preserves the
original exponent exactly, with an enlarged multiplicative constant.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.Analysis

theorem logProductPower_sub_le_sub {β s T : ℝ}
    (hβ : 0 ≤ β) (hβ2 : β ≤ 1 / 2) (hs : 6 ≤ s) (hsT : s ≤ T) :
    logProductPower β T - logProductPower β s ≤ T - s := by
  have hs0 : 0 < s := by linarith
  have hT0 : 0 < T := hs0.trans_le hsT
  have hdiv := logProductPower_div_antitone β hβ (by linarith) hs hsT
  have hmul := (div_le_div_iff₀ hT0 hs0).mp hdiv
  have hsmall := logProductPower_le_self hβ hβ2 hs
  have hp := mul_nonneg (sub_nonneg.mpr hsT) (sub_nonneg.mpr hsmall)
  apply le_of_mul_le_mul_right _ hs0
  nlinarith

theorem logProductPower_nat_eighth_le (n : ℕ) (hn : 8 ≤ n) :
    logProductPower (1 / 11) (6 + Real.log (n : ℝ)) ≤
      logProductPower (1 / 11) (6 + Real.log ((n / 8 : ℕ) : ℝ)) + Real.log 16 := by
  have hN : 1 ≤ n / 8 := by omega
  have hN0 : (0 : ℝ) < (n / 8 : ℕ) := by exact_mod_cast (show 0 < n / 8 by omega)
  have hN1 : (1 : ℝ) ≤ (n / 8 : ℕ) := by exact_mod_cast hN
  have hNn : ((n / 8 : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (Nat.div_le_self n 8)
  have hn16 : (n : ℝ) ≤ 16 * ((n / 8 : ℕ) : ℝ) := by
    exact_mod_cast (show n ≤ 16 * (n / 8) by omega)
  have hlogs : Real.log ((n / 8 : ℕ) : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log hN0 hNn
  have hlog16 : Real.log (n : ℝ) ≤ Real.log 16 + Real.log ((n / 8 : ℕ) : ℝ) := by
    calc
      _ ≤ Real.log (16 * ((n / 8 : ℕ) : ℝ)) :=
        Real.log_le_log (hN0.trans_le hNn) hn16
      _ = _ := Real.log_mul (by norm_num) hN0.ne'
  have h := logProductPower_sub_le_sub
    (β := (1 / 11 : ℝ)) (s := 6 + Real.log ((n / 8 : ℕ) : ℝ))
    (T := 6 + Real.log (n : ℝ)) (by norm_num) (by norm_num)
    (by linarith [Real.log_nonneg hN1]) (by linarith)
  linarith

/-- Rescaling by a fixed conductor factor preserves the arithmetic exponent. -/
theorem eighth_normalized_stretched_energy {a C : ℝ} (ha : 0 < a) (hC : 0 ≤ C)
    (E : ℕ → ℝ)
    (hE : ∀ᶠ N : ℕ in atTop, E N ≤ 8 + C * (N : ℝ) *
      Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (N : ℝ)))) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ n : ℕ in atTop,
      E (n / 8) / (((n / 8 : ℕ) : ℝ) + 1) ≤
        D * Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (n : ℝ))) := by
  let φ : ℕ → ℝ := fun n => logProductPower (1 / 11) (6 + Real.log (n : ℝ))
  let L : ℕ → ℝ := fun n => 6 + Real.log (n : ℝ)
  have hL : Tendsto L atTop atTop :=
    tendsto_atTop_add_const_left atTop 6
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hsmall : ∀ᶠ n : ℕ in atTop, a * (φ n / L n) < 1 := by
    have ht := ((tendsto_logProductPower_div_self (1 / 11)
      (by norm_num) (by norm_num)).comp hL).const_mul a
    simpa only [mul_zero, Function.comp_apply] using
      ht.eventually_lt_const (by simp : a * 0 < (1 : ℝ))
  have hcut : Tendsto (fun n : ℕ => n / 8) atTop atTop := by
    apply tendsto_atTop.mpr
    intro k
    filter_upwards [eventually_ge_atTop (8 * k)] with n hn
    omega
  refine ⟨64 * Real.exp 6 + C * Real.exp (a * Real.log 16), by positivity, ?_⟩
  filter_upwards [hcut.eventually hE, hsmall, eventually_ge_atTop (8 : ℕ)] with n hen hsn hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hL0 : 0 < L n := by dsimp [L]; linarith [Real.log_nonneg hn1]
  have haphi : a * φ n ≤ L n := by
    have hsn' : (a * φ n) / L n < 1 := by simpa only [mul_div_assoc] using hsn
    have hh := (div_lt_iff₀ hL0).mp hsn'
    linarith
  have hlinear : Real.exp (a * φ n) ≤ Real.exp 6 * (n : ℝ) := by
    calc
      _ ≤ Real.exp (L n) := Real.exp_le_exp.mpr haphi
      _ = _ := by dsimp [L]; rw [Real.exp_add, Real.exp_log hn0]
  have hden : 0 < ((n / 8 : ℕ) : ℝ) + 1 := by positivity
  have hratio : (n : ℝ) / (((n / 8 : ℕ) : ℝ) + 1) ≤ 8 := by
    apply (div_le_iff₀ hden).mpr
    exact_mod_cast (show n ≤ 8 * (n / 8 + 1) by omega)
  have hinverse : 8 / (((n / 8 : ℕ) : ℝ) + 1) ≤
      (64 * Real.exp 6) * Real.exp (-a * φ n) := by
    rw [show -a * φ n = -(a * φ n) by ring, Real.exp_neg, ← div_eq_mul_inv]
    apply (le_div_iff₀ (Real.exp_pos _)).mpr
    calc
      _ ≤ (8 / (((n / 8 : ℕ) : ℝ) + 1)) * (Real.exp 6 * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hlinear (by positivity)
      _ = (8 * Real.exp 6) * ((n : ℝ) / (((n / 8 : ℕ) : ℝ) + 1)) := by ring
      _ ≤ (8 * Real.exp 6) * 8 :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = _ := by ring
  have hprofile : φ n ≤ φ (n / 8) + Real.log 16 :=
    logProductPower_nat_eighth_le n hn
  have hexp : Real.exp (-a * φ (n / 8)) ≤
      Real.exp (a * Real.log 16) * Real.exp (-a * φ n) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hratio' : ((n / 8 : ℕ) : ℝ) / (((n / 8 : ℕ) : ℝ) + 1) ≤ 1 :=
    (div_le_one hden).mpr (by linarith)
  change E (n / 8) / (((n / 8 : ℕ) : ℝ) + 1) ≤
    (64 * Real.exp 6 + C * Real.exp (a * Real.log 16)) * Real.exp (-a * φ n)
  calc
    _ ≤ (8 + C * ((n / 8 : ℕ) : ℝ) * Real.exp (-a * φ (n / 8))) /
        (((n / 8 : ℕ) : ℝ) + 1) := div_le_div_of_nonneg_right hen hden.le
    _ = 8 / (((n / 8 : ℕ) : ℝ) + 1) + (C * Real.exp (-a * φ (n / 8))) *
        (((n / 8 : ℕ) : ℝ) / (((n / 8 : ℕ) : ℝ) + 1)) := by ring
    _ ≤ 8 / (((n / 8 : ℕ) : ℝ) + 1) + C * Real.exp (-a * φ (n / 8)) := by
      apply add_le_add le_rfl
      simpa using mul_le_mul_of_nonneg_left hratio' (mul_nonneg hC (Real.exp_pos _).le)
    _ ≤ (64 * Real.exp 6) * Real.exp (-a * φ n) +
        C * (Real.exp (a * Real.log 16) * Real.exp (-a * φ n)) :=
      add_le_add hinverse (mul_le_mul_of_nonneg_left hexp hC)
    _ = _ := by ring
end RiemannResearch.Analysis
