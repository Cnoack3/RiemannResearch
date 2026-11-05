/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Find
import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Order.LiminfLimsup
import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Cofinal cutoffs for one-sided moment estimates

Reducing a monotone prefix to nearby powers preserves logarithmic growth. Extended-real lower limits include infinite growth of the ratio.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.Analysis.CofinalMoments

/-- Locate an arbitrary integer cutoff between consecutive eighth powers. -/
theorem exists_eighth_power_block (X : ℕ) :
    ∃ k : ℕ, k ^ 8 ≤ X ∧ X < (k + 1) ^ 8 := by
  let P : ℕ → Prop := fun k => X < (k + 1) ^ 8
  have hex : ∃ k, P k :=
    ⟨X, (Nat.lt_succ_self X).trans_le (Nat.le_self_pow (by decide : 8 ≠ 0) (X + 1))⟩
  let k := Nat.find hex
  refine ⟨k, ?_, Nat.find_spec hex⟩
  by_cases hz : k = 0
  · simp [hz]
  · have hp : ¬ P (k-1) := Nat.find_min hex (show k-1 < k by omega)
    have hpred : k-1 + 1 = k := by omega
    simpa only [P, hpred, not_lt] using hp

/-- Moving a good cutoff down to an eighth power costs at most a fixed
factor on the logarithm. Cofinality permits arbitrarily sparse good cutoffs. -/
theorem frequently_eighth_power_log_bound {H : ℕ → ℝ} (hH : Monotone H)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hgood : ∃ᶠ X : ℕ in atTop, H X ≤ C * (Real.log (X : ℝ)) ^ B) :
    ∃ᶠ k : ℕ in atTop, H (k ^ 8) ≤ (C * 16 ^ B) * (Real.log (k : ℝ)) ^ B := by
  rw [frequently_atTop] at hgood ⊢
  intro K
  let u := max K 2
  obtain ⟨X, hXu, hX⟩ := hgood (u ^ 8)
  obtain ⟨k, hkX, hXk⟩ := exists_eighth_power_block X
  have huk : u ≤ k := by
    by_contra! h
    exact (not_lt_of_ge ((Nat.pow_le_pow_left h 8).trans hXu)) hXk
  have hk : 2 ≤ k := (le_max_right K 2).trans huk
  have hK : K ≤ k := (le_max_left K 2).trans huk
  have hkquad : k + 1 ≤ k ^ 2 := by nlinarith [Nat.mul_le_mul_left k hk]
  have hX16 : X ≤ k ^ 16 := by
    calc
      X ≤ (k + 1) ^ 8 := hXk.le
      _ ≤ (k ^ 2) ^ 8 := Nat.pow_le_pow_left hkquad 8
      _ = k ^ 16 := by rw [← pow_mul]
  have hXpos : 0 < X := lt_of_lt_of_le (pow_pos (show 0 < k by omega) _) hkX
  have hlog0 : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega))
  have hlk : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ k by omega))
  have hlog : Real.log (X : ℝ) ≤ 16 * Real.log (k : ℝ) := by
    calc
      _ ≤ Real.log ((k : ℝ) ^ 16) :=
        Real.log_le_log (by exact_mod_cast hXpos) (by exact_mod_cast hX16)
      _ = _ := by norm_num [Real.log_pow]
  refine ⟨k, hK, (hH hkX).trans (hX.trans ?_)⟩
  calc
    _ ≤ C * (16 * Real.log (k : ℝ)) ^ B :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hlog0 hlog hB) hC
    _ = _ := by rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 16) hlk]; ring

/-- The legal head and positive prime test at an eighth-power cutoff can be
chosen at the first and fourth powers of its integer parameter. -/
theorem exists_eighth_power_prime_scales {k : ℕ} (hk : 0 < k) :
    ∃ N p : ℕ, (N + 1).Prime ∧ k ≤ N ∧ N ≤ 2 * k ∧ p.Prime ∧ k ^ 4 < p ∧ p ≤ 2 * k ^ 4 := by
  obtain ⟨q, hq, hqlo, hqhi⟩ := Nat.exists_prime_lt_and_le_two_mul k hk.ne'
  obtain ⟨p, hp, hplo, hphi⟩ := Nat.exists_prime_lt_and_le_two_mul (k ^ 4) (pow_ne_zero _ hk.ne')
  refine ⟨q-1, p, ?_, by omega, by omega, hp, hplo, hphi⟩
  rwa [show q-1 + 1 = q by omega]

/-- An arbitrarily late estimate with a vanishing right-hand side forces the
fixed mean to vanish. -/
theorem eq_zero_of_frequently_abs_le {m : ℝ} {f : ℕ → ℝ}
    (h : ∃ᶠ k in atTop, |m| ≤ f k) (hf : Tendsto f atTop (𝓝 0)) : m = 0 := by
  by_contra hm
  have hlt := hf.eventually (gt_mem_nhds (abs_pos.mpr hm))
  obtain ⟨k, hk, hk'⟩ := (h.and_eventually hlt).exists
  exact (not_lt_of_ge hk) hk'

/-- At eighth-power cutoffs the logarithmic budget pays for a one-sided
polylogarithmic moment; the remaining Hilbert-space tail costs `O(1 / k)`. -/
theorem tendsto_budget (A : ℕ) (B S C T : ℝ) (hB : 0 ≤ B)
    (hBA : B ≤ (A : ℝ)) (hS : 0 ≤ S) (hC : 0 ≤ C) (hT : 0 ≤ T) :
    Tendsto (fun k : ℕ => (2 / (6 + Real.log (k : ℝ)) ^ (A + 2)) * (S + C * (Real.log (k : ℝ)) ^ B) + 2 * T / (6 + Real.log (k : ℝ)) ^ (A + 2) + 6 * T / (k : ℝ)) atTop (𝓝 0) := by
  let L : ℕ → ℝ := fun k => 6 + Real.log (k : ℝ)
  have ht : Tendsto (fun k : ℕ => Real.log (k : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hL : Tendsto L atTop atTop := tendsto_atTop_add_const_left atTop 6 ht
  have hu : Tendsto (fun k : ℕ => (2 * (S + C + T)) / L k + 6 * T / (k : ℝ)) atTop (𝓝 0) := by
    simpa only [add_zero] using (hL.const_div_atTop (2 * (S + C + T))).add
      ((tendsto_natCast_atTop_atTop : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop).const_div_atTop (6 * T))
  apply squeeze_zero' _ _ hu
  · filter_upwards [ht.eventually (eventually_ge_atTop (0 : ℝ))] with k hk
    have hpow := Real.rpow_nonneg hk B
    have hL0 : 0 ≤ 6 + Real.log (k : ℝ) := by linarith
    positivity
  · filter_upwards [ht.eventually (eventually_ge_atTop (0 : ℝ))] with k hk
    have h1 : 1 ≤ L k := by dsimp [L]; linarith
    have h0 : 0 < L k := zero_lt_one.trans_le h1
    have hA : 1 ≤ L k ^ A := one_le_pow₀ h1
    have htA : (Real.log (k : ℝ)) ^ B ≤ L k ^ A := by
      calc
        _ ≤ L k ^ B := Real.rpow_le_rpow hk (by dsimp [L]; linarith) hB
        _ ≤ L k ^ (A : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 hBA
        _ = _ := Real.rpow_natCast _ _
    have hnum : 2 * (S + C * (Real.log (k : ℝ)) ^ B + T) ≤ 2 * (S + C + T) * L k ^ A := by
      nlinarith only [mul_le_mul_of_nonneg_left htA hC,
        mul_le_mul_of_nonneg_left hA hS, mul_le_mul_of_nonneg_left hA hT]
    change (2 / L k ^ (A + 2)) * (S + C * (Real.log (k : ℝ)) ^ B) + 2 * T / L k ^ (A + 2) + 6 * T / (k : ℝ) ≤ _
    apply add_le_add_left
    calc
      _ = (2 * (S + C * (Real.log (k : ℝ)) ^ B + T)) / L k ^ (A + 2) := by ring
      _ ≤ (2 * (S + C + T) * L k ^ A) / L k ^ (A + 2) :=
        div_le_div_of_nonneg_right hnum (pow_nonneg h0.le _)
      _ = (2 * (S + C + T)) / L k ^ 2 := by
        rw [pow_add]; field_simp [h0.ne'] <;> ring
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) h0
        (by nlinarith only [mul_le_mul_of_nonneg_left h1 h0.le])

end RiemannResearch.Analysis.CofinalMoments

/-!
# Strict lower limits of logarithmic growth ratios

Taking the lower limit in the extended nonnegative reals retains the case
of divergence to infinity. For the usual real lower limit, a frequently
attained upper bound on the ratio is the corresponding order hypothesis.
-/
noncomputable section
open Filter
open scoped ENNReal

namespace RiemannResearch.Analysis.CofinalMoments

private theorem exp_bound_of_log_ratio_lt {h p b : ℝ} (hp : 0 < p)
    (hu : Real.log (2 + h) / p < b) : h ≤ Real.exp (b * p) := by
  have hlog := (div_lt_iff₀ hp).mp hu
  exact (show h ≤ 2 + h by linarith).trans
    ((Real.le_exp_log (2 + h)).trans (Real.exp_le_exp.mpr hlog.le))

/-- A strict upper bound on the extended lower limit gives a smaller
positive exponent on arbitrarily large cutoffs. -/
theorem exists_frequently_exp_of_liminf_log_ratio_lt
    {H φ : ℕ → ℝ} {t : ℝ} (ht : 0 < t)
    (hφ : ∀ᶠ X : ℕ in atTop, 0 < φ X)
    (h : Filter.liminf (fun X : ℕ =>
      ENNReal.ofReal (Real.log (2 + H X) / φ X)) atTop < ENNReal.ofReal t) :
    ∃ b : ℝ, 0 < b ∧ b < t ∧ ∃ᶠ X : ℕ in atTop, H X ≤ Real.exp (b * φ X) := by
  obtain ⟨c, hc, hct⟩ := exists_between h
  have hc0 : (0 : ℝ≥0∞) < c := (bot_le).trans_lt hc
  have hcfin : c ≠ ∞ := (lt_of_lt_of_le hct le_top).ne
  have hb := ENNReal.toReal_pos hc0.ne' hcfin
  have hce := ENNReal.ofReal_toReal hcfin
  have hbt : c.toReal < t := (ENNReal.ofReal_lt_ofReal_iff ht).mp (by rwa [hce])
  have hfreq : ∃ᶠ X : ℕ in atTop, ENNReal.ofReal (Real.log (2 + H X) / φ X) < c :=
    Filter.frequently_lt_of_liminf_lt (Filter.isCoboundedUnder_ge_of_le atTop
      (fun _ => le_top)) hc
  refine ⟨c.toReal, hb, hbt, (hfreq.and_eventually hφ).mono ?_⟩
  intro X hX
  have hlt : ENNReal.ofReal (Real.log (2 + H X) / φ X) < ENNReal.ofReal c.toReal := by
    rw [hce]
    exact hX.1
  exact exp_bound_of_log_ratio_lt hX.2 ((ENNReal.ofReal_lt_ofReal_iff hb).mp hlt)

/-- Real-valued version when the growth ratio admits a cofinal upper bound. -/
theorem exists_frequently_exp_of_real_liminf_log_ratio_lt
    {H φ : ℕ → ℝ} {t : ℝ} (ht : 0 < t)
    (hφ : ∀ᶠ X : ℕ in atTop, 0 < φ X)
    (hco : (atTop : Filter ℕ).IsCoboundedUnder (· ≥ ·)
      (fun X => Real.log (2 + H X) / φ X))
    (h : Filter.liminf (fun X : ℕ => Real.log (2 + H X) / φ X) atTop < t) :
    ∃ b : ℝ, 0 < b ∧ b < t ∧ ∃ᶠ X : ℕ in atTop, H X ≤ Real.exp (b * φ X) := by
  obtain ⟨b, hb, hbt⟩ := exists_between (max_lt_iff.mpr ⟨ht, h⟩)
  have hb0 := (le_max_left _ _).trans_lt hb
  have hlt := (le_max_right _ _).trans_lt hb
  have hfreq := Filter.frequently_lt_of_liminf_lt hco hlt
  refine ⟨b, hb0, hbt, (hfreq.and_eventually hφ).mono ?_⟩
  intro X hX
  exact exp_bound_of_log_ratio_lt hX.2 hX.1

end RiemannResearch.Analysis.CofinalMoments
