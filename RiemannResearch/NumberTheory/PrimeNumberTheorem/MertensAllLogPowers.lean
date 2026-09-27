import RiemannResearch.NumberTheory.PrimeNumberTheorem.MobiusLogBootstrapPower
import RiemannResearch.NumberTheory.PrimeNumberTheorem.MertensBootstrapCutoffs
import RiemannResearch.NumberTheory.PrimeNumberTheorem.MertensShiftedGlobal
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section
open Filter Asymptotics
open scoped Topology BigOperators

namespace RiemannResearch.NumberTheory.PrimeNumberTheorem

/-- The optimized finite scalar estimate loses no fixed logarithmic power.
The prime head has exponent p; the input Mertens bound has sqrt-log power p+1. -/
theorem mertens_bootstrap_power_scalar (p : ℕ)
    {q r Y J A C D t L H B : ℝ}
    (ht : 1 ≤ t) (hY : 1 ≤ Y) (hJ : t ^ p ≤ J)
    (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hr : r * t ^ p ≤ 1) (hAC : A * t ^ (p + 1) ≤ C)
    (hH : H + 1 ≤ 4 * t) (hL : t ≤ 1 + L)
    (hB : L + B ≤ 9 * t)
    (hq : q ≤ r + A + 1 / J + 1 / (Y * J) + A * (H + 1) +
      3 * D / (1 + L) ^ p + 2 * A * (L + B)) :
    q * t ^ p ≤ 3 + 23 * C + 3 * D := by
  have ht0 : 0 < t := by linarith
  have hs0 : 0 < t ^ p := pow_pos ht0 _
  have hJ0 : 0 < J := lt_of_lt_of_le hs0 hJ
  have hYJ0 : 0 < Y * J := mul_pos (by linarith) hJ0
  have hAC' : A * t ^ p * t ≤ C := by simpa only [pow_succ, mul_assoc] using hAC
  have hAt : A * t ^ p ≤ C := by
    have := mul_le_mul_of_nonneg_left ht (mul_nonneg hA hs0.le)
    nlinarith
  have hJt : (1 / J) * t ^ p ≤ 1 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hJ0).2
    simpa only [one_mul] using hJ
  have hYJ : t ^ p ≤ Y * J := by
    have := mul_le_mul_of_nonneg_right hY hJ0.le
    nlinarith
  have hYJt : (1 / (Y * J)) * t ^ p ≤ 1 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hYJ0).2
    simpa only [one_mul] using hYJ
  have hAH : A * (H + 1) * t ^ p ≤ 4 * C := by
    have hp := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hH hA) hs0.le
    nlinarith [hAC']
  have hLp : 0 < 1 + L := lt_of_lt_of_le ht0 hL
  have hden0 : 0 < (1 + L) ^ p := pow_pos hLp _
  have hden : t ^ p ≤ (1 + L) ^ p := pow_le_pow_left₀ ht0.le hL _
  have hDt : (3 * D / (1 + L) ^ p) * t ^ p ≤ 3 * D := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hden0).2
    exact mul_le_mul_of_nonneg_left hden (by positivity)
  have hAB : 2 * A * (L + B) * t ^ p ≤ 18 * C := by
    have hp := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hB hA) hs0.le
    nlinarith [hAC']
  have hqt := mul_le_mul_of_nonneg_right hq hs0.le
  nlinarith

theorem mertens_bootstrap_power_scalar_unscaled (p : ℕ)
    {X N Y J A C D t L H B : ℝ}
    (hN : 0 < N) (ht : 1 ≤ t) (hY : 1 ≤ Y) (hJ : t ^ p ≤ J)
    (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hYt : Y * t ^ p ≤ N) (hAC : A * t ^ (p + 1) ≤ C)
    (hH : H + 1 ≤ 4 * t) (hL : t ≤ 1 + L)
    (hB : L + B ≤ 9 * t)
    (hX : X * t ^ 2 ≤ Y + A * N +
      N * (1 / J + 1 / (Y * J) + A * (H + 1)) +
      3 * D * N / (1 + L) ^ p + 2 * A * N * (L + B)) :
    X * t ^ (p + 2) ≤ (3 + 23 * C + 3 * D) * N := by
  have hr : (Y / N) * t ^ p ≤ 1 := by
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ hN).2 (by simpa using hYt)
  have hq : X * t ^ 2 / N ≤ Y / N + A + 1 / J + 1 / (Y * J) +
      A * (H + 1) + 3 * D / (1 + L) ^ p + 2 * A * (L + B) := by
    apply (div_le_iff₀ hN).2
    have he : (Y / N + A + 1 / J + 1 / (Y * J) +
        A * (H + 1) + 3 * D / (1 + L) ^ p + 2 * A * (L + B)) * N =
        Y + A * N + N * (1 / J + 1 / (Y * J) + A * (H + 1)) +
        3 * D * N / (1 + L) ^ p + 2 * A * N * (L + B) := by
      have hc := div_mul_cancel₀ Y hN.ne'
      simp only [div_eq_mul_inv] at hc ⊢
      nlinarith only [hc]
    rw [he]
    exact hX
  have h := mertens_bootstrap_power_scalar p ht hY hJ hA hD hr hAC hH hL hB hq
  have hdiv : X * t ^ (p + 2) / N ≤ 3 + 23 * C + 3 * D := by
    convert h using 1 <;> rw [pow_add] <;> ring
  exact (div_le_iff₀ hN).mp hdiv

/-- Fully explicit finite cutoffs for the logarithmic Mertens bootstrap.
The parameter `t` is subsequently taken to be `sqrt(log N)`. -/
theorem exists_mertens_bootstrap_power_cutoffs (p N : ℕ) (t : ℝ)
    (hN : 0 < N) (ht : 4 ≤ t) (hlog : Real.log (N : ℝ) = t ^ 2)
    (htpow : t ^ p ≤ Real.exp t) :
    ∃ Y J : ℕ, 0 < Y ∧ Y ≤ N ∧ 0 < J ∧
      t ≤ (Y : ℝ) ∧ (Y : ℝ) * t ^ p ≤ N ∧
      t ^ p ≤ (J : ℝ) ∧ (harmonic J : ℝ) + 1 ≤ 4 * t ∧
      t ^ 2 / 2 ≤ Real.log (Y : ℝ) ∧
      t ≤ Real.log ((N : ℝ) / Y) ∧
      Real.log ((N : ℝ) / Y) + Real.log 4 + 5 ≤ 9 * t := by
  let z : ℝ := Real.exp (t ^ 2 - t)
  let Y : ℕ := ⌊z⌋₊
  let J : ℕ := ⌊t⌋₊ + 1
  have ht0 : 0 < t := by linarith
  have htlarge : 4 * t ≤ t ^ 2 := by
    nlinarith [mul_nonneg (le_of_lt ht0) (sub_nonneg.mpr ht)]
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast hN
  have hz0 : 0 < z := Real.exp_pos _
  have hz2 : 2 ≤ z := by
    have he := Real.add_one_le_exp (t ^ 2 - t)
    dsimp [z]
    nlinarith
  have hYupper : (Y : ℝ) ≤ z := Nat.floor_le (le_of_lt hz0)
  have hYlower : z - 1 < (Y : ℝ) := by
    have he := Nat.lt_floor_add_one z
    dsimp [Y]
    linarith
  have hYhalf : z / 2 ≤ (Y : ℝ) := by linarith
  have htY : t ≤ (Y : ℝ) := by
    have he := Real.add_one_le_exp (t ^ 2 - t)
    change t ^ 2 - t + 1 ≤ z at he
    nlinarith
  have hY0R : 0 < (Y : ℝ) := lt_of_lt_of_le ht0 htY
  have hY0 : 0 < Y := by exact_mod_cast hY0R
  have hNexp : Real.exp (t ^ 2) = (N : ℝ) := by
    rw [← hlog, Real.exp_log hN0]
  have hexpt : t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
  have hYt : (Y : ℝ) * t ≤ N := by
    calc
      (Y : ℝ) * t ≤ z * t := mul_le_mul_of_nonneg_right hYupper (le_of_lt ht0)
      _ ≤ z * Real.exp t := mul_le_mul_of_nonneg_left hexpt (le_of_lt hz0)
      _ = Real.exp (t ^ 2) := by
        dsimp [z]
        rw [← Real.exp_add]
        congr 1
        ring
      _ = N := hNexp
  have hYN : Y ≤ N := by
    have hy : (Y : ℝ) ≤ (N : ℝ) := by
      nlinarith [mul_nonneg (le_of_lt hY0R) (show 0 ≤ t - 1 by linarith)]
    exact_mod_cast hy
  have hJlower : t ≤ (J : ℝ) := by
    have he := Nat.lt_floor_add_one t
    simpa [J, Nat.cast_add, Nat.cast_one] using le_of_lt he
  have hJupper : (J : ℝ) ≤ t + 1 := by
    have he := Nat.floor_le (le_of_lt ht0)
    dsimp [J]
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith
  have hJ0 : 0 < J := by
    have hj : 0 < (J : ℝ) := lt_of_lt_of_le ht0 hJlower
    exact_mod_cast hj
  have hlogYupper : Real.log (Y : ℝ) ≤ t ^ 2 - t := by
    have he := Real.log_le_log hY0R hYupper
    simpa [z, Real.log_exp] using he
  have hlogYlower : t ^ 2 - t - Real.log 2 ≤ Real.log (Y : ℝ) := by
    have he := Real.log_le_log (by positivity : 0 < z / 2) hYhalf
    simpa [Real.log_div hz0.ne' (by norm_num : (2 : ℝ) ≠ 0), z, Real.log_exp] using he
  have hlog2 : Real.log 2 ≤ 1 := by
    have he := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at he ⊢
    exact he
  have hlog4 : Real.log 4 ≤ 3 := by
    have he := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    norm_num at he ⊢
    exact he
  have hlogY : t ^ 2 / 2 ≤ Real.log (Y : ℝ) := by nlinarith
  have hlogdiv : Real.log ((N : ℝ) / Y) = t ^ 2 - Real.log (Y : ℝ) := by
    rw [Real.log_div hN0.ne' hY0R.ne', hlog]
  have hYtp : (Y : ℝ) * t ^ p ≤ N := by
    calc
      _ ≤ z * t ^ p := mul_le_mul_of_nonneg_right hYupper (by positivity)
      _ ≤ z * Real.exp t := mul_le_mul_of_nonneg_left htpow hz0.le
      _ = Real.exp (t ^ 2) := by
        dsimp [z]
        rw [← Real.exp_add]
        congr 1
        ring
      _ = N := hNexp
  let J' : ℕ := ⌊Real.exp t⌋₊ + 1
  have hJ'0 : 0 < J' := by dsimp [J']; omega
  have hJ'lower : Real.exp t ≤ (J' : ℝ) := by
    have he := Nat.lt_floor_add_one (Real.exp t)
    simpa [J', Nat.cast_add, Nat.cast_one] using he.le
  have hJ'upper : (J' : ℝ) ≤ Real.exp t + 1 := by
    have he := Nat.floor_le (Real.exp_pos t).le
    dsimp [J']
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith
  have hexp1 : 1 ≤ Real.exp t := Real.one_le_exp_iff.mpr ht0.le
  have hlogJ : Real.log (J' : ℝ) ≤ t + 1 := by
    have hp : (0 : ℝ) < J' := by exact_mod_cast hJ'0
    have hJu : (J' : ℝ) ≤ 2 * Real.exp t := by linarith
    have he := Real.log_le_log hp hJu
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.exp_pos t).ne',
      Real.log_exp] at he
    linarith
  have hH : (harmonic J' : ℝ) + 1 ≤ 4 * t := by
    have hh := harmonic_le_one_add_log J'
    linarith
  refine ⟨Y, J', hY0, hYN, hJ'0, htY, hYtp,
    htpow.trans hJ'lower, hH, hlogY, ?_, ?_⟩
  · rw [hlogdiv]
    linarith
  · rw [hlogdiv]
    linarith


/-- Each application gains one power of sqrt(log N). No arithmetic
assumption is added: the required prime error comes from MediumPNT. -/
theorem M_sqrt_log_power_step (p : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hM : ∀ x : ℝ, 1 ≤ x →
      |M x| * (Real.sqrt (6 + Real.log x)) ^ (p + 1) ≤ B * x) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ N : ℕ in atTop,
      |M (N : ℝ)| * (Real.sqrt (Real.log (N : ℝ))) ^ (p + 2) ≤ K * N := by
  obtain ⟨D, hD, hR⟩ := R_inverseLogPower_bound (p + 2)
  refine ⟨3 + 23 * (B * (2 : ℝ) ^ (p + 1)) + 3 * D, by positivity, ?_⟩
  have hloglim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have htlim : Tendsto (fun N : ℕ => Real.sqrt (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hloglim
  have hpow : ∀ᶠ t : ℝ in atTop, t ^ p ≤ Real.exp t := by
    have hp := (isLittleO_pow_exp_pos_mul_atTop p (by norm_num : (0 : ℝ) < 1)).bound
      (by norm_num : (0 : ℝ) < 1)
    filter_upwards [hp, eventually_ge_atTop (0 : ℝ)] with t ht ht0
    simpa only [one_mul, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg ht0 p), abs_of_pos (Real.exp_pos t)] using ht
  filter_upwards [htlim.eventually (eventually_ge_atTop (4 : ℝ)),
    htlim.eventually hpow, eventually_ge_atTop (1 : ℕ)] with N ht4 htpow hN
  let t : ℝ := Real.sqrt (Real.log (N : ℝ))
  have hN0 : 0 < N := by omega
  have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1R
  have ht0 : 0 < t := by change 0 < Real.sqrt (Real.log (N : ℝ)); linarith
  have ht2 : t ^ 2 = Real.log (N : ℝ) := Real.sq_sqrt hlog0
  obtain ⟨Y, J, hY, hYN, hJ, htY, hYtp, hJtp, hH, hlogY, hL, hLB⟩ :=
    exists_mertens_bootstrap_power_cutoffs p N t hN0 ht4 ht2.symm htpow
  have hY0R : (0 : ℝ) < Y := by exact_mod_cast hY
  have hY1R : (1 : ℝ) ≤ Y := by exact_mod_cast hY
  let A : ℝ := B * (2 : ℝ) ^ (p + 1) / t ^ (p + 1)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hAC : A * t ^ (p + 1) ≤ B * (2 : ℝ) ^ (p + 1) := by
    dsimp [A]
    rw [div_mul_cancel₀ _ (pow_pos ht0 _).ne']
  have hMtail : ∀ u : ℝ, (Y : ℝ) ≤ u → |M u| ≤ A * u := by
    intro u hu
    have hu1 : 1 ≤ u := hY1R.trans hu
    have hu0 : 0 < u := lt_of_lt_of_le hY0R hu
    have hs0 : 0 ≤ Real.sqrt (6 + Real.log u) := Real.sqrt_nonneg _
    have hssq : (Real.sqrt (6 + Real.log u)) ^ 2 = 6 + Real.log u :=
      Real.sq_sqrt (by linarith [Real.log_nonneg hu1])
    have hlogmono := Real.log_le_log hY0R hu
    have hts : t ≤ 2 * Real.sqrt (6 + Real.log u) := by nlinarith
    have hp := pow_le_pow_left₀ ht0.le hts (p + 1)
    rw [mul_pow] at hp
    have hm : |M u| * t ^ (p + 1) ≤ (B * (2 : ℝ) ^ (p + 1)) * u := by
      calc
        _ ≤ |M u| * ((2 : ℝ) ^ (p + 1) *
            (Real.sqrt (6 + Real.log u)) ^ (p + 1)) :=
          mul_le_mul_of_nonneg_left hp (abs_nonneg _)
        _ = (2 : ℝ) ^ (p + 1) *
            (|M u| * (Real.sqrt (6 + Real.log u)) ^ (p + 1)) := by ring
        _ ≤ (2 : ℝ) ^ (p + 1) * (B * u) :=
          mul_le_mul_of_nonneg_left (hM u hu1) (by positivity)
        _ = _ := by ring
    have hh := (le_div_iff₀ (pow_pos ht0 (p + 1))).2 hm
    simpa only [A, div_mul_eq_mul_div] using hh
  have hf := M_log_bootstrap_finite_power p N Y J hY hYN hJ A D hA hD.le hMtail hR
  rw [abs_mul, abs_of_nonneg hlog0, ← ht2] at hf
  apply mertens_bootstrap_power_scalar_unscaled p
    (C := B * (2 : ℝ) ^ (p + 1))
    (L := Real.log ((N : ℝ) / Y)) (B := Real.log 4 + 5)
    (by exact_mod_cast hN0) (by change 1 ≤ t; linarith)
    hY1R hJtp hA hD.le hYtp hAC hH (by linarith)
  · simpa only [add_assoc] using hLB
  · simpa only [add_assoc] using hf

theorem M_shiftedSqrtLogPower_bound_of_eventual (n : ℕ)
    (K : ℝ) (hK : 0 ≤ K)
    (hM : ∀ᶠ N : ℕ in atTop,
      |M (N : ℝ)| * (Real.sqrt (Real.log (N : ℝ))) ^ n ≤ K * N) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, 1 ≤ x →
      |M x| * (Real.sqrt (6 + Real.log x)) ^ n ≤ B * x := by
  have hloglim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.mp
    (hM.and (hloglim.eventually (eventually_ge_atTop (1 : ℝ))))
  let T : ℕ := max T₀ 1
  let B : ℝ := max ((4 : ℝ) ^ n * K) ((Real.sqrt (6 + Real.log (T : ℝ))) ^ n)
  have hT1 : 1 ≤ T := le_max_right _ _
  have hT1R : (1 : ℝ) ≤ T := by exact_mod_cast hT1
  have hB0 : 0 ≤ B := (by positivity : 0 ≤ (4 : ℝ) ^ n * K).trans (le_max_left _ _)
  refine ⟨B, hB0, ?_⟩
  intro x hx
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < 6 + Real.log x := by linarith [Real.log_nonneg hx]
  have hs0 : 0 ≤ Real.sqrt (6 + Real.log x) := Real.sqrt_nonneg _
  have hscube0 : 0 ≤ (Real.sqrt (6 + Real.log x)) ^ n := by positivity
  have hcubic : |M x| * (Real.sqrt (6 + Real.log x)) ^ n ≤ B * x := by
    let N : ℕ := ⌊x⌋₊
    have hNupper : (N : ℝ) ≤ x := Nat.floor_le (le_of_lt hx0)
    have hNlower : x < (N : ℝ) + 1 := Nat.lt_floor_add_one x
    have he : M x = M (N : ℝ) := by simp [N, M]
    by_cases hNT : T ≤ N
    · have hrate := hT₀ N ((le_max_left T₀ 1).trans hNT)
      have hN1 : 1 ≤ N := hT1.trans hNT
      have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast hN1
      have hN0R : 0 < (N : ℝ) := by linarith
      have hx2N : x ≤ 2 * (N : ℝ) := by linarith
      have hlog2 : Real.log 2 ≤ 1 := by
        have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        norm_num at hh ⊢
        exact hh
      have hlogx : Real.log x ≤ Real.log (N : ℝ) + 1 := by
        have hh := Real.log_le_log hx0 hx2N
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hN0R.ne'] at hh
        linarith
      have hsN0 : 0 ≤ Real.sqrt (Real.log (N : ℝ)) := Real.sqrt_nonneg _
      have hsNsq := Real.sq_sqrt (show 0 ≤ Real.log (N : ℝ) by linarith [hrate.2])
      have hssq := Real.sq_sqrt (le_of_lt hL0)
      have hs : Real.sqrt (6 + Real.log x) ≤ 4 * Real.sqrt (Real.log (N : ℝ)) := by
        nlinarith [hrate.2]
      have hpow := pow_le_pow_left₀ hs0 hs n
      have hm := mul_le_mul_of_nonneg_left hpow (abs_nonneg (M x))
      have hratemul := mul_le_mul_of_nonneg_left hrate.1 (show (0 : ℝ) ≤ 4 ^ n by positivity)
      have h64 : (4 : ℝ) ^ n * K * (N : ℝ) ≤ B * x := by
        calc
          _ ≤ ((4 : ℝ) ^ n * K) * x := mul_le_mul_of_nonneg_left hNupper (by positivity)
          _ ≤ B * x := mul_le_mul_of_nonneg_right (le_max_left _ _) (le_of_lt hx0)
      rw [mul_pow] at hm
      rw [he] at hm ⊢
      calc
        _ ≤ |M (N : ℝ)| * ((4 : ℝ) ^ n *
            (Real.sqrt (Real.log (N : ℝ))) ^ n) := hm
        _ = (4 : ℝ) ^ n *
            (|M (N : ℝ)| * (Real.sqrt (Real.log (N : ℝ))) ^ n) := by ring
        _ ≤ (4 : ℝ) ^ n * (K * N) := hratemul
        _ = ((4 : ℝ) ^ n * K) * N := by ring
        _ ≤ B * x := h64
    · have hNT' : N + 1 ≤ T := by omega
      have hxT : x ≤ (T : ℝ) := by
        have hh : (N : ℝ) + 1 ≤ T := by exact_mod_cast hNT'
        linarith
      have hs : Real.sqrt (6 + Real.log x) ≤ Real.sqrt (6 + Real.log (T : ℝ)) :=
        Real.sqrt_le_sqrt (by linarith [Real.log_le_log hx0 hxT])
      have hpow := pow_le_pow_left₀ hs0 hs n
      have hright : (Real.sqrt (6 + Real.log x)) ^ n ≤ B :=
        hpow.trans (le_max_right _ _)
      calc
        _ ≤ x * (Real.sqrt (6 + Real.log x)) ^ n :=
          mul_le_mul_of_nonneg_right (M_abs_le_self (le_of_lt hx0)) hscube0
        _ ≤ x * B := mul_le_mul_of_nonneg_left hright (le_of_lt hx0)
        _ = B * x := by ring
  exact hcubic


/-- Unconditionally, the optimized bootstrap supplies every fixed
sqrt-logarithmic power. Constants depend on the power. -/
theorem M_shiftedSqrtLog_all_large_powers (n : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, 1 ≤ x →
      |M x| * (Real.sqrt (6 + Real.log x)) ^ (n + 3) ≤ B * x := by
  induction n with
  | zero =>
    obtain ⟨D, hD, hR⟩ := R_inverseLogFourth_bound
    obtain ⟨K, hK, hM⟩ :=
      M_mul_sqrt_log_cube_eventual_of_inverseLogFourth D hD.le hR
    simpa using M_shiftedSqrtLogPower_bound_of_eventual 3 K hK hM
  | succ n ih =>
    obtain ⟨B, hB, hM⟩ := ih
    obtain ⟨K, hK, hnext⟩ := M_sqrt_log_power_step (n + 2) B hB
      (by simpa only [Nat.add_assoc] using hM)
    simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using
      M_shiftedSqrtLogPower_bound_of_eventual (n + 2 + 2) K hK hnext

/-- Natural inverse-log powers of every fixed order follow without adding
an arithmetic hypothesis. -/
theorem M_shiftedSqrtLog_all_powers (n : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, 1 ≤ x →
      |M x| * (Real.sqrt (6 + Real.log x)) ^ n ≤ B * x := by
  obtain ⟨B, hB, hM⟩ := M_shiftedSqrtLog_all_large_powers n
  refine ⟨B, hB, ?_⟩
  intro x hx
  have hs0 := Real.sqrt_nonneg (6 + Real.log x)
  have hs : 1 ≤ Real.sqrt (6 + Real.log x) := by
    have hsq := Real.sq_sqrt (show 0 ≤ 6 + Real.log x by
      linarith [Real.log_nonneg hx])
    nlinarith [Real.log_nonneg hx]
  have hp : (Real.sqrt (6 + Real.log x)) ^ n ≤
      (Real.sqrt (6 + Real.log x)) ^ (n + 3) :=
    pow_le_pow_right₀ hs (by omega)
  exact (mul_le_mul_of_nonneg_left hp (abs_nonneg _)).trans (hM x hx)

/-- A provider in ordinary shifted-log powers, rather than sqrt-log powers. -/
theorem M_shiftedLog_all_nat_powers (n : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, 1 ≤ x →
      |M x| * (6 + Real.log x) ^ n ≤ B * x := by
  obtain ⟨B, hB, hM⟩ := M_shiftedSqrtLog_all_powers (2 * n)
  refine ⟨B, hB, ?_⟩
  intro x hx
  have hh := hM x hx
  rw [pow_mul, Real.sq_sqrt (show 0 ≤ 6 + Real.log x by
    linarith [Real.log_nonneg hx])] at hh
  exact hh

/-- Every fixed real logarithmic decay exponent is unconditional. The
constant may depend on the requested exponent; no uniform stretched
exponential decay assertion is encoded here. -/
theorem M_shiftedLog_all_powers (a : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, 1 ≤ x →
      |M x| ≤ B * x * (6 + Real.log x) ^ (-a) := by
  obtain ⟨n, han⟩ := exists_nat_ge a
  obtain ⟨B, hB, hM⟩ := M_shiftedLog_all_nat_powers n
  refine ⟨B, hB, ?_⟩
  intro x hx
  have hpos : 0 < 6 + Real.log x := by linarith [Real.log_nonneg hx]
  have hh := (le_div_iff₀ (pow_pos hpos n)).2 (hM x hx)
  have hh' : |M x| ≤ B * x * (6 + Real.log x) ^ (-(n : ℝ)) := by
    simpa only [Real.rpow_neg hpos.le, Real.rpow_natCast, div_eq_mul_inv] using hh
  apply hh'.trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hB (by linarith))
  exact Real.rpow_le_rpow_of_exponent_le
    (by linarith [Real.log_nonneg hx]) (by linarith)


end RiemannResearch.NumberTheory.PrimeNumberTheorem
