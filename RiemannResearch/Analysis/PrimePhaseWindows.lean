/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.ActualPrimeTorusFMZContinuous
import RiemannResearch.Analysis.ActualRationalFMZLimits
import RiemannResearch.Analysis.ActualZeroCountAsymptotics
import RiemannResearch.Analysis.ActualZeroCountNormalization
import RiemannResearch.Analysis.ActualZeroLoglogRate
import RiemannResearch.Analysis.ActualZeroOrdinate
import RiemannResearch.Analysis.FinitePrimeModeCoefficients
import RiemannResearch.Analysis.ZeroOrdinateEquidistribution
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Signed prime-phase laws in dilated and dyadic height windows

Source (target): *Modular Phase Reconstruction of Zeta Zeros from Pole Lattices*,
p. 8, https://drive.google.com/file/d/1opJNKzINIeBMDA_k6mr1jEtfW26_-2Cj/view.

Source (analytic input): Ford, Meng and Zaharescu, *Simultaneous distribution
of the fractional parts of Riemann zeta zeros*, Corollary 1.1,
https://arxiv.org/abs/1511.06814. The project's fractional Wiener estimate
gives the signed limit under the strict Fourier threshold B > card(P) + 1.

For a single prime, equation (1.10) of Ford and Zaharescu,
<https://www.ford126.web.illinois.edu/wwwpapers/fz.pdf>, gives the Fourier
coefficient used in the logarithmic cosine limit.

The signed order-height correction survives restriction to (T,r*T], with
factor r-1. For r>1 this is a forward height window; r<1 gives an oriented
boundary difference. The actual Riemann-von Mangoldt lower bound gives the
dyadic normalization. Both limits count zeros with analytic multiplicity.
-/

noncomputable section
open Filter Zeta23
open scoped Topology Asymptotics

namespace RiemannResearch.Analysis.PrimePhaseWindows
open ActualZeroOrdinate PrimeTorusHaar ActualPrimeTorusFMZ

/-- A signed order-height limit transfers to every fixed dilated window.
The boundary subtraction and the factor r-1 are retained exactly. -/
theorem centered_scaled_window_limit (A N : ℝ → ℂ) (I c : ℂ)
    (h : Tendsto (fun T => (A T - N T * I) / (T : ℂ)) atTop (𝓝 c))
    (r : ℝ) (hr : 0 < r) :
    Tendsto (fun T : ℝ =>
      (A (r * T) - A T - (N (r * T) - N T) * I) / (T : ℂ))
      atTop (𝓝 (((r : ℂ) - 1) * c)) := by
  have hscale : Tendsto (fun T : ℝ => r * T) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop (b / r)] with T hT
    simpa only [mul_comm] using (div_le_iff₀ hr).mp hT
  have hlim := ((h.comp hscale).const_mul (r : ℂ)).sub h
  have hc : (r : ℂ) * c - c = ((r : ℂ) - 1) * c := by ring
  rw [hc] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  have hTc : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  simp only [Function.comp_apply, Complex.ofReal_mul]
  field_simp
  ring

/-- The signed FMZ correction for each fixed dilation `r > 0`. -/
theorem scaled_window_signed_limit
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (f : C(Torus P, ℂ))
    (C B : ℝ) (hC : 0 ≤ C) (hB : (P.card : ℝ) + 1 < B)
    (hf : ∀ k : P → ℤ,
      ‖UnitAddTorus.mFourierCoeff (f : Torus P → ℂ) k‖ ≤ C * (1 + ‖k‖) ^ (-B))
    (r : ℝ) (hr : 0 < r) :
    Tendsto (fun T : ℝ =>
      (sampleFunctional P (r * T) f - sampleFunctional P T f -
        ((Ncount 0 (r * T) : ℂ) - (Ncount 0 T : ℂ)) * haarIntegral f) / (T : ℂ))
      atTop (𝓝 (((r : ℂ) - 1) * haarIntegral (f * primeDensity P))) :=
  centered_scaled_window_limit _ _ _ _
    (tendsto_centered_continuous_div_poisson P hP f C B hC hB hf) r hr

theorem eventually_dyadic_count_ge_log :
    ∀ᶠ T : ℝ in atTop, (1 / (4 * Real.pi)) * T * Real.log T ≤
      (Ncount T (2 * T) : ℝ) := by
  have hc : (1 : ℝ) / (4 * Real.pi) < 1 / (2 * Real.pi) := by
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
    nlinarith [Real.pi_pos]
  simpa only [zetaZeroConfig_N] using
    Assembly.eventually_N_ge_log_of_lt zetaZeroConfig
      (RvM.riemannVonMangoldt gammaFacts) hc

theorem tendsto_height_div_dyadic_count :
    Tendsto (fun T : ℝ => T / (Ncount T (2 * T) : ℝ)) atTop (𝓝 0) := by
  have hupper : ∀ᶠ T : ℝ in atTop,
      T / (Ncount T (2 * T) : ℝ) ≤ (4 * Real.pi) / Real.log T := by
    filter_upwards [eventually_dyadic_count_ge_log, eventually_gt_atTop (1 : ℝ)]
      with T hN hT
    have hTpos : 0 < T := by linarith
    have hL : 0 < Real.log T := Real.log_pos hT
    calc
      _ ≤ T / ((1 / (4 * Real.pi)) * T * Real.log T) :=
        div_le_div_of_nonneg_left hTpos.le (by positivity) hN
      _ = (4 * Real.pi) / Real.log T := by field_simp
  refine squeeze_zero' ?_ hupper ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    exact div_nonneg hT.le (Nat.cast_nonneg _)
  · simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop) :
        Tendsto (fun T : ℝ => (4 * Real.pi) * (Real.log T)⁻¹) atTop
          (𝓝 ((4 * Real.pi) * 0)))

/-- Multiplicity-weighted Haar equidistribution on `(T, 2*T]` for the stated Fourier class. -/
theorem dyadic_equidistribution
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (f : C(Torus P, ℂ))
    (C B : ℝ) (hC : 0 ≤ C) (hB : (P.card : ℝ) + 1 < B)
    (hf : ∀ k : P → ℤ,
      ‖UnitAddTorus.mFourierCoeff (f : Torus P → ℂ) k‖ ≤ C * (1 + ‖k‖) ^ (-B)) :
    Tendsto (fun T : ℝ =>
      (sampleFunctional P (2 * T) f - sampleFunctional P T f) /
        (Ncount T (2 * T) : ℂ)) atTop (𝓝 (haarIntegral f)) := by
  have hw := scaled_window_signed_limit P hP f C B hC hB hf 2 (by norm_num)
  have hr : Tendsto (fun T : ℝ => (T : ℂ) / (Ncount T (2 * T) : ℂ))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Complex.ofReal_div, Complex.ofReal_natCast,
      Complex.ofReal_zero] using
      (Complex.continuous_ofReal.tendsto 0).comp tendsto_height_div_dyadic_count
  have hlim := (hr.mul hw).const_add (haarIntegral f)
  simp only [zero_mul, add_zero] at hlim
  apply hlim.congr'
  filter_upwards [eventually_dyadic_count_ge_log, eventually_gt_atTop (1 : ℝ)]
    with T hN hT
  have hTpos : 0 < T := by linarith
  have hlog : 0 < Real.log T := Real.log_pos hT
  have hNpos : (0 : ℝ) < (Ncount T (2 * T) : ℝ) :=
    lt_of_lt_of_le (by positivity) hN
  have hNc : (Ncount T (2 * T) : ℂ) ≠ 0 := by exact_mod_cast hNpos.ne'
  have hTc : (T : ℂ) ≠ 0 := by exact_mod_cast hTpos.ne'
  have hadd : (Ncount 0 (2 * T) : ℂ) =
      (Ncount 0 T : ℂ) + (Ncount T (2 * T) : ℂ) := by
    exact_mod_cast Ncount_add (a := 0) (b := T) (c := 2*T) hTpos.le (by linarith)
  rw [hadd]
  field_simp
  ring

/-- Multiplicity-weighted mean of `cos(log p * γ)` over the actual zeros
in `(T, 2*T]`, divided by their exact count. -/
def dyadicPrimeCosineMean (p : ℕ) (T : ℝ) : ℝ :=
  (realSum (2 * T) (fun ρ => Real.cos (Real.log p * ρ.im)) -
    realSum T (fun ρ => Real.cos (Real.log p * ρ.im))) / (Ncount T (2 * T) : ℝ)

/-- Each fixed positive harmonic of one prime has a dyadic cosine bias.
The numerator is the Mangoldt weight of the prime power, hence is independent of k. -/
theorem tendsto_log_mul_dyadicPrimePowerCosineMean {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    Tendsto (fun T : ℝ => Real.log T * dyadicPrimeCosineMean (p ^ k) T)
      atTop (𝓝 (-Real.log p / (Real.sqrt p) ^ k)) := by
  have hpow : IsPrimePow (p ^ k) := ⟨p, k, hp.prime, hk, rfl⟩
  let A := fun T : ℝ => ordinateSum T (Real.log (p ^ k : ℕ))
  let J : ℝ := -Real.log p / (2 * Real.pi * (Real.sqrt p) ^ k)
  have hJ : rationalFMZMain (p ^ k) 1 = (J : ℂ) := by
    rw [PrimePhaseTorus.rationalFMZMain_prime_pow hp hk]
    dsimp [J]
    push_cast
    simp only [div_eq_mul_inv, mul_inv, inv_pow]
    ring
  have hs : Tendsto (fun T : ℝ => A T / (T : ℂ)) atTop (𝓝 (J : ℂ)) := by
    simpa only [A, centeredRationalOrdinate, if_neg hpow.one_lt.ne', sub_zero,
      Nat.cast_one, div_one, hJ] using
      tendsto_centeredRationalOrdinate_div hpow.one_lt.le (by decide : 1 ≤ 1)
  have hw := centered_scaled_window_limit A (fun _ => 0) 0 (J : ℂ) (by simpa using hs)
    2 (by norm_num)
  norm_num at hw
  have hr : Tendsto (fun T : ℝ => (A (2 * T) - A T).re / T) atTop (𝓝 J) := by
    simpa [Function.comp_def, Complex.div_ofReal_re] using
      Complex.continuous_re.continuousAt.tendsto.comp hw
  have hcount := Assembly.tendsto_dyadic_count_div_height_log zetaZeroConfig
    (RvM.riemannVonMangoldt gammaFacts)
  simp only [zetaZeroConfig_N] at hcount
  have hratio := hr.div hcount (by positivity : (1 : ℝ) / (2 * Real.pi) ≠ 0)
  have hcoeff : J / (1 / (2 * Real.pi)) = -Real.log p / (Real.sqrt p) ^ k := by
    dsimp [J]
    field_simp [Real.pi_ne_zero, (Real.sqrt_pos.2 (Nat.cast_pos.mpr hp.pos)).ne'] <;> ring
  rw [hcoeff] at hratio
  have hcos (t u : ℝ) : (ordinateSum t u).re = realSum t (fun ρ => Real.cos (u * ρ.im)) := by
    simp [ordinateSum, sum, realSum, ZeroOrdinate.phase, Complex.re_sum,
      Complex.mul_re, Complex.exp_re]
  apply hratio.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  simp only [Pi.div_apply, A, dyadicPrimeCosineMean, Complex.sub_re, hcos]
  rw [div_div_eq_mul_div, div_mul_eq_mul_div]
  field_simp [hT.ne']

/-- The first cosine Fourier coefficient at a fixed prime determines the
signed leading bias in its count-normalized dyadic mean. -/
theorem tendsto_log_mul_dyadicPrimeCosineMean {p : ℕ} (hp : p.Prime) :
    Tendsto (fun T : ℝ => Real.log T * dyadicPrimeCosineMean p T)
      atTop (𝓝 (-Real.log p / Real.sqrt p)) := by
  simpa only [pow_one] using tendsto_log_mul_dyadicPrimePowerCosineMean hp (k := 1) (by decide)

/-- The raw prime cosine mean satisfies an inverse logarithmic power bound
exactly up to and including exponent one. -/
theorem dyadicPrimeCosineMean_isBigO_log_rpow_iff {p : ℕ} (hp : p.Prime) (α : ℝ) :
    (dyadicPrimeCosineMean p =O[atTop] (fun T : ℝ => Real.log T ^ (-α))) ↔ α ≤ 1 := by
  have hlogp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hc : -Real.log p / Real.sqrt p ≠ 0 :=
    div_ne_zero (neg_ne_zero.mpr hlogp.ne') (Real.sqrt_pos.2 (Nat.cast_pos.mpr hp.pos)).ne'
  have htheta : (fun T : ℝ => (Real.log T)⁻¹) =Θ[atTop] dyadicPrimeCosineMean p :=
    Asymptotics.isTheta_of_div_tendsto_nhds_ne_zero
      (by simpa only [div_inv_eq_mul, mul_comm] using tendsto_log_mul_dyadicPrimeCosineMean hp) hc
  rw [← htheta.isBigO_congr_left]
  constructor
  · intro h
    by_contra! hα
    obtain ⟨C, hb⟩ := Asymptotics.isBigO_iff.mp h
    have hg := ((tendsto_rpow_atTop (sub_pos.mpr hα)).comp
      Real.tendsto_log_atTop).eventually_gt_atTop C
    obtain ⟨T, hbound, hlarge, hT⟩ := (hb.and (hg.and (eventually_gt_atTop (1 : ℝ)))).exists
    have hL := Real.log_pos hT
    have hpow := Real.rpow_pos_of_pos hL α
    change C < Real.log T ^ (α - 1) at hlarge
    change ‖(Real.log T)⁻¹‖ ≤ C * ‖Real.log T ^ (-α)‖ at hbound
    rw [Real.norm_of_nonneg (inv_nonneg.mpr hL.le), Real.norm_of_nonneg (Real.rpow_nonneg hL.le _),
      Real.rpow_neg hL.le, ← div_eq_mul_inv] at hbound
    apply (not_lt_of_ge ((le_div_iff₀ hpow).1 hbound))
    simpa only [Real.rpow_sub hL, Real.rpow_one, div_eq_mul_inv, mul_comm] using hlarge
  · intro hα
    apply Asymptotics.IsBigO.of_norm_eventuallyLE
    filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1] with T hT
    have hL := zero_le_one.trans hT
    change ‖(Real.log T)⁻¹‖ ≤ Real.log T ^ (-α)
    simpa only [Real.norm_of_nonneg (inv_nonneg.mpr hL), Real.rpow_neg hL (1 : ℝ), Real.rpow_one]
      using Real.rpow_le_rpow_of_exponent_le hT (neg_le_neg hα)

end RiemannResearch.Analysis.PrimePhaseWindows
