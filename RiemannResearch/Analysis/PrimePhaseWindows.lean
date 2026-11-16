/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.ActualPrimeTorusFMZContinuous
import RiemannResearch.Analysis.ActualZeroCountAsymptotics
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
https://arxiv.org/abs/1511.06814. The imported project formalization uses the
stronger Fourier threshold B > card(P)+1 and explicitly assumes Selberg.

The signed order-height correction survives restriction to (T,r*T], with
factor r-1. For r>1 this is a forward height window; r<1 gives an oriented
boundary difference. The dyadic normalized limit follows from the actual unconditional
Riemann-von Mangoldt lower bound. All analytic multiplicities are retained.
The zero-sampled limits remain conditional research reductions: their
UniformSelbergDensity (1/4) premise is not discharged here.
-/

noncomputable section
open Filter Zeta23
open scoped Topology

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
  <;> ring

/-- The PDF's long-window phase statistics retain the classical signed
correction, under the existing explicit Selberg premise. -/
theorem scaled_window_signed_limit_of_selberg
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (f : C(Torus P, ℂ))
    (C B : ℝ) (hC : 0 ≤ C) (hB : (P.card : ℝ) + 1 < B)
    (hf : ∀ k : P → ℤ,
      ‖UnitAddTorus.mFourierCoeff (f : Torus P → ℂ) k‖ ≤ C * (1 + ‖k‖) ^ (-B))
    (hD : UniformSelbergDensity (1 / 4)) (r : ℝ) (hr : 0 < r) :
    Tendsto (fun T : ℝ =>
      (sampleFunctional P (r * T) f - sampleFunctional P T f -
        ((Ncount 0 (r * T) : ℂ) - (Ncount 0 T : ℂ)) * haarIntegral f) / (T : ℂ))
      atTop (𝓝 (((r : ℂ) - 1) * haarIntegral (f * primeDensity P))) :=
  centered_scaled_window_limit _ _ _ _
    (tendsto_centered_continuous_div_poisson_of_selberg P hP f C B hC hB hf hD) r hr

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

/-- Multiplicity-weighted dyadic Haar equidistribution for the stated Fourier
class. No simplicity or RH premise; Selberg is still explicitly required. -/
theorem dyadic_equidistribution_of_selberg
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (f : C(Torus P, ℂ))
    (C B : ℝ) (hC : 0 ≤ C) (hB : (P.card : ℝ) + 1 < B)
    (hf : ∀ k : P → ℤ,
      ‖UnitAddTorus.mFourierCoeff (f : Torus P → ℂ) k‖ ≤ C * (1 + ‖k‖) ^ (-B))
    (hD : UniformSelbergDensity (1 / 4)) :
    Tendsto (fun T : ℝ =>
      (sampleFunctional P (2 * T) f - sampleFunctional P T f) /
        (Ncount T (2 * T) : ℂ)) atTop (𝓝 (haarIntegral f)) := by
  have hw := scaled_window_signed_limit_of_selberg P hP f C B hC hB hf hD
    2 (by norm_num)
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
  <;> ring

end RiemannResearch.Analysis.PrimePhaseWindows
