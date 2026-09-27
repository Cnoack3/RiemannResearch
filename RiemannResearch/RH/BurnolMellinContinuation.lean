import RiemannResearch.RH.BurnolDampingZeroShift
import RiemannResearch.RH.ZetaConductorRegularization
import Mathlib.Tactic.LinearCombination

/-!
# Continuation of the damped Mellin identity

Source: J.-F. Burnol, arXiv:math/0202166, Lemma 4.3 and Theorem 4.2.
The source supports the continuation and zero-propagation strategy.
We clear both zeta poles with the already verified entire conductor
multiplier. The normalization constant may be arbitrary. The analytic
Mellin function and its identity on Re(s)>1 remain explicit hypotheses;
this module does not assert arithmetic finite-energy membership.
-/

noncomputable section
open Filter Set
open scoped Topology

namespace RiemannResearch.RH.Burnol
open ArithmeticConductorCommonZeros ZetaConductorRegularization

private theorem mellinHalfPlane_convex :
    Convex ℝ {s : ℂ | (1 / 2 : ℝ) < s.re} := by
  intro x hx y hy a b ha hb hab
  change (1 / 2 : ℝ) < (a • x + b • y).re
  simp only [Complex.add_re, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hx' : (1 / 2 : ℝ) < x.re := hx
  have hy' : (1 / 2 : ℝ) < y.re := hy
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    simpa [ha0, hb1] using hy'
  · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have hax := mul_pos hapos (sub_pos.mpr hx')
    have hby := mul_nonneg hb (sub_nonneg.mpr hy'.le)
    nlinarith

/-- The entire conductor factors permit continuation across both zeta poles. -/
theorem damped_mellin_conductor_identity
    (ε : ℝ) (hε : 0 ≤ ε) (C : ℂ) (M : ℂ → ℂ)
    (hM : AnalyticOnNhd ℂ M {s | (1 / 2 : ℝ) < s.re})
    (hseed : ∀ᶠ s : ℂ in 𝓝 (2 : ℂ),
      s * riemannZeta (s + (ε : ℂ)) * M s =
        riemannZeta s * (1 - C * riemannZeta (s + (ε : ℂ))))
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    s * conductorZeta 2 (s + (ε : ℂ)) * conductorSymbol 2 s * M s =
      conductorZeta 2 s *
        (conductorSymbol 2 (s + (ε : ℂ)) - C * conductorZeta 2 (s + (ε : ℂ))) := by
  have hshift (z : ℂ) : AnalyticAt ℂ (fun t : ℂ => t + (ε : ℂ)) z :=
    analyticAt_id.add analyticAt_const
  have hZ (z : ℂ) : AnalyticAt ℂ (conductorZeta 2) z :=
    analyticAt_conductorZeta 2 (by norm_num) z
  have hA (z : ℂ) : AnalyticAt ℂ (conductorSymbol 2) z :=
    analyticAt_conductorSymbol 2 z
  have hf : AnalyticOnNhd ℂ
      (fun z => z * conductorZeta 2 (z + (ε : ℂ)) * conductorSymbol 2 z * M z)
      {z | (1 / 2 : ℝ) < z.re} := by
    intro z hz
    exact ((analyticAt_id.mul ((hZ _).comp (hshift z))).mul (hA z)).mul (hM z hz)
  have hg : AnalyticOnNhd ℂ
      (fun z => conductorZeta 2 z *
        (conductorSymbol 2 (z + (ε : ℂ)) - C * conductorZeta 2 (z + (ε : ℂ))))
      {z | (1 / 2 : ℝ) < z.re} := by
    intro z hz
    exact (hZ z).mul (((hA _).comp (hshift z)).sub
      (analyticAt_const.mul ((hZ _).comp (hshift z))))
  have he : (fun z => z * conductorZeta 2 (z + (ε : ℂ)) * conductorSymbol 2 z * M z)
      =ᶠ[𝓝 (2 : ℂ)] (fun z => conductorZeta 2 z *
        (conductorSymbol 2 (z + (ε : ℂ)) - C * conductorZeta 2 (z + (ε : ℂ)))) := by
    have hn : ∀ᶠ z : ℂ in 𝓝 (2 : ℂ), z ≠ 1 :=
      compl_singleton_mem_nhds (by norm_num : (2 : ℂ) ≠ 1)
    have hε2 : (2 : ℂ) + (ε : ℂ) ≠ 1 := by
      intro h
      have hr := congrArg Complex.re h
      norm_num at hr
      linarith
    have hp : ∀ᶠ z : ℂ in 𝓝 (2 : ℂ), z + (ε : ℂ) ≠ 1 :=
      (isOpen_ne.preimage (continuous_id.add continuous_const)).mem_nhds hε2
    filter_upwards [hseed, hn, hp] with z hz hz1 hzε
    rw [conductorZeta_of_ne_one 2 hz1, conductorZeta_of_ne_one 2 hzε]
    linear_combination conductorSymbol 2 z * conductorSymbol 2 (z + (ε : ℂ)) * hz
  exact (hf.eqOn_of_preconnected_of_eventuallyEq hg mellinHalfPlane_convex.isPreconnected
    (z₀ := (2 : ℂ)) (by norm_num) he).eq_of_mem hs

/-- Holomorphy forces the normalization through the removable point at one. -/
theorem normalization_of_mellin_identity
    (ε : ℝ) (hε : 0 < ε) (C : ℂ) (M : ℂ → ℂ)
    (hM : AnalyticOnNhd ℂ M {s | (1 / 2 : ℝ) < s.re})
    (hseed : ∀ᶠ s : ℂ in 𝓝 (2 : ℂ),
      s * riemannZeta (s + (ε : ℂ)) * M s =
        riemannZeta s * (1 - C * riemannZeta (s + (ε : ℂ)))) :
    C * riemannZeta (1 + (ε : ℂ)) = 1 := by
  have hi := damped_mellin_conductor_identity ε hε.le C M hM hseed 1 (by norm_num)
  rw [conductorSymbol_one 2 (by norm_num)] at hi
  simp only [mul_zero, zero_mul] at hi
  have hb := (mul_eq_zero.mp hi.symm).resolve_left
    (conductorZeta_one_ne_zero 2 (by norm_num))
  have hr : (1 + (ε : ℂ)).re ≠ 1 := by
    simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re]
    linarith
  have hp : 1 + (ε : ℂ) ≠ 1 := by intro h; apply hr; simp [h]
  rw [conductorZeta_of_ne_one 2 hp] at hb
  apply mul_right_cancel₀ (conductorSymbol_ne_zero_of_re_ne_one 2 (by norm_num)
    (1 + (ε : ℂ)) hr)
  linear_combination -hb

/-- A holomorphic Mellin identity propagates each eligible denominator zero.
No division at a zero, uniform norm bound, or arithmetic interchange is used. -/
theorem zero_propagation_of_mellin_identity
    (ε : ℝ) (hε : 0 ≤ ε) (C : ℂ) (M : ℂ → ℂ)
    (hM : AnalyticOnNhd ℂ M {s | (1 / 2 : ℝ) < s.re})
    (hright : ∀ s : ℂ, 1 < s.re →
      s * riemannZeta (s + (ε : ℂ)) * M s =
        riemannZeta s * (1 - C * riemannZeta (s + (ε : ℂ))))
    (ρ : ℂ) (hhalf : (1 / 2 : ℝ) + ε < ρ.re) (hone : ρ.re < 1)
    (hz : riemannZeta ρ = 0) : riemannZeta (ρ - (ε : ℂ)) = 0 := by
  have hseed : ∀ᶠ s : ℂ in 𝓝 (2 : ℂ),
      s * riemannZeta (s + (ε : ℂ)) * M s =
        riemannZeta s * (1 - C * riemannZeta (s + (ε : ℂ))) := by
    have hh : ∀ᶠ s : ℂ in 𝓝 (2 : ℂ), 1 < s.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hh] with s hs
    exact hright s hs
  have hs : (1 / 2 : ℝ) < (ρ - (ε : ℂ)).re := by
    simp only [Complex.sub_re, Complex.ofReal_re]
    linarith
  have hρ1 : ρ ≠ 1 := by intro h; simp [h] at hone
  have hsone : (ρ - (ε : ℂ)).re < 1 := by
    simp only [Complex.sub_re, Complex.ofReal_re]
    linarith
  have hs1 : ρ - (ε : ℂ) ≠ 1 := by intro h; simp [h] at hsone
  have hAρ := conductorSymbol_ne_zero_of_re_ne_one 2 (by norm_num) ρ hone.ne
  have hAs := conductorSymbol_ne_zero_of_re_ne_one 2 (by norm_num)
    (ρ - (ε : ℂ)) hsone.ne
  have hi := damped_mellin_conductor_identity ε hε C M hM hseed (ρ - (ε : ℂ)) hs
  rw [sub_add_cancel, conductorZeta_eq_zero_of_zeta_zero 2 hρ1 hz] at hi
  simp only [mul_zero, zero_mul, sub_zero] at hi
  have hzs : conductorZeta 2 (ρ - (ε : ℂ)) = 0 :=
    (mul_eq_zero.mp hi.symm).resolve_right hAρ
  rw [conductorZeta_of_ne_one 2 hs1] at hzs
  exact (mul_eq_zero.mp hzs).resolve_right hAs

/-- Burnol's continuation-to-RH reduction, allowing an arbitrary normalization
at each damping stage. Holomorphy and the arithmetic right-half-plane identity
are explicit obligations. No uniform estimate on the family is assumed. -/
theorem riemannHypothesis_of_mellin_identity_sequence
    (ε : ℕ → ℝ) (hpos : ∀ j, 0 < ε j)
    (hlim : Tendsto ε atTop (𝓝 0))
    (C : ℕ → ℂ) (M : ℕ → ℂ → ℂ)
    (hM : ∀ j, AnalyticOnNhd ℂ (M j) {s | (1 / 2 : ℝ) < s.re})
    (hright : ∀ j, ∀ s : ℂ, 1 < s.re →
      s * riemannZeta (s + (ε j : ℂ)) * M j s =
        riemannZeta s * (1 - C j * riemannZeta (s + (ε j : ℂ)))) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_zero_propagation_sequence ε hpos hlim
  intro j ρ hhalf hone hz
  exact zero_propagation_of_mellin_identity (ε j) (hpos j).le (C j) (M j)
    (hM j) (hright j) ρ hhalf hone hz

end RiemannResearch.RH.Burnol
