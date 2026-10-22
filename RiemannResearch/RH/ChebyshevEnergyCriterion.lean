import RiemannResearch.RH.ChebyshevZeroObstruction
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

/-!
# Chebyshev energy implies RH: analytic continuation through meromorphic germs

Source: user-provided V_Zeta_Zeros_Fourier_Chebyshev_Handoff_2026-09-16,
Section 19. The proof combines the existing Chebyshev Mellin and pole
modules using Mathlib meromorphic identity continuation.
Classification: conditional research reduction. The actual weighted
arithmetic energy hypothesis remains Open; this file proves its RH consumer.

The only substantive assumption in the final theorem is actual integrability
of the complete Chebyshev error square for every positive damping parameter.
The identity theorem is implemented using propagation of meromorphic order top.
This avoids treating the totalized Bochner integral outside its convergence
domain as an analytic continuation without first proving the needed equality.
-/

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Topology

namespace RiemannResearch.RH.ChebyshevMellin

/-- Zeta is meromorphic also at its pole, not just away from one. -/
theorem riemannZeta_meromorphicAt_everywhere (z : ℂ) :
    MeromorphicAt riemannZeta z := by
  by_cases hz1 : z = 1
  · subst z
    have hc : MeromorphicAt (fun _ : ℂ => (1 : ℂ)) 1 :=
      analyticAt_const.meromorphicAt
    have hi : MeromorphicAt (fun w : ℂ => w) 1 :=
      analyticAt_id.meromorphicAt
    have hΛ : MeromorphicAt completedRiemannZeta 1 := by
      have he : completedRiemannZeta = fun w : ℂ =>
          completedRiemannZeta₀ w - 1 / w - 1 / (1 - w) :=
        funext completedRiemannZeta_eq
      rw [he]
      exact ((differentiable_completedZeta₀.analyticAt 1).meromorphicAt.sub
        (hc.div hi)).sub (hc.div (hc.sub hi))
    have hprod : MeromorphicAt
        (fun w : ℂ => completedRiemannZeta w * (Complex.Gammaℝ w)⁻¹) 1 :=
      hΛ.mul (Complex.differentiable_Gammaℝ_inv.analyticAt 1).meromorphicAt
    have he : (fun w : ℂ => completedRiemannZeta w * (Complex.Gammaℝ w)⁻¹)
        =ᶠ[𝓝 (1 : ℂ)] riemannZeta := by
      filter_upwards [eventually_ne_nhds (one_ne_zero : (1 : ℂ) ≠ 0)] with w hw
      simpa only [div_eq_mul_inv] using (riemannZeta_def_of_ne_zero hw).symm
    exact hprod.congr (he.filter_mono nhdsWithin_le_nhds)
  · exact (Zeta23.riemannZeta_analyticOnNhd_compl_one z hz1).meromorphicAt

theorem meromorphicError_meromorphicAt_everywhere (z : ℂ) :
    MeromorphicAt meromorphicError z := by
  have hz := riemannZeta_meromorphicAt_everywhere z
  change MeromorphicAt
    (fun w : ℂ => -deriv riemannZeta w / (w * riemannZeta w) - 1 / (w - 1)) z
  exact (hz.deriv.neg.div (analyticAt_id.meromorphicAt.mul hz)).sub
    (analyticAt_const.meromorphicAt.div
      (analyticAt_id.sub analyticAt_const).meromorphicAt)

/-- Actual Mellin holomorphy on a half-plane continues the arithmetic identity
as equality of punctured germs. No identification at a totalized pole is needed. -/
theorem errorMellin_germ_eq_of_halfplane_analytic {a : ℝ} (ha : a < 2)
    (hM : ∀ z : ℂ, a < z.re → AnalyticAt ℂ errorMellin z)
    {z : ℂ} (hz : a < z.re) :
    errorMellin =ᶠ[𝓝[≠] z] meromorphicError := by
  let U : Set ℂ := {w | a < w.re}
  let D : ℂ → ℂ := fun w => errorMellin w - meromorphicError w
  have hD : MeromorphicOn D U := by
    intro w hw
    exact (hM w hw).meromorphicAt.sub (meromorphicError_meromorphicAt_everywhere w)
  have hU : IsPreconnected U := (convex_halfSpace_re_gt a).isPreconnected
  have h2 : (2 : ℂ) ∈ U := by simpa [U] using ha
  have hzU : z ∈ U := hz
  have ht2 : meromorphicOrderAt D (2 : ℂ) = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    have hright : ∀ᶠ w : ℂ in 𝓝 (2 : ℂ), (1 : ℝ) < w.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hright.filter_mono nhdsWithin_le_nhds] with w hw
    exact sub_eq_zero.mpr (error_mellin_identity hw)
  have htz : meromorphicOrderAt D z = ⊤ := by
    by_contra hn
    exact (hD.meromorphicOrderAt_ne_top_of_isPreconnected hU hzU h2 hn) ht2
  have he := meromorphicOrderAt_eq_top_iff.mp htz
  filter_upwards [he] with w hw
  exact sub_eq_zero.mp hw

/-- A zero strictly inside the energy half-plane contradicts finite energy.
This theorem makes no assertion about the boundary case s = 2 Re(rho). -/
theorem not_errorFiniteEnergy_of_offline_zero
    {ρ : ℂ} (hhalf : (1 / 2 : ℝ) < ρ.re) (hone : ρ.re < 1)
    (hzero : riemannZeta ρ = 0) {s : ℝ} (hs : s / 2 < ρ.re) :
    ¬ ErrorFiniteEnergy s := by
  intro henergy
  have hρ0 : ρ ≠ 0 := by intro he; norm_num [he] at hhalf
  have hρ1 : ρ ≠ 1 := by intro he; norm_num [he] at hone
  have he : errorMellin =ᶠ[𝓝[≠] ρ] meromorphicError :=
    errorMellin_germ_eq_of_halfplane_analytic (by linarith : s / 2 < 2)
      (fun w hw => errorMellin_analyticAt_of_energy henergy hw) hs
  have hn := (errorMellin_analyticAt_of_energy henergy hs).meromorphicOrderAt_nonneg
  rw [meromorphicOrderAt_congr he, meromorphicError_order_at_zero hρ0 hρ1 hzero] at hn
  exact (by decide : ¬ (0 : WithTop ℤ) ≤ -1) hn

/-- The weighted Chebyshev-error energy criterion implies Mathlib's RH. -/
theorem riemannHypothesis_of_all_chebyshev_damping
    (h : ∀ ε : ℝ, 0 < ε → ErrorFiniteEnergy (1 + ε)) :
    RiemannHypothesis := by
  by_contra hRH
  obtain ⟨ρ, hhalf, hone, hzero, _hpole, _hhardy⟩ :=
    not_RH_exists_chebyshev_pole_and_hardy_obstructions hRH
  have hε : 0 < ρ.re - 1 / 2 := by linarith
  exact not_errorFiniteEnergy_of_offline_zero hhalf hone hzero
    (by linarith : (1 + (ρ.re - 1 / 2)) / 2 < ρ.re) (h _ hε)

private theorem errorMellin_scaled_boundary_norm_sq_le
    {ρ : ℂ} (henergy : ErrorFiniteEnergy (2 * ρ.re)) {t : ℝ} (ht : 0 < t) :
    ‖(t : ℂ) * errorMellin (ρ + (t : ℂ))‖ ^ 2 ≤
      t / 2 * MeasureTheory.WeightedMellin.energy
        (fun x : ℝ => (Chebyshev.psi x : ℂ) - (x : ℂ)) (2 * ρ.re) := by
  have hz : (2 * ρ.re) / 2 < (ρ + (t : ℂ)).re := by
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith
  have hb := MeasureTheory.WeightedMellin.transform_norm_sq_le
    (error_finiteEnergy henergy) hz
  rw [← errorMellin_eq_transform] at hb
  have hd : 2 * (ρ + (t : ℂ)).re - 2 * ρ.re = 2 * t := by
    simp only [Complex.add_re, Complex.ofReal_re]
    ring
  rw [hd] at hb
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  calc
    _ ≤ t ^ 2 * (MeasureTheory.WeightedMellin.energy
          (fun x : ℝ => (Chebyshev.psi x : ℂ) - (x : ℂ)) (2 * ρ.re) / (2 * t)) :=
      mul_le_mul_of_nonneg_left hb (sq_nonneg t)
    _ = _ := by field_simp [ne_of_gt ht]

/-- Finite weighted energy rules out a simple pole exactly on the boundary.
The Cauchy--Schwarz bound only permits inverse-square-root radial growth. -/
theorem not_errorFiniteEnergy_at_offline_zero_endpoint
    {ρ : ℂ} (hhalf : (1 / 2 : ℝ) < ρ.re) (hone : ρ.re < 1)
    (hzero : riemannZeta ρ = 0) : ¬ ErrorFiniteEnergy (2 * ρ.re) := by
  intro henergy
  have hρ0 : ρ ≠ 0 := by intro he; norm_num [he] at hhalf
  have hρ1 : ρ ≠ 1 := by intro he; norm_num [he] at hone
  have hm := meromorphicError_meromorphicAt_everywhere ρ
  obtain ⟨g, hga, hgn, hrepr⟩ :=
    (meromorphicOrderAt_eq_int_iff (n := -1) hm).mp
      (meromorphicError_order_at_zero hρ0 hρ1 hzero)
  have hM (w : ℂ) (hw : ρ.re < w.re) : AnalyticAt ℂ errorMellin w := by
    apply errorMellin_analyticAt_of_energy henergy
    linarith
  have hident (w : ℂ) (hw : ρ.re < w.re)
      (hwA : AnalyticAt ℂ meromorphicError w) : errorMellin w = meromorphicError w := by
    have he := errorMellin_germ_eq_of_halfplane_analytic (by linarith : ρ.re < 2) hM hw
    exact tendsto_nhds_unique_of_eventuallyEq
      ((hM w hw).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      (hwA.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) he
  let t : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let z : ℕ → ℂ := fun n => ρ + (t n : ℂ)
  have ht (n : ℕ) : 0 < t n := by dsimp [t]; positivity
  have htlim : Tendsto t atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hzlim : Tendsto z atTop (𝓝 ρ) := by
    simpa [z] using tendsto_const_nhds.add
      ((Complex.continuous_ofReal.tendsto (0 : ℝ)).comp htlim)
  have hzne (n : ℕ) : z n ≠ ρ := by
    intro he
    have hre := congrArg Complex.re he
    simp only [z, Complex.add_re, Complex.ofReal_re] at hre
    have hp := ht n
    linarith
  have hzlimNE : Tendsto z atTop (𝓝[≠] ρ) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨hzlim, Filter.Eventually.of_forall (fun n => hzne n)⟩
  have hbound : ∀ᶠ n in atTop,
      ‖g (z n)‖ ^ 2 ≤ t n / 2 * MeasureTheory.WeightedMellin.energy
        (fun x : ℝ => (Chebyshev.psi x : ℂ) - (x : ℂ)) (2 * ρ.re) := by
    filter_upwards [hzlimNE.eventually hrepr,
      hzlimNE.eventually hm.eventually_analyticAt] with n hrep hnA
    have hzn : ρ.re < (z n).re := by
      simp only [z, Complex.add_re, Complex.ofReal_re]
      linarith [ht n]
    have hid := hident (z n) hzn hnA
    have hzsub : z n - ρ = (t n : ℂ) := by dsimp [z]; ring
    have hrep' : meromorphicError (z n) = (t n : ℂ)⁻¹ * g (z n) := by
      simpa only [hzsub, zpow_neg_one, smul_eq_mul] using hrep
    have htnc : (t n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ht n).ne'
    have hres : (t n : ℂ) * errorMellin (z n) = g (z n) := by
      rw [hid, hrep']
      simp [htnc]
    have hb := errorMellin_scaled_boundary_norm_sq_le henergy (ht n)
    change ‖(t n : ℂ) * errorMellin (z n)‖ ^ 2 ≤ _ at hb
    rwa [hres] at hb
  have hgLim : Tendsto (fun n => ‖g (z n)‖ ^ 2) atTop (𝓝 (‖g ρ‖ ^ 2)) :=
    ((hga.continuousAt.tendsto.comp hzlim).norm).pow 2
  have hELim : Tendsto (fun n => t n / 2 * MeasureTheory.WeightedMellin.energy
      (fun x : ℝ => (Chebyshev.psi x : ℂ) - (x : ℂ)) (2 * ρ.re)) atTop (𝓝 0) := by
    simpa using (htlim.div_const (2 : ℝ)).mul_const
      (MeasureTheory.WeightedMellin.energy
        (fun x : ℝ => (Chebyshev.psi x : ℂ) - (x : ℂ)) (2 * ρ.re))
  have hle : ‖g ρ‖ ^ 2 ≤ 0 := le_of_tendsto_of_tendsto hgLim hELim hbound
  have hnorm : ‖g ρ‖ = 0 := by nlinarith [norm_nonneg (g ρ)]
  exact hgn (norm_eq_zero.mp hnorm)

/-- This discharges the full endpoint-inclusive target in ChebyshevZeroObstruction. -/
theorem offLineZeroDampedEnergyDivergence : OffLineZeroDampedEnergyDivergenceTarget := by
  intro ρ hzero hhalf hone ε hε hle
  by_cases hlt : ε < 2 * ρ.re - 1
  · exact not_errorFiniteEnergy_of_offline_zero hhalf hone hzero (by linarith)
  · have heq : 1 + ε = 2 * ρ.re := by linarith
    rw [heq]
    exact not_errorFiniteEnergy_at_offline_zero_endpoint hhalf hone hzero

end RiemannResearch.RH.ChebyshevMellin
