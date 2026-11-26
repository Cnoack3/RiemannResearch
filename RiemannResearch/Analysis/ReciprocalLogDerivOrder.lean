import RiemannResearch.RH.ChebyshevMellinRH
import RiemannResearch.Analysis.MontgomeryPositiveGapDensity

/-! At a zeta zero of multiplicity m, the reciprocal logarithmic derivative
has a simple analytic zero with derivative 1/m. The local principal-part
calculation follows the zero case in Zeta23.Analytic.rectangleIntegral'_mul_logDeriv_of_poles.
The meromorphic order uses ChebyshevMellin.logDeriv_order_at_zero. -/
noncomputable section
open Filter Zeta23
open scoped Topology

namespace RiemannResearch.Analysis.ReciprocalLogDerivOrder

/-- The reciprocal logarithmic derivative, including its zero value at a zeta zero. -/
def reciprocalLogDeriv : ℂ → ℂ := (logDeriv riemannZeta)⁻¹

theorem reciprocal_order_at_zero {ρ : ℂ} (hone : ρ ≠ 1) (hz : riemannZeta ρ = 0) :
    meromorphicOrderAt reciprocalLogDeriv ρ = 1 := by
  rw [reciprocalLogDeriv, meromorphicOrderAt_inv,
    RiemannResearch.RH.ChebyshevMellin.logDeriv_order_at_zero hone hz]
  norm_num

theorem reciprocal_value_at_zero {ρ : ℂ} (hz : riemannZeta ρ = 0) :
    reciprocalLogDeriv ρ = 0 := by
  simp [reciprocalLogDeriv, logDeriv_apply, hz]

theorem reciprocal_analytic_at_zero {ρ : ℂ} (hone : ρ ≠ 1) (hz : riemannZeta ρ = 0) :
    AnalyticAt ℂ reciprocalLogDeriv ρ :=
  AnalyticAt.of_meromorphicOrderAt_pos
    (by rw [reciprocal_order_at_zero hone hz]; exact zero_lt_one) (reciprocal_value_at_zero hz)

/-- The normalized pole of ζ'/ζ has residue equal to the full analytic multiplicity. -/
theorem zeta_logDeriv_residue {ρ : ℂ} (hone : ρ ≠ 1) :
    Tendsto (fun s => (s-ρ)*logDeriv riemannZeta s) (𝓝[≠] ρ) (𝓝 (zeroMult ρ : ℂ)) := by
  let m := zeroMult ρ
  have ha := riemannZeta_analyticOnNhd_compl_one ρ hone
  obtain ⟨g,hg,hg₀,hfac⟩ := ha.analyticOrderAt_ne_top.mp (analyticOrderAt_riemannZeta_ne_top hone)
  have hfactor : riemannZeta =ᶠ[𝓝 ρ] (fun s => (s-ρ)^m * g s) := hfac
  have hreg : ContinuousAt (fun s => logDeriv g s) ρ :=
    hg.deriv.continuousAt.div hg.continuousAt hg₀
  have hlim : Tendsto (fun s => (m:ℂ) + (s-ρ)*logDeriv g s) (𝓝[≠] ρ) (𝓝 (m:ℂ)) := by
    have hcont : ContinuousAt (fun s => (m:ℂ) + (s-ρ)*logDeriv g s) ρ :=
      continuousAt_const.add ((continuousAt_id.sub continuousAt_const).mul hreg)
    simpa only [sub_self, zero_mul, add_zero] using hcont.tendsto.mono_left nhdsWithin_le_nhds
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hfactor.eventually_nhds,
    mem_nhdsWithin_of_mem_nhds (hg.continuousAt.eventually_ne hg₀),
    mem_nhdsWithin_of_mem_nhds hg.eventually_analyticAt] with s hs hfs hgs hgas
  have hsr : s-ρ ≠ 0 := sub_ne_zero.mpr (by simpa using hs)
  have hh : riemannZeta =ᶠ[𝓝 s] (fun u : ℂ => (u-ρ)^m * g u) := hfs
  have he : logDeriv riemannZeta s = logDeriv (fun u : ℂ => (u-ρ)^m * g u) s := by
    simp only [logDeriv_apply, hh.deriv_eq, hh.self_of_nhds]
  have hw : logDeriv (fun u : ℂ => (u-ρ)^m) s = (m:ℂ)/(s-ρ) := by
    rw [show (fun u : ℂ => (u-ρ)^m) = (fun u : ℂ => u^m) ∘ (fun u => u-ρ) from rfl,
      logDeriv_comp (by fun_prop) (by fun_prop), logDeriv_pow]
    simp
  rw [he, logDeriv_mul (f := fun u : ℂ => (u-ρ)^m) (g := g) s
    (pow_ne_zero _ hsr) hgs (by fun_prop) hgas.differentiableAt, hw]
  field_simp [hsr] <;> ring

/-- Exact slope of the locally analytic reciprocal at an actual nontrivial zero. -/
theorem hasDerivAt_reciprocal {ρ : ℂ} (hz : IsNontrivialZero ρ) :
    HasDerivAt reciprocalLogDeriv ((zeroMult ρ : ℂ)⁻¹) ρ := by
  have hone : ρ ≠ 1 := by rintro rfl; simpa using hz.2.2
  have hpos := zetaSeam.one_le_mult ρ hz
  have hn : zeroMult ρ ≠ 0 := by omega
  have hn' : (zeroMult ρ : ℂ) ≠ 0 := by exact_mod_cast hn
  have hi := (zeta_logDeriv_residue hone).inv₀ hn'
  rw [hasDerivAt_iff_tendsto_slope, slope_fun_def_field]
  have hr : (logDeriv riemannZeta ρ)⁻¹ = 0 := reciprocal_value_at_zero hz.1
  simpa only [reciprocalLogDeriv, Pi.inv_apply, hr, sub_zero, mul_inv_rev, div_eq_mul_inv]
    using hi

theorem reciprocal_simple_at_zero {ρ : ℂ} (hz : IsNontrivialZero ρ) :
    analyticOrderAt reciprocalLogDeriv ρ = 1 := by
  have hone : ρ ≠ 1 := by rintro rfl; simpa using hz.2.2
  refine (reciprocal_analytic_at_zero hone hz.1).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
    (reciprocal_value_at_zero hz.1) ?_
  rw [(hasDerivAt_reciprocal hz).deriv]
  apply inv_ne_zero
  exact_mod_cast (show zeroMult ρ ≠ 0 by have := zetaSeam.one_le_mult ρ hz; omega)

/-- Recover the multiplicity exactly from the slope of the order-one zero. -/
theorem multiplicity_eq_inverse_slope {ρ : ℂ} (hz : IsNontrivialZero ρ) :
    (zeroMult ρ : ℂ) = (deriv reciprocalLogDeriv ρ)⁻¹ := by
  rw [(hasDerivAt_reciprocal hz).deriv, inv_inv]

/-- Multiplicity weight read from an order-one zero of the reciprocal. -/
def slopeWeight (ρ : ℂ) : ℝ :=
  ((deriv reciprocalLogDeriv ρ)⁻¹).re

theorem slopeWeight_eq_mult {ρ : ℂ} (h : IsNontrivialZero ρ) :
    slopeWeight ρ = (zeroMult ρ : ℝ) := by
  unfold slopeWeight
  rw [← multiplicity_eq_inverse_slope h]
  simp

/-- Sum over distinct complex zeros with weights obtained from simple slopes. -/
def slopeSum (T : ℝ) (f : ℂ → ℝ) : ℝ :=
  ∑ ρ ∈ ActualZeroOrdinate.cutoff T, slopeWeight ρ * f ρ

theorem slopeSum_eq_copies (T : ℝ) (f : ℂ → ℝ) :
    slopeSum T f = ∑ c : ActualZeroOrdinate.Copies T, f c.1.1 := by
  rw [← ActualZeroOrdinate.realSum_eq_copies]
  exact Finset.sum_congr rfl (fun ρ hρ =>
    congrArg (fun a : ℝ => a * f ρ) (slopeWeight_eq_mult (ActualZeroOrdinate.mem_cutoff.mp hρ).1))

/-- Recover any two-point test of the full occurrence multiset from simple roots. -/
theorem slopePairSum_eq_copies (T : ℝ) (w : ℂ → ℂ → ℝ) :
    slopeSum T (fun ρ => slopeSum T (w ρ)) =
      ∑ i : ActualZeroOrdinate.Copies T, ∑ j : ActualZeroOrdinate.Copies T, w i.1.1 j.1.1 := by
  rw [slopeSum_eq_copies]
  exact Finset.sum_congr rfl (fun i _ => slopeSum_eq_copies T (w i.1.1))

/-- Ordinary positive-gap mass evaluated at one copy of each distinct complex zero. -/
theorem positiveGapMass_eq_slopePair (T q : ℝ) :
    MontgomeryPositiveGap.positiveGapMass T q =
      slopeSum T (fun ρ => slopeSum T (fun σ =>
        let d := Real.log T / (2 * Real.pi) * (σ.im - ρ.im)
        if 0 < d ∧ d ≤ q then 1 else 0)) / (T * Real.log T / (2 * Real.pi)) := by
  rw [slopePairSum_eq_copies] <;> rfl

end RiemannResearch.Analysis.ReciprocalLogDerivOrder
