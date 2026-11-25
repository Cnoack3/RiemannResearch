import RiemannResearch.Analysis.ActualInghamGabrielDamping
import RiemannResearch.RH.RiemannHypothesisRightHalfStrip
import RiemannResearch.RH.BurnolDampingZeroShift

/-! # Analytic reciprocal zeta across its removable point

This representative of the reciprocal has a simple zero at one and agrees
with the ordinary inverse away from one. Under RH it is holomorphic on
the open right half-plane needed by complex damping. -/

noncomputable section
open Complex Filter
open scoped Topology
namespace RiemannResearch.Analysis.RHInteriorLogDerivative
open RiemannResearch.Analysis.InghamMollifier

def analyticReciprocalZeta (s : ℂ) : ℂ := (s-1) / gabrielRegularZeta s

@[simp] theorem analyticReciprocalZeta_one : analyticReciprocalZeta 1 = 0 := by
  simp [analyticReciprocalZeta]

theorem analyticReciprocalZeta_off_one {s : ℂ} (h : s ≠ 1) :
    analyticReciprocalZeta s = (riemannZeta s)⁻¹ := by
  unfold analyticReciprocalZeta
  rw [gabrielRegularZeta,if_neg h]
  by_cases hz : riemannZeta s = 0
  · simp [hz]
  · field_simp [sub_ne_zero.mpr h,hz]

theorem hasDerivAt_analyticReciprocalZeta_one :
    HasDerivAt analyticReciprocalZeta 1 1 := by
  have h := ((hasDerivAt_id (1:ℂ)).sub_const 1).div
    (analyticAt_gabrielRegularZeta 1).differentiableAt.hasDerivAt (by simp)
  change HasDerivAt ((fun x : ℂ => x-1) / gabrielRegularZeta) 1 1
  simpa only [gabrielRegularZeta_one,sub_self,mul_one,
    zero_mul,sub_zero,one_pow,div_one, id_eq,Pi.div_apply] using h

theorem analyticAt_reciprocalZeta_of_riemannHypothesis (hRH : RiemannHypothesis) {s : ℂ}
    (hs : 1/2 < s.re) : AnalyticAt ℂ analyticReciprocalZeta s := by
  have hg : gabrielRegularZeta s ≠ 0 := by
    by_cases h : s = 1
    · simp [h]
    rw [gabrielRegularZeta, if_neg h]
    apply mul_ne_zero (sub_ne_zero.mpr h)
    rcases lt_or_ge s.re 1 with hr | hr
    · exact RiemannResearch.RH.riemannHypothesis_iff_right_half_strip_zero_free.mp hRH s hs hr
    · exact riemannZeta_ne_zero_of_one_le_re hr
  exact (analyticAt_id.sub analyticAt_const).div (analyticAt_gabrielRegularZeta s) hg

/-- A holomorphic right-half-plane reciprocal would rule out every right
zero, including a zero at which the pointwise inverse is totalized. -/
theorem riemannHypothesis_iff_analytic_reciprocalZeta :
    RiemannHypothesis ↔ ∀ s : ℂ, 1/2 < s.re → AnalyticAt ℂ analyticReciprocalZeta s := by
  refine ⟨fun h s hs => analyticAt_reciprocalZeta_of_riemannHypothesis h hs,?_⟩
  intro h
  apply RiemannResearch.RH.riemannHypothesis_iff_right_half_strip_zero_free.mpr
  intro s hs hs' hz
  have hs1 : s ≠ 1 := fun e => by simp [e] at hs'
  have hzc := (differentiableAt_riemannZeta hs1).continuousAt
  have hprod := hzc.mul (h s hs).continuousAt
  have hn := RiemannResearch.RH.Burnol.zeta_eventually_ne_zero_punctured s hs1
  have hne : ∀ᶠ z in 𝓝 s, z ≠ 1 := compl_singleton_mem_nhds hs1
  have he : (fun z => riemannZeta z * analyticReciprocalZeta z) =ᶠ[𝓝[≠] s] fun _ => 1 := by
    filter_upwards [hn,hne.filter_mono nhdsWithin_le_nhds] with z hn hz1
    rw [analyticReciprocalZeta_off_one hz1,mul_inv_cancel₀ hn]
  have hlim := (hprod.tendsto.mono_left nhdsWithin_le_nhds).congr' he
  simpa [hz] using (tendsto_nhds_unique hlim (tendsto_const_nhds (x := (1:ℂ))))

end RiemannResearch.Analysis.RHInteriorLogDerivative

namespace RiemannResearch.Analysis.RHInteriorLogDerivative

/--
info: 'RiemannResearch.Analysis.RHInteriorLogDerivative.riemannHypothesis_iff_analytic_reciprocalZeta' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms riemannHypothesis_iff_analytic_reciprocalZeta

end RiemannResearch.Analysis.RHInteriorLogDerivative
