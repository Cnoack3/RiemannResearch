import RiemannResearch.RH.ParetoShiftedZetaCompactWindow
import RiemannResearch.RH.CriticalLineZeros

/-! # The critical-line quotient on the damping scale at an actual zero

The order of vanishing determines the complete rescaled local profile.
At a simple critical zero the squared defect has the Cauchy profile. -/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace RiemannResearch.RH.Pareto.ResidueMellin
open MellinFrequency (criticalPoint criticalPoint_re criticalPoint_ne_one)

/-- Along a ray in the height/damping plane, the nonvanishing analytic
factor cancels in the limit and the full actual zero multiplicity remains. -/
theorem shiftedZetaQuotient_scaled_limit (a u : ℝ) :
    Tendsto (fun ε : ℝ => shiftedZetaQuotient ε (a + ε*u))
      (𝓝[>] (0 : ℝ)) (𝓝 ((((u:ℂ)*Complex.I)/(1+(u:ℂ)*Complex.I)) ^ Zeta23.zeroMult (criticalPoint a))) := by
  let z := criticalPoint a
  let m := Zeta23.zeroMult z
  let v := (u:ℂ)*Complex.I
  let p (ε : ℝ) := z + (ε : ℂ)*v
  let q (ε : ℝ) := z + (ε : ℂ)*(1+v)
  have hz := criticalPoint_ne_one a
  have ha := Zeta23.riemannZeta_analyticOnNhd_compl_one z hz
  obtain ⟨g,hg,hg₀,hfac⟩ := ha.analyticOrderAt_ne_top.mp (Zeta23.analyticOrderAt_riemannZeta_ne_top hz)
  have hp : Tendsto p (𝓝[>] (0:ℝ)) (𝓝 z) := by
    have h : Continuous p := by dsimp [p]; fun_prop
    simpa [p] using (h.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
  have hq : Tendsto q (𝓝[>] (0:ℝ)) (𝓝 z) := by
    have h : Continuous q := by dsimp [q]; fun_prop
    simpa [q] using (h.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
  have hR := (hg.continuousAt.tendsto.comp hp).div (hg.continuousAt.tendsto.comp hq) hg₀
  have hlim : Tendsto (fun ε => (v/(1+v))^m * (g (p ε)/g (q ε)))
      (𝓝[>] (0:ℝ)) (𝓝 ((v/(1+v))^m)) := by
    simpa only [Function.comp_apply, Pi.div_apply, div_self hg₀, mul_one] using
      hR.const_mul ((v/(1+v))^m)
  apply hlim.congr'
  filter_upwards [hp.eventually hfac,hq.eventually hfac,
    (self_mem_nhdsWithin : ∀ᶠ ε in 𝓝[>] (0:ℝ), 0 < ε)] with ε hP hQ he
  change 0 < ε at he
  have hp' : criticalPoint (a+ε*u) = p ε := by
    dsimp [p,z,v,MellinFrequency.criticalPoint]; push_cast; ring
  have hq' : criticalPoint (a+ε*u)+(ε:ℂ) = q ε := by rw [hp']; dsimp [p,q]; ring
  change (v/(1+v))^m*(g (p ε)/g (q ε)) =
    riemannZeta (criticalPoint (a+ε*u))/riemannZeta (criticalPoint (a+ε*u)+(ε:ℂ))
  change riemannZeta (p ε) = (p ε-z)^m*g (p ε) at hP
  change riemannZeta (q ε) = (q ε-z)^m*g (q ε) at hQ
  rw [hp', show p ε+(ε:ℂ)=q ε by dsimp [p,q]; ring, hP,hQ, mul_div_mul_comm, ← div_pow]
  have hεc : (ε:ℂ) ≠ 0 := by exact_mod_cast he.ne'
  simp only [p,q,add_sub_cancel_left,mul_div_mul_left _ _ hεc]

/-- Rescaled squared quotient defect, including the angular Mellin weight. -/
theorem shiftedZeta_boundarySquare_scaled_limit (a u : ℝ) :
    Tendsto (fun ε : ℝ => boundarySquare (fun t => 1-shiftedZetaQuotient ε t) (a+ε*u))
      (𝓝[>] (0:ℝ)) (𝓝 (‖1-(((u:ℂ)*Complex.I)/(1+(u:ℂ)*Complex.I)) ^ Zeta23.zeroMult (criticalPoint a)‖^2 /
        (1/4+a^2))) := by
  have ht : Tendsto (fun ε : ℝ => a+ε*u) (𝓝[>] (0:ℝ)) (𝓝 a) := by
    have h : Continuous (fun ε : ℝ => a + ε*u) := by fun_prop
    simpa only [zero_mul, add_zero] using (h.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
  exact (((tendsto_const_nhds (x := (1:ℂ))).sub
    (shiftedZetaQuotient_scaled_limit a u)).norm.pow 2).div
    ((tendsto_const_nhds (x := (1/4:ℝ))).add (ht.pow 2)) (by positivity)

theorem simple_zero_scaled_boundary (a u : ℝ) (hm : Zeta23.zeroMult (criticalPoint a) = 1) :
    Tendsto (fun ε : ℝ => boundarySquare (fun t => 1-shiftedZetaQuotient ε t) (a+ε*u))
      (𝓝[>] (0:ℝ)) (𝓝 ((1+u^2)⁻¹/(1/4+a^2))) := by
  have h := shiftedZeta_boundarySquare_scaled_limit a u
  rw [hm, pow_one] at h
  have hn : (1:ℂ)+(u:ℂ)*Complex.I ≠ 0 := fun hz => by
    have := congrArg Complex.re hz
    simp at this
  have he : 1-((u:ℂ)*Complex.I)/(1+(u:ℂ)*Complex.I) = ((1:ℂ)+(u:ℂ)*Complex.I)⁻¹ := by
    field_simp [hn]; ring
  rw [he, norm_inv, inv_pow, Complex.sq_norm, Complex.normSq_apply] at h
  simpa [pow_two,Complex.mul_re,Complex.mul_im] using h

end RiemannResearch.RH.Pareto.ResidueMellin

namespace RiemannResearch.RH.Pareto.ResidueMellin

/--
info: 'RiemannResearch.RH.Pareto.ResidueMellin.shiftedZetaQuotient_scaled_limit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms shiftedZetaQuotient_scaled_limit

end RiemannResearch.RH.Pareto.ResidueMellin

namespace RiemannResearch.RH.Pareto.ResidueMellin

/--
info: 'RiemannResearch.RH.Pareto.ResidueMellin.simple_zero_scaled_boundary' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms simple_zero_scaled_boundary

end RiemannResearch.RH.Pareto.ResidueMellin
