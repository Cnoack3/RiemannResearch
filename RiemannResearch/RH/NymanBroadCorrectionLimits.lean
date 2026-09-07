import RiemannResearch.RH.NymanBroadCorrelationBounds
import RiemannResearch.RH.ArchimedeanCorrectionLimit

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Vanishing complete gamma and higher-power corrections for the actual family

The uniform quadratic displacement was proved for the varying normalized
arithmetic profiles. Combining it with the actual finite second moments
gives both correction limits; no fixed-profile substitution is made.
-/

open MeasureTheory Set Filter
open scoped Topology
namespace RiemannResearch.RH
open RiemannResearch.Analysis PrimeCompensationLimits

/-- The complete gamma displacement of the actual broad arithmetic family
vanishes. The underlying bound is an explicit constant times R⁻². -/
theorem tendsto_gammaDisplacement_nymanBroadCorrelation (n : ℕ) (hn : 2≤n)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ)
    (hc : HasCompactSupport φ) (hmass : (∫x,φ x) ≠ 0) :
    Tendsto (fun R => gammaDisplacementCorrection (nymanBroadCorrelation n φ R) R)
      atTop (𝓝 0) := by
  obtain ⟨V,B,hV,hB,hbounds⟩ := eventually_nymanBroadCorrelation_uniform_bounds n hn hφ hc hmass
  let J := ∫t in Ioi 0,displacementKernel t*t^2
  have hlim : Tendsto (fun R : ℝ => (2*B/R^2)*J) atTop (𝓝 0) := by
    have h := ((tendsto_inv_atTop_zero.pow 2).const_mul (2*B)).mul_const J
    simpa only [inv_pow,zero_pow (by decide : (2:ℕ)≠0),mul_zero,zero_mul,
      div_eq_mul_inv] using h
  apply squeeze_zero_norm' _ hlim
  filter_upwards [hbounds] with R hR
  rcases hR with ⟨hcd,hcc,hci,hdi,hvar,hzero,hdisp⟩
  simpa only [Real.norm_eq_abs,J] using
    (gammaDisplacementCorrection_bound (nymanBroadCorrelation n φ R) hcd.continuous R B hB
      (fun t _ => hdisp (t/R))).2

/-- Every higher prime power is retained in this actual varying-family limit;
the dominating arithmetic second moment is an unconditionally summable series. -/
theorem tendsto_higherPrimePowerDisplacement_nymanBroadCorrelation (n : ℕ) (hn : 2≤n)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ)
    (hc : HasCompactSupport φ) (hmass : (∫x,φ x) ≠ 0) :
    Tendsto (fun R => higherPrimePowerCorrection (nymanBroadCorrelation n φ R) R)
      atTop (𝓝 0) := by
  obtain ⟨V,B,hV,hB,hbounds⟩ := eventually_nymanBroadCorrelation_uniform_bounds n hn hφ hc hmass
  let J := ∑'pj:ℕ×ℕ,higherPrimePowerWeight pj.1 pj.2 *
    higherPrimePowerDisplacement pj.1 pj.2^2
  have hlim : Tendsto (fun R : ℝ => (2*B/R^2)*J) atTop (𝓝 0) := by
    have h := ((tendsto_inv_atTop_zero.pow 2).const_mul (2*B)).mul_const J
    simpa only [inv_pow,zero_pow (by decide : (2:ℕ)≠0),mul_zero,zero_mul,
      div_eq_mul_inv] using h
  apply squeeze_zero_norm' _ hlim
  filter_upwards [hbounds] with R hR
  rcases hR with ⟨hcd,hcc,hci,hdi,hvar,hzero,hdisp⟩
  simpa only [Real.norm_eq_abs,J] using
    (higherPrimePowerCorrection_bound (nymanBroadCorrelation n φ R) R B hB
      (fun t => hdisp (t/R))).2


/-- Both complete displacement corrections have a common inverse-square
bound for the actual varying arithmetic family. -/
theorem eventually_nymanBroad_displacement_inverse_square_bound (n : ℕ) (hn : 2≤n)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ)
    (hc : HasCompactSupport φ) (hmass : (∫x,φ x) ≠ 0) :
    ∃ K : ℝ, 0≤K ∧ ∀ᶠ R : ℝ in atTop,
      |gammaDisplacementCorrection (nymanBroadCorrelation n φ R) R|≤K/R^2 ∧
      |higherPrimePowerCorrection (nymanBroadCorrelation n φ R) R|≤K/R^2 := by
  obtain ⟨V,B,hV,hB,hbounds⟩ := eventually_nymanBroadCorrelation_uniform_bounds n hn hφ hc hmass
  let Jg := ∫t in Ioi 0,displacementKernel t*t^2
  let Jp := ∑'pj:ℕ×ℕ,higherPrimePowerWeight pj.1 pj.2 *
    higherPrimePowerDisplacement pj.1 pj.2^2
  have hg : Jg≤|Jg|+|Jp| := by linarith [le_abs_self Jg,abs_nonneg Jp]
  have hp : Jp≤|Jg|+|Jp| := by linarith [le_abs_self Jp,abs_nonneg Jg]
  refine ⟨2*B*(|Jg|+|Jp|),by positivity,?_⟩
  filter_upwards [hbounds] with R hR
  rcases hR with ⟨hcd,hcc,hci,hdi,hvar,hzero,hdisp⟩
  have hfactor : 0≤2*B/R^2 := by positivity
  constructor
  · have hbound := (gammaDisplacementCorrection_bound (nymanBroadCorrelation n φ R)
      hcd.continuous R B hB (fun t _ => hdisp (t/R))).2
    exact hbound.trans ((mul_le_mul_of_nonneg_left hg hfactor).trans_eq (by ring))
  · have hbound := (higherPrimePowerCorrection_bound (nymanBroadCorrelation n φ R)
      R B hB (fun t => hdisp (t/R))).2
    exact hbound.trans ((mul_le_mul_of_nonneg_left hp hfactor).trans_eq (by ring))

end RiemannResearch.RH
