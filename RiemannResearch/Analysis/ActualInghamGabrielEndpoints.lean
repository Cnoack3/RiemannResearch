import RiemannResearch.Analysis.ActualInghamCauchyObservation
import RiemannResearch.Analysis.ActualInghamRightMoment
import RiemannResearch.Analysis.ActualInghamMixedMomentBound
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-!
# The actual damped endpoint budgets in Gabriel's interpolation formula

Chourasiya and Simonič, https://arxiv.org/html/2507.15184v2, Corollary 6,
equation (30), use endpoint budgets of the form
`∫ u in Ioi 0, exp (−u) * ∫ t in 0..T*a*sqrt u, f t`.
We take the permitted splitting point A = 0. The results below bound both
actual endpoint budgets unconditionally and preserve the two- and three-log
powers of the underlying vertical moments. The moving right endpoint has an
exact Gamma-function majorant. The mixed-exponent holomorphic strip inequality
is a separate ingredient.
-/
noncomputable section
open MeasureTheory Set Complex Filter
namespace RiemannResearch.Analysis.InghamMollifier

/-- Damped endpoint term from Corollary 6 with lower cutoff zero. -/
def gabrielEndpoint (f : ℝ → ℝ) (T a : ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), Real.exp (-u) * ∫ t in (0 : ℝ)..T * a * Real.sqrt u, f t

private theorem gamma_monomial_integrable (n : ℕ) :
    IntegrableOn (fun u : ℝ => Real.exp (-u) * u ^ n) (Ioi 0) := by
  have h := Real.GammaIntegral_convergent (s := (n : ℝ) + 1) (by positivity)
  simpa only [add_sub_cancel_right, Real.rpow_natCast] using h

private theorem gamma_monomial (n : ℕ) :
    (∫ u in Ioi (0 : ℝ), Real.exp (-u) * u ^ n) = (n.factorial : ℝ) := by
  have h := (Real.Gamma_eq_integral (s := (n : ℝ) + 1) (by positivity)).symm
  simpa only [add_sub_cancel_right, Real.rpow_natCast, Real.Gamma_nat_eq_factorial] using h

private theorem damped_add_cube :
    IntegrableOn (fun u : ℝ => Real.exp (-u) + Real.exp (-u) * u ^ 3) (Ioi 0) ∧
      (∫ u in Ioi (0 : ℝ), Real.exp (-u) + Real.exp (-u) * u ^ 3) = 7 := by
  have h0 : IntegrableOn (fun u : ℝ => Real.exp (-u)) (Ioi 0) := by
    simpa using gamma_monomial_integrable 0
  have v0 : (∫ u in Ioi (0 : ℝ), Real.exp (-u)) = 1 := by simpa using gamma_monomial 0
  refine ⟨h0.add (gamma_monomial_integrable 3), ?_⟩
  rw [integral_add h0 (gamma_monomial_integrable 3), v0, gamma_monomial]
  norm_num [Nat.factorial]

private theorem endpoint_continuous {f : ℝ → ℝ} (hf : Continuous f) (T a : ℝ) :
    Continuous (fun u : ℝ => Real.exp (-u) * ∫ t in (0 : ℝ)..T*a*Real.sqrt u, f t) := by
  exact (Real.continuous_exp.comp continuous_neg).mul
    ((intervalIntegral.continuous_primitive (fun p q => hf.intervalIntegrable p q) 0).comp
      (continuous_const.mul Real.continuous_sqrt))

/-- Exact integration of the affine majorant for a translated-window second moment. -/
theorem gabrielEndpoint_of_affine {f : ℝ → ℝ} (hf : Continuous f)
    (hpos : ∀ t, 0 ≤ f t) {A B T a : ℝ} (hT : 0 ≤ T) (ha : 0 ≤ a)
    (hF : ∀ U : ℝ, 0 ≤ U → (∫ t in 0..U, f t) ≤ A + B * U) :
    IntegrableOn (fun u : ℝ => Real.exp (-u) * ∫ t in 0..T*a*Real.sqrt u, f t) (Ioi 0) ∧
    gabrielEndpoint f T a ≤ A + B * (T*a) * Real.Gamma (3 / 2) := by
  have h0 : IntegrableOn (fun u : ℝ => Real.exp (-u)) (Ioi 0) := by
    simpa using gamma_monomial_integrable 0
  have v0 : (∫ u in Ioi (0 : ℝ), Real.exp (-u)) = 1 := by simpa using gamma_monomial 0
  have hhalf : (3 / 2 : ℝ) - 1 = 1 / 2 := by norm_num
  have hs : IntegrableOn (fun u : ℝ => Real.exp (-u) * Real.sqrt u) (Ioi 0) := by
    simpa only [hhalf, ← Real.sqrt_eq_rpow] using
      Real.GammaIntegral_convergent (s := 3 / 2) (by norm_num)
  have vs : (∫ u in Ioi (0 : ℝ), Real.exp (-u) * Real.sqrt u) = Real.Gamma (3 / 2) := by
    simpa only [hhalf, ← Real.sqrt_eq_rpow] using
      (Real.Gamma_eq_integral (s := 3 / 2) (by norm_num)).symm
  let g := fun u : ℝ => A * Real.exp (-u) + (B * (T*a)) * (Real.exp (-u) * Real.sqrt u)
  have hg : IntegrableOn g (Ioi 0) := (h0.const_mul A).add (hs.const_mul _)
  have hmono (u : ℝ) :
      Real.exp (-u) * (∫ t in 0..T*a*Real.sqrt u, f t) ≤ g u := by
    calc _ ≤ Real.exp (-u) * (A + B * (T*a*Real.sqrt u)) :=
          mul_le_mul_of_nonneg_left (hF _ (by positivity)) (Real.exp_pos _).le
         _ = g u := by dsimp [g]; ring
  have hint : IntegrableOn (fun u : ℝ => Real.exp (-u) * ∫ t in 0..T*a*Real.sqrt u, f t)
      (Ioi 0) := by
    apply hg.mono' (endpoint_continuous hf T a).aestronglyMeasurable
    apply ae_of_all
    intro u
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le
      (intervalIntegral.integral_nonneg (by positivity) (fun t _ => hpos t)))]
    exact hmono u
  refine ⟨hint, (integral_mono_ae hint hg (ae_of_all _ hmono)).trans_eq ?_⟩
  dsimp [g]
  rw [integral_add (h0.const_mul A) (hs.const_mul _), integral_const_mul, integral_const_mul,
    v0, vs, mul_one]

/-- The complete right endpoint term at `1 + δ / log X` with its exact
Gamma factor. In (30) the scale is `a = sqrt ((1/2) / κ)`. -/
theorem actual_gabriel_right_endpoint_le {δ : ℝ} (hδ : 0 < δ)
    {X : ℕ} (hX : 2 ≤ X) {T a : ℝ} (hT : 0 ≤ T) (ha : 0 ≤ a) :
    let β := 1 + δ / Real.log (X : ℝ)
    let f := fun t : ℝ => ‖riemannZeta ((β : ℂ) + I * t) *
      mollifier X ((β : ℂ) + I * t) - 1‖ ^ 2
    IntegrableOn (fun u : ℝ => Real.exp (-u) * ∫ t in 0..T*a*Real.sqrt u, f t) (Ioi 0) ∧
    gabrielEndpoint f T a ≤ movingRightMomentConstant δ * (1 + Real.log X) ^ 3 *
      (1 + (T*a/(X : ℝ)) * Real.Gamma (3/2)) := by
  dsimp only
  have hx : 1 < (X : ℝ) := by exact_mod_cast (by omega : 1 < X)
  have hβ : 1 < 1 + δ / Real.log (X : ℝ) := by
    have := div_pos hδ (Real.log_pos hx); linarith
  have hc := (vertical_error_continuous X hβ.ne').pow 2
  simp only [mollifiedError, mul_comm _ I] at hc
  let K := movingRightMomentConstant δ * (1 + Real.log X) ^ 3
  have hm := gabrielEndpoint_of_affine hc (fun t => sq_nonneg _) hT ha
    (A := K) (B := K / X) (fun U hU => by
      have h := actual_moving_right_error_moment_log_cube_le hδ hX (H := 0) (T := U) hU
      rw [sub_zero] at h
      refine h.trans_eq ?_
      dsimp [K]
      ring)
  refine ⟨hm.1, hm.2.trans_eq ?_⟩
  dsimp [K]
  ring

private theorem sqrt_le_one_add {u : ℝ} (hu : 0 ≤ u) : Real.sqrt u ≤ 1 + u := by
  nlinarith [sq_nonneg (Real.sqrt u - 1), Real.sq_sqrt hu]

/-- The complete critical-line endpoint term in (30), with `A = 0`.
The constant is uniform in the height, cutoff and Gaussian scale. -/
theorem exists_actual_gabriel_left_endpoint_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {X : ℕ}, 1 ≤ X → ∀ {T a : ℝ}, 2 ≤ T → (X : ℝ) ≤ T → 0 ≤ a →
      let f := fun t : ℝ => ‖riemannZeta ((1 / 2 : ℂ) + I*t) *
        mollifier X ((1 / 2 : ℂ) + I*t) - 1‖ ^ (4/3 : ℝ)
      IntegrableOn (fun u : ℝ => Real.exp (-u) * ∫ t in 0..T*a*Real.sqrt u, f t) (Ioi 0) ∧
      gabrielEndpoint f T a ≤ C * T * (1 + Real.log T)^2 * (1+a)^3 := by
  obtain ⟨K,hK,hcrit⟩ := exists_actual_critical_error_moment_bound
  refine ⟨28*K, by positivity, ?_⟩
  intro X hX T a hT hXT ha
  let f := fun t : ℝ => ‖riemannZeta ((1 / 2 : ℂ) + I*t) *
        mollifier X ((1 / 2 : ℂ) + I*t) - 1‖ ^ (4/3 : ℝ)
  change IntegrableOn (fun u : ℝ => Real.exp (-u) * ∫ t in 0..T*a*Real.sqrt u, f t) (Ioi 0) ∧ _
  have hc : Continuous f := by
    simpa only [f, mollifiedError, mul_comm _ I] using
      (critical_error_continuous X).rpow_const (fun _ => Or.inr (by norm_num : (0 : ℝ) ≤ 4/3))
  have hp (t : ℝ) : 0 ≤ f t := by dsimp [f]; positivity
  have ht : 0 < T := by linarith
  have hlog := Real.log_nonneg (show 1 ≤ T by linarith)
  let D := K*T*(1+Real.log T)^2*(1+a)^3
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let g := fun u : ℝ => (4*D) * (Real.exp (-u) + Real.exp (-u)*u^3)
  have hg : IntegrableOn g (Ioi 0) := damped_add_cube.1.const_mul _
  have hmono (u : ℝ) (hu : 0 ≤ u) :
      Real.exp (-u) * (∫ t in 0..T*a*Real.sqrt u, f t) ≤ g u := by
    let V := T*(1+a)*(1+u)
    have hTV : T ≤ V := by
      dsimp [V]
      calc T = T*1*1 := by ring
           _ ≤ _ := by gcongr <;> linarith
    have hUV : T*a*Real.sqrt u ≤ V := by
      dsimp [V]; gcongr
      · linarith
      · exact sqrt_le_one_add hu
    have hL : 1 + Real.log V ≤ (1+Real.log T)*(1+a)*(1+u) := by
      dsimp [V]
      rw [Real.log_mul (mul_pos ht (by positivity)).ne' (by positivity),
        Real.log_mul ht.ne' (by positivity)]
      have h1 := Real.log_le_sub_one_of_pos (show 0 < 1+a by positivity)
      have h2 := Real.log_le_sub_one_of_pos (show 0 < 1+u by positivity)
      nlinarith [mul_nonneg hlog ha, mul_nonneg hlog hu, mul_nonneg ha hu,
        mul_nonneg (mul_nonneg hlog ha) hu]
    have hstep := intervalIntegral.integral_mono_interval (μ := volume) (le_refl (0 : ℝ))
      (show 0 ≤ T*a*Real.sqrt u by positivity) hUV (ae_of_all _ hp) (hc.intervalIntegrable 0 V)
    have hF : (∫ t in 0..T*a*Real.sqrt u, f t) ≤ D * (1+u)^3 := by
      refine (hstep.trans (hcrit V (hT.trans hTV) X hX (hXT.trans hTV))).trans ?_
      calc K*V*(1+Real.log V)^2 ≤ K*V*((1+Real.log T)*(1+a)*(1+u))^2 := by
             have hVlog := Real.log_nonneg (show 1 ≤ V by linarith)
             gcongr
           _ = _ := by dsimp [D,V]; ring
    calc _ ≤ Real.exp (-u)*(D * (1+u)^3) := mul_le_mul_of_nonneg_left hF (Real.exp_pos _).le
         _ ≤ g u := by
           have hpoly : (1+u)^3 ≤ 4*(1+u^3) := by
             nlinarith [mul_nonneg (show 0 ≤ 1+u by linarith) (sq_nonneg (u-1))]
           dsimp [g]
           nlinarith [mul_nonneg (mul_nonneg (Real.exp_pos (-u)).le hD) (sub_nonneg.mpr hpoly)]
  have hint : IntegrableOn (fun u : ℝ => Real.exp (-u) * ∫ t in 0..T*a*Real.sqrt u, f t)
      (Ioi 0) := by
    apply hg.mono' (endpoint_continuous hc T a).aestronglyMeasurable
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le
      (intervalIntegral.integral_nonneg (by positivity) (fun t _ => hp t)))]
    exact hmono u (le_of_lt hu)
  refine ⟨hint, (integral_mono_ae hint hg ?_).trans_eq ?_⟩
  · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with u hu
    exact hmono u (le_of_lt hu)
  · dsimp [g]
    rw [integral_const_mul, damped_add_cube.2]
    dsimp [D]
    ring

end RiemannResearch.Analysis.InghamMollifier
