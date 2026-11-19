/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.ActualZeroDisplacementMoments
import RiemannResearch.Analysis.ActualZeroInghamHorizontalEnergy

/-! # Square-root-width frequency shifts at the Ingham tangent

The nonlinear exponent in Chourasiya–Simonič's Ingham estimate has a quadratic
gain of at least (8/9)δ² over its central tangent. Completing the square
retains an adjustable slope shift on the scale √log T. Integer exponential
moments inherit the gain through the finite actual-zero tail.
-/

noncomputable section
open Set Filter Zeta23
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.ActualZeroOrdinate

/-- The reflected nonlinear Ingham curve has a quadratic gain throughout
the entire horizontal displacement interval. -/
theorem exists_strictTail_ingham_quadratic :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, max 2 (Real.exp 1) ≤ T →
      ∀ t ∈ Icc (0 : ℝ) (1/2), strictTail T t ≤ C*T*(Real.log T)^3 *
        Real.exp (-(Real.log T)*((4/3)*t+(8/9)*t^2)) := by
  obtain ⟨D,hD,hd⟩ := exists_ingham_littlewood_density_all_heights
  refine ⟨2*D,by positivity,?_⟩
  intro T hT t ht
  have hT₂ := (le_max_left (2 : ℝ) (Real.exp 1)).trans hT
  have hT₀ : 0 < T := by linarith
  have hL : 1 ≤ Real.log T := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) ((le_max_right _ _).trans hT)
  let σ := 1/2+t
  let q := 3*(1-σ)/(2-σ)
  let Δ := (4/3)*t+(8/9)*t^2
  have hσ : σ ∈ Icc (1/2 : ℝ) 1 := ⟨by dsimp [σ]; linarith [ht.1],by dsimp [σ]; linarith [ht.2]⟩
  have hΔ : 0 ≤ Δ := by dsimp [Δ]; have := ht.1; positivity
  have hq : q ≤ 1-Δ := by
    apply (div_le_iff₀ (by linarith [hσ.2] : 0 < 2-σ)).mpr
    dsimp [σ,Δ]
    nlinarith only [pow_nonneg ht.1 3]
  have hTq : T^q ≤ T*Real.exp (-(Real.log T)*Δ) := by
    calc
      _ ≤ T^(1-Δ) := Real.rpow_le_rpow_of_exponent_le (by linarith [hT₂]) hq
      _ = _ := by rw [Real.rpow_def_of_pos hT₀,show Real.log T*(1-Δ) =
        Real.log T + -(Real.log T)*Δ by ring, Real.exp_add, Real.exp_log hT₀]
  have hLq : (Real.log T)^(2+q) ≤ (Real.log T)^(3 : ℕ) := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hL
    norm_num
    linarith only [hq,hΔ]
  have h := hd T hT₂ σ hσ
  change rightInclusiveCount T σ ≤ D * min (T*Real.log T) (T^q*(Real.log T)^(2+q)) at h
  calc
    _ ≤ 2*rightInclusiveCount T σ := strictTail_le_twice_inclusive T t ht.1
    _ ≤ 2*(D*(T^q*(Real.log T)^(2+q))) :=
      mul_le_mul_of_nonneg_left (h.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hD.le)) (by norm_num)
    _ ≤ 2*(D*((T*Real.exp (-(Real.log T)*Δ))*(Real.log T)^3)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (mul_le_mul hTq hLq (Real.rpow_nonneg (by linarith) _) (by positivity)) hD.le) (by norm_num)
    _ = _ := by dsimp [Δ]; ring

/-- An adjustable square-root-width slope gain has a uniform exponential
price exp(9s²/32). The inequality applies in every positive integer order. -/
theorem exists_ingham_tilted_moment_sqrt_window :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, max 2 (Real.exp 1) ≤ T →
      ∀ s : ℝ, ∀ p : ℕ, ∀ v : ℝ, 0 ≤ v →
      let L := Real.log T
      let q := (4/3)*L + s*Real.sqrt L
      v < q →
      (∑ i : Copies T, copyDisplacement T i^(p+1) * Real.exp (v*copyDisplacement T i)) / T ≤
        C * Real.exp (9*s^2/32) * L^3 * (((p+1).factorial : ℝ)*q/(q-v)^(p+2)) := by
  obtain ⟨C,hC,h⟩ := exists_strictTail_ingham_quadratic
  refine ⟨C,hC,?_⟩
  intro T hT s p v hv L q hvq
  have ht1 : 1 < T := by linarith [(le_max_left (2:ℝ) (Real.exp 1)).trans hT]
  have ht0 := zero_lt_one.trans ht1
  have hL : 0 < L := Real.log_pos ht1
  have htail (t : ℝ) (ht : t ∈ Icc (0:ℝ) (1/2)) :
      strictTail T t ≤ C*Real.exp (9*s^2/32)*T*L^3*Real.exp (-q*t) := by
    apply (h T hT t ht).trans
    have hsq : (Real.sqrt L*t)^2 = L*t^2 := by rw [mul_pow,Real.sq_sqrt hL.le]
    have harg : -L*((4/3)*t+(8/9)*t^2) ≤ 9*s^2/32 + (-q*t) := by
      dsimp [q]
      nlinarith only [sq_nonneg (Real.sqrt L*t-9*s/16),hsq]
    have he := Real.exp_le_exp.mpr harg
    rw [Real.exp_add] at he
    change C*T*L^3*Real.exp (-L*((4/3)*t+(8/9)*t^2)) ≤ _
    apply (mul_le_mul_of_nonneg_left he (show 0 ≤ C*T*L^3 by positivity)).trans_eq
    ring
  have hh := tiltedMoment_le_expTail p (show 0 ≤ C*Real.exp (9*s^2/32)*T*L^3 by positivity)
    hv hvq htail
  apply (div_le_iff₀ ht0).mpr
  apply hh.trans_eq
  ring

/-- The same height threshold works for every order in the square-root
window with fixed upper shift r. The factorial contains all order dependence. -/
theorem exists_critical_tilt_scaled_moments (r : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop, ∀ p : ℕ, ∀ v : ℝ,
      0 ≤ v → v ≤ (4/3)*Real.log T + r*Real.sqrt (Real.log T) →
      let L := Real.log T
      (Real.sqrt L)^(p+2) * ((∑ i : Copies T, copyDisplacement T i^(p+1) *
        Real.exp (v*copyDisplacement T i)) / T) ≤
        K * L^4 * ((p+1).factorial : ℝ) := by
  obtain ⟨C,hC,h⟩ := exists_ingham_tilted_moment_sqrt_window
  let s := |r|+1
  let K := C*Real.exp (9*s^2/32)*(4/3+s)
  have hs : 0 < s := by dsimp [s]; positivity
  have hrs : r+1 ≤ s := by dsimp [s]; linarith [le_abs_self r]
  refine ⟨K,by dsimp [K]; positivity,?_⟩
  filter_upwards [eventually_ge_atTop (max 2 (Real.exp 1))] with T ht
  intro p v hv hwidth
  let L := Real.log T
  let R := Real.sqrt L
  let q := (4/3)*L+s*R
  have ht0 : 0 < T := by linarith [(le_max_left (2:ℝ) (Real.exp 1)).trans ht]
  have hL1 : 1 ≤ L := by
    simpa only [L,Real.log_exp] using Real.log_le_log (Real.exp_pos 1) ((le_max_right _ _).trans ht)
  have hL := zero_lt_one.trans_le hL1
  have hR : 0 < R := Real.sqrt_pos.mpr hL
  have hRsq : R^2=L := Real.sq_sqrt hL.le
  have hRle : R ≤ L := by
    by_contra! hh
    nlinarith only [hRsq,hL1,hh,mul_pos (show 0<R-1 by linarith) hR]
  have hgap : R ≤ q-v := by
    change v ≤ (4/3)*L+r*R at hwidth
    dsimp only [q]
    nlinarith only [hwidth,mul_le_mul_of_nonneg_right hrs hR.le]
  have hvq : v < q := by linarith [hgap,hR]
  have hq : q ≤ (4/3+s)*L := by
    dsimp only [q]
    nlinarith only [mul_le_mul_of_nonneg_left hRle hs.le]
  have hh := h T ht s p v hv hvq
  have hq0 : 0 ≤ q := hv.trans hvq.le
  have hP : R^(p+2) ≤ (q-v)^(p+2) := pow_le_pow_left₀ hR.le hgap _
  let S := (∑ i : Copies T, copyDisplacement T i^(p+1) * Real.exp (v*copyDisplacement T i))/T
  have hS : 0 ≤ S := div_nonneg (Finset.sum_nonneg fun i _ =>
    mul_nonneg (pow_nonneg (abs_nonneg _) _) (Real.exp_pos _).le) ht0.le
  change S ≤ C*Real.exp (9*s^2/32)*L^3*(((p+1).factorial : ℝ)*q/(q-v)^(p+2)) at hh
  have hm : (q-v)^(p+2)*S ≤ (C*Real.exp (9*s^2/32)*L^3)*(((p+1).factorial : ℝ)*q) := by
    rw [← mul_div_assoc] at hh
    have hstep := (le_div_iff₀ (pow_pos (sub_pos.mpr hvq) _)).mp hh
    simpa only [mul_comm] using hstep
  change R^(p+2)*S ≤ K*L^4*((p+1).factorial : ℝ)
  apply ((mul_le_mul_of_nonneg_right hP hS).trans hm).trans
  apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg _))
    (show 0 ≤ C*Real.exp (9*s^2/32)*L^3 by positivity)).trans_eq
  dsimp only [K]
  ring

/-- Above order seven the critical tilted moment divided by height tends to
zero, even when the tilt exceeds the Ingham tangent by a fixed square-root shift. -/
theorem tendsto_tilted_moment_at_ingham_tangent (p : ℕ) (hp : 7 ≤ p) (v : ℝ → ℝ) (r : ℝ)
    (hv : ∀ᶠ T : ℝ in atTop, 0 ≤ v T ∧ v T ≤ (4/3)*Real.log T + r*Real.sqrt (Real.log T)) :
    Tendsto (fun T : ℝ => (∑ i : Copies T, copyDisplacement T i^(p+1) *
      Real.exp (v T*copyDisplacement T i)) / T) atTop (𝓝 0) := by
  obtain ⟨K,hK,hh⟩ := exists_critical_tilt_scaled_moments r
  let A := K*((p+1).factorial : ℝ)
  have hR := Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  have hz := hR.const_div_atTop A
  apply squeeze_zero' _ _ hz
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with T ht
    exact div_nonneg (Finset.sum_nonneg fun i _ =>
      mul_nonneg (pow_nonneg (abs_nonneg _) _) (Real.exp_pos _).le) ht.le
  · filter_upwards [hh,hv,hR.eventually_ge_atTop 1,eventually_gt_atTop (1:ℝ)] with T h hv hR1 ht
    let L := Real.log T
    let R := Real.sqrt L
    let S := (∑ i : Copies T, copyDisplacement T i^(p+1) * Real.exp (v T*copyDisplacement T i))/T
    change 1 ≤ R at hR1
    have hRp := zero_lt_one.trans_le hR1
    have hL := Real.log_pos ht
    have hRsq : R^2=L := Real.sq_sqrt hL.le
    have hs := h p (v T) hv.1 hv.2
    change R^(p+2)*S ≤ K*L^4*((p+1).factorial : ℝ) at hs
    have hP : R^9 ≤ R^(p+2) := pow_le_pow_right₀ hR1 (by omega)
    have hS : 0 ≤ S := div_nonneg (Finset.sum_nonneg fun i _ =>
      mul_nonneg (pow_nonneg (abs_nonneg _) _) (Real.exp_pos _).le) (zero_lt_one.trans ht).le
    have hm := (mul_le_mul_of_nonneg_right hP hS).trans hs
    change S ≤ A/R
    apply (le_div_iff₀ hRp).mpr
    have hmul : (S*R)*R^8 ≤ A*R^8 := by
      rw [← hRsq] at hm
      dsimp only [A]
      nlinarith only [hm]
    exact le_of_mul_le_mul_right hmul (pow_pos hRp 8)

end RiemannResearch.Analysis.ActualZeroOrdinate
