/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualDensityHarmonicOperator
import RiemannResearch.Analysis.ActualSelbergDensityInterpolation
import RiemannResearch.Analysis.ActualZeroPhaseBootstrap
import RiemannResearch.Analysis.ActualPhaseGramExpansion
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Actual ordinate phase Gram on square-root logarithmic supports

The kernel-checked Ingham tangent has slope 4/3 and two surplus logarithms
after count normalization. For displacement k/√log T and log d ≤ c√log T
the bad operator tends to zero as soon as c < 4k/3. The Landau residual
and the prime-power arithmetic main also tend to zero. The existing finite
bootstrap therefore gives invertibility for cosh(3c²/4) < 2, and the norm
of the entire phase Gram minus the identity tends to zero when
log d = o(√log T). All zero counts carry the original multiplicities.
-/

noncomputable section
open Filter Complex Set Zeta23
open scoped BigOperators InnerProductSpace

namespace RiemannResearch.Analysis.ActualZeroPhaseMoments
open ActualZeroOrdinate HorizontalEuclideanMoments HorizontalPhaseBootstrap
open ZeroOrdinate ContinuousLinearMap FiniteHyperbolicHarmonicCap RiemannResearch.Fourier

theorem finPrimePowerMainOperator_norm_le (d : ℕ) (hd : 1 ≤ d) :
    ‖finPrimePowerMainOperator d‖ ≤ Real.log (d : ℝ) + Real.log 4 + 4 := by
  let M : Matrix (Fin d) (Fin d) ℂ := fun n m =>
    (primePowerCovarianceSymmetricEntry (n.val+1) (m.val+1) : ℂ)
  have hM : star M = M := by
    ext n m
    change star ((primePowerCovarianceSymmetricEntry (m.val+1) (n.val+1) : ℝ) : ℂ) =
      ((primePowerCovarianceSymmetricEntry (n.val+1) (m.val+1) : ℝ) : ℂ)
    rw [Complex.star_def, Complex.conj_ofReal,
      primePowerCovarianceSymmetricEntry_symm _ _ (by omega) (by omega)]
  have hsa : IsSelfAdjoint (finPrimePowerMainOperator d) := by
    change star (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) M) = Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) M
    rw [← map_star, hM]
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hC : 0 ≤ Real.log (d : ℝ) + Real.log 4 + 4 := by
    linarith only [Real.log_nonneg hdR, Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]
  apply norm_le_of_abs_re_inner_le _ _ hC hsa.isSymmetric
  intro f
  exact (Complex.abs_re_le_norm _).trans (finPrimePowerMainOperator_inner_norm_le d f)

private theorem sqrtLog_tendsto :
    Tendsto (fun T : ℝ => Real.sqrt (Real.log T)) atTop atTop :=
  Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop

theorem landauGram_sub_one_tendsto_sqrt_log (d : ℝ → ℕ) {c : ℝ} (hc : 0 ≤ c)
    (hs : ∀ᶠ T : ℝ in atTop, 1 ≤ d T ∧ Real.log (d T : ℝ) ≤ c * Real.sqrt (Real.log T)) :
    Tendsto (fun T : ℝ => ‖landauGram T (d T) - 1‖) atTop (nhds 0) := by
  let P := fun T : ℝ => finPrimePowerMainOperator (d T)
  let τ := fun T : ℝ => T / ((2*Real.pi) * (Ncount 0 T : ℝ))
  let k := Real.log 4 + 4
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hR := actualLandauResidual_norm_tendsto_zero_sqrt_support d c (by
    filter_upwards [hs, eventually_gt_atTop (0 : ℝ)] with T hT hTp
    exact ⟨hT.1, hT.2.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
      (Real.log_le_log hTp (by linarith))) hc)⟩)
  have hmaj : Tendsto (fun T : ℝ => 8 * (c / Real.sqrt (Real.log T) + k / Real.log T)) atTop (nhds 0) := by
    have h := ((sqrtLog_tendsto.const_div_atTop c).add (Real.tendsto_log_atTop.const_div_atTop k)).const_mul 8
    simpa only [add_zero, mul_zero] using h
  have hmain : Tendsto (fun T => ‖τ T • P T‖) atTop (nhds 0) := by
    apply squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _) _ hmaj
    filter_upwards [hs, eventually_count_ge_log, eventually_gt_atTop (1 : ℝ)] with T hsT hN hT
    have hTp := zero_lt_one.trans hT
    have hL := Real.log_pos hT
    have hR := Real.sqrt_pos.2 hL
    have hτ : 0 ≤ τ T := by dsimp [τ]; positivity
    have hτle : τ T ≤ 8 / Real.log T := by
      have hn := (show 0 < (1/(16*Real.pi))*T*Real.log T by positivity).trans_le hN
      dsimp [τ]
      apply (div_le_iff₀ (mul_pos (by positivity) hn)).mpr
      have h := mul_le_mul_of_nonneg_left hN (show 0 ≤ (8 / Real.log T) * (2 * Real.pi) by positivity)
      calc
        _ = ((8 / Real.log T) * (2 * Real.pi)) * ((1/(16*Real.pi))*T*Real.log T) := by field_simp [Real.pi_ne_zero,hL.ne']; ring
        _ ≤ _ := by simpa only [mul_assoc] using h
    have hP : ‖P T‖ ≤ c * Real.sqrt (Real.log T) + k :=
      (finPrimePowerMainOperator_norm_le _ hsT.1).trans (by dsimp [k]; linarith only [hsT.2])
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ]
    apply (mul_le_mul hτle hP (norm_nonneg _) (by positivity)).trans_eq
    field_simp [hL.ne',hR.ne']
    nlinarith only [congrArg (fun x : ℝ => c*x) (Real.sq_sqrt hL.le)]
  have h := hR.add hmain
  simp only [add_zero] at h
  apply squeeze_zero (fun _ => norm_nonneg _) _ h
  intro T
  have he : landauGram T (d T) - 1 = actualLandauResidual T (d T) - τ T • P T := by
    dsimp [actualLandauResidual,τ,P]; abel
  rw [he]
  exact norm_sub_le _ _

private theorem normalized_ingham_tangent_tail :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ T : ℝ in atTop, ∀ δ ∈ Icc (0 : ℝ) (1/2),
      strictTail T δ / (Ncount 0 T : ℝ) ≤ A * (Real.log T)^2 * Real.exp (-(4/3*Real.log T)*δ) := by
  obtain ⟨C,H,hC,hH,h⟩ := ingham_tangent_density_log_loss
  let k : ℝ := 1/(16*Real.pi)
  have hk : 0 < k := by dsimp [k]; positivity
  refine ⟨2*C/k, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop H, eventually_count_ge_log] with T hT hN
  have hTp := zero_lt_one.trans (hH.trans_le hT)
  have hL := Real.log_pos (hH.trans_le hT)
  intro δ hδ
  have hct := h T hT (1/2+δ) ⟨by linarith only [hδ.1], by linarith only [hδ.2]⟩
  rw [show 1/2+δ-1/2=δ by ring] at hct
  norm_num only [Real.rpow_ofNat] at hct
  have hn := (show 0 < k*T*Real.log T by positivity).trans_le hN
  apply (div_le_iff₀ hn).mpr
  apply (strictTail_le_twice_inclusive T δ hδ.1).trans
  apply (mul_le_mul_of_nonneg_left hct (by norm_num : (0 : ℝ) ≤ 2)).trans
  have heq : 2*(C*T*Real.log T^3*Real.exp (-(4/3*Real.log T)*δ)) =
      (2*C/k*Real.log T^2*Real.exp (-(4/3*Real.log T)*δ))*(k*T*Real.log T) := by field_simp [hk.ne']
  rw [heq]
  exact mul_le_mul_of_nonneg_left hN (by positivity)

/-- A fixed strict margin at the square-root scale absorbs the two
normalized Ingham logarithms and the harmonic cap uniformly. -/
theorem badCorrection_tendsto_zero_sqrt_mask (d : ℝ → ℕ) {c k : ℝ} (hc : 0 ≤ c)
    (hck : c < 4*k/3)
    (hs : ∀ᶠ T : ℝ in atTop, 1 ≤ d T ∧ Real.log (d T : ℝ) ≤ c * Real.sqrt (Real.log T)) :
    Tendsto (fun T : ℝ => ‖badCorrection T (d T) (k / Real.sqrt (Real.log T))‖) atTop (nhds 0) := by
  obtain ⟨A,hA,h⟩ := normalized_ingham_tangent_tail
  let m := 4*k/3-c
  have hm : 0 < m := sub_pos.mpr hck
  have hk : 0 < k := by linarith only [hc,hck]
  have hh4 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 4 m hm).comp sqrtLog_tendsto
  have hh5 := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 5 m hm).comp sqrtLog_tendsto).const_mul c
  have hh := (hh4.add hh5).const_mul A
  simp only [add_zero, mul_zero, Function.comp_apply, Real.rpow_ofNat] at hh
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ hh
  filter_upwards [hs,h,sqrtLog_tendsto.eventually_ge_atTop (2*k),eventually_gt_atTop (1 : ℝ)] with T hsT hT hR hTp
  let L := Real.log T
  let R := Real.sqrt L
  let δ := k/R
  have hLp : 0 < L := Real.log_pos hTp
  have hRp : 0 < R := Real.sqrt_pos.2 hLp
  have hRs : R^2=L := Real.sq_sqrt hLp.le
  have hδ : δ ∈ Icc (0 : ℝ) (1/2) :=
    ⟨(div_pos hk hRp).le, (div_le_iff₀ hRp).mpr (by linarith only [hR])⟩
  have hdR : (1 : ℝ) ≤ d T := by exact_mod_cast hsT.1
  have hd : (d T : ℝ) ≤ Real.exp (c*R) := by
    rw [← Real.exp_log (zero_lt_one.trans_le hdR)]
    exact Real.exp_le_exp.mpr hsT.2
  have hcap : harmonicHyperbolicCap (d T) ≤ Real.exp (c*R)*(1+c*R) :=
    (harmonicHyperbolicCap_le_card_log _ hsT.1).trans (mul_le_mul hd (by dsimp [R,L]; linarith only [hsT.2])
      (by linarith only [Real.log_nonneg hdR]) (Real.exp_pos _).le)
  have heq : -(4/3*L)*δ = -(4*k/3)*R := by dsimp [δ]; field_simp [hRp.ne']; nlinarith only [hRs, congrArg (fun x : ℝ => k*x) hRs]
  have hfrac := hT δ hδ
  change _ ≤ A*L^2*Real.exp (-(4/3*L)*δ) at hfrac
  rw [heq] at hfrac
  apply (badCorrection_norm_le_harmonic T (d T) δ).trans
  apply (mul_le_mul hfrac hcap (harmonicHyperbolicCap_nonneg _) (by positivity)).trans_eq
  change A*L^2*Real.exp (-(4*k/3)*R)*(Real.exp (c*R)*(1+c*R)) =
    A*(R^4*Real.exp (-m*R) + c*(R^5*Real.exp (-m*R)))
  rw [show Real.exp (-m*R) = Real.exp (-(4*k/3)*R)*Real.exp (c*R) by
    rw [← Real.exp_add]; congr 1; dsimp [m]; ring, ← hRs]
  ring

/-- Strictly inside the optimized square-root support the actual Gram
is eventually invertible, with no density axiom beyond Lean's kernel. -/
theorem eventually_phaseGram_isUnit_of_ingham_sqrt (d : ℝ → ℕ) {c : ℝ} (hc : 0 ≤ c)
    (hsmall : Real.cosh (3*c^2/4) < 2)
    (hs : ∀ᶠ T : ℝ in atTop, 1 ≤ d T ∧ Real.log (d T : ℝ) ≤ c * Real.sqrt (Real.log T)) :
    ∀ᶠ T : ℝ in atTop, IsUnit (phaseGram T (d T)) := by
  let k₀ := 3*c/4
  have hop : IsOpen {k : ℝ | Real.cosh (k*c) < 2} := isOpen_lt (by fun_prop) continuous_const
  have hmem : k₀ ∈ {k : ℝ | Real.cosh (k*c) < 2} := by
    change Real.cosh (k₀*c) < 2
    rwa [show k₀*c = 3*c^2/4 by dsimp [k₀]; ring]
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hop k₀ hmem
  let k := k₀+ε/2
  have hkm : k ∈ Metric.ball k₀ ε := by
    rw [Metric.mem_ball, Real.dist_eq, show k-k₀ = ε/2 by dsimp [k]; ring, abs_of_pos (by linarith)]
    linarith only [hε]
  have hkc : Real.cosh (k*c) < 2 := hball hkm
  have hck : c < 4*k/3 := by dsimp [k,k₀]; linarith only [hε]
  have hk : 0 < k := by linarith only [hc,hck]
  have hlim := (landauGram_sub_one_tendsto_sqrt_log d hc hs).add (badCorrection_tendsto_zero_sqrt_mask d hc hck hs)
  simp only [add_zero] at hlim
  filter_upwards [hs,hlim.eventually (Iio_mem_nhds (sub_pos.mpr hkc)),eventually_gt_atTop (1 : ℝ)]
    with T hsT hsm hT
  let R := Real.sqrt (Real.log T)
  let δ := k/R
  have hRp : 0 < R := Real.sqrt_pos.2 (Real.log_pos hT)
  have hδ : 0 ≤ δ := (div_pos hk hRp).le
  have hdR : (1 : ℝ) ≤ d T := by exact_mod_cast hsT.1
  have hz : δ*Real.log (d T : ℝ) ≤ k*c := by
    have h := mul_le_mul_of_nonneg_left hsT.2 hδ
    exact h.trans_eq (by dsimp [δ]; field_simp [hRp.ne']; dsimp [R]; ring)
  have hcos := Real.cosh_le_cosh.mpr
    (show |δ*Real.log (d T : ℝ)| ≤ |k*c| by rwa [abs_of_nonneg (mul_nonneg hδ (Real.log_nonneg hdR)),
        abs_of_nonneg (mul_nonneg hk.le hc)])
  apply phaseGram_isUnit T (d T) hsT.1 δ hδ _ _ le_rfl le_rfl
  linarith only [hsm,hcos]

/-- The whole operator, not just its entries, converges to the identity
on every sequence of dimensions with log d = o(√log T). -/
theorem phaseGram_sub_one_tendsto_of_subsqrt (d : ℝ → ℕ) (hd : ∀ᶠ T : ℝ in atTop, 1 ≤ d T)
    (hs : Tendsto (fun T : ℝ => Real.log (d T : ℝ)/Real.sqrt (Real.log T)) atTop (nhds 0)) :
    Tendsto (fun T : ℝ => ‖phaseGram T (d T) - 1‖) atTop (nhds 0) := by
  have hsupport : ∀ᶠ T : ℝ in atTop, 1 ≤ d T ∧ Real.log (d T : ℝ) ≤ 1 * Real.sqrt (Real.log T) := by
    filter_upwards [hd,hs.eventually (Iio_mem_nhds zero_lt_one),eventually_gt_atTop (1 : ℝ)]
      with T hdT hratio hT
    exact ⟨hdT,(div_lt_iff₀ (Real.sqrt_pos.2 (Real.log_pos hT))).mp hratio |>.le⟩
  let δ := fun T : ℝ => 1/Real.sqrt (Real.log T)
  let w := fun T : ℝ => (Real.cosh (δ T*Real.log (d T : ℝ))-1)/2
  have harg : Tendsto (fun T : ℝ => δ T*Real.log (d T : ℝ)) atTop (nhds 0) := by
    simpa only [δ,div_eq_mul_inv,one_mul,mul_comm] using hs
  have hw : Tendsto w atTop (nhds 0) := by
    have h := ((Real.continuous_cosh.tendsto 0).comp harg).sub (tendsto_const_nhds (x := (1 : ℝ)))
    simpa only [w,Real.cosh_zero,sub_self,zero_div,Function.comp_apply] using h.div_const 2
  have hland := landauGram_sub_one_tendsto_sqrt_log d zero_le_one hsupport
  have hbad := badCorrection_tendsto_zero_sqrt_mask d (k := 1) zero_le_one (by norm_num) hsupport
  have hmaj := ((hland.add hbad).add hw).div ((tendsto_const_nhds (x := (1 : ℝ))).sub hw) (by norm_num)
  simp only [add_zero,sub_zero,zero_div] at hmaj
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ hmaj
  filter_upwards [hd,hw.eventually (Iio_mem_nhds zero_lt_one)] with T hdT hε
  exact phaseGram_norm_sub_one_le T (d T) hdT (δ T) (by dsimp [δ]; positivity) _ _ le_rfl le_rfl hε

end RiemannResearch.Analysis.ActualZeroPhaseMoments
