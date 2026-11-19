/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualSquareRootPhaseGram
import RiemannResearch.Analysis.ActualGrowingPhaseGram

/-!
# Published discrete mean square and polynomial-dimensional phase bounds

Bui, Florea and Milinovich, *Negative discrete moments of the derivative of
the Riemann zeta-function*, Bull. London Math. Soc. 56 (2024), Theorem 3.1 and
its proof in §3, DOI 10.1112/blms.13092. The ordinary mean-square theorem
assumes RH. Its displayed off-diagonal sum with powers (m/n)^ρ and the
subsequent arithmetic estimates Σ₂–Σ₄ only use the unconditional Gonek
explicit formula (Lemma 3.2). Reflection pairs supply the conjugate
lower-triangular term for the centered Landau Gram in this repository.
Retaining the support logarithm in the displayed estimates gives d log d log(dT).
For Σ₂ use sqrt(log d) log log(3d) ≪ log d. For Σ₃ and Σ₄ their displayed bounds
are respectively d log²d and d log d log(2T), with d ≥ 2. The coefficient change a_n = √n v_n makes the diagonal norm exactly ‖v‖².

The reflected quadratic error is a scoped source input. The transfer to
the ordinary Gram uses RH explicitly.
-/

noncomputable section
open Filter Set Complex Zeta23
open scoped BigOperators Topology InnerProductSpace
namespace RiemannResearch.Analysis.ActualZeroPhaseMoments
open ActualZeroOrdinate HorizontalEuclideanMoments ContinuousLinearMap RiemannResearch.Fourier

/-- Source §3 upper-triangular error and its conjugate, normalized by all
positive-ordinate copies. The large-height domain excludes an empty normalizer. -/
def BuiFloreaMilinovichReflectedError : Prop :=
  ∃ A H : ℝ, 0 ≤ A ∧ 1 < H ∧ ∀ T ≥ H, 0 < Ncount 0 T → ∀ d : ℕ, 2 ≤ d →
    ∀ v : Space d, |(actualLandauResidual T d).reApplyInnerSelf v| ≤
      (A*(d:ℝ)*Real.log (d:ℝ)*Real.log ((d:ℝ)*T)/(Ncount 0 T : ℝ))*‖v‖^2

private theorem actualLandauResidual_isSelfAdjoint (T : ℝ) (d : ℕ) :
    IsSelfAdjoint (actualLandauResidual T d) := by
  let R := actualLandauResidual T d
  let M : Matrix (Fin d) (Fin d) ℂ := fun i j => euclideanEntry R i j
  have he : R = Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) M := by
    apply euclideanEntry_ext
    intro i j
    rw [euclideanEntry_toEuclideanCLM]
  have hm : star M = M := by
    ext i j
    exact (actualLandauResidual_entry_star T d i j).symm
  change star R = R
  rw [he,← map_star,hm]

/-- The paper's scalar quadratic error carries the same constant to the
full Hilbert operator, including arbitrary complex coefficient vectors. -/
theorem BuiFloreaMilinovichReflectedError.residual_refined (h : BuiFloreaMilinovichReflectedError) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ T : ℝ in atTop, ∀ d : ℕ, 2 ≤ d →
      ‖actualLandauResidual T d‖ ≤ A*(d:ℝ)*Real.log (d:ℝ)*Real.log ((d:ℝ)*T)/(Ncount 0 T : ℝ) := by
  obtain ⟨A,H,hA,hH,hh⟩ := h
  refine ⟨A,hA,?_⟩
  filter_upwards [eventually_ge_atTop H,eventually_count_pos] with T hT hN d hd
  have hT1 : 1 ≤ T := hH.le.trans hT
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (show 1≤d by omega)
  have hld := Real.log_nonneg hdR
  have hlt := Real.log_nonneg (one_le_mul_of_one_le_of_one_le hdR hT1)
  have hs := (actualLandauResidual_isSelfAdjoint T d).isSymmetric
  apply norm_le_of_abs_re_inner_le _ _ (by positivity) hs
  intro v
  have hv := hh T hT hN d hd v
  change |(inner ℂ (actualLandauResidual T d v) v).re| ≤ _ at hv
  have heq : inner ℂ (actualLandauResidual T d v) v = inner ℂ v (actualLandauResidual T d v) := hs v v
  rw [heq] at hv
  exact hv

/-- The theorem's squared-log error follows from the finer support-log estimate. -/
theorem BuiFloreaMilinovichReflectedError.residual (h : BuiFloreaMilinovichReflectedError) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ T : ℝ in atTop, ∀ d : ℕ, 2 ≤ d →
      ‖actualLandauResidual T d‖ ≤ A*(d:ℝ)*(Real.log ((d:ℝ)*T))^2/(Ncount 0 T : ℝ) := by
  obtain ⟨A,hA,h⟩ := h.residual_refined
  refine ⟨A,hA,?_⟩
  filter_upwards [h,eventually_gt_atTop (1:ℝ)] with T hh hT d hd
  have hdR : (1:ℝ)≤d := by exact_mod_cast (show 1≤d by omega)
  have hs : Real.log (d:ℝ) ≤ Real.log ((d:ℝ)*T) :=
    Real.log_le_log (zero_lt_one.trans_le hdR) (by nlinarith only [mul_le_mul_of_nonneg_left hT.le (Nat.cast_nonneg d)])
  have hlt := Real.log_nonneg (one_le_mul_of_one_le_of_one_le hdR hT.le)
  apply (hh d hd).trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  rw [sq,← mul_assoc]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (mul_nonneg hA (Nat.cast_nonneg _))) hlt

/-- Every fixed polynomial support below T is admitted for the reflected
residual, improving the power range in the in-tree contour estimate. -/
theorem BuiFloreaMilinovichReflectedError.eventually_residual_small (h : BuiFloreaMilinovichReflectedError)
    (b : ℝ) (hb : 0 ≤ b) (hb1 : b < 1) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ d : ℕ, 2 ≤ d → (d : ℝ) ≤ T^b → ‖actualLandauResidual T d‖ ≤ ε := by
  obtain ⟨A,hA,h⟩ := h.residual
  let q : ℝ := 1/(16*Real.pi)
  have hq : 0 < q := by dsimp [q]; positivity
  let C := A*(1+b)^2/q
  have hC : 0 ≤ C := by dsimp [C]; positivity
  filter_upwards [h,eventually_count_ge_log,eventually_rpow_le_log_neg (show b-1<0 by linarith only [hb1]) 2,
      Real.tendsto_log_atTop.eventually_ge_atTop (C/ε),eventually_gt_atTop (1:ℝ)]
      with T hbound hN hdec hlarge hT d hd hdT
  have hTp := zero_lt_one.trans hT
  have hL := Real.log_pos hT
  have hdR : (1:ℝ) ≤ d := by exact_mod_cast (show 1≤d by omega)
  have hdp := zero_lt_one.trans_le hdR
  have hld := Real.log_le_log hdp hdT
  rw [Real.log_rpow hTp] at hld
  have hlog : 0 ≤ Real.log ((d:ℝ)*T) := Real.log_nonneg (one_le_mul_of_one_le_of_one_le hdR hT.le)
  have hs : Real.log ((d:ℝ)*T) ≤ (1+b)*Real.log T := by
    rw [Real.log_mul hdp.ne' hTp.ne']; linarith only [hld]
  have hn : 0 < q*T*Real.log T := by positivity
  have hu := div_le_div₀ (show 0 ≤ A*T^b*((1+b)*Real.log T)^2 by positivity)
    (mul_le_mul (mul_le_mul_of_nonneg_left hdT hA) (pow_le_pow_left₀ hlog hs 2)
      (sq_nonneg _) (by positivity)) hn hN
  apply (hbound d hd).trans (hu.trans _)
  have he : A*T^b*((1+b)*Real.log T)^2/(q*T*Real.log T)=C*T^(b-1)*Real.log T := by
    dsimp [C]
    rw [Real.rpow_sub hTp,Real.rpow_one]; field_simp [hq.ne',hTp.ne',hL.ne']
  rw [he]
  rw [Real.rpow_neg hL.le,Real.rpow_ofNat] at hdec
  apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdec hC) hL.le).trans
  have hCe := (div_le_iff₀ hε).mp hlarge
  apply (show C*(Real.log T^2)⁻¹*Real.log T=C/Real.log T by field_simp [hL.ne']).le.trans
  exact (div_le_iff₀ hL).mpr (by linarith only [hCe])


/-- Near the support endpoint the residual vanishes whenever d log d = o(T).
The paper's retained support logarithm is enough for this uniform criterion. -/
theorem BuiFloreaMilinovichReflectedError.residual_tendsto_support_endpoint (h : BuiFloreaMilinovichReflectedError)
    (d : ℝ → ℕ) (hd : ∀ᶠ T : ℝ in atTop, 2 ≤ d T)
    (hs : Tendsto (fun T : ℝ => (d T:ℝ)*Real.log (d T:ℝ)/T) atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => ‖actualLandauResidual T (d T)‖) atTop (𝓝 0) := by
  obtain ⟨A,hA,hres⟩ := h.residual_refined
  let q : ℝ := 1/(16*Real.pi)
  have hq : 0 < q := by dsimp [q]; positivity
  have hu := hs.const_mul (2*A/q)
  simp only [mul_zero] at hu
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ hu
  filter_upwards [hd,hres,eventually_count_ge_log,hs.eventually (Iio_mem_nhds zero_lt_one),
      eventually_gt_atTop (Real.exp 1)] with T hdT hR hN hratio hT
  have hTp := (Real.exp_pos _).trans hT
  have hL : 1 < Real.log T := by simpa using Real.log_lt_log (Real.exp_pos _) hT
  have hLp := zero_lt_one.trans hL
  have hdR : (1:ℝ) ≤ d T := by exact_mod_cast (show 1 ≤ d T by omega)
  have hdp := zero_lt_one.trans_le hdR
  have hdlin : (d T:ℝ) ≤ T := by
    by_contra! hgt
    have hld := hL.trans (Real.log_lt_log hTp hgt)
    have hh := (div_lt_iff₀ hTp).mp hratio
    have hh' := mul_lt_mul_of_pos_left hld hdp
    linarith only [hgt,hh,hh']
  have hlog : Real.log ((d T:ℝ)*T) ≤ 2*Real.log T := by
    rw [Real.log_mul hdp.ne' hTp.ne']; linarith only [Real.log_le_log hdp hdlin]
  have hld := Real.log_nonneg hdR
  have hn : 0 < q*T*Real.log T := by positivity
  apply (hR (d T) hdT).trans
  apply (div_le_div₀ (show 0≤ A*(d T:ℝ)*Real.log (d T:ℝ)*(2*Real.log T) by positivity)
    (mul_le_mul_of_nonneg_left hlog (by positivity)) hn hN).trans_eq
  change A*(d T:ℝ)*Real.log (d T:ℝ)*(2*Real.log T)/(q*T*Real.log T)=2*A/q*((d T:ℝ)*Real.log (d T:ℝ)/T)
  field_simp [hq.ne',hTp.ne',hLp.ne']

/-- At exponent b < 1 the reflected Gram lies within b+ε of the identity.
The coefficient of b is the exact Riemann–von Mangoldt normalization. -/
theorem BuiFloreaMilinovichReflectedError.eventually_landau_norm (h : BuiFloreaMilinovichReflectedError)
    (b : ℝ) (hb : 0 ≤ b) (hb1 : b < 1) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ d : ℕ, 2 ≤ d → (d : ℝ) ≤ T^b → ‖landauGram T d - 1‖ ≤ b+ε := by
  let t := ε/(3*(1+b))
  let q := 1/(2*Real.pi*(1+t))
  let k := Real.log 4+4
  have ht : 0 < t := by dsimp [t]; positivity
  have hk : 0 ≤ k := by dsimp [k]; linarith only [Real.log_nonneg (by norm_num : (1:ℝ)≤4)]
  have hqpos : 0 < q := by dsimp [q]; positivity
  have hq : q < 1/(2*Real.pi) := by
    apply one_div_lt_one_div_of_lt (by positivity)
    nlinarith only [mul_pos (show 0 < 2*Real.pi by positivity) ht]
  have ht' : t*b ≤ ε/3 := by
    have h := mul_le_mul_of_nonneg_left (show b≤1+b by linarith) ht.le
    apply h.trans_eq; dsimp [t]; field_simp [show 1+b≠0 by positivity]
  filter_upwards [h.eventually_residual_small b hb hb1 (ε/3) (by positivity),eventually_count_ge_log_of_lt hq,
      Real.tendsto_log_atTop.eventually_ge_atTop (3*(1+t)*k/ε),eventually_gt_atTop (1:ℝ)]
      with T hR hN hLlarge hT d hd hdT
  have hTp := zero_lt_one.trans hT
  have hL := Real.log_pos hT
  have hn := (show 0 < q*T*Real.log T by positivity).trans_le hN
  let τ := T/(2*Real.pi*(Ncount 0 T : ℝ))
  have hτ : 0 ≤ τ := by dsimp [τ]; positivity
  have hτle : τ ≤ (1+t)/Real.log T := by
    apply (div_le_iff₀ (mul_pos (by positivity) hn)).mpr
    have h := mul_le_mul_of_nonneg_left hN (show 0 ≤ (1+t)/Real.log T*(2*Real.pi) by positivity)
    calc
      _ = ((1+t)/Real.log T*(2*Real.pi))*(q*T*Real.log T) := by
        dsimp [q]; field_simp [Real.pi_ne_zero,hL.ne',show 1+t≠0 by positivity]
      _ ≤ _ := by simpa only [mul_assoc] using h
  have hdp : 0 < (d:ℝ) := by exact_mod_cast (show 0<d by omega)
  have hdlog := Real.log_le_log hdp hdT
  rw [Real.log_rpow hTp] at hdlog
  have hP := (finPrimePowerMainOperator_norm_le d (by omega)).trans
    (show Real.log (d:ℝ)+Real.log 4+4 ≤ b*Real.log T+k by dsimp [k]; linarith only [hdlog])
  have herr : (1+t)/Real.log T*(b*Real.log T+k) ≤ b+2*ε/3 := by
    have he : (1+t)/Real.log T*(b*Real.log T+k)=b+t*b+((1+t)*k)/Real.log T := by
      field_simp [hL.ne']
    have hsmall : (1+t)*k/Real.log T ≤ ε/3 := (div_le_iff₀ hL).mpr (by
      have hh := (div_le_iff₀ hε).mp hLlarge
      linarith only [hh])
    rw [he]; linarith only [ht',hsmall]
  have hm : ‖τ • finPrimePowerMainOperator d‖ ≤ b+2*ε/3 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hτ]
    exact (mul_le_mul hτle hP (norm_nonneg _) (by positivity)).trans herr
  have he : landauGram T d-1=actualLandauResidual T d-τ • finPrimePowerMainOperator d := by
    dsimp [actualLandauResidual,τ]; abel
  rw [he]
  exact (norm_sub_le _ _).trans ((add_le_add (hR d hd hdT) hm).trans_eq (by ring))

theorem landauGram_eq_phaseGram_of_RH (hRH : RiemannHypothesis) (T : ℝ) (d : ℕ) :
    landauGram T d = phaseGram T d := by
  apply sub_eq_zero.mp
  rw [landauGram_sub_phaseGram_eq_full_copy_sum]
  have h (c : Copies T) : copyCoshCorrection d c.1.1=0 := by
    have hz := Zeta23.RH_implies_on_line hRH (mem_cutoff.mp c.1.2).1
    apply euclideanEntry_ext
    intro n m
    rw [copyCoshCorrection_entry,hz]
    simp [euclideanEntry]
  simp only [h,Finset.sum_const_zero,smul_zero]

theorem BuiFloreaMilinovichReflectedError.eventually_phase_frame_RH (h : BuiFloreaMilinovichReflectedError)
    (hRH : RiemannHypothesis) (b : ℝ) (hb : 0 ≤ b) (hb1 : b < 1) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ d : ℕ, 2 ≤ d → (d : ℝ) ≤ T^b →
      ‖phaseGram T d-1‖ ≤ b+ε ∧ ∀ v : Space d,
        (1-b-ε)*‖v‖^2 ≤ (phaseGram T d).reApplyInnerSelf v := by
  filter_upwards [h.eventually_landau_norm b hb hb1 ε hε] with T hT d hd hdT
  have hg := hT d hd hdT
  rw [landauGram_eq_phaseGram_of_RH hRH] at hg
  refine ⟨hg,fun v => ?_⟩
  have he := qform_le_norm (1-phaseGram T d) v
  rw [qform_sub,qform_one,norm_sub_rev] at he
  have hq := he.trans (mul_le_mul_of_nonneg_right hg (sq_nonneg ‖v‖))
  linarith only [hq]



/-- Eventual invertibility of the reflected operator throughout b < 1. -/
theorem BuiFloreaMilinovichReflectedError.eventually_landau_isUnit (h : BuiFloreaMilinovichReflectedError)
    (b : ℝ) (hb : 0 ≤ b) (hb1 : b < 1) :
    ∀ᶠ T : ℝ in atTop, ∀ d : ℕ, 2 ≤ d → (d : ℝ) ≤ T^b → IsUnit (landauGram T d) := by
  filter_upwards [h.eventually_landau_norm b hb hb1 ((1-b)/2) (by linarith only [hb1])] with T hT d hd hdT
  have hs : ‖1-landauGram T d‖ < 1 := by
    rw [norm_sub_rev]
    exact (hT d hd hdT).trans_lt (by linarith only [hb1])
  simpa only [sub_sub_cancel] using isUnit_one_sub_of_norm_lt_one hs

theorem BuiFloreaMilinovichReflectedError.eventually_phase_isUnit_RH (h : BuiFloreaMilinovichReflectedError)
    (hRH : RiemannHypothesis) (b : ℝ) (hb : 0 ≤ b) (hb1 : b < 1) :
    ∀ᶠ T : ℝ in atTop, ∀ d : ℕ, 2 ≤ d → (d : ℝ) ≤ T^b → IsUnit (phaseGram T d) := by
  simpa only [landauGram_eq_phaseGram_of_RH hRH] using h.eventually_landau_isUnit b hb hb1

/-- Subpolynomial support gives norm convergence of the reflected operator.
Under RH the same convergence holds for the ordinary phase Gram. -/
theorem BuiFloreaMilinovichReflectedError.landau_tendsto_subpolynomial (h : BuiFloreaMilinovichReflectedError)
    (d : ℝ → ℕ) (hd : ∀ᶠ T : ℝ in atTop, 2 ≤ d T)
    (hs : Tendsto (fun T : ℝ => Real.log (d T : ℝ)/Real.log T) atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => ‖landauGram T (d T)-1‖) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let b := min (ε/3) (1/2)
  have hb : 0 < b := lt_min (by positivity) (by norm_num)
  have hb1 : b < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hh : ∀ᶠ T : ℝ in atTop, ‖landauGram T (d T)-1‖ < ε := by
    filter_upwards [h.eventually_landau_norm b hb.le hb1 (ε/3) (by positivity),
        hd,hs.eventually (Iio_mem_nhds hb),eventually_gt_atTop (1:ℝ)] with T hT hdT hlog h₁
    have hTp := zero_lt_one.trans h₁
    have hdp : 0 < (d T:ℝ) := by exact_mod_cast (show 0<d T by omega)
    have hlog' := (div_lt_iff₀ (Real.log_pos h₁)).mp hlog
    have hd' : (d T:ℝ) ≤ T^b := by
      rw [← Real.exp_log hdp,Real.rpow_def_of_pos hTp,mul_comm]
      exact Real.exp_le_exp.mpr hlog'.le
    exact (hT _ hdT hd').trans_lt (by linarith only [min_le_left (ε/3) (1/2:ℝ),hε])
  obtain ⟨H,hH⟩ := eventually_atTop.mp hh
  exact ⟨H,fun T hT => by simpa only [Real.dist_eq,sub_zero,abs_of_nonneg (norm_nonneg _)] using hH T hT⟩

theorem BuiFloreaMilinovichReflectedError.phase_tendsto_subpolynomial_RH (h : BuiFloreaMilinovichReflectedError)
    (hRH : RiemannHypothesis) (d : ℝ → ℕ) (hd : ∀ᶠ T : ℝ in atTop, 2 ≤ d T)
    (hs : Tendsto (fun T : ℝ => Real.log (d T : ℝ)/Real.log T) atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => ‖phaseGram T (d T)-1‖) atTop (𝓝 0) := by
  simpa only [landauGram_eq_phaseGram_of_RH hRH] using h.landau_tendsto_subpolynomial d hd hs

end RiemannResearch.Analysis.ActualZeroPhaseMoments
