/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualHyperbolicDensityBudget
import RiemannResearch.Analysis.ActualZeroDensityWindow
import RiemannResearch.Analysis.ActualZeroDensityCutoff

/-!
# One-point strict-tail transfer to the complete signed harmonic budget

The counting, reflection, cutoff, finite-height remainder and operator steps
are proved here or in the imported modules. The only unresolved analytic
input is the explicit one-point actual count-difference hypothesis.
The power-shaped consumer adapts the statement of Chourasiya--Simonic,
arXiv:2507.15184v2, Theorem 1, not its analytic proof:
https://arxiv.org/html/2507.15184v2.
No source theorem is turned into an axiom. All signed channels, analytic
multiplicities, composite coordinates and the full N(T) normalization survive
through the original actual operators.
-/

noncomputable section
open Filter
set_option maxHeartbeats 800000

namespace RiemannResearch.Analysis.ActualZeroPhaseMoments
open ActualZeroOrdinate Zeta23 ZeroDensityRate FiniteHyperbolicHarmonicCap

/-- Sharp finite source transfer: the initial closed count is retained and
copies on the current strict-mask boundary are subtracted exactly. -/
theorem strictHarmonicBudget_le_of_densityDifference
    (T H δ F : ℝ) (d : ℕ) (hδ : 0 ≤ δ)
    (hcount : rightInclusiveCount T (1/2+δ)-rightInclusiveCount H (1/2+δ) ≤ F) :
    (strictTail T δ/(Ncount 0 T : ℝ))*harmonicHyperbolicCap d ≤
      (2*(F+rightInclusiveCount H (1/2+δ)-rightBoundaryCount T (1/2+δ))/
        (Ncount 0 T : ℝ))*harmonicHyperbolicCap d := by
  have hc : strictTail T δ ≤
      2*(F+rightInclusiveCount H (1/2+δ)-rightBoundaryCount T (1/2+δ)) := by
    rw [strictTail_eq_inclusive_sub_boundary T δ hδ]
    linarith
  exact mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hc (Nat.cast_nonneg _))
    (harmonicHyperbolicCap_nonneg d)

theorem strictHarmonicBudget_le_at_positiveCutoff
    (T : ℝ) (d : ℕ) (hd : 1 ≤ d) (M K E ω : ℝ)
    (hM : 0 < M) (hK : 0 < K) (hN : 0 < (Ncount 0 T : ℝ))
    (hcount : rightInclusiveCount T
      (1/2+positiveCountCutoff M (2*K*harmonicHyperbolicCap d/(Ncount 0 T : ℝ)) ω) ≤
      K*Real.exp (-M*inghamRate (positiveCountCutoff M (2*K*harmonicHyperbolicCap d/(Ncount 0 T : ℝ)) ω))+E) :
    (strictTail T (positiveCountCutoff M (2*K*harmonicHyperbolicCap d/(Ncount 0 T : ℝ)) ω)/
      (Ncount 0 T : ℝ))*harmonicHyperbolicCap d ≤
      Real.exp (-ω)+(2*E/(Ncount 0 T : ℝ))*harmonicHyperbolicCap d := by
  let A : ℝ := 2*K*harmonicHyperbolicCap d/(Ncount 0 T : ℝ)
  have hdR : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hW : 0 < harmonicHyperbolicCap d :=
    hdR.trans_le (harmonicHyperbolicCap_ge_card d)
  have hA : 0 < A := by dsimp [A]; positivity
  have hc : strictTail T (positiveCountCutoff M A ω) ≤
      2*(K*Real.exp (-M*inghamRate (positiveCountCutoff M A ω))+E) :=
    (strictTail_le_twice_inclusive _ _ (positiveCountCutoff_nonneg A ω hM)).trans
      (mul_le_mul_of_nonneg_left hcount (by norm_num))
  calc
    _ ≤ (2*(K*Real.exp (-M*inghamRate
      (positiveCountCutoff M A ω))+E)/(Ncount 0 T : ℝ))*harmonicHyperbolicCap d :=
      mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hc hN.le) hW.le
    _ = A*Real.exp (-M*inghamRate (positiveCountCutoff M A ω))+
      (2*E/(Ncount 0 T : ℝ))*harmonicHyperbolicCap d := by
        dsimp [A]
        simp only [div_eq_mul_inv]
        ring
    _ ≤ _ := add_le_add (positiveCountCutoff_exp_le hM hA) le_rfl

/-- Only the published difference estimate at the actual chosen point is
assumed. Its fixed initial count is kept, including zeros on its boundary. -/
theorem strictHarmonicBudget_tendsto_zero_of_difference
    (d : ℝ → ℕ) (M K E ω : ℝ → ℝ) (H : ℝ)
    (hd : ∀ᶠ T : ℝ in atTop, 1 ≤ d T)
    (hM : ∀ᶠ T : ℝ in atTop, 0 < M T)
    (hK : ∀ᶠ T : ℝ in atTop, 0 < K T)
    (hcount : ∀ᶠ T : ℝ in atTop,
      let δ := positiveCountCutoff (M T) (2*K T*harmonicHyperbolicCap (d T)/(Ncount 0 T : ℝ)) (ω T)
      rightInclusiveCount T (1/2+δ)-rightInclusiveCount H (1/2+δ) ≤
        K T*Real.exp (-M T*inghamRate δ)+E T)
    (hω : Tendsto ω atTop atTop)
    (hrem : Tendsto (fun T : ℝ =>
      (2*(E T+(Ncount 0 H : ℝ))/(Ncount 0 T : ℝ))*harmonicHyperbolicCap (d T))
        atTop (nhds 0)) :
    Tendsto (fun T : ℝ =>
      (strictTail T (positiveCountCutoff (M T) (2*K T*harmonicHyperbolicCap (d T)/(Ncount 0 T : ℝ)) (ω T))/
        (Ncount 0 T : ℝ))*harmonicHyperbolicCap (d T))
      atTop (nhds 0) := by
  have hexp : Tendsto (fun T => Real.exp (-ω T)) atTop (nhds 0) :=
    by simpa only [Function.comp_def, pow_zero, one_mul] using
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0).comp hω
  have hmajor : Tendsto (fun T => Real.exp (-ω T)+
      (2*(E T+(Ncount 0 H : ℝ))/(Ncount 0 T : ℝ))*harmonicHyperbolicCap (d T))
        atTop (nhds 0) := by simpa using hexp.add hrem
  refine squeeze_zero' ?_ ?_ hmajor
  · exact Eventually.of_forall fun T =>
      mul_nonneg (div_nonneg (strictTail_nonneg _ _) (Nat.cast_nonneg _))
        (harmonicHyperbolicCap_nonneg _)
  · filter_upwards [hd, hM, hK, hcount, eventually_count_pos]
      with T hdT hm hk hc hn
    have hnR : (0 : ℝ) < (Ncount 0 T : ℝ) := by exact_mod_cast hn
    apply strictHarmonicBudget_le_at_positiveCutoff T (d T) hdT (M T) (K T)
      (E T+(Ncount 0 H : ℝ)) (ω T) hm hk hnR
    have hi := rightInclusiveCount_le_count H
      (1/2+positiveCountCutoff (M T) (2*K T*harmonicHyperbolicCap (d T)/(Ncount 0 T : ℝ)) (ω T))
    dsimp only at hc
    linarith

theorem actualSignedTailBudget_tendsto_zero_of_harmonic
    (d : ℝ → ℕ) (δ : ℝ → ℝ)
    (h : Tendsto (fun T : ℝ =>
      (strictTail T (δ T)/(Ncount 0 T : ℝ))*harmonicHyperbolicCap (d T))
      atTop (nhds 0)) :
    Tendsto (fun T => actualSignedTailBudget T (d T) (δ T)) atTop (nhds 0) :=
  squeeze_zero (fun T => actualSignedTailBudget_nonneg T (d T) (δ T))
    (fun T => actualSignedTailBudget_le_harmonic T (d T) (δ T)) h

theorem signedBadHyperbolic_norm_tendsto_zero_of_harmonic
    (d : ℝ → ℕ) (δ : ℝ → ℝ)
    (h : Tendsto (fun T : ℝ =>
      (strictTail T (δ T)/(Ncount 0 T : ℝ))*harmonicHyperbolicCap (d T))
      atTop (nhds 0)) :
    Tendsto (fun T => ‖signedBadHyperbolic T (d T) (δ T)‖) atTop (nhds 0) :=
  squeeze_zero (fun _T => norm_nonneg _)
    (fun T => signedBadHyperbolic_norm_le_harmonic T (d T) (δ T)) h

/-- The one-point limit supplies precisely the signed one-sided provider
used by the existing good-zero centered-frame theorem, uniformly in f. -/
theorem eventually_signedBadHyperbolic_upper_of_harmonic
    (d : ℝ → ℕ) (δ : ℝ → ℝ)
    (h : Tendsto (fun T : ℝ =>
      (strictTail T (δ T)/(Ncount 0 T : ℝ))*harmonicHyperbolicCap (d T))
      atTop (nhds 0)) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, SignedBadHyperbolicUpper T (d T) (δ T) ε := by
  filter_upwards [h.eventually_le_const hε] with T ht
  intro f
  exact (signedBadHyperbolic_upper_harmonic T (d T) (δ T) f).trans
    (mul_le_mul_of_nonneg_right ht (sq_nonneg ‖f‖))


/-- The original masked-good operator approaches the full actual operator;
this difference identity keeps both signed hyperbolic channels. -/
theorem goodHyperbolic_distance_tendsto_zero_of_harmonic
    (d : ℝ → ℕ) (δ : ℝ → ℝ)
    (h : Tendsto (fun T : ℝ =>
      (strictTail T (δ T)/(Ncount 0 T : ℝ))*harmonicHyperbolicCap (d T))
      atTop (nhds 0)) :
    Tendsto (fun T => ‖goodHyperbolic T (d T) (δ T)-landauGram T (d T)‖)
      atTop (nhds 0) := by
  have hn := signedBadHyperbolic_norm_tendsto_zero_of_harmonic d δ h
  apply hn.congr'
  exact Eventually.of_forall fun T => by
    change ‖signedBadHyperbolic T (d T) (δ T)‖ =
      ‖(landauGram T (d T)-signedBadHyperbolic T (d T) (δ T))-landauGram T (d T)‖
    rw [sub_eq_add_neg, sub_eq_add_neg,
      add_comm (landauGram T (d T)) (-signedBadHyperbolic T (d T) (δ T)),
      add_assoc, add_neg_cancel, add_zero, norm_neg]

end RiemannResearch.Analysis.ActualZeroPhaseMoments

namespace RiemannResearch.Analysis.ActualZeroPhaseMoments
open ActualZeroOrdinate Zeta23 ZeroDensityRate FiniteHyperbolicHarmonicCap
/-- Source-shaped one-point difference estimate suffices. All fixed-height
and logarithmic errors are discharged by the unconditional actual count
normalization. The only zeta-density premise is hcount. -/
theorem shrinking_harmonic_tail_of_logDifference
    (d : ℝ → ℕ) (M K ω : ℝ → ℝ) (H B₂ B₃ : ℝ)
    (hB₂ : 0 ≤ B₂) (hB₃ : 0 ≤ B₃)
    (hsupport : ∀ᶠ T : ℝ in atTop,
      1 ≤ d T ∧ Real.log (d T : ℝ) ≤ Real.log T/2)
    (hM : ∀ᶠ T : ℝ in atTop, 0 < M T)
    (hK : ∀ᶠ T : ℝ in atTop, 0 < K T)
    (hω : Tendsto ω atTop atTop)
    (hratio : Tendsto (fun T : ℝ =>
      max 0 (Real.log (2*K T*harmonicHyperbolicCap (d T)/(Ncount 0 T : ℝ))+ω T)/
        M T) atTop (nhds 0))
    (hcount : ∀ᶠ T : ℝ in atTop,
      let δ := positiveCountCutoff (M T)
        (2*K T*harmonicHyperbolicCap (d T)/(Ncount 0 T : ℝ)) (ω T)
      rightInclusiveCount T (1/2+δ)-rightInclusiveCount H (1/2+δ) ≤
        K T*Real.exp (-M T*inghamRate δ)+
          B₂*(Real.log T)^2+B₃*Real.log T) :
    let δ := fun T => positiveCountCutoff (M T)
      (2*K T*harmonicHyperbolicCap (d T)/(Ncount 0 T : ℝ)) (ω T)
    Tendsto δ atTop (nhds 0) ∧
      Tendsto (fun T => (strictTail T (δ T)/(Ncount 0 T : ℝ))*
        harmonicHyperbolicCap (d T)) atTop (nhds 0) ∧
      Tendsto (fun T => actualSignedTailBudget T (d T) (δ T)) atTop (nhds 0) ∧
      Tendsto (fun T => ‖signedBadHyperbolic T (d T) (δ T)‖) atTop (nhds 0) := by
  let δ := fun T => positiveCountCutoff (M T)
    (2*K T*harmonicHyperbolicCap (d T)/(Ncount 0 T : ℝ)) (ω T)
  have hδ : Tendsto δ atTop (nhds 0) :=
    positiveCountCutoff_tendsto_zero M _ ω hM hratio
  have ht : Tendsto (fun T => (strictTail T (δ T)/(Ncount 0 T : ℝ))*
      harmonicHyperbolicCap (d T)) atTop (nhds 0) := by
    apply strictHarmonicBudget_tendsto_zero_of_difference d M K
      (fun T => B₂*(Real.log T)^2+B₃*Real.log T) ω H
      (hsupport.mono fun _ h => h.1) hM hK
    · filter_upwards [hcount] with T hc
      dsimp only at hc ⊢
      linarith
    · exact hω
    · exact finiteHeight_log_remainder_tendsto_zero d H B₂ B₃ hB₂ hB₃ hsupport
  exact ⟨hδ, ht, actualSignedTailBudget_tendsto_zero_of_harmonic d δ ht,
    signedBadHyperbolic_norm_tendsto_zero_of_harmonic d δ ht⟩
end RiemannResearch.Analysis.ActualZeroPhaseMoments

namespace RiemannResearch.Analysis.ActualZeroPhaseMoments
open ActualZeroOrdinate Zeta23 ZeroDensityRate FiniteHyperbolicHarmonicCap
/-- The exact source scale now needs only its actual one-point difference
estimate. Every other density-transfer and shrinking-rate step is proved. -/
theorem shrinking_harmonic_tail_of_sourceDifference
    (d : ℝ → ℕ) (ω : ℝ → ℝ) (C H B₂ B₃ : ℝ)
    (hC : 0 < C) (hB₂ : 0 ≤ B₂) (hB₃ : 0 ≤ B₃)
    (hd : ∀ᶠ T : ℝ in atTop, 1 ≤ d T)
    (hsmall : Tendsto (fun T : ℝ => Real.log (d T : ℝ)/Real.log T) atTop (nhds 0))
    (hω : Tendsto ω atTop atTop)
    (hωsmall : Tendsto (fun T : ℝ => ω T/Real.log T) atTop (nhds 0))
    (hcount : ∀ᶠ T : ℝ in atTop,
      let L := Real.log T
      let δ := positiveCountCutoff (L+Real.log L)
        (2*(C*T*L^3)*harmonicHyperbolicCap (d T)/(Ncount 0 T : ℝ)) (ω T)
      rightInclusiveCount T (1/2+δ)-rightInclusiveCount H (1/2+δ) ≤
        (C*T*L^3)*Real.exp (-(L+Real.log L)*inghamRate δ)+B₂*L^2+B₃*L) :
    let δ := fun T => positiveCountCutoff (Real.log T+Real.log (Real.log T))
      (2*(C*T*(Real.log T)^3)*harmonicHyperbolicCap (d T)/(Ncount 0 T : ℝ)) (ω T)
    Tendsto δ atTop (nhds 0) ∧
      Tendsto (fun T => (strictTail T (δ T)/(Ncount 0 T : ℝ))*
        harmonicHyperbolicCap (d T)) atTop (nhds 0) ∧
      Tendsto (fun T => actualSignedTailBudget T (d T) (δ T)) atTop (nhds 0) ∧
      Tendsto (fun T => ‖signedBadHyperbolic T (d T) (δ T)‖) atTop (nhds 0) := by
  have hs : ∀ᶠ T : ℝ in atTop,
      1 ≤ d T ∧ Real.log (d T : ℝ) ≤ Real.log T/2 := by
    filter_upwards [hd, Real.tendsto_log_atTop.eventually_gt_atTop 0,
      hsmall.eventually_le_const (by norm_num : (0:ℝ)<1/2)] with T hdT hl ht
    refine ⟨hdT, ?_⟩
    have h := (div_le_iff₀ hl).mp ht
    linarith
  have hm : ∀ᶠ T : ℝ in atTop, 0 < Real.log T+Real.log (Real.log T) := by
    filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1] with T ht
    have h := Real.log_nonneg ht
    linarith
  have hk : ∀ᶠ T : ℝ in atTop, 0 < C*T*(Real.log T)^3 := by
    filter_upwards [eventually_gt_atTop (0:ℝ),
      Real.tendsto_log_atTop.eventually_gt_atTop 0] with T ht hl
    positivity
  exact shrinking_harmonic_tail_of_logDifference d
    (fun T => Real.log T+Real.log (Real.log T)) (fun T => C*T*(Real.log T)^3)
    ω H B₂ B₃ hB₂ hB₃ hs hm hk hω
    (source_positive_margin_ratio_tendsto_zero d ω C hC hd hsmall hωsmall) hcount
end RiemannResearch.Analysis.ActualZeroPhaseMoments

namespace RiemannResearch.Analysis.ActualZeroPhaseMoments
open ActualZeroOrdinate Zeta23 ZeroDensityRate FiniteHyperbolicHarmonicCap
/-- Direct consumer of the source's power-shaped finite-height difference
estimate. The only analytic premise is the one-point hcount; this declaration
does not import or axiomatize Chourasiya--Simonic Theorem 1. -/
theorem shrinking_harmonic_tail_of_inghamDifference
    (d : ℝ → ℕ) (ω : ℝ → ℝ) (C H B₂ B₃ : ℝ)
    (hC : 0 < C) (hB₂ : 0 ≤ B₂) (hB₃ : 0 ≤ B₃)
    (hd : ∀ᶠ T : ℝ in atTop, 1 ≤ d T)
    (hsmall : Tendsto (fun T : ℝ => Real.log (d T : ℝ)/Real.log T) atTop (nhds 0))
    (hω : Tendsto ω atTop atTop)
    (hωsmall : Tendsto (fun T : ℝ => ω T/Real.log T) atTop (nhds 0))
    (hcount : ∀ᶠ T : ℝ in atTop,
      let δ := sourceCountCutoff T (d T) C (ω T)
      let σ := 1/2+δ
      rightInclusiveCount T σ-rightInclusiveCount H σ ≤
        C*T ^ (3*(1-σ)/(2-σ))*(Real.log T) ^ ((7-5*σ)/(2-σ))+
          B₂*(Real.log T)^2+B₃*Real.log T) :
    let δ := fun T => sourceCountCutoff T (d T) C (ω T)
    Tendsto δ atTop (nhds 0) ∧
      Tendsto (fun T => (strictTail T (δ T)/(Ncount 0 T : ℝ))*
        harmonicHyperbolicCap (d T)) atTop (nhds 0) ∧
      Tendsto (fun T => actualSignedTailBudget T (d T) (δ T)) atTop (nhds 0) ∧
      Tendsto (fun T => ‖signedBadHyperbolic T (d T) (δ T)‖) atTop (nhds 0) := by
  apply shrinking_harmonic_tail_of_sourceDifference d ω C H B₂ B₃
    hC hB₂ hB₃ hd hsmall hω hωsmall
  filter_upwards [hcount, (sourceCountCutoff_shrinking d ω C hC hd hsmall hωsmall).2,
    eventually_gt_atTop (0 : ℝ), Real.tendsto_log_atTop.eventually_gt_atTop 0]
    with T hc hδ ht hl
  let δ := sourceCountCutoff T (d T) C (ω T)
  have hden : 3-2*δ ≠ 0 := ne_of_gt (by dsimp [δ]; linarith)
  have hex :
      T ^ (3*(1-(1/2+δ))/(2-(1/2+δ)))*
        (Real.log T) ^ ((7-5*(1/2+δ))/(2-(1/2+δ))) =
      T*(Real.log T)^3*Real.exp (-(Real.log T+Real.log (Real.log T))*inghamRate δ) := by
    rw [tExponent_eq_one_sub_rate δ hden, logExponent_eq_three_sub_rate δ hden,
      inghamPower_eq_expDecay ht hl]
  change rightInclusiveCount T (1/2+δ)-rightInclusiveCount H (1/2+δ) ≤
    (C*T*(Real.log T)^3)*Real.exp (-(Real.log T+Real.log (Real.log T))*inghamRate δ)+
      B₂*(Real.log T)^2+B₃*Real.log T
  calc
    _ ≤ C*(T ^ (3*(1-(1/2+δ))/(2-(1/2+δ)))*
      (Real.log T) ^ ((7-5*(1/2+δ))/(2-(1/2+δ))))+
      B₂*(Real.log T)^2+B₃*Real.log T := by
        simpa only [mul_assoc] using hc
    _ = _ := by rw [hex]; ring
end RiemannResearch.Analysis.ActualZeroPhaseMoments
