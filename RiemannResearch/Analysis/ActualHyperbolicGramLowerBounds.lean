/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualLandauOperatorResidual
import RiemannResearch.Analysis.PrimePowerCovarianceEuclideanNorm
import RiemannResearch.Analysis.CenteredHyperbolicRows
import RiemannResearch.Analysis.WeightedGroundStateForm

/-!
# Unconditional lower bounds for the full actual hyperbolic Gram

The conjugate analysis rows reproduce the original Landau operator's
transpose entries and its standard complex quadratic form. All zero
multiplicities, every integer coordinate and all prime-power interactions
are retained. The exact negative sinh square and complete arithmetic graph
square precede the estimates. The existing Landau residual and count
providers yield every lower coefficient h < 1-theta at theta <= 2/7.

Source: assembly of the existing actual Landau/count/arithmetic declarations
for the user-requested lower-bound problem (2026-10-05). Analytic provenance
and the separate shrinking-mask obligation are recorded in
RH/ActualHyperbolicLowerBounds20261005.md. No density or RH provider is assumed.
-/

noncomputable section
open scoped BigOperators InnerProductSpace

namespace RiemannResearch.Analysis.ActualZeroPhaseMoments
open ActualZeroOrdinate ContinuousLinearMap RiemannResearch.Fourier HorizontalEuclideanMoments
def frequencyIndexEquiv (d : ℕ) : Fin d ≃ integerFrequencyIndex d where
  toFun i := ⟨i.val + 1, Finset.mem_Ioc.mpr ⟨by omega, by omega⟩⟩
  invFun n := ⟨n.val - 1, by have := Finset.mem_Ioc.mp n.property; omega⟩
  left_inv i := by ext; simp
  right_inv n := by ext; have := Finset.mem_Ioc.mp n.property; simp; omega

def reindexedFrequencyVector (d : ℕ) (f : Space d) :
    EuclideanSpace ℂ (integerFrequencyIndex d) :=
  WithLp.toLp 2 (fun n => f ((frequencyIndexEquiv d).symm n))

theorem reindexedFrequencyVector_norm_sq (d : ℕ) (f : Space d) :
    ‖reindexedFrequencyVector d f‖^2 = ‖f‖^2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  exact (Equiv.sum_comp (frequencyIndexEquiv d).symm (fun i => ‖f i‖^2))

theorem finPrimePowerMainOperator_inner_eq (d : ℕ) (f : Space d) :
    inner ℂ f (finPrimePowerMainOperator d f) =
      inner ℂ (reindexedFrequencyVector d f)
        (primePowerMainOperator d (reindexedFrequencyVector d f)) := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  change (∑ i : Fin d, (∑ j : Fin d,
      (primePowerCovarianceSymmetricEntry (i.val+1) (j.val+1) : ℂ) * f j) *
        star (f i)) =
    ∑ n : integerFrequencyIndex d, (∑ m : integerFrequencyIndex d,
      (primePowerCovarianceSymmetricEntry n.val m.val : ℂ) *
        f ((frequencyIndexEquiv d).symm m)) * star (f ((frequencyIndexEquiv d).symm n))
  rw [← Equiv.sum_comp (frequencyIndexEquiv d)]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Equiv.symm_apply_apply]
  congr 1
  rw [← Equiv.sum_comp (frequencyIndexEquiv d)]
  rfl

theorem finPrimePowerMainOperator_inner_norm_le (d : ℕ) (f : Space d) :
    ‖inner ℂ f (finPrimePowerMainOperator d f)‖ ≤
      (Real.log d + Real.log 4 + 4)*‖f‖^2 := by
  rw [finPrimePowerMainOperator_inner_eq]
  simpa only [reindexedFrequencyVector_norm_sq] using
    primePowerMainOperator_inner_norm_le d (reindexedFrequencyVector d f)

theorem real_inner_operator_abs_le (d : ℕ) (A : Space d →L[ℂ] Space d)
    (f : Space d) :
    |(inner ℂ f (A f)).re| ≤ ‖A‖*‖f‖^2 := by
  calc
    _ ≤ ‖inner ℂ f (A f)‖ := Complex.abs_re_le_norm _
    _ ≤ ‖f‖*‖A f‖ := norm_inner_le_norm _ _
    _ ≤ ‖f‖*(‖A‖*‖f‖) :=
      mul_le_mul_of_nonneg_left (A.le_opNorm f) (norm_nonneg _)
    _ = _ := by ring

theorem landauGram_exact_decomposition (T : ℝ) (d : ℕ) :
    landauGram T d = 1 -
      (T / ((2*Real.pi)*(Zeta23.Ncount 0 T : ℝ))) • finPrimePowerMainOperator d +
      actualLandauResidual T d := by
  unfold actualLandauResidual
  abel

theorem landauGram_form_exact (T : ℝ) (d : ℕ) (f : Space d) :
    (inner ℂ f (landauGram T d f)).re =
      ‖f‖^2-(T/((2*Real.pi)*(Zeta23.Ncount 0 T : ℝ))) *
        (inner ℂ f (finPrimePowerMainOperator d f)).re+
        (inner ℂ f (actualLandauResidual T d f)).re := by
  rw [landauGram_exact_decomposition]
  simp [add_apply, sub_apply, ContinuousLinearMap.one_def, ContinuousLinearMap.id_apply, smul_apply, inner_add_right, inner_sub_right,
    RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_right,
    Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, inner_self_eq_norm_sq_to_K,
    Complex.ofReal_re]
  norm_cast
  have hcast : (↑T/(2*↑Real.pi*↑(Zeta23.Ncount 0 T)) : ℂ) =
      ((T/(2*Real.pi*(Zeta23.Ncount 0 T : ℝ)) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hcast]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem landauGram_form_lower (T : ℝ) (d : ℕ) (hT : 0 ≤ T) (f : Space d) :
    (1 - (T/((2*Real.pi)*(Zeta23.Ncount 0 T : ℝ))) *
        (Real.log d+Real.log 4+4) - ‖actualLandauResidual T d‖)*‖f‖^2 ≤
      (inner ℂ f (landauGram T d f)).re := by
  have hτ : 0 ≤ T/((2*Real.pi)*(Zeta23.Ncount 0 T : ℝ)) := by positivity
  have hA := (Complex.re_le_norm _).trans
    (finPrimePowerMainOperator_inner_norm_le d f)
  have hE := (abs_le.mp (real_inner_operator_abs_le d
    (actualLandauResidual T d) f)).1
  have hmul := mul_le_mul_of_nonneg_left hA hτ
  rw [landauGram_form_exact]
  nlinarith



def actualHyperbolicLower (T : ℝ) (d : ℕ) : ℝ :=
  1 - (T/((2*Real.pi)*(Zeta23.Ncount 0 T : ℝ))) *
    (Real.log d+Real.log 4+4) - ‖actualLandauResidual T d‖
open CenteredHyperbolicFrames ZeroOrdinate
local instance (T : ℝ) : DecidableEq (Copies T) := Classical.decEq _
def actualPhaseRow (T : ℝ) (d : ℕ) (c : Copies T) (n : Fin d) : ℂ :=
  (((Real.sqrt (Zeta23.Ncount 0 T : ℝ))⁻¹ : ℝ) : ℂ) *
    star (copyPhaseVector d c.1.1 n)
def actualShift (T : ℝ) (c : Copies T) : ℝ := c.1.1.re-1/2
def centeredFrequency (d : ℕ) (n : Fin d) : ℝ :=
  logFrequency d n-Real.log (d : ℝ)/2

private theorem inv_sqrt_count_mul (T : ℝ) :
    (((Real.sqrt (Zeta23.Ncount 0 T : ℝ))⁻¹ : ℝ) : ℂ) *
      (((Real.sqrt (Zeta23.Ncount 0 T : ℝ))⁻¹ : ℝ) : ℂ) =
      (Zeta23.Ncount 0 T : ℂ)⁻¹ := by
  rw [← Complex.ofReal_mul, ← pow_two, inv_pow,
    Real.sq_sqrt (Nat.cast_nonneg (Zeta23.Ncount 0 T))]
  simp

theorem actualPhaseRow_product (T : ℝ) (d : ℕ)
    (c : Copies T) (n m : Fin d) :
    actualPhaseRow T d c n * star (actualPhaseRow T d c m) =
      (Zeta23.Ncount 0 T : ℂ)⁻¹ * phase (frequencyGap m n) c.1.1.im := by
  unfold actualPhaseRow
  simp only [star_mul, star_star, Complex.star_def, Complex.conj_ofReal]
  calc
    _ = ((((Real.sqrt (Zeta23.Ncount 0 T : ℝ))⁻¹ : ℝ) : ℂ) *
      (((Real.sqrt (Zeta23.Ncount 0 T : ℝ))⁻¹ : ℝ) : ℂ)) *
      (copyPhaseVector d c.1.1 m * star (copyPhaseVector d c.1.1 n)) := by
        simp only [← Complex.star_def, star_star]
        ring
    _ = _ := by rw [inv_sqrt_count_mul, copyPhaseVector_kernel]

theorem actualPhaseRow_hyperbolic_entry (T : ℝ) (d : ℕ) (n m : Fin d) :
    hyperbolicKernel Finset.univ (fun _ : Copies T => (1 : ℝ))
      (actualShift T) (centeredFrequency d) (actualPhaseRow T d) n m =
      euclideanEntry (landauGram T d) m n := by
  rw [landauGram_entry, landauSum_eq_cosh, sum_eq_copies, Finset.mul_sum]
  unfold hyperbolicKernel
  simp only [Complex.ofReal_one, one_mul]
  apply Finset.sum_congr rfl
  intro c hc
  have hh : Real.cosh (actualShift T c *
      (centeredFrequency d n-centeredFrequency d m)) =
      Real.cosh (frequencyGap m n*(c.1.1.re-1/2)) := by
    rw [show actualShift T c*(centeredFrequency d n-centeredFrequency d m) =
      -(frequencyGap m n*(c.1.1.re-1/2)) by
        unfold actualShift centeredFrequency frequencyGap logFrequency; ring,
      Real.cosh_neg]
  calc
    _ = (Real.cosh (actualShift T c*
      (centeredFrequency d n-centeredFrequency d m)) : ℂ) *
      (actualPhaseRow T d c n*star (actualPhaseRow T d c m)) := by ring
    _ = _ := by rw [actualPhaseRow_product, hh]; ring

private theorem operator_apply_eq_entries (d : ℕ) (H : Space d →L[ℂ] Space d)
    (f : Space d) (n : Fin d) :
    H f n = ∑ m, euclideanEntry H n m*f m := by
  have hf : f = ∑ m : Fin d, f m • EuclideanSpace.single m 1 := by
    ext m; simp [Pi.single_apply]
  conv_lhs => rw [hf, map_sum]
  simp only [map_smul, WithLp.ofLp_sum, Finset.sum_apply,
    WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  change (∑ m, f m*euclideanEntry H n m) = _
  apply Finset.sum_congr rfl
  intro m hm
  ring

theorem actualHyperbolic_rows_eq (T : ℝ) (d : ℕ) (f : Space d) :
    ‖cosineAnalysis (actualPhaseRow T d) (actualShift T) (centeredFrequency d) f‖^2-
      ‖sineAnalysis (actualPhaseRow T d) (actualShift T) (centeredFrequency d) f‖^2 =
      (inner ℂ f (landauGram T d f)).re := by
  rw [← finite_hyperbolic_form_eq]
  have hkernel : hyperbolicKernel Finset.univ (fun _ : Copies T => (1 : ℝ))
      (actualShift T) (centeredFrequency d) (actualPhaseRow T d) =
      (fun n m => euclideanEntry (landauGram T d) m n) := by
    funext n m
    exact actualPhaseRow_hyperbolic_entry T d n m
  rw [hkernel]
  have hform :
      ZeroSamplingQuadratic.form Finset.univ
        (fun n m => euclideanEntry (landauGram T d) m n) (fun n => f n) =
        inner ℂ f (landauGram T d f) := by
    rw [PiLp.inner_apply]
    simp only [RCLike.inner_apply, operator_apply_eq_entries, Finset.sum_mul]
    unfold ZeroSamplingQuadratic.form
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro m hm
    change f m*star (f n)*euclideanEntry (landauGram T d) n m =
      euclideanEntry (landauGram T d) n m*f m*star (f n)
    ring
  exact congrArg Complex.re hform

theorem actualHyperbolic_rows_lower (T : ℝ) (d : ℕ) (hT : 0 ≤ T) (f : Space d) :
    actualHyperbolicLower T d*‖f‖^2 ≤
      ‖cosineAnalysis (actualPhaseRow T d) (actualShift T) (centeredFrequency d) f‖^2-
      ‖sineAnalysis (actualPhaseRow T d) (actualShift T) (centeredFrequency d) f‖^2 := by
  rw [actualHyperbolic_rows_eq]
  exact landauGram_form_lower T d hT f

theorem actualShift_bounds (T : ℝ) (c : Copies T) :
    |actualShift T c| ≤ 1/2 :=
  (displacement_lt_half c.1.property).le

theorem centeredFrequency_bounds (d : ℕ) (n : Fin d) :
    |centeredFrequency d n| ≤ Real.log (d : ℝ)/2 := by
  rw [abs_le]
  have hn := logFrequency_bounds d n
  unfold centeredFrequency
  constructor <;> linarith

def fullArithmeticWeight (d : ℕ) (n : Fin d) : ℝ :=
  integerFrequencySchurWeight (n.val+1)
def fullArithmeticKernel (d : ℕ) (n m : Fin d) : ℝ :=
  primePowerCovarianceSymmetricEntry (n.val+1) (m.val+1)
def fullArithmeticDiagonal (d : ℕ) (f : Space d) : ℝ :=
  ∑ n, ((∑ m, fullArithmeticKernel d n m*fullArithmeticWeight d m) /
    fullArithmeticWeight d n)*‖f n‖^2
def fullArithmeticGraphEnergy (d : ℕ) (f : Space d) : ℝ :=
  (1/2:ℝ)*∑ n, ∑ m,
    fullArithmeticKernel d n m*fullArithmeticWeight d n*fullArithmeticWeight d m*
      ‖f n/(fullArithmeticWeight d n : ℂ)-f m/(fullArithmeticWeight d m : ℂ)‖^2

theorem operator_inner_eq_transpose_form (d : ℕ)
    (H : Space d →L[ℂ] Space d) (f : Space d) :
    ZeroSamplingQuadratic.form Finset.univ (fun n m => euclideanEntry H m n)
      (fun n => f n) = inner ℂ f (H f) := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, operator_apply_eq_entries, Finset.sum_mul]
  unfold ZeroSamplingQuadratic.form
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  change f m*star (f n)*euclideanEntry H n m =
      euclideanEntry H n m*f m*star (f n)
  ring

theorem finPrimePowerMainOperator_inner_groundState (d : ℕ) (f : Space d) :
    (inner ℂ f (finPrimePowerMainOperator d f)).re =
      fullArithmeticDiagonal d f-fullArithmeticGraphEnergy d f := by
  rw [← operator_inner_eq_transpose_form]
  have hentry (n m : Fin d) :
      euclideanEntry (finPrimePowerMainOperator d) m n =
        (fullArithmeticKernel d n m : ℂ) := by
    rw [finPrimePowerMainOperator_entry]
    unfold fullArithmeticKernel
    exact congrArg (fun r:ℝ => (r:ℂ))
      (primePowerCovarianceSymmetricEntry_symm (m.val+1) (n.val+1) (by omega) (by omega))
  simp_rw [hentry]
  exact ZeroSamplingQuadratic.weighted_groundState_identity
    (fullArithmeticKernel d)
    (fun n m => primePowerCovarianceSymmetricEntry_symm
      (n.val+1) (m.val+1) (by omega) (by omega))
    (fullArithmeticWeight d)
    (fun n => integerFrequencySchurWeight_pos (n.val+1) (by omega))
    (fun n => f n)

theorem fullArithmeticGraphEnergy_nonneg (d : ℕ) (f : Space d) :
    0 ≤ fullArithmeticGraphEnergy d f := by
  unfold fullArithmeticGraphEnergy
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro n hn
  apply Finset.sum_nonneg
  intro m hm
  apply mul_nonneg _ (sq_nonneg _)
  apply mul_nonneg _ (integerFrequencySchurWeight_pos (m.val+1) (by omega)).le
  exact mul_nonneg (primePowerCovarianceSymmetricEntry_nonneg _ _)
    (integerFrequencySchurWeight_pos (n.val+1) (by omega)).le


theorem landauGram_form_exact_graph (T : ℝ) (d : ℕ) (f : Space d) :
    (inner ℂ f (landauGram T d f)).re =
      ‖f‖^2-(T/((2*Real.pi)*(Zeta23.Ncount 0 T : ℝ)))*fullArithmeticDiagonal d f+
        (T/((2*Real.pi)*(Zeta23.Ncount 0 T : ℝ)))*fullArithmeticGraphEnergy d f+
        (inner ℂ f (actualLandauResidual T d f)).re := by
  rw [landauGram_form_exact, finPrimePowerMainOperator_inner_groundState]
  ring

theorem landauGram_form_lower_graph (T : ℝ) (d : ℕ) (f : Space d) :
    (1-‖actualLandauResidual T d‖)*‖f‖^2-
      (T/((2*Real.pi)*(Zeta23.Ncount 0 T : ℝ)))*fullArithmeticDiagonal d f+
      (T/((2*Real.pi)*(Zeta23.Ncount 0 T : ℝ)))*fullArithmeticGraphEnergy d f ≤
      (inner ℂ f (landauGram T d f)).re := by
  rw [landauGram_form_exact_graph]
  have hE := (abs_le.mp (real_inner_operator_abs_le d
    (actualLandauResidual T d) f)).1
  nlinarith

theorem actual_full_centered_frame_lower (T : ℝ) (d : ℕ)
    (hT : 0 ≤ T) (hd : 1 ≤ d) (hh : 0 ≤ actualHyperbolicLower T d) :
    ∀ f : Space d,
      ((Real.sqrt (actualHyperbolicLower T d)-
          ((Real.cosh (Real.log (d : ℝ)/4)-1)/2)*‖rowAnalysis (actualPhaseRow T d)‖) /
        ((1+Real.cosh (Real.log (d : ℝ)/4))/2))*‖f‖ ≤
        ‖rowAnalysis (actualPhaseRow T d) f‖ := by
  have hlog : 0 ≤ Real.log (d : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hd)
  have h := finite_centered_frame_lower (actualPhaseRow T d) (actualShift T)
    (centeredFrequency d) (Real.log (d : ℝ)/2) (1/2) (actualHyperbolicLower T d)
    (by positivity) (by norm_num) (actualShift_bounds T) (centeredFrequency_bounds d)
    hh (actualHyperbolic_rows_lower T d hT)
  simpa only [show (1/2:ℝ)*(Real.log (d : ℝ)/2) = Real.log (d : ℝ)/4 by ring] using h

open Filter in
theorem eventually_landauGram_lower_power_support
    (d : ℝ → ℕ) (a θ h : ℝ) (hθ : 0 ≤ θ) (hθmax : θ ≤ 2/7)
    (hh : h < 1-θ)
    (hsupport : ∀ᶠ T : ℝ in atTop,
      1 ≤ d T ∧ Real.log (d T : ℝ) ≤ a+θ*Real.log (T+3)) :
    ∀ᶠ T : ℝ in atTop, ∀ f : Space (d T),
      h*‖f‖^2 ≤ (inner ℂ f (landauGram T (d T) f)).re := by
  let η : ℝ := 1-θ-h
  have hη : 0 < η := by dsimp [η]; linarith
  let r : ℝ := 1+η/(2*(θ+1))
  have hθone : 0 < θ+1 := by linarith
  have hr : 1 < r := by
    have hp : 0 < η/(2*(θ+1)) := div_pos hη (by positivity)
    dsimp [r]
    linarith
  have hr0 : 0 < r := by linarith
  have hrθ : r*θ ≤ θ+η/2 := by
    have heq : (r-1)*(2*(θ+1)) = η := by
      dsimp [r]
      field_simp [hθone.ne']
      <;> ring
    nlinarith
  let c : ℝ := 1/((2*Real.pi)*r)
  have hc : 0 < c := by dsimp [c]; positivity
  have hcupper : c < 1/(2*Real.pi) := by
    dsimp [c]
    exact one_div_lt_one_div_of_lt (by positivity)
      (by nlinarith [Real.pi_pos])
  let B : ℝ := a+θ*Real.log 4+Real.log 4+4
  have hscrit : ∀ᶠ T : ℝ in atTop,
      1 ≤ d T ∧ Real.log (d T : ℝ) ≤ a+(2/7:ℝ)*Real.log (T+3) := by
    filter_upwards [hsupport, eventually_ge_atTop (1:ℝ)] with T hs hT
    refine ⟨hs.1, hs.2.trans ?_⟩
    have hL : 0 ≤ Real.log (T+3) := Real.log_nonneg (by linarith)
    nlinarith
  have hE := actualLandauResidual_norm_tendsto_zero_critical_power_support d a hscrit
  have hEsmall : ∀ᶠ T : ℝ in atTop, ‖actualLandauResidual T (d T)‖ < η/4 :=
    hE.eventually (gt_mem_nhds (by positivity : (0:ℝ) < η/4))
  filter_upwards [hsupport, eventually_count_ge_log_of_lt hcupper, hEsmall,
    eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (4*r*|B|/η)]
    with T hs hN hEs hT hLlarge
  have hT0 : 0 < T := by linarith
  have hL : 0 < Real.log T := Real.log_pos hT
  have hNr : (0:ℝ) < (Zeta23.Ncount 0 T : ℝ) :=
    lt_of_lt_of_le (by positivity) hN
  have hshift : Real.log (T+3) ≤ Real.log T+Real.log 4 := by
    calc
      _ ≤ Real.log (T*4) := Real.log_le_log (by linarith) (by linarith)
      _ = _ := Real.log_mul hT0.ne' (by norm_num)
  have hK : Real.log (d T : ℝ)+Real.log 4+4 ≤ θ*Real.log T+|B| := by
    have hθshift := mul_le_mul_of_nonneg_left hshift hθ
    have hB := le_abs_self B
    dsimp [B] at hB
    linarith
  have hK0 : 0 ≤ Real.log (d T : ℝ)+Real.log 4+4 := by
    have hdR : (1:ℝ) ≤ d T := by exact_mod_cast hs.1
    have := Real.log_nonneg hdR
    have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)
    positivity
  have hτ : T/((2*Real.pi)*(Zeta23.Ncount 0 T : ℝ)) ≤ r/Real.log T := by
    calc
      _ ≤ T/((2*Real.pi)*(c*T*Real.log T)) :=
        div_le_div_of_nonneg_left hT0.le (by positivity)
          (mul_le_mul_of_nonneg_left hN (by positivity))
      _ = _ := by
        dsimp [c]
        field_simp [Real.pi_ne_zero, hr0.ne', hT0.ne', hL.ne']
  have hbudget : (r/Real.log T) *
      (Real.log (d T : ℝ)+Real.log 4+4) ≤ r*θ+η/4 := by
    have hb : r*|B|/Real.log T ≤ η/4 := by
      have hz := (div_le_iff₀ hη).mp hLlarge
      apply (div_le_iff₀ hL).mpr
      nlinarith
    calc
      _ ≤ (r/Real.log T)*(θ*Real.log T+|B|) :=
        mul_le_mul_of_nonneg_left hK (by positivity)
      _ = r*θ+r*|B|/Real.log T := by field_simp [hL.ne']
      _ ≤ _ := by linarith
  have hmain : (T/((2*Real.pi)*(Zeta23.Ncount 0 T : ℝ))) *
      (Real.log (d T : ℝ)+Real.log 4+4) ≤ r*θ+η/4 :=
    (mul_le_mul_of_nonneg_right hτ hK0).trans hbudget
  have hcoef : h ≤ actualHyperbolicLower T (d T) := by
    unfold actualHyperbolicLower
    dsimp [η] at hrθ hmain hEs
    linarith
  intro f
  exact (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)).trans
    (landauGram_form_lower T (d T) hT0.le f)

end RiemannResearch.Analysis.ActualZeroPhaseMoments
