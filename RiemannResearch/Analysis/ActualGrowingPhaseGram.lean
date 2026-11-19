/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualDensityHarmonicOperator
import RiemannResearch.Analysis.ActualCriticalFarStrip
import RiemannResearch.Analysis.FiniteQuadraticCoshCorrection
import RiemannResearch.Analysis.ActualZeroDisplacementMoments

/-!
# Growing-dimensional full phase-Gram correction

The complete Landau minus phase operator is a finite signed sum over
actual zero copies. Each displacement up to 3/8 has a quadratic
dimension-linear majorant. For the other copies the unweighted harmonic
cap applies. The two terms give an O(d/log²T) bound at polynomially
growing dimension from any positive Selberg density exponent. A fixed
zero-free half-plane through 7/8 gives the same bound at all dimensions.
-/

noncomputable section
open Filter Complex Set Zeta23
open scoped BigOperators InnerProductSpace

namespace RiemannResearch.Analysis.ActualZeroPhaseMoments
open ActualZeroOrdinate HorizontalEuclideanMoments HorizontalPhaseBootstrap
open ZeroOrdinate ContinuousLinearMap FiniteHyperbolicHarmonicCap

def quadraticCorrectionConstant : ℝ := 64/9 * Real.sqrt (3/2)
theorem quadraticCorrectionConstant_pos : 0 < quadraticCorrectionConstant := by
  unfold quadraticCorrectionConstant
  positivity

theorem landauGram_sub_phaseGram_eq_full_copy_sum (T : ℝ) (d : ℕ) :
    landauGram T d - phaseGram T d = (Ncount 0 T : ℝ)⁻¹ •
      ∑ c : Copies T, copyCoshCorrection d c.1.1 := by
  have hgood (ρ : ℂ) : goodWeight (-1) ρ = 0 := by
    have h : ¬ |ρ.re-1/2| ≤ -1 := not_le.mpr (by linarith only [abs_nonneg (ρ.re-1/2)])
    simp only [goodWeight, if_neg h]
  have hbad (ρ : ℂ) : badRealWeight (-1) ρ = 1 := by
    have h : ¬ |ρ.re-1/2| ≤ -1 := not_le.mpr (by linarith only [abs_nonneg (ρ.re-1/2)])
    simp only [badRealWeight, if_neg h]
  have he : landauGram T d - phaseGram T d = badCorrection T d (-1) := by
    apply euclideanEntry_ext
    intro n m
    rw [euclideanEntry_sub, landauGram_entry, phaseGram_entry, badCorrection_entry, ← mul_sub,
      landau_minus_ordinate_split T (frequencyGap n m) (-1)]
    have hz : weightedCoshCorrection T (frequencyGap n m) (goodWeight (-1)) = 0 := by
      simp [weightedCoshCorrection, ActualZeroOrdinate.sum, hgood]
    rw [hz, zero_add]
  rw [he, badCorrection_eq_copy_sum]
  simp only [hbad, one_smul]

/-- Any per-copy quadratic bound on a central strip transfers to the full
multiplicity-normalized norm with its complementary harmonic tail. -/
theorem landauPhase_norm_le_moment_of_copy_bound (T : ℝ) (d : ℕ) (δ B : ℝ) (hB : 0 ≤ B)
    (hcopy : ∀ ρ ∈ cutoff T, |ρ.re-1/2| ≤ δ → ‖copyCoshCorrection d ρ‖ ≤ B*(ρ.re-1/2)^2) :
    ‖landauGram T d - phaseGram T d‖ ≤ B * displacementMoment T 2 +
      strictTail T δ / (Ncount 0 T : ℝ) * harmonicHyperbolicCap d := by
  let κ := (Ncount 0 T : ℝ)⁻¹
  let A := landauGram T d - phaseGram T d
  let E := badCorrection T d δ
  have hκ : 0 ≤ κ := by dsimp [κ]; positivity
  have hcentral : ‖A - E‖ ≤ B * displacementMoment T 2 := by
    change ‖landauGram T d - phaseGram T d - badCorrection T d δ‖ ≤ _
    rw [landauGram_sub_phaseGram_eq_full_copy_sum, badCorrection_eq_copy_sum,
      ← smul_sub, ← Finset.sum_sub_distrib, norm_smul, Real.norm_eq_abs, abs_of_nonneg hκ]
    calc
      _ ≤ κ * ∑ c : Copies T, ‖copyCoshCorrection d c.1.1 -
          badRealWeight δ c.1.1 • copyCoshCorrection d c.1.1‖ :=
        mul_le_mul_of_nonneg_left (_root_.norm_sum_le _ _) hκ
      _ ≤ κ * ∑ c : Copies T, B * copyDisplacement T c ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hκ
        apply Finset.sum_le_sum
        intro c _
        by_cases hc : |c.1.1.re-1/2| ≤ δ
        · simp only [badRealWeight, if_pos hc, zero_smul, sub_zero, copyDisplacement, sq_abs]
          exact hcopy c.1.1 c.1.2 hc
        · simp only [badRealWeight, if_neg hc, one_smul, sub_self, norm_zero]
          exact mul_nonneg hB (sq_nonneg _)
      _ = _ := by rw [← Finset.mul_sum]; dsimp [κ, displacementMoment]; ring
  have hfar := badCorrection_norm_le_harmonic T d δ
  exact (show ‖A‖ ≤ ‖A-E‖ + ‖E‖ by simpa only [sub_add_cancel] using norm_add_le (A-E) E).trans
    (add_le_add hcentral hfar)

/-- The explicit finite budget at displacement 3/8 is uniform in every
height and dimension, including empty windows. -/
theorem landauPhase_norm_le_secondMoment_harmonic (T : ℝ) (d : ℕ) :
    ‖landauGram T d - phaseGram T d‖ ≤
      quadraticCorrectionConstant * (d : ℝ) * displacementMoment T 2 +
      strictTail T (3/8) / (Ncount 0 T : ℝ) * harmonicHyperbolicCap d :=
  landauPhase_norm_le_moment_of_copy_bound T d (3/8) _ (mul_nonneg quadraticCorrectionConstant_pos.le (Nat.cast_nonneg _))
    (fun ρ _ hρ => copyCoshCorrection_norm_le_quadratic d ρ hρ)

theorem landauPhase_norm_le_secondMoment_of_halfPlane {B : ℝ} (hZ : ZetaZeroFreeHalfPlane B)
    (hB : B ≤ 7/8) (T : ℝ) (d : ℕ) :
    ‖landauGram T d - phaseGram T d‖ ≤ quadraticCorrectionConstant * (d : ℝ) * displacementMoment T 2 := by
  have h := landauPhase_norm_le_secondMoment_harmonic T d
  rw [strictTail_eq_zero_of_zeroFreeHalfPlane hZ T (3/8) (by linarith only [hB]),
    zero_div, zero_mul, add_zero] at h
  exact h

private theorem selberg_second_and_far {a : ℝ} (ha : 0 < a) (hD : UniformSelbergDensity a) :
    ∃ C F : ℝ, 0 < C ∧ 0 < F ∧ ∀ᶠ T : ℝ in atTop,
      displacementMoment T 2 ≤ C / (Real.log T)^2 ∧
        strictTail T (3/8) / (Ncount 0 T : ℝ) ≤ F * T ^ (-3*a/8) := by
  obtain ⟨K,hK,hM⟩ := exists_selberg_displacementMoment_bound ha hD
  obtain ⟨F,H,hF,hH,hD⟩ := hD
  let k : ℝ := 1 / (16 * Real.pi)
  have hk : 0 < k := by dsimp [k]; positivity
  refine ⟨(2*K+1)/a^2, 2*F/k + 1, by positivity, by positivity, ?_⟩
  filter_upwards [hM, eventually_count_ge_log, eventually_ge_atTop H] with T hm hN hT
  have hT1 := hH.trans_le hT
  have hTp := zero_lt_one.trans hT1
  have hL := Real.log_pos hT1
  constructor
  · have h := hm 1
    norm_num at h
    apply (le_div_iff₀ (sq_pos_of_pos hL)).mpr
    apply (le_div_iff₀ (sq_pos_of_pos ha)).mpr
    nlinarith only [h]
  · have ht := strictTail_of_selbergDensity T F a (3/8) hTp ⟨by norm_num, by norm_num⟩ (hD T hT)
    have hn := (show 0 < k*T*Real.log T by positivity).trans_le hN
    have he : Real.exp (-(a*Real.log T)*(3/8)) = T ^ (-3*a/8) := by
      rw [Real.rpow_def_of_pos hTp]; congr 1; ring
    rw [he] at ht
    apply (div_le_iff₀ hn).mpr
    have h := mul_le_mul_of_nonneg_left hN (show 0 ≤ (2*F/k+1) * T ^ (-3*a/8) by positivity)
    apply ht.trans (le_trans _ h)
    have heq : (2*F/k+1)*T^(-3*a/8)*(k*T*Real.log T) =
      2*F*T*Real.log T*T^(-3*a/8) + k*T*Real.log T*T^(-3*a/8) := by field_simp [hk.ne']
    rw [heq]
    linarith only [show 0 ≤ k*T*Real.log T*T^(-3*a/8) by positivity]

/-- The full norm estimate, including the explicit far count and its
unrestricted finite-dimensional harmonic cap. -/
theorem landauPhase_norm_selberg_dimension_profile {a : ℝ} (ha : 0 < a) (hD : UniformSelbergDensity a) :
    ∃ C F : ℝ, 0 < C ∧ 0 < F ∧ ∀ᶠ T : ℝ in atTop, ∀ d : ℕ,
      ‖landauGram T d - phaseGram T d‖ ≤ C * (d : ℝ) / (Real.log T)^2 +
        F * T ^ (-3*a/8) * harmonicHyperbolicCap d := by
  obtain ⟨C,F,hC,hF,h⟩ := selberg_second_and_far ha hD
  refine ⟨quadraticCorrectionConstant*C,F,mul_pos quadraticCorrectionConstant_pos hC,hF,?_⟩
  filter_upwards [h] with T hT
  intro d
  refine (landauPhase_norm_le_secondMoment_harmonic T d).trans (add_le_add ?_ ?_)
  · apply (mul_le_mul_of_nonneg_left hT.1 (mul_nonneg quadraticCorrectionConstant_pos.le (Nat.cast_nonneg d))).trans_eq
    ring
  · exact mul_le_mul_of_nonneg_right hT.2 (harmonicHyperbolicCap_nonneg _)

/-- The fixed zero-free half-plane removes the restriction on dimension
altogether. The actual continuum-contact half-plane satisfies B < 7/8. -/
theorem landauPhase_norm_selberg_all_dimensions {a B : ℝ} (ha : 0 < a) (hD : UniformSelbergDensity a)
    (hZ : ZetaZeroFreeHalfPlane B) (hB : B ≤ 7/8) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ d : ℕ,
      ‖landauGram T d - phaseGram T d‖ ≤ C * (d : ℝ) / (Real.log T)^2 := by
  obtain ⟨C,F,hC,_,h⟩ := selberg_second_and_far ha hD
  refine ⟨quadraticCorrectionConstant*C,mul_pos quadraticCorrectionConstant_pos hC,?_⟩
  filter_upwards [h] with T hT
  intro d
  apply (landauPhase_norm_le_secondMoment_of_halfPlane hZ hB T d).trans
  apply (mul_le_mul_of_nonneg_left hT.1 (mul_nonneg quadraticCorrectionConstant_pos.le (Nat.cast_nonneg d))).trans_eq
  ring

/-- Any polynomial dimension range consumes only a negligible part of
the far term. The constant is common to every allowed dimension. -/
theorem landauPhase_norm_selberg_polynomial_dimensions {a : ℝ} (ha : 0 < a)
    (hD : UniformSelbergDensity a) (b : ℝ) (hb : 0 ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ d : ℕ, 1 ≤ d → (d : ℝ) ≤ T^b →
      ‖landauGram T d - phaseGram T d‖ ≤ C * (d : ℝ) / (Real.log T)^2 := by
  obtain ⟨C,F,hC,hF,h⟩ := landauPhase_norm_selberg_dimension_profile ha hD
  refine ⟨C + F*(1+b), by positivity, ?_⟩
  have hneg : -3*a/8 < 0 := by linarith only [ha]
  filter_upwards [h, eventually_rpow_le_log_neg hneg 3, eventually_gt_atTop (Real.exp 1)] with T hT ht hTe
  have hTp := (Real.exp_pos _).trans hTe
  have hL : 1 < Real.log T := by simpa using Real.log_lt_log (Real.exp_pos _) hTe
  have hLp := zero_lt_one.trans hL
  rw [Real.rpow_neg hLp.le] at ht
  norm_num only [Real.rpow_ofNat] at ht
  intro d hd hdT
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hld := Real.log_le_log (zero_lt_one.trans_le hdR) hdT
  rw [Real.rpow_def_of_pos hTp, Real.log_exp] at hld
  have hcap : harmonicHyperbolicCap d ≤ (d : ℝ) * ((1+b)*Real.log T) :=
    (harmonicHyperbolicCap_le_card_log d hd).trans (mul_le_mul_of_nonneg_left (by linarith only [hL,hld]) (Nat.cast_nonneg _))
  have hfar := mul_le_mul (mul_le_mul_of_nonneg_left ht hF.le) hcap (harmonicHyperbolicCap_nonneg d) (by positivity)
  apply (hT d).trans ((add_le_add le_rfl hfar).trans_eq ?_)
  field_simp [hLp.ne']

end RiemannResearch.Analysis.ActualZeroPhaseMoments
