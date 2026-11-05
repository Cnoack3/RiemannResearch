/-
Copyright (c) 2026 Gershon Bialer and the RiemannResearch contributors.
Released under the Apache License, Version 2.0.
-/
import RiemannResearch.NumberTheory.PrimeNumberTheorem.MertensLogSquaredTail
import Mathlib.NumberTheory.LSeries.Dirichlet
import RiemannResearch.NumberTheory.PrimeNumberTheorem.Defs
import RiemannResearch.NumberTheory.PrimeNumberTheorem.ClassicalMertensReciprocalRectangle

/-!
# A square-root-logarithm bound for the ordinary Mertens function

The inverse Mellin transform of the smoothed Möbius sum has kernel 1/ζ.
Extending 1/ζ by zero at 1 makes the singularity removable, so the
rectangle shift contributes no residue. Taking log T = √(a log X) balances truncation against the shifted edge.

The smoothing, contour shift and boundary estimates adapt the Apache-2.0
work of Gershon Bialer, `MathExtras/NumberTheory/PrimeCounting`, at
https://github.com/gersh/ternary-goldbach-lean/tree/27df23af6a712895f22204d0d81102baa74f0ebe/MathExtras/NumberTheory/PrimeCounting .
We retain only lemmas used for the ordinary Mertens bound and supply the
adjustable contour width from our classical reciprocal-zeta rectangle.
The exact logarithmic tail integral is proved in MertensLogSquaredTail.
The underlying smoothed Perron and rectangle calculus come from the
repository’s existing PrimeNumberTheoremAnd modules.
-/
noncomputable section
open _root_.Filter _root_.Asymptotics _root_.Finset _root_.Complex _root_.Real _root_.MeasureTheory
open ArithmeticFunction (vonMangoldt)
open scoped BigOperators ArithmeticFunction.Moebius Topology
set_option maxHeartbeats 2000000
set_option linter.style.longLine false

namespace RiemannResearch.NumberTheory.PrimeNumberTheorem.Quantitative.MobiusContour

local notation "ζ" => riemannZeta
local notation "𝓜" => mellin

/-- Width of the certified classical rectangle for 1/ζ. -/
noncomputable def contourWidth : ℝ := classical_mertens_reciprocal_rectangle.choose

theorem contourWidth_pos : 0 < contourWidth :=
  classical_mertens_reciprocal_rectangle.choose_spec.1.1

theorem contourWidth_small : contourWidth < (1 / 42 : ℝ) :=
  classical_mertens_reciprocal_rectangle.choose_spec.1.2

noncomputable def contourLogWeight (T : ℝ) : ℝ := (1 + Real.log T)^2

noncomputable def contourTailScale (T : ℝ) : ℝ := T / contourLogWeight T

private theorem contourLogWeight_pos {T : ℝ} (hT : 3 < T) : 0 < contourLogWeight T := by
  have ht := Real.log_pos (by linarith : 1 < T)
  exact sq_pos_of_pos (by linarith : 0 < 1 + Real.log T)

private theorem contourTailScale_pos {T : ℝ} (hT : 3 < T) : 0 < contourTailScale T :=
  div_pos (by linarith) (contourLogWeight_pos hT)

private theorem contour_log_weight_dominates {T : ℝ} (hT : 3 < T) :
    (Real.log (2 + T))^2 ≤ contourLogWeight T := by
  have hTpos : 0 < T := by linarith
  have hl : Real.log (2 + T) ≤ 1 + Real.log T := calc
    _ ≤ Real.log (2 * T) := Real.log_le_log (by linarith) (by linarith)
    _ = Real.log 2 + Real.log T := Real.log_mul (by norm_num) hTpos.ne'
    _ ≤ _ := by linarith [Real.log_two_lt_d9]
  exact pow_le_pow_left₀ (Real.log_nonneg (by linarith)) hl 2

private theorem contour_log_tail_bound : ∃ C > 0, ∀ T : ℝ, 3 < T →
    (∫ t in Set.Ici T, (Real.log t)^2 / t^2) ≤ C / contourTailScale T := by
  refine ⟨2, by norm_num, fun T hT => (mertens_log_sq_tail_le hT).trans_eq ?_⟩
  change 2 * contourLogWeight T / T = 2 / (T / contourLogWeight T)
  field_simp [(contourLogWeight_pos hT).ne', (show 0 < T by linarith).ne'] <;> ring

noncomputable def smoothedMobiusIntegrand
    (SmoothingF : ℝ → ℝ) (ε : ℝ) (X : ℝ) : ℂ → ℂ :=
  fun s ↦ (riemannZeta s)⁻¹ *
    mellin (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) s * (X : ℂ) ^ s

noncomputable def M1New (SmoothingF : ℝ → ℝ) (ε X T : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t : ℝ in Set.Iic (-T),
      smoothedMobiusIntegrand SmoothingF ε X ((1 + (Real.log X)⁻¹) + t * I)))

noncomputable def M2New (SmoothingF : ℝ → ℝ) (ε X T σ' : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ₀ in σ'..(1 + (Real.log X)⁻¹),
    smoothedMobiusIntegrand SmoothingF ε X (σ₀ - T * I)))

noncomputable def M3New (SmoothingF : ℝ → ℝ) (ε X T σ' : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t : ℝ in Set.Icc (-T) T,
      smoothedMobiusIntegrand SmoothingF ε X (σ' + t * I)))

noncomputable def M4New (SmoothingF : ℝ → ℝ) (ε X T σ' : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ₀ in σ'..(1 + (Real.log X)⁻¹),
    smoothedMobiusIntegrand SmoothingF ε X (σ₀ + T * I)))

noncomputable def M5New (SmoothingF : ℝ → ℝ) (ε X T : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t : ℝ in Set.Ici T,
      smoothedMobiusIntegrand SmoothingF ε X ((1 + (Real.log X)⁻¹) + t * I)))

def MobiusBoundaryBoundsCorrectProp : Prop :=
  ∀ {SmoothingF : ℝ → ℝ},
    Function.support SmoothingF ⊆ Set.Icc (1 / 2) 2 →
    ContDiff ℝ 1 SmoothingF →
    ∃ Cfar > 0, ∃ Ccut > 0,
      ∀ {ε X T : ℝ}, 0 < ε → ε < 1 → 3 < X → 3 < T →
        let σ' := 1 - contourWidth / Real.log T
        ‖M1New SmoothingF ε X T‖ ≤ Cfar * (X / (ε * contourTailScale T)) ∧
        ‖M5New SmoothingF ε X T‖ ≤ Cfar * (X / (ε * contourTailScale T)) ∧
        ‖M2New SmoothingF ε X T σ'‖ ≤ Cfar * (X / (ε * contourTailScale T)) ∧
        ‖M3New SmoothingF ε X T σ'‖ ≤ Ccut * (X ^ (1 - contourWidth / Real.log T) * contourLogWeight T) / ε ∧
        ‖M4New SmoothingF ε X T σ'‖ ≤ Cfar * (X / (ε * contourTailScale T))

noncomputable def smoothedMobius (SmoothingF : ℝ → ℝ) (ε : ℝ) (X : ℝ) : ℂ :=
  VerticalIntegral' (smoothedMobiusIntegrand SmoothingF ε X) ((1 : ℝ) + (Real.log X)⁻¹)

/-- A fixed interior coefficient for the unconditional, unweighted Mertens bound. -/
noncomputable def contourRate : ℝ := Real.sqrt contourWidth / 4

theorem contourRate_pos : 0 < contourRate :=
  div_pos (Real.sqrt_pos.mpr contourWidth_pos) (by norm_num)

/-- Replacing the logarithmic weights on both contour edges by `√T`
forces this upper bound on the coefficient of the resulting estimate. -/
theorem contourRate_upper_of_edge_bounds {a s c : ℝ} (ha : 0 ≤ a) (hs : 0 < s)
    (hc : 0 ≤ c) (hfar : 2*c ≤ s/2) (hcut : 2*c ≤ a/s-s/2) :
    c ≤ Real.sqrt a / 4 := by
  have h₁ : 4*c ≤ s := by linarith
  have h₂ : (2*c + s/2)*s ≤ a :=
    (le_div_iff₀ hs).mp (by linarith only [hcut])
  have h₃ : (4*c)*(4*c) ≤ (2*c + s/2)*s :=
    mul_le_mul (by linarith only [hfar]) h₁ (by positivity) (by positivity)
  by_contra! h
  have h₄ : Real.sqrt a < 4*c := by linarith
  have h₅ := mul_self_lt_mul_self (Real.sqrt_nonneg a) h₄
  nlinarith only [h₂,h₃,h₅,Real.sq_sqrt ha]

noncomputable def contourEndpoint : ℝ := Real.sqrt contourWidth / 2

theorem contourEndpoint_pos : 0 < contourEndpoint :=
  div_pos (Real.sqrt_pos.mpr contourWidth_pos) (by norm_num)

noncomputable def mertens_eps (X : ℝ) : ℝ :=
  (1 + Real.sqrt contourWidth * Real.sqrt (Real.log X)) *
    Real.exp (-contourEndpoint * Real.sqrt (Real.log X))

def MobiusPullPropPunctured : Prop :=
  ∀ {SmoothingF : ℝ → ℝ} {ε : ℝ}, 0 < ε → ε < 1 →
    ∀ {X : ℝ}, 3 < X → ∀ {T : ℝ}, 0 < T → ∀ {σ' : ℝ}, 0 < σ' → σ' < 1 →
      Function.support SmoothingF ⊆ Set.Icc (1 / 2) 2 →
      (∀ x > 0, 0 ≤ SmoothingF x) →
      (∫ x in Set.Ioi (0:ℝ), SmoothingF x / x = 1) →
      ContDiff ℝ 1 SmoothingF →
      HolomorphicOn (smoothedMobiusIntegrand SmoothingF ε X)
        (((Set.Icc σ' 2) ×ℂ (Set.Icc (-T) T)) \ {1}) →
      Integrable (fun t : ℝ ↦
        smoothedMobiusIntegrand SmoothingF ε X ((1 + (Real.log X)⁻¹) + t * I)) →
      smoothedMobius SmoothingF ε X =
        M1New SmoothingF ε X T - M2New SmoothingF ε X T σ' +
        M3New SmoothingF ε X T σ' + M4New SmoothingF ε X T σ' + M5New SmoothingF ε X T

theorem inv_riemannZeta_tendsto_zero_near_one :
    Tendsto (fun s => (riemannZeta s)⁻¹) (𝓝[≠] (1 : ℂ)) (𝓝 0) := by
  have hres : Tendsto (fun s => (s - 1) * riemannZeta s) (𝓝[≠] 1) (𝓝 1) :=
    riemannZeta_residue_one
  have hinv : Tendsto (fun s => ((s - 1) * riemannZeta s)⁻¹) (𝓝[≠] 1) (𝓝 1) := by
    have := hres.inv₀ (by norm_num : (1 : ℂ) ≠ 0)
    simpa using this
  have hsub : Tendsto (fun s : ℂ => s - 1) (𝓝[≠] 1) (𝓝 0) := by
    have : Tendsto (fun s : ℂ => s - 1) (𝓝 1) (𝓝 (1 - 1)) :=
      (continuous_id.sub continuous_const).tendsto 1
    simpa using this.mono_left nhdsWithin_le_nhds
  have hprod : Tendsto (fun s : ℂ => (s - 1) * ((s - 1) * riemannZeta s)⁻¹)
      (𝓝[≠] 1) (𝓝 (0 * 1)) := hsub.mul hinv
  rw [zero_mul] at hprod
  apply hprod.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ hs1, one_mul]

theorem smoothedMobiusIntegrand_isBigO_one_near_one
    {SmoothingF : ℝ → ℝ} {ε : ℝ} (εpos : 0 < ε) (εlt1 : ε < 1)
    (suppF : Function.support SmoothingF ⊆ Set.Icc (1 / 2) 2)
    (nonnegF : ∀ x > 0, 0 ≤ SmoothingF x)
    (massF : ∫ x in Set.Ioi (0:ℝ), SmoothingF x / x = 1)
    (diffF : ContDiff ℝ 1 SmoothingF)
    {X : ℝ} (hX : 0 < X) :
    (smoothedMobiusIntegrand SmoothingF ε X) =O[𝓝[≠] (1 : ℂ)] (1 : ℂ → ℂ) := by
  have hmellin1 : DifferentiableAt ℂ
      (fun z => mellin (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) z) (1 : ℂ) :=
    Smooth1MellinDifferentiable diffF suppF ⟨εpos, εlt1⟩ nonnegF massF (by norm_num)
  have hcpow1 : ContinuousAt (fun z : ℂ => (X : ℂ) ^ z) (1 : ℂ) :=
    continuousAt_const_cpow (by exact_mod_cast hX.ne')
  have hg : Tendsto (fun s => mellin (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) s * (X : ℂ) ^ s)
      (𝓝 (1 : ℂ)) (𝓝 (mellin (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) 1 * (X : ℂ) ^ (1 : ℂ))) :=
    (hmellin1.continuousAt.mul hcpow1).tendsto
  have hkernel : Tendsto (fun s => (riemannZeta s)⁻¹) (𝓝[≠] (1 : ℂ)) (𝓝 0) :=
    inv_riemannZeta_tendsto_zero_near_one
  have hprod : Tendsto (smoothedMobiusIntegrand SmoothingF ε X) (𝓝[≠] (1 : ℂ))
      (𝓝 (0 * (mellin (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) 1 * (X : ℂ) ^ (1 : ℂ)))) := by
    have := hkernel.mul (hg.mono_left nhdsWithin_le_nhds)
    apply this.congr
    intro s; simp only [smoothedMobiusIntegrand]; ring
  rw [zero_mul] at hprod
  exact hprod.isBigO_one ℂ

theorem mobiusPullPropPunctured_holds : MobiusPullPropPunctured := by
  intro SmoothingF ε ε_pos ε_lt_one X X_gt T T_pos σ' σ'_pos σ'_lt_one
    suppSmoothingF SmoothingFnonneg mass_one ContDiffSmoothingF holoOn hInt
  have X_eq_gt_one : (1 : ℝ) < 1 + (Real.log X)⁻¹ := by
    nth_rewrite 1 [← add_zero (1 : ℝ)]
    have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
    have : 0 < (Real.log X)⁻¹ := by positivity
    linarith
  have hlogX_gt1 : (1 : ℝ) < Real.log X := by
    rw [show (1:ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
    apply Real.log_lt_log (Real.exp_pos 1)
    have := Real.exp_one_lt_d9; linarith
  have X_eq_lt_two : (1 + (Real.log X)⁻¹) < 2 := by
    rw [← one_add_one_eq_two]; gcongr; exact inv_lt_one_of_one_lt₀ hlogX_gt1
  have X_eq_le_two : 1 + (Real.log X)⁻¹ ≤ 2 := X_eq_lt_two.le
  have temp : ↑(1 + (Real.log X)⁻¹) = (1 : ℂ) + ↑(Real.log X)⁻¹ := by simp
  set fTempRR : ℝ → ℝ → ℂ := fun x ↦ fun y ↦
    smoothedMobiusIntegrand SmoothingF ε X ((x : ℝ) + (y : ℝ) * I) with hfTempRR
  set fTempC : ℂ → ℂ := fun z ↦ fTempRR z.re z.im with hfTempC
  have hfC : ∀ s : ℂ, fTempC s = smoothedMobiusIntegrand SmoothingF ε X s := by
    intro s; rw [hfTempC, hfTempRR]; simp [re_add_im]
  have pInRectangleInterior :
      (Rectangle (σ' - ↑T * I) (1 + (Real.log X)⁻¹ + T * I) ∈ nhds (1 : ℂ)) := by
    refine rectangle_mem_nhds_iff.mpr <| mem_reProdIm.mpr ?_
    have hre_z : (σ' - ↑T * I).re = σ' := by simp
    have him_z : (σ' - ↑T * I).im = -T := by simp
    have hre_w : ((1 : ℂ) + ↑(Real.log X)⁻¹ + ↑T * I).re = 1 + (Real.log X)⁻¹ := by simp
    have him_w : ((1 : ℂ) + ↑(Real.log X)⁻¹ + ↑T * I).im = T := by simp
    refine ⟨?_, ?_⟩
    · show ((1 : ℂ)).re ∈ Set.uIoo (σ' - ↑T * I).re ((1 : ℂ) + ↑(Real.log X)⁻¹ + ↑T * I).re
      rw [hre_z, hre_w, Set.uIoo, inf_eq_left.mpr (by linarith), sup_eq_right.mpr (by linarith)]
      exact Set.mem_Ioo.mpr ⟨by simp [σ'_lt_one], by simp; linarith⟩
    · show ((1 : ℂ)).im ∈ Set.uIoo (σ' - ↑T * I).im ((1 : ℂ) + ↑(Real.log X)⁻¹ + ↑T * I).im
      rw [him_z, him_w, Set.uIoo, inf_eq_left.mpr (by linarith), sup_eq_right.mpr (by linarith)]
      exact Set.mem_Ioo.mpr ⟨by simp; linarith, by simp; linarith⟩
  have hzero : RectangleIntegral' fTempC (σ' - ↑T * I) (1 + ↑(Real.log X)⁻¹ + T * I) = 0 := by
    have key := ResidueTheoremOnRectangleWithSimplePole'
      (f := fTempC) (z := σ' - ↑T * I) (w := 1 + ↑(Real.log X)⁻¹ + T * I)
      (p := (1 : ℂ)) (A := (0 : ℂ)) ?_ ?_ ?_ ?_ ?_
    · exact key
    ·
      simp only [sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
        sub_zero, add_re, one_re, inv_re, normSq_ofReal, div_self_mul_self', add_zero, ofReal_inv]
      linarith
    ·
      simp only [sub_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
        zero_sub, add_im, one_im, inv_im, neg_zero, zero_div, zero_add, neg_neg, ofReal_inv]
      linarith
    ·
      exact pInRectangleInterior
    ·
      have hsub : (Rectangle (σ' - ↑T * I) (1 + ↑(Real.log X)⁻¹ + T * I) \ {(1 : ℂ)})
          ⊆ (((Set.Icc σ' 2) ×ℂ (Set.Icc (-T) T)) \ {(1 : ℂ)}) := by
        apply Set.diff_subset_diff_left
        intro s hs
        rw [Rectangle, Complex.mem_reProdIm] at hs
        rw [Complex.mem_reProdIm]
        have hre_z : (σ' - ↑T * I).re = σ' := by simp
        have hre_w : ((1 : ℂ) + ↑(Real.log X)⁻¹ + ↑T * I).re = 1 + (Real.log X)⁻¹ := by simp
        have him_z : (σ' - ↑T * I).im = -T := by simp
        have him_w : ((1 : ℂ) + ↑(Real.log X)⁻¹ + ↑T * I).im = T := by simp
        have hre := hs.1
        have him := hs.2
        rw [hre_z, hre_w, Set.uIcc_of_le (by linarith)] at hre
        rw [him_z, him_w, Set.uIcc_of_le (by linarith)] at him
        refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
        · exact hre.1
        · exact le_trans hre.2 (by linarith)
        · exact him.1
        · exact him.2
      intro s hs
      have hdiff : DifferentiableWithinAt ℂ (smoothedMobiusIntegrand SmoothingF ε X)
          (Rectangle (σ' - ↑T * I) (1 + ↑(Real.log X)⁻¹ + T * I) \ {(1 : ℂ)}) s :=
        (holoOn s (hsub hs)).mono hsub
      exact hdiff.congr (fun z _ => hfC z) (hfC s)
    ·
      have hbig := smoothedMobiusIntegrand_isBigO_one_near_one
        ε_pos ε_lt_one suppSmoothingF SmoothingFnonneg mass_one ContDiffSmoothingF
        (X := X) (by linarith : (0:ℝ) < X)
      have hfun : fTempC = smoothedMobiusIntegrand SmoothingF ε X := funext hfC
      have hsub_eq : (fTempC - fun s : ℂ => (0 : ℂ) / (s - 1))
          = smoothedMobiusIntegrand SmoothingF ε X := by
        funext s; simp [hfC s]
      rw [hsub_eq]; exact hbig
  have hpiI : (2 * (π : ℂ) * I) ≠ 0 := by
    have h2 : (2 : ℂ) ≠ 0 := by norm_num
    have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero (mul_ne_zero h2 hpi) Complex.I_ne_zero
  rw [RectangleIntegral', RectangleIntegral, HIntegral, HIntegral, VIntegral, VIntegral,
    smul_eq_mul, mul_eq_zero] at hzero
  rcases hzero with hzero | hbracket
  · exact absurd hzero (by simp [hpiI])
  simp only [hfC] at hbracket
  have hre_z : (σ' - ↑T * I).re = σ' := by simp
  have him_z : (σ' - ↑T * I).im = -T := by simp
  have hre_w : ((1 : ℂ) + ↑(Real.log X)⁻¹ + ↑T * I).re = 1 + (Real.log X)⁻¹ := by simp
  have him_w : ((1 : ℂ) + ↑(Real.log X)⁻¹ + ↑T * I).im = T := by simp
  rw [hre_z, him_z, hre_w, him_w] at hbracket
  have hTle : (-T : ℝ) ≤ T := by linarith
  have hIccL : (∫ y in Set.Icc (-T) T, smoothedMobiusIntegrand SmoothingF ε X (↑σ' + ↑y * I))
      = ∫ y in -T..T, smoothedMobiusIntegrand SmoothingF ε X (↑σ' + ↑y * I) := by
    rw [intervalIntegral.integral_of_le hTle, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  unfold smoothedMobius VerticalIntegral'
  rw [verticalIntegral_split_three (a := -T) (b := T)]
  swap
  · refine hInt.congr (Filter.Eventually.of_forall fun t => ?_)
    rw [temp]
  unfold M1New M2New M3New M4New M5New VIntegral
  rw [hIccL]
  simp only [temp, smul_eq_mul, ofReal_neg, neg_mul, sub_eq_add_neg, mul_comm I] at hbracket ⊢
  linear_combination (1 / (2 * (π : ℂ) * I)) * hbracket

noncomputable def mertens_T (X : ℝ) : ℝ :=
  Real.exp (Real.sqrt contourWidth * Real.sqrt (Real.log X))

private theorem mertens_eps_mem : ∀ᶠ X in atTop, mertens_eps X ∈ Set.Ioo 0 1 := by
  have hlim : Tendsto (fun X : ℝ => contourEndpoint * Real.sqrt (Real.log X)) atTop atTop :=
    Tendsto.const_mul_atTop contourEndpoint_pos (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop)
  filter_upwards [hlim.eventually_gt_atTop 4] with X hX
  let y := contourEndpoint * Real.sqrt (Real.log X)
  have hy : 4 < y := hX
  have hz : Real.sqrt contourWidth * Real.sqrt (Real.log X) = 2 * y := by
    dsimp [y, contourEndpoint]
    ring
  have hexp : 1 + 2 * y < Real.exp y := by
    have h := pow_le_pow_left₀ (by linarith : 0 ≤ y / 2 + 1) (Real.add_one_le_exp (y/2)) 2
    have heq : Real.exp (y/2)^2 = Real.exp y := by rw [sq, ← Real.exp_add]; congr 1 <;> ring
    rw [heq] at h
    nlinarith only [h, mul_pos (by linarith : 0 < y) (by linarith : 0 < y - 4)]
  have he : mertens_eps X = (1 + 2 * y) / Real.exp y := by
    rw [mertens_eps, hz, neg_mul, Real.exp_neg, div_eq_mul_inv]
  rw [he]
  exact ⟨div_pos (by linarith) (Real.exp_pos _), (div_lt_one (Real.exp_pos _)).mpr hexp⟩

/-- The exact logarithmic tail and the shifted boundary give the same error
as removing the smoothing at the balanced truncation height. -/
private theorem mertens_boundary_balance {X : ℝ} (hX : 1 < X) :
    X / (mertens_eps X * contourTailScale (mertens_T X)) = X * mertens_eps X ∧
    X ^ (1 - contourWidth / Real.log (mertens_T X)) * contourLogWeight (mertens_T X) /
      mertens_eps X = X * mertens_eps X := by
  let u := Real.sqrt contourWidth
  let v := Real.sqrt (Real.log X)
  let w := 1 + u * v
  let E := Real.exp ((u / 2) * v)
  have hu : 0 < u := Real.sqrt_pos.mpr contourWidth_pos
  have hv : 0 < v := Real.sqrt_pos.mpr (Real.log_pos hX)
  have hw : 0 < w := by dsimp only [w]; positivity
  have hE : 0 < E := Real.exp_pos _
  have hXpos : 0 < X := by linarith
  have hlogT : Real.log (mertens_T X) = u * v := Real.log_exp _
  have hε : mertens_eps X = w / E := by
    change (1 + u * v) * Real.exp (-(u / 2) * v) = (1 + u * v) / Real.exp ((u / 2) * v)
    simp only [neg_mul, Real.exp_neg, div_eq_mul_inv]
  have hT : mertens_T X = E ^ 2 := by
    change Real.exp (u * v) = Real.exp ((u / 2) * v) ^ 2
    rw [sq, ← Real.exp_add]
    congr 1 <;> ring
  have hW : contourLogWeight (mertens_T X) = w ^ 2 := by
    rw [contourLogWeight, hlogT]
  have hbalance : Real.log X * (contourWidth / (u * v)) = u * v := by
    have hA : contourWidth = u ^ 2 := (Real.sq_sqrt contourWidth_pos.le).symm
    have hL : Real.log X = v ^ 2 := (Real.sq_sqrt (Real.log_nonneg hX.le)).symm
    rw [hL, hA]
    field_simp [hu.ne', hv.ne'] <;> ring
  have hpower : X ^ (1 - contourWidth / Real.log (mertens_T X)) = X / mertens_T X := by
    rw [Real.rpow_sub hXpos, Real.rpow_one, Real.rpow_def_of_pos hXpos, hlogT, hbalance] <;> rfl
  rw [hpower, contourTailScale, hW, hε, hT]
  constructor <;> field_simp [hw.ne', hE.ne'] <;> ring

theorem mobiusIntegrand_holomorphicOn_punctured_box
    {SmoothingF : ℝ → ℝ} {ε : ℝ} (εpos : 0 < ε) (εlt1 : ε < 1)
    (suppF : Function.support SmoothingF ⊆ Set.Icc (1 / 2) 2)
    (nonnegF : ∀ x > 0, 0 ≤ SmoothingF x)
    (massF : ∫ x in Set.Ioi (0:ℝ), SmoothingF x / x = 1)
    (diffF : ContDiff ℝ 1 SmoothingF)
    {T₀ : ℝ} (hT₀ : 3 ≤ T₀)
    (hzne : ∀ (T : ℝ), T₀ ≤ T →
      ∀ s ∈ (((Set.Icc ((1 : ℝ) - contourWidth / Real.log T) 2) ×ℂ (Set.Icc (-T) T)) \ {1}),
        riemannZeta s ≠ 0)
    {X : ℝ} (hX : 0 < X) {T : ℝ} (hT : T₀ ≤ T) :
    HolomorphicOn (smoothedMobiusIntegrand SmoothingF ε X)
      (((Set.Icc ((1 : ℝ) - contourWidth / Real.log T) 2) ×ℂ (Set.Icc (-T) T)) \ {1}) := by
  have hcontourWidth_pos : 0 < contourWidth := contourWidth_pos
  have hT_ge3 : (3 : ℝ) ≤ T := le_trans hT₀ hT
  have hlogT_pos : 0 < Real.log T := Real.log_pos (by linarith)
  have hFlt1 : contourWidth < 1 := lt_trans contourWidth_small (by norm_num)
  have hlogT_ge1 : (1 : ℝ) ≤ Real.log T := by
    rw [show (1:ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
    apply Real.log_le_log (Real.exp_pos 1)
    have := Real.exp_one_lt_d9; linarith
  have hwindow_pos : 0 < 1 - contourWidth / Real.log T := by
    have hdiv : contourWidth / Real.log T < 1 := by
      rw [div_lt_one hlogT_pos]; linarith
    linarith
  intro s hs
  have hs_ne_one : s ≠ 1 := fun h => hs.2 (by simp [h])
  have hmem := Complex.mem_reProdIm.mp hs.1
  have hre_lb : (1 : ℝ) - contourWidth / Real.log T ≤ s.re := hmem.1.1
  have hre_pos : 0 < s.re := lt_of_lt_of_le hwindow_pos hre_lb
  have hinvζ : DifferentiableAt ℂ (fun z => (riemannZeta z)⁻¹) s :=
    (differentiableAt_riemannZeta hs_ne_one).inv (hzne T hT s hs)
  have hmellin : DifferentiableAt ℂ (fun z => mellin (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) z) s :=
    Smooth1MellinDifferentiable diffF suppF ⟨εpos, εlt1⟩ nonnegF massF hre_pos
  have hcpow : DifferentiableAt ℂ (fun z => (X : ℂ) ^ z) s := by
    apply DifferentiableAt.const_cpow (by fun_prop)
    left; exact_mod_cast hX.ne'
  have : DifferentiableAt ℂ (smoothedMobiusIntegrand SmoothingF ε X) s := by
    unfold smoothedMobiusIntegrand
    exact (hinvζ.mul hmellin).mul hcpow
  exact this.differentiableWithinAt

theorem LSeries_moebius_eq_inv_zeta {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (μ n : ℂ)) s = (ζ s)⁻¹ := by
  have h := LSeries_one_mul_Lseries_moebius hs
  rw [LSeries_one_eq_riemannZeta hs] at h
  apply mul_left_cancel₀ (riemannZeta_ne_zero_of_one_lt_re hs)
  simpa only [mul_inv_cancel₀ (riemannZeta_ne_zero_of_one_lt_re hs)] using h

theorem inv_zeta_bdd_on_vertical_line_gt_one {σ₀ : ℝ} (σ₀_gt : 1 < σ₀) :
    ∃ C > 0, ∀ t : ℝ, ‖(riemannZeta ((σ₀ : ℂ) + t * I))⁻¹‖ ≤ C := by
  set C : ℝ := (∑' n, ‖LSeries.term (fun n => (μ n : ℂ)) (σ₀ : ℂ) n‖) + 1 with hC
  have hC_pos : 0 < C := by
    have : 0 ≤ ∑' n, ‖LSeries.term (fun n => (μ n : ℂ)) (σ₀ : ℂ) n‖ :=
      tsum_nonneg (fun _ => norm_nonneg _)
    rw [hC]; linarith
  refine ⟨C, hC_pos, ?_⟩
  intro t
  set s : ℂ := (σ₀ : ℂ) + t * I with hs
  have hsre : s.re = σ₀ := by simp [hs]
  have hsre_gt : 1 < s.re := by rw [hsre]; exact σ₀_gt
  rw [← LSeries_moebius_eq_inv_zeta hsre_gt]
  have hsum : LSeriesSummable (fun n => (μ n : ℂ)) s :=
    LSeriesSummable_of_bounded_of_one_lt_re (f := fun n => (μ n : ℂ)) (m := 1)
      (fun n _ => by
        rw [Complex.norm_intCast]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one) hsre_gt
  have hterm_eq : ∀ n : ℕ, ‖LSeries.term (fun n => (μ n : ℂ)) s n‖
      = ‖LSeries.term (fun n => (μ n : ℂ)) (σ₀ : ℂ) n‖ := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [LSeries.term]
    · rw [LSeries.term_def _ _ _, LSeries.term_def _ _ _]
      simp only [hn.ne', if_neg, ne_eq, Nat.cast_eq_zero, not_false_eq_true]
      rw [norm_div, norm_div, Complex.norm_natCast_cpow_of_pos hn,
        Complex.norm_natCast_cpow_of_pos hn, hsre, Complex.ofReal_re]
  calc ‖LSeries (fun n => (μ n : ℂ)) s‖
      = ‖∑' n, LSeries.term (fun n => (μ n : ℂ)) s n‖ := rfl
    _ ≤ ∑' n, ‖LSeries.term (fun n => (μ n : ℂ)) s n‖ := norm_tsum_le_tsum_norm hsum.norm
    _ = ∑' n, ‖LSeries.term (fun n => (μ n : ℂ)) (σ₀ : ℂ) n‖ := by
        exact tsum_congr hterm_eq
    _ ≤ C := by rw [hC]; linarith

theorem mobiusIntegrand_integrable_right_line
    {SmoothingF : ℝ → ℝ} {ε : ℝ} (εpos : 0 < ε) (εlt1 : ε < 1)
    {X : ℝ} (hX : 3 < X)
    (suppF : Function.support SmoothingF ⊆ Set.Icc (1 / 2) 2)
    (nonnegF : ∀ x > 0, 0 ≤ SmoothingF x)
    (massF : ∫ x in Set.Ioi (0:ℝ), SmoothingF x / x = 1)
    (diffF : ContDiff ℝ 1 SmoothingF) :
    Integrable (fun t : ℝ ↦
      smoothedMobiusIntegrand SmoothingF ε X ((1 + (Real.log X)⁻¹) + t * I)) := by
  set σ₀ : ℝ := 1 + (Real.log X)⁻¹ with hσ₀
  have σ₀_gt : 1 < σ₀ := by
    rw [hσ₀]; nth_rewrite 1 [← add_zero 1]
    have hlog : 0 < Real.log X := Real.log_pos (by linarith)
    have : 0 < (Real.log X)⁻¹ := by positivity
    linarith
  have hXpos : 0 < X := by linarith
  have hlogX_gt1 : 1 < Real.log X := by
    rw [show (1:ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
    apply Real.log_lt_log (Real.exp_pos 1)
    have := Real.exp_one_lt_d9; linarith
  have σ₀_le_2 : σ₀ ≤ 2 := by
    rw [hσ₀, ← one_add_one_eq_two]; gcongr
    exact (inv_lt_one_of_one_lt₀ hlogX_gt1).le
  obtain ⟨C, C_pos, hC⟩ := inv_zeta_bdd_on_vertical_line_gt_one σ₀_gt
  have hMint : Integrable (fun (t : ℝ) ↦
      mellin (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) ((σ₀ : ℂ) + (t : ℂ) * I)) volume :=
    SmoothedChebyshevDirichlet_aux_integrable diffF nonnegF suppF massF εpos εlt1 σ₀_gt σ₀_le_2
  set c : ℝ := C * X ^ σ₀ with hc
  have hbdd : ∀ t : ℝ, ‖(riemannZeta ((σ₀ : ℂ) + (t : ℂ) * I))⁻¹
      * (X : ℂ) ^ ((σ₀ : ℂ) + (t : ℂ) * I)‖ ≤ c := by
    intro t
    rw [Complex.norm_mul, hc]
    gcongr
    · exact hC t
    · rw [Complex.norm_cpow_eq_rpow_re_of_pos hXpos]
      simp
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ ↦ (riemannZeta ((σ₀ : ℂ) + (t : ℂ) * I))⁻¹
        * (X : ℂ) ^ ((σ₀ : ℂ) + (t : ℂ) * I)) volume := by
    apply Continuous.aestronglyMeasurable
    rw [← continuousOn_univ]
    intro t _
    have s_ne_one : (σ₀ : ℂ) + (t : ℂ) * I ≠ 1 := by
      intro h
      have : σ₀ = 1 := by have := congr_arg Complex.re h; simpa using this
      linarith [σ₀_gt]
    apply ContinuousAt.continuousWithinAt
    have hg : ContinuousAt (fun x : ℝ => (σ₀ : ℂ) + (x : ℂ) * I) t := by fun_prop
    apply ContinuousAt.mul
    · apply ContinuousAt.inv₀
      · have diffζ : ContinuousAt riemannZeta ((fun x : ℝ => (σ₀ : ℂ) + (x : ℂ) * I) t) :=
          (differentiableAt_riemannZeta s_ne_one).continuousAt
        exact ContinuousAt.comp diffζ hg
      · exact riemannZeta_ne_zero_of_one_lt_re (by simp [σ₀_gt])
    · have hc : ContinuousAt (fun z : ℂ => (X : ℂ) ^ z)
          ((fun x : ℝ => (σ₀ : ℂ) + (x : ℂ) * I) t) :=
        continuousAt_const_cpow (by exact_mod_cast hXpos.ne')
      exact ContinuousAt.comp hc hg
  have key := hMint.bdd_mul hmeas (ae_of_all _ hbdd)
  apply key.congr
  filter_upwards with t
  show (riemannZeta ((σ₀ : ℂ) + (t : ℂ) * I))⁻¹ * (X : ℂ) ^ ((σ₀ : ℂ) + (t : ℂ) * I)
      * mellin (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) ((σ₀ : ℂ) + (t : ℂ) * I)
    = smoothedMobiusIntegrand SmoothingF ε X (((1 : ℝ) + (Real.log X)⁻¹) + t * I)
  unfold smoothedMobiusIntegrand
  rw [hσ₀]
  push_cast
  ring

theorem zeta_ne_zero_on_vinogradov_box :
    ∃ (T₀ : ℝ), 3 ≤ T₀ ∧ ∀ (T : ℝ), T₀ ≤ T →
      ∀ s ∈ (((Set.Icc ((1 : ℝ) - contourWidth / Real.log T) 2) ×ℂ (Set.Icc (-T) T)) \ {1}),
        riemannZeta s ≠ 0 := by
  refine ⟨3, le_rfl, ?_⟩
  intro T hT s hs
  exact classical_mertens_reciprocal_rectangle.choose_spec.2.2.2 T hT s hs.1

private theorem norm_mobius_boundary_sum (a b c d e : ℂ) :
    ‖a - b + c + d + e‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ := by
  calc
    _ ≤ ‖a - b + c + d‖ + ‖e‖ := norm_add_le _ _
    _ ≤ ‖a - b + c‖ + ‖d‖ + ‖e‖ := by gcongr; exact norm_add_le _ _
    _ ≤ ‖a - b‖ + ‖c‖ + ‖d‖ + ‖e‖ := by gcongr; exact norm_add_le _ _
    _ ≤ _ := by gcongr; exact norm_sub_le _ _

private theorem smoothedMobius_bound_at_contourEndpoint
    (hBounds : MobiusBoundaryBoundsCorrectProp) {f : ℝ → ℝ}
    (hsupp : Function.support f ⊆ Set.Icc (1 / 2) 2)
    (hnonneg : ∀ x > 0, 0 ≤ f x)
    (hmass : ∫ x in Set.Ioi (0 : ℝ), f x / x = 1)
    (hdiff : ContDiff ℝ 1 f) :
    ∃ C : ℝ, ∀ᶠ X in atTop,
      ‖smoothedMobius f (mertens_eps X) X‖ ≤ C * (X * mertens_eps X) := by
  obtain ⟨Cfar, _, Ccut, _, hBd⟩ := hBounds hsupp hdiff
  obtain ⟨T₀, hT₀, hzero⟩ := zeta_ne_zero_on_vinogradov_box
  have hTlim : Tendsto mertens_T atTop atTop :=
    Real.tendsto_exp_atTop.comp (Tendsto.const_mul_atTop (Real.sqrt_pos.mpr contourWidth_pos)
      (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop))
  refine ⟨4 * Cfar + Ccut, ?_⟩
  filter_upwards [Filter.eventually_gt_atTop (3 : ℝ), hTlim.eventually_gt_atTop T₀, mertens_eps_mem]
      with X hX hT hεmem
  have hX1 : 1 < X := by linarith
  have hT3 : 3 < mertens_T X := hT₀.trans_lt hT
  have hlog : 1 < Real.log (mertens_T X) := logt_gt_one hT3.le
  have hA : 0 < contourWidth / Real.log (mertens_T X) :=
    div_pos contourWidth_pos (by linarith)
  have hA1 : contourWidth / Real.log (mertens_T X) < 1 :=
    (div_lt_one (by linarith : 0 < Real.log (mertens_T X))).mpr (by linarith [contourWidth_small])
  let σ := 1 - contourWidth / Real.log (mertens_T X)
  have hσ : 0 < σ := sub_pos.mpr hA1
  have hσ1 : σ < 1 := sub_lt_self _ hA
  obtain ⟨hε, hε1⟩ := hεmem
  have hbox := mobiusIntegrand_holomorphicOn_punctured_box hε hε1 hsupp hnonneg hmass hdiff
    hT₀ hzero (by linarith : 0 < X) hT.le
  have hint := mobiusIntegrand_integrable_right_line hε hε1 hX hsupp hnonneg hmass hdiff
  have hsum := mobiusPullPropPunctured_holds hε hε1 hX (by linarith : 0 < mertens_T X)
    hσ hσ1 hsupp hnonneg hmass hdiff hbox hint
  obtain ⟨h1, h5, h2, h3, h4⟩ := hBd hε hε1 hX hT3
  obtain ⟨hfar, hcut⟩ := mertens_boundary_balance hX1
  rw [hfar] at h1 h2 h4 h5
  rw [mul_div_assoc, hcut] at h3
  rw [hsum]
  apply (norm_mobius_boundary_sum _ _ _ _ _).trans
  calc
    _ ≤ _ := add_le_add (add_le_add (add_le_add (add_le_add h1 h2) h3) h4) h5
    _ = _ := by ring

def MobiusStripInvZetaConsumerBound : Prop :=
  ∃ C > 0, ∀ {X T : ℝ}, 3 < X → 3 < T →
    ∀ {σ t : ℝ}, (1 ≤ σ ∨ |t| ≤ T) →
      σ ∈ Set.Icc (1 - contourWidth / Real.log T) (1 + (Real.log X)⁻¹) →
      1 / ‖ζ (σ + t * I)‖ ≤ C * (Real.log (2 + |t|)) ^ 2

theorem mobiusIntegrand_norm_eq (SmoothingF : ℝ → ℝ) (ε X : ℝ) (s : ℂ) :
    ‖smoothedMobiusIntegrand SmoothingF ε X s‖ =
      ‖(riemannZeta s)⁻¹‖ * ‖mellin (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) s‖ * ‖(X : ℂ) ^ s‖ := by
  unfold smoothedMobiusIntegrand
  rw [norm_mul, norm_mul]

theorem norm_cpow_ofReal {X : ℝ} (hX : 0 < X) (s : ℂ) :
    ‖(X : ℂ) ^ s‖ = X ^ s.re := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hX]

theorem norm_inv_zeta (s : ℂ) : ‖(riemannZeta s)⁻¹‖ = 1 / ‖riemannZeta s‖ := by
  rw [norm_inv, one_div]

theorem mobiusFarTail_integrand_bound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Set.Icc (1 / 2) 2)
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (hStrip : MobiusStripInvZetaConsumerBound) :
    ∃ C > 0, ∀ {ε X T : ℝ} (_ : ε ∈ Set.Ioo (0:ℝ) 1) (_ : 3 < X) (_ : 3 < T)
      (t : ℝ) (_ : t ≤ -T),
      ‖smoothedMobiusIntegrand SmoothingF ε X ((1 + (Real.log X)⁻¹) + t * I)‖ ≤
        C * (X / ε) * (Real.log (-t)) ^ 2 / (-t) ^ 2 := by
  obtain ⟨Cz, Czpos, hZ⟩ := hStrip
  obtain ⟨Cm, Cmpos, hMel⟩ := MellinOfSmooth1b diffSmoothingF suppSmoothingF
  refine ⟨4 * Cz * Cm * Real.exp 1, by positivity, ?_⟩
  intro ε X T hε hX hT t ht
  have hXpos : (0:ℝ) < X := by linarith
  have hTpos : (0:ℝ) < T := by linarith
  have htT : t ≤ -T := ht
  have htneg : t < 0 := by linarith
  have htabs : 3 ≤ |t| := by rw [abs_of_neg htneg]; linarith
  set σ : ℝ := 1 + (Real.log X)⁻¹ with hσdef
  have hlogXpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hσmem : σ ∈ Set.Icc (1 - contourWidth / Real.log T) (1 + (Real.log X)⁻¹) := by
    constructor
    · have hF : 0 ≤ contourWidth / Real.log T := by
        have hFnn : 0 ≤ contourWidth := contourWidth_pos.le
        have hLT : 0 < Real.log T := Real.log_pos (by linarith)
        positivity
      have : 0 ≤ (Real.log X)⁻¹ := by positivity
      simp only [hσdef]; linarith
    · simp only [hσdef]; exact le_refl _
  have hcons : (1 : ℝ) ≤ σ := by
    simp only [hσdef]
    have hnn : 0 ≤ (Real.log X)⁻¹ := by positivity
    linarith
  have hZσ0 := hZ (t := t) hX hT (Or.inl hcons) hσmem
  set s : ℂ := (1 + (Real.log X)⁻¹ : ℂ) + t * I with hsdef
  have hsζ : ((σ : ℂ) + t * I) = s := by rw [hsdef, hσdef]; push_cast; ring
  have hZσ : 1 / ‖ζ s‖ ≤ Cz * (Real.log (2 + |t|)) ^ 2 := by rw [← hsζ]; exact hZσ0
  have hsre : s.re = σ := by simp [hsdef, hσdef]
  have hinvlogXnn : 0 ≤ (Real.log X)⁻¹ := by positivity
  have hσ1 : (1:ℝ)/2 ≤ s.re := by
    rw [hsre, hσdef]; linarith
  have hσ2 : s.re ≤ 2 := by
    rw [hsre, hσdef]
    have : (Real.log X)⁻¹ ≤ 1 := by
      apply inv_le_one_of_one_le₀
      rw [Real.le_log_iff_exp_le (by linarith)]
      exact Real.exp_one_lt_d9.le.trans (by linarith)
    linarith
  have hMelS := hMel (1/2) (by norm_num) s hσ1 hσ2 ε hε.1 hε.2
  have hXs : ‖(X:ℂ)^s‖ = X * Real.exp 1 := by
    rw [norm_cpow_ofReal hXpos s, hsre, hσdef, Real.rpow_add hXpos, Real.rpow_one,
      Real.rpow_inv_log (by linarith) (by linarith)]
  have hsim : s.im = t := by simp [hsdef]
  have hsnorm2 : t ^ 2 ≤ ‖s‖ ^ 2 := by
    have hnsq : ‖s‖ ^ 2 = s.re ^ 2 + s.im ^ 2 := by
      have h := (Complex.normSq_eq_norm_sq s).symm
      rw [Complex.normSq_apply] at h
      rw [h]; ring
    rw [hnsq, hsre, hsim]; nlinarith [sq_nonneg σ]
  rw [mobiusIntegrand_norm_eq, norm_inv_zeta, hXs]
  have h1 : 0 ≤ ‖mellin (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) s‖ := norm_nonneg _
  have hεpos := hε.1
  have hsnorm_pos : 0 < ‖s‖ := by
    rw [hsdef]; apply norm_pos_iff.mpr
    intro h; rw [Complex.ext_iff] at h
    simp at h; rcases h with ⟨_, hi⟩
    have : t = 0 := by simpa using hi
    linarith
  have habs : |t| = -t := abs_of_neg htneg
  have hmtpos : 0 < -t := by linarith
  have hmtge3 : (3:ℝ) ≤ -t := by rw [← habs]; exact htabs
  have hlog_bridge : Real.log (2 + |t|) ≤ 2 * Real.log (-t) := by
    rw [habs, two_mul, ← Real.log_mul (by linarith) (by linarith)]
    apply Real.log_le_log (by linarith)
    nlinarith
  have hlogmt_nn : 0 ≤ Real.log (-t) := Real.log_nonneg (by linarith)
  have hsq_bridge : (Real.log (2 + |t|)) ^ 2 ≤ 4 * (Real.log (-t)) ^ 2 := by
    have h0 : 0 ≤ Real.log (2 + |t|) := Real.log_nonneg (by rw [habs]; linarith)
    nlinarith [hlog_bridge, h0, hlogmt_nn]
  have ht2eq : t ^ 2 = (-t) ^ 2 := by ring
  calc 1 / ‖ζ s‖ * ‖mellin (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) s‖ * (X * Real.exp 1)
      ≤ (Cz * (Real.log (2 + |t|)) ^ 2) * (Cm * (ε * ‖s‖ ^ 2)⁻¹) * (X * Real.exp 1) := by
        gcongr
    _ ≤ 4 * Cz * Cm * Real.exp 1 * (X / ε) * (Real.log (-t)) ^ 2 / (-t) ^ 2 := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        have hlog2 : 0 ≤ (Real.log (2 + |t|)) ^ 2 := sq_nonneg _
        have hmt2pos : 0 < (-t) ^ 2 := by positivity
        have hsnorm2pos : 0 < ‖s‖ ^ 2 := by positivity
        rw [mul_inv]
        have hinv : (‖s‖ ^ 2)⁻¹ ≤ ((-t) ^ 2)⁻¹ := by
          apply inv_anti₀ hmt2pos
          rw [← ht2eq]; exact hsnorm2
        have hXe : 0 ≤ X * Real.exp 1 := by positivity
        have hkey : Cz * (Real.log (2 + |t|)) ^ 2 * (Cm * (ε⁻¹ * (‖s‖ ^ 2)⁻¹)) * (X * Real.exp 1)
            ≤ 4 * Cz * Cm * Real.exp 1 * (X * ε⁻¹) * (Real.log (-t)) ^ 2 * ((-t) ^ 2)⁻¹ := by
          have e1 : Cz * (Real.log (2 + |t|)) ^ 2 * (Cm * (ε⁻¹ * (‖s‖ ^ 2)⁻¹)) * (X * Real.exp 1)
              ≤ Cz * (4 * (Real.log (-t)) ^ 2) * (Cm * (ε⁻¹ * ((-t) ^ 2)⁻¹)) * (X * Real.exp 1) := by
            gcongr
          refine e1.trans (le_of_eq ?_); ring
        calc Cz * (Real.log (2 + |t|)) ^ 2 * (Cm * (ε⁻¹ * (‖s‖ ^ 2)⁻¹)) * (X * Real.exp 1)
            ≤ _ := hkey
          _ = 4 * Cz * Cm * Real.exp 1 * (X * ε⁻¹) * (Real.log (-t)) ^ 2 * ((-t) ^ 2)⁻¹ := by ring

theorem mobiusM1_bound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Set.Icc (1 / 2) 2)
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (hStrip : MobiusStripInvZetaConsumerBound) :
    ∃ C > 0, ∀ {ε X T : ℝ} (_ : ε ∈ Set.Ioo (0:ℝ) 1) (_ : 3 < X) (_ : 3 < T),
      ‖M1New SmoothingF ε X T‖ ≤ C * (X / (ε * contourTailScale T)) := by
  have h_M1_bound : ∃ C > 0, ∀ {ε X T : ℝ} (_ : ε ∈ Set.Ioo (0:ℝ) 1) (_ : 3 < X) (_ : 3 < T),
      ‖∫ t in Set.Iic (-T),
        smoothedMobiusIntegrand SmoothingF ε X ((1 + (Real.log X)⁻¹) + t * I)‖ ≤
        C * (X / ε) * (1 / contourTailScale T) := by
    obtain ⟨C₁, hC₁pos, hC₁⟩ := mobiusFarTail_integrand_bound suppSmoothingF diffSmoothingF hStrip
    obtain ⟨C₂, hC₂pos, hC₂⟩ := contour_log_tail_bound
    refine ⟨C₁ * C₂, mul_pos hC₁pos hC₂pos, fun {ε X T} εinIoo Xgt3 Tgt3 ↦
      (MeasureTheory.norm_integral_le_integral_norm _).trans ?_⟩
    refine (MeasureTheory.integral_mono_of_nonneg
      (g := fun t ↦ C₁ * (X / ε) * Real.log (-t) ^ 2 / (-t) ^ 2) ?_ ?_ ?_).trans ?_
    · exact Filter.Eventually.of_forall fun x ↦ norm_nonneg _
    ·
      have h_integrable : MeasureTheory.IntegrableOn
          (fun t ↦ (Real.log t)^2 / t^2) (Set.Ici T) := mertens_log_sq_tail_integrable Tgt3
      have h_integrable : MeasureTheory.IntegrableOn (fun t ↦
          (Real.log (-t))^2 / (-t)^2) (Set.Iic (-T)) := by
        convert h_integrable.comp_neg using 1; norm_num [Set.indicator]
      simpa only [mul_div_assoc] using h_integrable.const_mul _
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Iic] with t ht
        using hC₁ εinIoo Xgt3 Tgt3 t ht
    · convert mul_le_mul_of_nonneg_left (hC₂ T Tgt3) (show 0 ≤ C₁ * (X / ε) by
        exact mul_nonneg hC₁pos.le
          (div_nonneg (by linarith [Xgt3]) (by linarith [εinIoo.1]))) using 1 <;> ring_nf
      rw [← MeasureTheory.integral_const_mul, MeasureTheory.integral_Ici_eq_integral_Ioi,
        ← neg_neg T, ← integral_comp_neg_Iic]
      norm_num
      ring_nf
  obtain ⟨C, hC₀, hC⟩ := h_M1_bound; use C / (2 * Real.pi)
  refine ⟨by positivity, fun {ε X T} hε hX hT ↦ ?_⟩
  have hTT : (0:ℝ) < contourTailScale T := contourTailScale_pos (by linarith)
  have hεpos := hε.1
  have hprefac : ‖(1 / (2 * (π:ℂ) * I)) * I‖ = 1 / (2 * Real.pi) := by
    rw [show (1 / (2 * (π:ℂ) * I)) * I = 1 / (2 * (π:ℂ)) from by
        field_simp]
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat,
      show ‖(π:ℂ)‖ = Real.pi from (RCLike.norm_ofReal _).trans (abs_of_pos Real.pi_pos)]
  unfold M1New
  rw [show (1 / (2 * (π:ℂ) * I)) * (I * ∫ t in Set.Iic (-T),
        smoothedMobiusIntegrand SmoothingF ε X ((1 + (Real.log X)⁻¹) + t * I))
      = ((1 / (2 * (π:ℂ) * I)) * I) * (∫ t in Set.Iic (-T),
        smoothedMobiusIntegrand SmoothingF ε X ((1 + (Real.log X)⁻¹) + t * I)) from by ring,
    norm_mul, hprefac]
  calc 1 / (2 * Real.pi) * ‖∫ t in Set.Iic (-T),
          smoothedMobiusIntegrand SmoothingF ε X ((1 + (Real.log X)⁻¹) + t * I)‖
      ≤ 1 / (2 * Real.pi) * (C * (X / ε) * (1 / contourTailScale T)) :=
        mul_le_mul_of_nonneg_left (hC hε hX hT) (by positivity)
    _ = C / (2 * Real.pi) * (X / (ε * contourTailScale T)) := by
        rw [div_mul_eq_div_div]; ring

theorem mobiusM2_obligation {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Set.Icc (1 / 2) 2)
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (hStrip : MobiusStripInvZetaConsumerBound) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {ε X T : ℝ} (_ : ε ∈ Set.Ioo (0:ℝ) 1) (_ : 3 < X) (_ : 3 < T),
        let σ' := 1 - contourWidth / Real.log T
        ∫ σ₀ in σ'..(1 + (Real.log X)⁻¹),
            ‖smoothedMobiusIntegrand SmoothingF ε X (σ₀ - T * I)‖
          ≤ K * (X / (ε * contourTailScale T)) := by
  obtain ⟨Cz, Czpos, hZ⟩ := hStrip
  obtain ⟨Cm, Cmpos, hMel⟩ := MellinOfSmooth1b diffSmoothingF suppSmoothingF
  have hFpos : 0 < contourWidth := contourWidth_pos
  have hFsmall : contourWidth < 1 := lt_trans contourWidth_small (by norm_num)
  refine ⟨Cz * Cm * Real.exp 1 * 18, by positivity, ?_⟩
  intro ε X T εinIoo Xgt3 Tgt3
  simp only []
  set σ' : ℝ := 1 - contourWidth / Real.log T with hσ'def
  set b : ℝ := 1 + (Real.log X)⁻¹ with hbdef
  have hlogT_pos : 0 < Real.log T := Real.log_pos (by linarith)
  have hlogX_pos : 0 < Real.log X := Real.log_pos (by linarith)
  have hTpos : (0:ℝ) < T := by linarith
  have hXpos : (0:ℝ) < X := by linarith
  have hεpos : 0 < ε := εinIoo.1
  have hε1 : ε < 1 := εinIoo.2
  have hlogX_ge1 : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact Real.exp_one_lt_d9.le.trans (by linarith)
  have hb_le2 : b ≤ 2 := by
    rw [hbdef]; have : (Real.log X)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hlogX_ge1
    linarith
  have hb_ge1 : (1:ℝ) ≤ b := by
    rw [hbdef]; have hinv_nn : 0 ≤ (Real.log X)⁻¹ := by positivity
    linarith
  have hFdivT_lt1 : contourWidth / Real.log T < 1 := by
    rw [div_lt_one hlogT_pos]
    have h3 : (1:ℝ) ≤ Real.log T := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      exact Real.exp_one_lt_d9.le.trans (by linarith)
    linarith [hFsmall]
  have hFdivT_pos : 0 < contourWidth / Real.log T := by positivity
  have hσ'pos : 0 < σ' := by rw [hσ'def]; linarith
  have hσ'_lt1 : σ' < 1 := by rw [hσ'def]; linarith
  have hσ'_le_b : σ' ≤ b := le_trans (le_of_lt hσ'_lt1) hb_ge1
  set M₀ : ℝ := Cz * Cm * Real.exp 1 * (X * (Real.log (2 + T))^2 / (ε * T^2)) with hM₀def
  have hpointwise : ∀ σ₀ ∈ Set.Ioc σ' b,
      ‖smoothedMobiusIntegrand SmoothingF ε X (σ₀ - T * I)‖ ≤ M₀ := by
    intro σ₀ hσ₀
    obtain ⟨hσ₀lo, hσ₀hi⟩ := hσ₀
    have hre : ((σ₀ : ℂ) - T * I).re = σ₀ := by simp [Complex.sub_re, Complex.mul_re]
    have hs_eq : (σ₀ : ℂ) - T * I = (σ₀ : ℂ) + ((-T : ℝ) : ℂ) * I := by push_cast; ring
    have hσ₀mem : σ₀ ∈ Set.Icc (1 - contourWidth / Real.log T) (1 + (Real.log X)⁻¹) :=
      ⟨by rw [← hσ'def]; linarith, by rw [← hbdef]; exact hσ₀hi⟩
    have hconsT : |(-T : ℝ)| ≤ T := le_of_eq (by rw [abs_neg, abs_of_pos hTpos])
    have hZbnd0 := hZ (t := -T) Xgt3 Tgt3 (Or.inr hconsT) hσ₀mem
    have habsT : |(-T)| = T := by rw [abs_neg, abs_of_pos hTpos]
    have hZbnd : 1 / ‖ζ ((σ₀ : ℂ) - T * I)‖ ≤ Cz * Real.log (2 + T) ^ 2 := by
      rw [hs_eq]; rw [habsT] at hZbnd0; exact hZbnd0
    have hsnorm_ge : T ≤ ‖(σ₀ : ℂ) - T * I‖ := by
      have h : ‖(σ₀ : ℂ) - (T:ℂ) * I‖^2 = σ₀^2 + T^2 := by
        rw [← Complex.normSq_eq_norm_sq]
        simp [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
          Complex.mul_re, Complex.mul_im]; ring
      nlinarith [norm_nonneg ((σ₀ : ℂ) - (T:ℂ) * I), sq_nonneg σ₀, h]
    have hMellinbnd : ‖mellin (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (σ₀ - T * I)‖
        ≤ Cm / (ε * T^2) := by
      have := hMel σ' hσ'pos (σ₀ - T * I) (by rw [hre]; linarith [hσ₀lo])
        (by rw [hre]; linarith [hσ₀hi]) ε hεpos hε1
      refine this.trans ?_
      rw [div_eq_mul_inv]
      apply mul_le_mul_of_nonneg_left _ Cmpos.le
      apply inv_anti₀ (by positivity)
      apply mul_le_mul_of_nonneg_left _ hεpos.le
      exact pow_le_pow_left₀ hTpos.le hsnorm_ge 2
    have hXbnd : ‖(X:ℂ)^((σ₀ : ℂ) - T * I)‖ ≤ Real.exp 1 * X := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hXpos, hre]
      have hmono : X ^ σ₀ ≤ X ^ b :=
        Real.rpow_le_rpow_left_iff (by linarith : 1 < X) |>.mpr hσ₀hi
      refine hmono.trans ?_
      rw [hbdef, Real.rpow_add hXpos, Real.rpow_one, mul_comm]
      gcongr
      rw [Real.rpow_inv_log (by linarith) (by linarith)]
    rw [mobiusIntegrand_norm_eq, norm_inv_zeta]
    have hprod := mul_le_mul (mul_le_mul hZbnd hMellinbnd (norm_nonneg _) (by positivity))
      hXbnd (norm_nonneg _) (by positivity)
    refine hprod.trans (le_of_eq ?_)
    rw [hM₀def]
    field_simp
  have hM₀nn : 0 ≤ M₀ := by rw [hM₀def]; positivity
  have hint_le : ∫ σ₀ in σ'..b,
      ‖smoothedMobiusIntegrand SmoothingF ε X (σ₀ - T * I)‖ ≤ M₀ * (b - σ') := by
    rw [intervalIntegral.integral_of_le hσ'_le_b]
    have hle : ∫ σ₀ in Set.Ioc σ' b,
          ‖smoothedMobiusIntegrand SmoothingF ε X (σ₀ - T * I)‖ ∂volume
        ≤ ∫ _σ₀ in Set.Ioc σ' b, M₀ ∂volume := by
      apply MeasureTheory.integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall fun _ ↦ norm_nonneg _
      · exact integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with σ₀ hσ₀
          using hpointwise σ₀ hσ₀
    have hconst : ∫ _σ₀ in Set.Ioc σ' b, M₀ ∂volume = M₀ * (b - σ') := by
      rw [MeasureTheory.setIntegral_const, smul_eq_mul, Real.volume_real_Ioc,
        max_eq_left (by linarith), mul_comm]
    rw [hconst] at hle; exact hle
  refine hint_le.trans ?_
  have hlen_le : b - σ' ≤ 2 := by linarith [hσ'pos, hb_le2]
  have htail : 0 < contourTailScale T := contourTailScale_pos Tgt3
  have habsorb : (Real.log (2 + T))^2 / T^2 ≤ 9 / contourTailScale T := calc
    _ ≤ contourLogWeight T / T^2 :=
      div_le_div_of_nonneg_right (contour_log_weight_dominates Tgt3) (sq_nonneg T)
    _ ≤ contourLogWeight T / T :=
      div_le_div_of_nonneg_left (contourLogWeight_pos Tgt3).le hTpos (by nlinarith)
    _ = 1 / contourTailScale T := by rw [one_div, contourTailScale, inv_div]
    _ ≤ _ := div_le_div_of_nonneg_right (by norm_num) htail.le
  rw [hM₀def]
  have key : Cz * Cm * Real.exp 1 * (X * Real.log (2 + T) ^ 2 / (ε * T ^ 2)) * (b - σ')
      ≤ (Cz * Cm * Real.exp 1 * 18) * (X / (ε * contourTailScale T)) := by
    have hfactor : X * Real.log (2 + T) ^ 2 / (ε * T ^ 2)
        = (X / ε) * (Real.log (2 + T) ^ 2 / T ^ 2) := by field_simp
    rw [hfactor]
    have h1 : (Real.log (2 + T) ^ 2 / T ^ 2) * (b - σ') ≤ (9 / contourTailScale T) * 2 := by
      apply mul_le_mul habsorb hlen_le (by linarith [hσ'pos, hb_ge1]) (by positivity)
    calc Cz * Cm * Real.exp 1 * ((X / ε) * (Real.log (2 + T) ^ 2 / T ^ 2)) * (b - σ')
        = (Cz * Cm * Real.exp 1) * (X / ε) *
            ((Real.log (2 + T) ^ 2 / T ^ 2) * (b - σ')) := by ring
      _ ≤ (Cz * Cm * Real.exp 1) * (X / ε) * ((9 / contourTailScale T) * 2) := by
          apply mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (Cz * Cm * Real.exp 1 * 18) * (X / (ε * contourTailScale T)) := by
          rw [div_mul_eq_div_div]; ring
  exact key

theorem mobiusM2_bound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Set.Icc (1 / 2) 2)
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (hStrip : MobiusStripInvZetaConsumerBound) :
    ∃ C ≥ 0, ∀ {ε X T : ℝ} (_ : ε ∈ Set.Ioo (0:ℝ) 1) (_ : 3 < X) (_ : 3 < T),
      let σ' := 1 - contourWidth / Real.log T
      ‖M2New SmoothingF ε X T σ'‖ ≤ C * (X / (ε * contourTailScale T)) := by
  obtain ⟨K, hKnn, hK⟩ := mobiusM2_obligation suppSmoothingF diffSmoothingF hStrip
  refine ⟨K / (2 * Real.pi), by positivity, ?_⟩
  intro ε X T εinIoo Xgt3 Tgt3
  simp only []
  set σ' : ℝ := 1 - contourWidth / Real.log T with hσ'def
  set b : ℝ := 1 + (Real.log X)⁻¹ with hbdef
  change ‖(1 / (2 * (π : ℂ) * I)) *
      (∫ σ₀ in σ'..b, smoothedMobiusIntegrand SmoothingF ε X (↑σ₀ - ↑T * I))‖ ≤
        K / (2 * Real.pi) * (X / (ε * contourTailScale T))
  have hnorm_const : ‖(1 / (2 * (π : ℂ) * I) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [norm_div, norm_one, norm_mul, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_ofNat, show ‖(π : ℂ)‖ = Real.pi from
          (RCLike.norm_ofReal _).trans (abs_of_pos Real.pi_pos)]
  rw [norm_mul, hnorm_const]
  have hlogT_pos : 0 < Real.log T := Real.log_pos (by linarith)
  have hFpos : 0 < contourWidth := contourWidth_pos
  have hlogX_pos : 0 < Real.log X := Real.log_pos (by linarith)
  have hσ'_le_b : σ' ≤ b := by
    have hFT : 0 ≤ contourWidth / Real.log T := by positivity
    have hLX : 0 ≤ (Real.log X)⁻¹ := by positivity
    have h1 : σ' ≤ 1 := by rw [hσ'def]; linarith
    have h2 : (1:ℝ) ≤ b := by rw [hbdef]; linarith
    linarith
  have h_int_le :
      ‖∫ σ₀ in σ'..b, smoothedMobiusIntegrand SmoothingF ε X (↑σ₀ - ↑T * I)‖
        ≤ ∫ σ₀ in σ'..b, ‖smoothedMobiusIntegrand SmoothingF ε X (↑σ₀ - ↑T * I)‖ :=
    intervalIntegral.norm_integral_le_integral_norm hσ'_le_b
  have h_obl := hK εinIoo Xgt3 Tgt3
  simp only [] at h_obl
  calc 1 / (2 * Real.pi)
        * ‖∫ σ₀ in σ'..b, smoothedMobiusIntegrand SmoothingF ε X (↑σ₀ - ↑T * I)‖
      ≤ 1 / (2 * Real.pi)
          * ∫ σ₀ in σ'..b, ‖smoothedMobiusIntegrand SmoothingF ε X (↑σ₀ - ↑T * I)‖ :=
        mul_le_mul_of_nonneg_left h_int_le (by positivity)
    _ ≤ 1 / (2 * Real.pi) * (K * (X / (ε * contourTailScale T))) :=
        mul_le_mul_of_nonneg_left h_obl (by positivity)
    _ = K / (2 * Real.pi) * (X / (ε * contourTailScale T)) := by ring

theorem mobiusM3_obligation {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Set.Icc (1 / 2) 2)
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (hStrip : MobiusStripInvZetaConsumerBound) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {ε X T : ℝ} (_ : ε ∈ Set.Ioo (0:ℝ) 1) (_ : 3 < X) (_ : 3 < T),
        let σ' := 1 - contourWidth / Real.log T
        ∫ t in (-T)..T,
            ‖smoothedMobiusIntegrand SmoothingF ε X (σ' + t * I)‖
          ≤ K * (X ^ (1 - contourWidth / Real.log T) * contourLogWeight T) / ε := by
  obtain ⟨Cz, Czpos, hZ⟩ := hStrip
  obtain ⟨Cm, Cmpos, hMel⟩ := MellinOfSmooth1b diffSmoothingF suppSmoothingF
  have hFpos : 0 < contourWidth := contourWidth_pos
  have hFsmall : contourWidth < 1 / 30 := lt_trans contourWidth_small (by norm_num)
  refine ⟨Cz * Cm * (16 * Real.pi), by positivity, ?_⟩
  intro ε X T εinIoo Xgt3 Tgt3
  simp only []
  set σ' : ℝ := 1 - contourWidth / Real.log T with hσ'def
  have hlogT_pos : 0 < Real.log T := Real.log_pos (by linarith)
  have hlogX_pos : 0 < Real.log X := Real.log_pos (by linarith)
  have hTpos : (0:ℝ) < T := by linarith
  have hXpos : (0:ℝ) < X := by linarith
  have hεpos : 0 < ε := εinIoo.1
  have hε1 : ε < 1 := εinIoo.2
  have hlogT_ge1 : 1 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact Real.exp_one_lt_d9.le.trans (by linarith)
  have hFdivT_lt : contourWidth / Real.log T < 1 / 30 := by
    rw [div_lt_iff₀ hlogT_pos]
    calc contourWidth < 1/30 := hFsmall
      _ ≤ 1/30 * Real.log T := by nlinarith [hlogT_ge1]
  have hFdivT_pos : 0 < contourWidth / Real.log T := by positivity
  have hσ'_lt1 : σ' < 1 := by rw [hσ'def]; linarith
  have hσ'_gt : (1:ℝ)/2 < σ' := by rw [hσ'def]; linarith
  have hσ'pos : 0 < σ' := by linarith
  have hσ'mem : σ' ∈ Set.Icc (1 - contourWidth / Real.log T) (1 + (Real.log X)⁻¹) := by
    constructor
    · rw [hσ'def]
    · have : 0 ≤ (Real.log X)⁻¹ := by positivity
      have : σ' ≤ 1 := hσ'_lt1.le
      have h2 : 0 ≤ (Real.log X)⁻¹ := by positivity
      linarith
  set Cint : ℝ := Cz * Cm * Real.log (2 + T) ^ 2 * X ^ σ' / ε with hCintdef
  have hpointwise : ∀ t ∈ Set.Ioc (-T) T,
      ‖smoothedMobiusIntegrand SmoothingF ε X (σ' + t * I)‖
        ≤ Cint * (σ' ^ 2 + t ^ 2)⁻¹ := by
    intro t ht
    obtain ⟨htlo, hthi⟩ := ht
    have habsT : |t| ≤ T := abs_le.mpr ⟨by linarith, hthi⟩
    have hre : ((σ' : ℂ) + t * I).re = σ' := by
      simp [Complex.add_re, Complex.mul_re]
    have hZbnd0 := hZ (t := t) Xgt3 Tgt3 (Or.inr habsT) hσ'mem
    have hlogmono : Real.log (2 + |t|) ≤ Real.log (2 + T) :=
      Real.log_le_log (by positivity) (by linarith [habsT])
    have hlogt_nn : 0 ≤ Real.log (2 + |t|) :=
      Real.log_nonneg (by have := abs_nonneg t; linarith)
    have hZbnd : 1 / ‖ζ ((σ' : ℂ) + t * I)‖ ≤ Cz * Real.log (2 + T) ^ 2 := by
      refine hZbnd0.trans ?_
      apply mul_le_mul_of_nonneg_left _ Czpos.le
      nlinarith [hlogmono, hlogt_nn, Real.log_nonneg (show (1:ℝ) ≤ 2 + T by linarith)]
    have hsnorm_sq : ‖(σ' : ℂ) + t * I‖ ^ 2 = σ' ^ 2 + t ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq]
      simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero,
        add_zero, zero_add]
      ring
    have hMellinbnd : ‖mellin (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (σ' + t * I)‖
        ≤ Cm * (ε * (σ' ^ 2 + t ^ 2))⁻¹ := by
      have := hMel σ' hσ'pos (σ' + t * I) (by rw [hre]) (by rw [hre]; linarith) ε hεpos hε1
      rwa [hsnorm_sq] at this
    have hXbnd : ‖(X:ℂ)^((σ' : ℂ) + t * I)‖ = X ^ σ' := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hXpos, hre]
    rw [mobiusIntegrand_norm_eq, norm_inv_zeta, hXbnd]
    have hstep := mul_le_mul hZbnd hMellinbnd (norm_nonneg _) (by positivity)
    calc 1 / ‖ζ ((σ' : ℂ) + t * I)‖ *
            ‖mellin (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (σ' + t * I)‖ * X ^ σ'
        ≤ (Cz * Real.log (2 + T) ^ 2) * (Cm * (ε * (σ' ^ 2 + t ^ 2))⁻¹) * X ^ σ' := by
          apply mul_le_mul_of_nonneg_right hstep (by positivity)
      _ = Cint * (σ' ^ 2 + t ^ 2)⁻¹ := by
          rw [hCintdef]
          have hdenom : (ε * (σ' ^ 2 + t ^ 2))⁻¹
              = ε⁻¹ * (σ' ^ 2 + t ^ 2)⁻¹ := by rw [mul_inv]
          rw [hdenom]; ring
  have hCint_nn : 0 ≤ Cint := by rw [hCintdef]; positivity
  have hTle : -T ≤ T := by linarith
  have hint_le : ∫ t in (-T)..T,
      ‖smoothedMobiusIntegrand SmoothingF ε X (σ' + t * I)‖
        ≤ ∫ t in (-T)..T, Cint * (σ' ^ 2 + t ^ 2)⁻¹ := by
    rw [intervalIntegral.integral_of_le hTle, intervalIntegral.integral_of_le hTle]
    apply MeasureTheory.integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall fun _ ↦ norm_nonneg _
    · apply MeasureTheory.Integrable.const_mul
      apply Continuous.integrableOn_Ioc
      apply Continuous.inv₀
      · fun_prop
      · intro x; positivity
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
        using hpointwise t ht
  refine hint_le.trans ?_
  rw [intervalIntegral.integral_const_mul,
      integral_inv_sq_add_sq (ne_of_gt hσ'pos)]
  have harctan_bnd : σ'⁻¹ * (Real.arctan (T / σ') - Real.arctan (-T / σ')) ≤ σ'⁻¹ * Real.pi := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have h1 : Real.arctan (T / σ') ≤ Real.pi / 2 := (Real.arctan_lt_pi_div_two _).le
    have h2 : -(Real.pi / 2) ≤ Real.arctan (-T / σ') := (Real.neg_pi_div_two_lt_arctan _).le
    linarith
  have hXσ'pos : 0 < X ^ σ' := Real.rpow_pos_of_pos hXpos _
  have hwpos : 0 < contourLogWeight T := contourLogWeight_pos Tgt3
  have hlogsq_le : Real.log (2 + T) ^ 2 ≤ 8 * contourLogWeight T :=
    (contour_log_weight_dominates Tgt3).trans (by linarith)
  have hσ'inv_le : σ'⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hσ'pos (by norm_num)]; linarith
  have hπpos := Real.pi_pos
  have hCC_nn : (0:ℝ) ≤ Cz * Cm := by positivity
  have hstepA : Cint * (σ'⁻¹ * (Real.arctan (T / σ') - Real.arctan (-T / σ')))
      ≤ Cint * (σ'⁻¹ * Real.pi) :=
    mul_le_mul_of_nonneg_left harctan_bnd hCint_nn
  refine hstepA.trans ?_
  rw [hCintdef]
  have hstep1 : Cz * Cm * Real.log (2 + T) ^ 2 * X ^ σ' / ε * (σ'⁻¹ * Real.pi)
      ≤ Cz * Cm * (8 * contourLogWeight T) * X ^ σ' / ε * (2 * Real.pi) := by
    have hL : Cz * Cm * Real.log (2 + T) ^ 2 * X ^ σ' / ε
        ≤ Cz * Cm * (8 * contourLogWeight T) * X ^ σ' / ε := by
      gcongr
    have hR : σ'⁻¹ * Real.pi ≤ 2 * Real.pi := by
      apply mul_le_mul_of_nonneg_right hσ'inv_le hπpos.le
    apply mul_le_mul hL hR (by positivity) (by positivity)
  refine hstep1.trans (le_of_eq ?_)
  field_simp
  ring

theorem mobiusM3_bound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Set.Icc (1 / 2) 2)
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (hStrip : MobiusStripInvZetaConsumerBound) :
    ∃ C ≥ 0, ∀ {ε X T : ℝ} (_ : ε ∈ Set.Ioo (0:ℝ) 1) (_ : 3 < X) (_ : 3 < T),
      let σ' := 1 - contourWidth / Real.log T
      ‖M3New SmoothingF ε X T σ'‖ ≤ C * (X ^ (1 - contourWidth / Real.log T) * contourLogWeight T) / ε := by
  obtain ⟨K, hKnn, hK⟩ := mobiusM3_obligation suppSmoothingF diffSmoothingF hStrip
  refine ⟨K / (2 * Real.pi), by positivity, ?_⟩
  intro ε X T εinIoo Xgt3 Tgt3
  simp only []
  set σ' : ℝ := 1 - contourWidth / Real.log T with hσ'def
  change ‖(1 / (2 * (π : ℂ) * I)) *
      (I * (∫ t in Set.Icc (-T) T,
        smoothedMobiusIntegrand SmoothingF ε X (↑σ' + ↑t * I)))‖ ≤
        K / (2 * Real.pi) * (X ^ (1 - contourWidth / Real.log T) * contourLogWeight T) / ε
  have hprefactor : (1 / (2 * (π : ℂ) * I)) * I = 1 / (2 * (π : ℂ)) := by field_simp
  have hTle : (-T : ℝ) ≤ T := by linarith
  have hIcc : (∫ t in Set.Icc (-T) T,
        smoothedMobiusIntegrand SmoothingF ε X (↑σ' + ↑t * I))
      = ∫ t in (-T)..T, smoothedMobiusIntegrand SmoothingF ε X (↑σ' + ↑t * I) := by
    rw [intervalIntegral.integral_of_le hTle,
        ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [hIcc,
    show (1 / (2 * (π : ℂ) * I)) *
        (I * (∫ t in (-T)..T,
          smoothedMobiusIntegrand SmoothingF ε X (↑σ' + ↑t * I))) =
      ((1 / (2 * (π : ℂ) * I)) * I) *
        (∫ t in (-T)..T,
          smoothedMobiusIntegrand SmoothingF ε X (↑σ' + ↑t * I)) from by ring,
    hprefactor]
  have hnorm_const : ‖(1 / (2 * (π : ℂ)) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat,
        show ‖(π : ℂ)‖ = Real.pi from
          (RCLike.norm_ofReal _).trans (abs_of_pos Real.pi_pos)]
  rw [norm_mul, hnorm_const]
  have h_int_le :
      ‖∫ t in (-T)..T, smoothedMobiusIntegrand SmoothingF ε X (↑σ' + ↑t * I)‖
        ≤ ∫ t in (-T)..T,
            ‖smoothedMobiusIntegrand SmoothingF ε X (↑σ' + ↑t * I)‖ :=
    intervalIntegral.norm_integral_le_integral_norm hTle
  have h_obl := hK εinIoo Xgt3 Tgt3
  simp only [] at h_obl
  calc 1 / (2 * Real.pi)
        * ‖∫ t in (-T)..T, smoothedMobiusIntegrand SmoothingF ε X (↑σ' + ↑t * I)‖
      ≤ 1 / (2 * Real.pi)
          * ∫ t in (-T)..T, ‖smoothedMobiusIntegrand SmoothingF ε X (↑σ' + ↑t * I)‖ :=
        mul_le_mul_of_nonneg_left h_int_le (by positivity)
    _ ≤ 1 / (2 * Real.pi) * (K * (X ^ (1 - contourWidth / Real.log T) * contourLogWeight T) / ε) :=
        mul_le_mul_of_nonneg_left h_obl (by positivity)
    _ = K / (2 * Real.pi) * (X ^ (1 - contourWidth / Real.log T) * contourLogWeight T) / ε := by ring

theorem smoothedMobiusIntegrand_conj {SmoothingF : ℝ → ℝ} {ε X : ℝ}
    (Xpos : 0 < X) (s : ℂ) :
    smoothedMobiusIntegrand SmoothingF ε X (starRingEnd ℂ s) =
      starRingEnd ℂ (smoothedMobiusIntegrand SmoothingF ε X s) := by
  unfold smoothedMobiusIntegrand
  simp only [map_mul, map_inv₀]
  congr 1
  · congr 1
    · congr 1
      exact riemannZeta_conj s
    · unfold mellin
      rw [← integral_conj]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro x xpos
      simp only [smul_eq_mul, map_mul, Complex.conj_ofReal]
      congr 1
      nth_rw 1 [← map_one (starRingEnd ℂ)]
      rw [← map_sub, Complex.cpow_conj, Complex.conj_ofReal]
      rw [Complex.arg_ofReal_of_nonneg xpos.le]
      exact Real.pi_ne_zero.symm
  · rw [Complex.cpow_conj, Complex.conj_ofReal]
    rw [Complex.arg_ofReal_of_nonneg Xpos.le]
    exact Real.pi_ne_zero.symm

theorem mobiusM4_bound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Set.Icc (1 / 2) 2)
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (hStrip : MobiusStripInvZetaConsumerBound) :
    ∃ C ≥ 0, ∀ {ε X T : ℝ} (_ : ε ∈ Set.Ioo (0:ℝ) 1) (_ : 3 < X) (_ : 3 < T),
      let σ' := 1 - contourWidth / Real.log T
      ‖M4New SmoothingF ε X T σ'‖ ≤ C * (X / (ε * contourTailScale T)) := by
  obtain ⟨C, Cnn, hM2⟩ := mobiusM2_bound suppSmoothingF diffSmoothingF hStrip
  refine ⟨C, Cnn, ?_⟩
  intro ε X T εinIoo Xgt3 Tgt3
  simp only []
  set σ' : ℝ := 1 - contourWidth / Real.log T with hσ'def
  have hXpos : (0:ℝ) < X := by linarith
  have hM2I4 : M4New SmoothingF ε X T σ' = -starRingEnd ℂ (M2New SmoothingF ε X T σ') := by
    unfold M2New M4New
    simp only [map_mul, map_div₀, conj_I, conj_ofReal, conj_ofNat, map_one]
    rw [mul_neg, div_neg, neg_mul_comm, ← mul_neg]
    congr 1
    rw [← intervalIntegral_conj, neg_neg]
    refine intervalIntegral.integral_congr (fun x hx ↦ ?_)
    rw [← smoothedMobiusIntegrand_conj hXpos]
    congr 1
    simp only [map_sub, map_add, map_one, map_mul, conj_I, conj_ofReal, map_inv₀, mul_neg,
      sub_neg_eq_add]
  rw [hM2I4, norm_neg, RCLike.norm_conj]
  have := hM2 εinIoo Xgt3 Tgt3
  simp only [] at this
  exact this

theorem mobiusM5_bound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Set.Icc (1 / 2) 2)
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (hStrip : MobiusStripInvZetaConsumerBound) :
    ∃ C > 0, ∀ {ε X T : ℝ} (_ : ε ∈ Set.Ioo (0:ℝ) 1) (_ : 3 < X) (_ : 3 < T),
      ‖M5New SmoothingF ε X T‖ ≤ C * (X / (ε * contourTailScale T)) := by
  obtain ⟨C, Cpos, hM1⟩ := mobiusM1_bound suppSmoothingF diffSmoothingF hStrip
  refine ⟨C, Cpos, fun {ε X T} εinIoo Xgt3 Tgt3 ↦ ?_⟩
  have hXpos : (0:ℝ) < X := by linarith
  have hconj : M5New SmoothingF ε X T = starRingEnd ℂ (M1New SmoothingF ε X T) := by
    unfold M1New M5New
    simp only [map_mul, map_div₀, conj_I, conj_ofReal, conj_ofNat, map_one]
    rw [neg_mul, mul_neg, ← neg_mul]
    congr 1
    · ring
    · rw [← integral_conj, ← integral_comp_neg_Ioi, integral_Ici_eq_integral_Ioi]
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      simp only []
      rw [← smoothedMobiusIntegrand_conj hXpos]
      congr 1
      simp only [map_add, map_one, map_mul, conj_I, conj_ofReal, map_inv₀, map_neg, mul_neg,
        neg_neg]
      push_cast
      ring
  rw [hconj, RCLike.norm_conj]
  exact hM1 εinIoo Xgt3 Tgt3

theorem mobiusBoundaryBounds_of_stripInvZeta
    (hStrip : MobiusStripInvZetaConsumerBound) : MobiusBoundaryBoundsCorrectProp := by
  intro SmoothingF suppSmoothingF diffSmoothingF
  obtain ⟨C1, hC1pos, hM1⟩ := mobiusM1_bound suppSmoothingF diffSmoothingF hStrip
  obtain ⟨C5, hC5pos, hM5⟩ := mobiusM5_bound suppSmoothingF diffSmoothingF hStrip
  obtain ⟨C2, hC2nn, hM2⟩ := mobiusM2_bound suppSmoothingF diffSmoothingF hStrip
  obtain ⟨C3, hC3nn, hM3⟩ := mobiusM3_bound suppSmoothingF diffSmoothingF hStrip
  obtain ⟨C4, hC4nn, hM4⟩ := mobiusM4_bound suppSmoothingF diffSmoothingF hStrip
  refine ⟨max (max C1 C5) (max C2 C4) + 1, by positivity, C3 + 1, by positivity, ?_⟩
  intro ε X T εpos εlt1 Xgt3 Tgt3
  have hεIoo : ε ∈ Set.Ioo (0:ℝ) 1 := ⟨εpos, εlt1⟩
  have hXnn : 0 ≤ X / (ε * contourTailScale T) := by
    have : 0 < contourTailScale T := contourTailScale_pos Tgt3
    positivity
  have hcutnn : 0 ≤ X ^ (1 - contourWidth / Real.log T) * contourLogWeight T / ε := by
    have : 0 < contourLogWeight T := contourLogWeight_pos Tgt3
    have : 0 < X ^ (1 - contourWidth / Real.log T) := Real.rpow_pos_of_pos (by linarith) _
    positivity
  have hb1 := hM1 hεIoo Xgt3 Tgt3
  have hb5 := hM5 hεIoo Xgt3 Tgt3
  have hb2 := hM2 hεIoo Xgt3 Tgt3
  have hb3 := hM3 hεIoo Xgt3 Tgt3
  have hb4 := hM4 hεIoo Xgt3 Tgt3
  simp only [] at hb2 hb3 hb4
  refine ⟨hb1.trans ?_, hb5.trans ?_, hb2.trans ?_, hb3.trans ?_, hb4.trans ?_⟩
  · apply mul_le_mul_of_nonneg_right _ hXnn
    have : C1 ≤ max (max C1 C5) (max C2 C4) := le_trans (le_max_left _ _) (le_max_left _ _)
    linarith
  · apply mul_le_mul_of_nonneg_right _ hXnn
    have : C5 ≤ max (max C1 C5) (max C2 C4) := le_trans (le_max_right _ _) (le_max_left _ _)
    linarith
  · apply mul_le_mul_of_nonneg_right _ hXnn
    have : C2 ≤ max (max C1 C5) (max C2 C4) := le_trans (le_max_left _ _) (le_max_right _ _)
    linarith
  · have hmono : C3 * (X ^ (1 - contourWidth / Real.log T) * contourLogWeight T) / ε
        ≤ (C3 + 1) * (X ^ (1 - contourWidth / Real.log T) * contourLogWeight T) / ε := by
      rw [div_le_div_iff_of_pos_right εpos]
      apply mul_le_mul_of_nonneg_right (by linarith)
      have : 0 < contourLogWeight T := contourLogWeight_pos Tgt3
      have : 0 < X ^ (1 - contourWidth / Real.log T) := Real.rpow_pos_of_pos (by linarith) _
      positivity
    exact hmono
  · apply mul_le_mul_of_nonneg_right _ hXnn
    have : C4 ≤ max (max C1 C5) (max C2 C4) := le_trans (le_max_right _ _) (le_max_right _ _)
    linarith

theorem M_eq_sum_range (X : ℝ) :
    M X = ∑ n ∈ Finset.range (⌊X⌋₊ + 1), (μ n : ℝ) := by
  rw [M, Nat.range_succ_eq_Icc_zero, Finset.Iic_eq_Icc, Nat.bot_eq_zero]

theorem smoothedMobius_close_aux {Smooth1 : (ℝ → ℝ) → ℝ → ℝ → ℝ} (SmoothingF : ℝ → ℝ)
    (c₁ : ℝ) (c₁_pos : 0 < c₁) (c₁_lt : c₁ < 1)
    (c₂ : ℝ) (c₂_pos : 0 < c₂) (c₂_lt : c₂ < 2)
    (hc₂ : ∀ (ε x : ℝ), ε ∈ Set.Ioo 0 1 → 1 + c₂ * ε ≤ x → Smooth1 SmoothingF ε x = 0)
    (C : ℝ) (C_eq : C = 6 * (3 * c₁ + c₂))
    (ε : ℝ) (ε_pos : 0 < ε) (ε_lt_one : ε < 1)
    (X : ℝ) (X_pos : 0 < X) (X_gt_three : 3 < X)
    (X_bound_1 : 1 ≤ X * ε * c₁) (X_bound_2 : 1 ≤ X * ε * c₂)
    (smooth1BddAbove : ∀ (n : ℕ), 0 < n → Smooth1 SmoothingF ε (↑n / X) ≤ 1)
    (smooth1BddBelow : ∀ (n : ℕ), 0 < n → Smooth1 SmoothingF ε (↑n / X) ≥ 0)
    (smoothIs1 : ∀ (n : ℕ), 0 < n → ↑n ≤ X * (1 - c₁ * ε) →
      Smooth1 SmoothingF ε (↑n / X) = 1)
    (smoothIs0 : ∀ (n : ℕ), 1 + c₂ * ε ≤ ↑n / X → Smooth1 SmoothingF ε (↑n / X) = 0) :
    ‖(↑((∑' (n : ℕ), (μ n : ℝ) * Smooth1 SmoothingF ε (↑n / X)) : ℝ) : ℂ) -
        (M X : ℂ)‖ ≤ C * ε * X := by
  norm_cast
  rw [M_eq_sum_range]
  let F := Smooth1 SmoothingF ε
  let n₀ := ⌈X * (1 - c₁ * ε)⌉₊
  have n₀_pos : 0 < n₀ := by
    simp only [Nat.ceil_pos, n₀]
    subst C_eq
    have : c₁ * ε < 1 := mul_lt_one_of_nonneg_of_lt_one_left c₁_pos.le c₁_lt ε_lt_one.le
    have : (0 : ℝ) < 1 - c₁ * ε := by linarith
    positivity
  have n₀_inside_le_X : X * (1 - c₁ * ε) ≤ X := by
    nth_rewrite 2 [← mul_one X]
    apply mul_le_mul_of_nonneg_left _ X_pos.le
    apply sub_le_self
    positivity
  have n₀_le : n₀ ≤ X * ((1 - c₁ * ε)) + 1 := by
    simp only [n₀]
    exact le_of_lt (Nat.ceil_lt_add_one (by bound))
  have n₀_gt : X * ((1 - c₁ * ε)) ≤ n₀ := by
    simp only [n₀]
    exact Nat.le_ceil (X * (1 - c₁ * ε))
  have sumμ : Summable (fun (n : ℕ) ↦ (μ n : ℝ) * F (n / X)) := by
    apply summable_of_ne_finset_zero (s := Finset.range ⌈X * (1 + c₂ * ε)⌉₊)
    intro a ha
    apply mul_eq_zero_of_right
    apply hc₂ _ _ ⟨ε_pos, ε_lt_one⟩
    rw [Finset.mem_range, not_lt] at ha
    rw [le_div_iff₀ X_pos]
    have hcl : X * (1 + c₂ * ε) ≤ (a : ℝ) := (Nat.ceil_le).1 ha
    rw [mul_comm]; exact hcl
  have sumμn₀ (n₀ : ℕ) : Summable (fun n ↦ (μ (n + n₀) : ℝ) * F ((n + n₀) / X)) := by
    exact_mod_cast sumμ.comp_injective fun Q => by omega
  rw[← Summable.sum_add_tsum_nat_add' (k := n₀) (mod_cast sumμn₀ n₀)]
  let n₁ := ⌊X * (1 + c₂ * ε)⌋₊
  have n₁_pos : 0 < n₁ := by
    dsimp only [n₁]
    apply Nat.le_floor
    rw[Nat.succ_eq_add_one, zero_add]
    norm_cast
    apply one_le_mul_of_one_le_of_one_le (by linarith)
    apply le_add_of_nonneg_right
    positivity
  have n₁_ge : X * (1 + c₂ * ε) - 1 ≤ n₁ := by
    simp only [tsub_le_iff_right, n₁]
    exact le_of_lt (Nat.lt_floor_add_one (X * (1 + c₂ * ε)))
  have n₁_le : (n₁ : ℝ) ≤ X * (1 + c₂ * ε) := by
    simp only [n₁]
    exact Nat.floor_le (by bound)
  have n₁_ge_n₀ : n₀ ≤ n₁ := by
    exact_mod_cast le_imp_le_of_le_of_le n₀_le n₁_ge (by linarith)
  have n₁_sub_n₀ : (n₁ : ℝ) - n₀ ≤ X * ε * (c₂ + c₁) := by
    calc
      (n₁ : ℝ) - n₀ ≤ X * (1 + c₂ * ε) - n₀ := by
                        exact sub_le_sub_right n₁_le ↑n₀
       _            ≤ X * (1 + c₂ * ε) - (X * (1 - c₁ * ε)) := by
          exact tsub_le_tsub_left n₀_gt (X * (1 + c₂ * ε))
       _            = X * ε * (c₂ + c₁) := by ring
  have hn₁eq : (n₁ - n₀) + n₀ = n₁ := by omega
  rw[show (∑' (n : ℕ), (μ (n + n₀) : ℝ) * Smooth1 SmoothingF ε (((n + n₀ : ℕ) : ℝ) / X)) =
      (∑ n ∈ Finset.range (n₁ - n₀), (μ (n + n₀) : ℝ) * Smooth1 SmoothingF ε (((n + n₀ : ℕ) : ℝ) / X)) +
      (∑' (n : ℕ), (μ (n + n₁) : ℝ) * Smooth1 SmoothingF ε (((n + n₁ : ℕ) : ℝ) / X)) by
    rw[← Summable.sum_add_tsum_nat_add' (k := n₁ - n₀)
        (f := fun n => (μ (n + n₀) : ℝ) * Smooth1 SmoothingF ε ((↑(n + n₀) : ℝ) / X))
        (by have h := sumμn₀ n₁
            apply h.congr; intro n
            simp only [F]
            rw [show n + (n₁ - n₀) + n₀ = n + n₁ by omega]
            push_cast; ring_nf)]
    simp only [Nat.cast_add]
    congr 1
    apply tsum_congr
    intro n
    rw [Nat.cast_sub n₁_ge_n₀, show n + (n₁ - n₀) + n₀ = n + n₁ by omega]
    push_cast; ring_nf]
  rw [show(∑' (n : ℕ), (μ (n + n₁) : ℝ) * F (↑(n + n₁) / X)) = (μ n₁ : ℝ) * F (↑n₁ / X) by
    have : (∑' (n : ℕ), (μ (n + n₁) : ℝ) * F (↑(n + n₁) / X)) =
        (μ n₁ : ℝ) * F (↑n₁ / X) + (∑' (n : ℕ), (μ (n + 1 + n₁) : ℝ) * F (↑(n + 1 + n₁) / X)) := by
      let fTemp := fun n ↦ (μ (n + n₁) : ℝ) * F ((↑n + ↑n₁) / X)
      have hTemp (n : ℕ): fTemp n = (μ (n + n₁) : ℝ) * F (↑(n + n₁) / X) := by rw[Nat.cast_add]
      rw[← tsum_congr hTemp, ← tsum_congr fun n ↦ (hTemp (n + 1))]
      have : (μ n₁ : ℝ) * F (↑n₁ / X) = fTemp 0 := by
        dsimp only [fTemp]
        rw[← Nat.cast_add, zero_add]
      rw[this]
      exact Summable.tsum_eq_zero_add (sumμn₀ n₁)
    rw[this]
    apply add_eq_left.mpr
    convert tsum_zero with n
    convert mul_zero _
    apply smoothIs0
    rw[← mul_le_mul_iff_left₀ X_pos]
    rw [(by field_simp : ↑(n + 1 + n₁) / X * X = ↑(n + 1 + n₁)),
      (by ring : (1 + c₂ * ε) * X = 1 + (X * (1 + c₂ * ε) - 1)), Nat.cast_add, Nat.cast_add]
    bound]
  have X_le_floor_add_one : X ≤ ↑⌊X + 1⌋₊ := by
    rw[Nat.floor_add_one (by linarith), Nat.cast_add, Nat.cast_one]
    apply le_trans <| Nat.le_ceil X
    exact_mod_cast Nat.ceil_le_floor_add_one X
  have floor_X_add_one_le_self : ↑⌊X + 1⌋₊ ≤ X + 1 := Nat.floor_le (by positivity)
  have hn₀_le_floorX1 : n₀ ≤ ⌊X + 1⌋₊ := by
    simp only [Nat.ceil_le, n₀]
    exact le_trans n₀_inside_le_X X_le_floor_add_one
  rw [show ∑ n ∈ Finset.range (⌊X⌋₊ + 1), (μ n : ℝ) =
      (∑ x ∈ Finset.range n₀, (μ x : ℝ)) +
      ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), (μ (x + n₀) : ℝ) by
    rw [show (⌊X⌋₊ + 1) = ⌊X + 1⌋₊ by rw [Nat.floor_add_one X_pos.le]]
    conv_lhs => rw [show ⌊X + 1⌋₊ = n₀ + (⌊X + 1⌋₊ - n₀) by omega]
    rw [Finset.sum_range_add]
    simp only [add_comm n₀]]
  rw [show ∑ n ∈ Finset.range n₀, (μ n : ℝ) * F (↑n / X) =
      ∑ n ∈ Finset.range n₀, (μ n : ℝ) by
    apply Finset.sum_congr rfl
    intro n hn
    obtain rfl|n_zero := eq_or_ne n 0
    · simp only [ArithmeticFunction.map_zero, Int.cast_zero, CharP.cast_eq_zero,
        zero_div, zero_mul, Nat.cast_zero]
    · convert mul_one _
      apply smoothIs1 n (Nat.zero_lt_of_ne_zero n_zero) ?_
      simp only [Finset.mem_range, n₀] at hn
      exact Nat.lt_ceil.mp hn |>.le]
  have muBnd1 :
    ∀ n ∈ Finset.range (n₁ - n₀), ‖(μ (n + n₀) : ℝ)‖ ≤ 1 := by
    intro n _
    rw [Real.norm_eq_abs]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have bnd1 :
    ∑ n ∈ Finset.range (n₁ - n₀), ‖(μ (n + n₀) : ℝ)‖ * ‖F ((↑n + ↑n₀) / X)‖
    ≤ (n₁ - n₀) * (1 : ℝ) := by
    have : ((n₁ : ℝ) - n₀) * (1 : ℝ) =
        (∑ n ∈ Finset.range (n₁ - n₀), (1 : ℝ)) := by
      rw [← Nat.cast_sub n₁_ge_n₀]; simp
    rw [this]
    apply Finset.sum_le_sum
    intro n hn
    rw [← mul_one (1 : ℝ)]
    apply mul_le_mul (muBnd1 _ hn) _ (norm_nonneg _) (by norm_num)
    rw[Real.norm_of_nonneg, ← Nat.cast_add]
    · dsimp only [F]
      apply smooth1BddAbove
      bound
    rw[← Nat.cast_add]
    dsimp only [F]
    apply smooth1BddBelow
    bound
  have bnd2 :
    ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), ‖(μ (x + n₀) : ℝ)‖ ≤ ((⌊X + 1⌋₊ : ℝ) - n₀) * (1 : ℝ) := by
    have : ((⌊X + 1⌋₊ : ℝ) - n₀) * (1 : ℝ) =
        (∑ n ∈ Finset.range (⌊X + 1⌋₊ - n₀), (1 : ℝ)) := by
      rw [← Nat.cast_sub hn₀_le_floorX1]; simp
    rw[this]
    apply Finset.sum_le_sum
    intro n _
    rw [Real.norm_eq_abs]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have muBndLast : ‖(μ n₁ : ℝ)‖ * ‖F (↑n₁ / X)‖ ≤ 1 := by
    rw [← mul_one (1 : ℝ)]
    apply mul_le_mul _ _ (norm_nonneg _) (by norm_num)
    · rw [Real.norm_eq_abs]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    rw [Real.norm_of_nonneg (smooth1BddBelow _ n₁_pos)]
    exact smooth1BddAbove _ n₁_pos
  calc
    _ = ‖∑ n ∈ Finset.range (n₁ - n₀), (μ (n + n₀) : ℝ) * F ((↑n + ↑n₀) / X) -
          ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), (μ (x + n₀) : ℝ) + (μ n₁ : ℝ) * F (↑n₁ / X)‖ := by
      congr 1
      push_cast
      ring
    _ ≤ (∑ n ∈ Finset.range (n₁ - n₀), ‖(μ (n + n₀) : ℝ)‖ * ‖F ((↑n + ↑n₀) / X)‖) +
        ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), ‖(μ (x + n₀) : ℝ)‖ +
        ‖(μ n₁ : ℝ)‖ * ‖F (↑n₁ / X)‖ := by
      apply norm_add_le_of_le
      · apply norm_sub_le_of_le
        · apply norm_sum_le_of_le
          intro b _
          exact norm_mul_le_of_le (by rfl) (by rfl)
        apply norm_sum_le_of_le
        intro b _
        rfl
      exact_mod_cast norm_mul_le_of_le (by rfl) (by rfl)
    _ ≤ (((n₁ : ℝ) - n₀) * (1 : ℝ)) + (((⌊X + 1⌋₊ : ℝ) - n₀) * (1 : ℝ)) + 1 := by
      apply add_le_add (add_le_add bnd1 bnd2) muBndLast
    _ ≤ C * ε * X := by
      have hn₁n₀ : ((n₁ : ℝ) - n₀) ≤ X * ε * (c₂ + c₁) := n₁_sub_n₀
      have hfloor_n₀ : ((⌊X + 1⌋₊ : ℝ) - n₀) ≤ 2 * (X * ε * c₁) := by
        rw [(by ring : 2 * (X * ε * c₁) = (X * (1 + ε * c₁)) - (X * (1 - ε * c₁)))]
        apply sub_le_sub
        · apply le_trans floor_X_add_one_le_self
          nth_rewrite 1 [(by ring : X * (1 + ε * c₁) = X + X * ε * c₁)]
          rw [add_le_add_iff_left]
          linarith [X_bound_1]
        · have : X * (1 - ε * c₁) = X * (1 - c₁ * ε) := by ring
          rw [this]; exact n₀_gt
      have key : ((n₁ : ℝ) - n₀) + ((⌊X + 1⌋₊ : ℝ) - n₀) + 1
          ≤ X * ε * (c₂ + c₁) + 2 * (X * ε * c₁) + X * ε * c₁ := by
        apply add_le_add (add_le_add hn₁n₀ hfloor_n₀)
        linarith [X_bound_1]
      calc
        ((n₁ : ℝ) - n₀) * 1 + ((⌊X + 1⌋₊ : ℝ) - n₀) * 1 + 1
            = ((n₁ : ℝ) - n₀) + ((⌊X + 1⌋₊ : ℝ) - n₀) + 1 := by ring
        _ ≤ X * ε * (c₂ + c₁) + 2 * (X * ε * c₁) + X * ε * c₁ := key
        _ = (4 * c₁ + c₂) * (ε * X) := by ring
        _ ≤ C * ε * X := by
          rw [C_eq]
          have h0 : 0 ≤ ε * X := by positivity
          nlinarith [h0, mul_pos ε_pos X_pos, c₁_pos, c₂_pos]

theorem lseriesSummable_moebius {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (μ n : ℂ)) s :=
  LSeriesSummable_of_bounded_of_one_lt_re (m := 1)
    (fun n _ => by
      simp only [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one) hs

set_option backward.isDefEq.respectTransparency false in
theorem smoothedMobius_aux_tsum_integral {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFpos : ∀ x > 0, 0 ≤ SmoothingF x)
    (suppSmoothingF : Function.support SmoothingF ⊆ Set.Icc (1 / 2) 2)
    (mass_one : ∫ (x : ℝ) in Set.Ioi 0, SmoothingF x / x = 1) {X : ℝ}
    (X_pos : 0 < X) {ε : ℝ} (εpos : 0 < ε)
    (ε_lt_one : ε < 1) {σ : ℝ} (σ_gt : 1 < σ) (σ_le : σ ≤ 2) :
    ∫ (t : ℝ),
      ∑' (n : ℕ), (μ n : ℂ) / (n : ℂ) ^ (σ + t * I) *
        mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + t * I) * (X : ℂ) ^ (σ + t * I) =
    ∑' (n : ℕ),
      ∫ (t : ℝ), (μ n : ℂ) / (n : ℂ) ^ (σ + ↑t * I) *
        mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) * (X : ℂ) ^ (σ + t * I) := by
  have abs_two : ∀ a : ℝ, ∀ i : ℕ, ‖(i : ℂ) ^ ((σ : ℂ) + ↑a * I)‖₊ = i ^ σ := by
    intro a i
    simp_rw [← norm_toNNReal]
    rw [norm_natCast_cpow_of_re_ne_zero _ (by simp only [add_re, ofReal_re, mul_re, I_re, mul_zero,
      ofReal_im, I_im, mul_one, sub_self, add_zero, ne_eq]; linarith)]
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, Real.toNNReal_of_nonneg <| rpow_nonneg (y := σ) (x := i) (by linarith)]
    norm_cast
  rw [MeasureTheory.integral_tsum]
  · have x_neq_zero : X ≠ 0 := by linarith
    intro i
    by_cases i_eq_zero : i = 0
    · simpa [i_eq_zero] using aestronglyMeasurable_const
    · apply Continuous.aestronglyMeasurable
      have cont_mellin_smooth : Continuous fun (a : ℝ) ↦
          mellin (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (σ + ↑a * I) := by
        rw [← continuousOn_univ]
        refine ContinuousOn.comp' ?_ ?_ ?_ (t := {z : ℂ | 0 < z.re })
        · refine continuousOn_of_forall_continuousAt ?_
          intro z hz
          exact (Smooth1MellinDifferentiable diffSmoothingF suppSmoothingF ⟨εpos, ε_lt_one⟩
            SmoothingFpos mass_one hz).continuousAt
        · fun_prop
        · simp only [Set.mapsTo_univ_iff, Set.mem_setOf_eq, add_re, ofReal_re, mul_re, I_re, mul_zero,
            ofReal_im, I_im, mul_one, sub_self, add_zero, forall_const]; linarith
      fun_prop (disch := simp[i_eq_zero, x_neq_zero])
  · rw [← lt_top_iff_ne_top]
    simp_rw [enorm_mul, enorm_eq_nnnorm, nnnorm_div, ← norm_toNNReal,
      Complex.norm_cpow_eq_rpow_re_of_pos X_pos, norm_toNNReal, abs_two]
    simp only [nnnorm_real, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, add_zero]
    simp_rw [MeasureTheory.lintegral_mul_const' (r := ↑(X ^ σ).toNNReal) (hr := by simp),
      ENNReal.tsum_mul_right]
    apply WithTop.mul_lt_top ?_ ENNReal.coe_lt_top
    conv =>
      arg 1
      arg 1
      intro i
      rw [MeasureTheory.lintegral_const_mul' (hr := by simp)]
    rw [ENNReal.tsum_mul_right]
    apply WithTop.mul_lt_top
    · have hsumm : Summable (fun i : ℕ => ‖(μ i : ℂ)‖₊ / (i : NNReal) ^ σ) := by
        apply NNReal.summable_coe.mp
        have h := (lseriesSummable_moebius (s := σ)
          (by simp only [ofReal_re]; linarith)).norm
        apply h.congr
        intro n
        rw [LSeries.term_def]
        split_ifs with h
        · simp [h]
        · rw [NNReal.coe_div]
          simp only [coe_nnnorm, NNReal.coe_rpow, NNReal.coe_natCast]
          rw [norm_div, Complex.norm_natCast_cpow_of_pos (by omega), Complex.ofReal_re]
      have hfin := (ENNReal.tsum_coe_ne_top_iff_summable).mpr hsumm
      have hlt := lt_of_le_of_ne le_top hfin
      exact hlt
    · exact MeasureTheory.hasFiniteIntegral_iff_enorm.mp
        (SmoothedChebyshevDirichlet_aux_integrable diffSmoothingF SmoothingFpos suppSmoothingF
            mass_one εpos ε_lt_one σ_gt σ_le).hasFiniteIntegral

set_option backward.isDefEq.respectTransparency false in
theorem smoothedMobius_dirichlet {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFpos : ∀ x > 0, 0 ≤ SmoothingF x)
    (suppSmoothingF : Function.support SmoothingF ⊆ Set.Icc (1 / 2) 2)
    (mass_one : ∫ x in Set.Ioi (0 : ℝ), SmoothingF x / x = 1)
    {X : ℝ} (X_gt : 3 < X) {ε : ℝ} (εpos : 0 < ε) (ε_lt_one : ε < 1) :
    smoothedMobius SmoothingF ε X =
      ∑' n, (μ n : ℂ) * Smooth1 SmoothingF ε (n / X) := by
  dsimp [smoothedMobius, smoothedMobiusIntegrand, VerticalIntegral', VerticalIntegral]
  set σ : ℝ := 1 + (Real.log X)⁻¹
  have log_gt : 1 < Real.log X := logt_gt_one X_gt.le
  have σ_gt : 1 < σ := by
    simp only [σ]
    have : 0 < (Real.log X)⁻¹ := by simp only [inv_pos]; linarith
    linarith
  have σ_le : σ ≤ 2 := by
    simp only [σ]
    have : (Real.log X)⁻¹ < 1 := inv_lt_one_of_one_lt₀ log_gt
    linarith
  calc
    _ = 1 / (2 * π * I) * (I * ∫ (t : ℝ), ∑' n, (μ n : ℂ) / (n : ℂ) ^ (σ + ↑t * I) *
      mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) * X ^ (σ + ↑t * I)) := ?_
    _ = 1 / (2 * π * I) * (I * ∑' n, ∫ (t : ℝ), (μ n : ℂ) / (n : ℂ) ^ (σ + ↑t * I) *
      mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) * X ^ (σ + ↑t * I)) := ?_
    _ = 1 / (2 * π * I) * (I * ∑' n, (μ n : ℂ) * ∫ (t : ℝ),
      mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) *
        (X / (n : ℂ)) ^ (σ + ↑t * I)) := ?_
    _ = 1 / (2 * π) * (∑' n, (μ n : ℂ) * ∫ (t : ℝ),
      mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) *
        (X / (n : ℂ)) ^ (σ + ↑t * I)) := ?_
    _ = ∑' n, (μ n : ℂ) * (1 / (2 * π) * ∫ (t : ℝ),
      mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) *
        (X / (n : ℂ)) ^ (σ + ↑t * I)) := ?_
    _ = ∑' n, (μ n : ℂ) * (1 / (2 * π) * ∫ (t : ℝ),
      mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) *
        ((n : ℂ) / X) ^ (-(σ + ↑t * I))) := ?_
    _ = _ := ?_
  · congr; ext t
    rw [show ((riemannZeta (σ + ↑t * I))⁻¹ : ℂ) = ∑' n, (μ n : ℂ) / (n : ℂ) ^ (σ + ↑t * I) from ?_]
    · rw [← tsum_mul_right, ← tsum_mul_right]
    · rw [← LSeries_moebius_eq_inv_zeta (by simp [σ_gt])]
      dsimp only [LSeries, LSeries.term]
      apply tsum_congr
      intro n
      by_cases h : n = 0 <;> simp [h]
  · congr
    exact smoothedMobius_aux_tsum_integral diffSmoothingF SmoothingFpos
      suppSmoothingF mass_one (by linarith) εpos ε_lt_one σ_gt σ_le
  · field_simp; congr; ext n; rw [← MeasureTheory.integral_const_mul]; congr; ext t
    by_cases n_ne_zero : n = 0
    · simp [n_ne_zero]
    rw [mul_div_assoc, mul_assoc]
    congr
    rw [(div_eq_iff ?_).mpr]
    · have := @mul_cpow_ofReal_nonneg (a := X / (n : ℝ)) (b := (n : ℝ)) (r := σ + I * t) ?_ ?_
      · push_cast at this ⊢
        rw [← this, div_mul_cancel₀]
        · simp only [ne_eq, Nat.cast_eq_zero, n_ne_zero, not_false_eq_true]
      · apply div_nonneg (by linarith : 0 ≤ X); simp
      · simp
    · simp only [ne_eq, cpow_eq_zero_iff, Nat.cast_eq_zero, n_ne_zero, false_and,
        not_false_eq_true]
  · conv => rw [← mul_assoc, div_mul]; lhs; lhs; rhs; simp
  · simp_rw [← tsum_mul_left, ← mul_assoc, mul_comm]
  · have ht (t : ℝ) : -(σ + t * I) = (-1) * (σ + t * I) := by simp
    have hn (n : ℂ) : (n / X) ^ (-1 : ℂ) = X / n := by simp [cpow_neg_one]
    have (n : ℕ) : (log ((n : ℂ) / (X : ℂ)) * -1).im = 0 := by
      simp [Complex.log_im, arg_eq_zero_iff, div_nonneg (Nat.cast_nonneg _) (by linarith : 0 ≤ X)]
    have h (n : ℕ) (t : ℝ) : ((n : ℂ) / X) ^ ((-1 : ℂ) * (σ + t * I)) =
        ((n / X) ^ (-1 : ℂ)) ^ (σ + ↑t * I) := by
      rw [cpow_mul] <;> {rw [this n]; simp [Real.pi_pos, Real.pi_nonneg]}
    conv => rhs; lhs; intro n; rhs; rhs; rhs; intro t; rhs; rw [ht t, h n t]; lhs; rw [hn]
  · push_cast
    congr
    ext n
    by_cases n_zero : n = 0
    · simp [n_zero]
    have n_pos : 0 < n := by
      simpa only [n_zero, gt_iff_lt, false_or] using (Nat.eq_zero_or_pos n)
    congr
    have := mellinInv_mellin_eq σ (f := fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (x := n / X)
      ?_ ?_ ?_ ?_
    · beta_reduce at this
      dsimp [mellinInv, VerticalIntegral] at this
      convert! this using 4
      · norm_cast
      · rw [mul_comm]
        norm_cast
    · exact div_pos (by exact_mod_cast n_pos) (by linarith : 0 < X)
    · apply Smooth1MellinConvergent diffSmoothingF suppSmoothingF ⟨εpos, ε_lt_one⟩
        SmoothingFpos mass_one
      simp only [ofReal_re]
      linarith
    · dsimp [VerticalIntegrable]
      apply SmoothedChebyshevDirichlet_aux_integrable diffSmoothingF SmoothingFpos
        suppSmoothingF mass_one εpos ε_lt_one σ_gt σ_le
    · refine ContinuousAt.comp (g := ofReal) RCLike.continuous_ofReal.continuousAt ?_
      exact Smooth1ContinuousAt diffSmoothingF SmoothingFpos suppSmoothingF
        εpos (by positivity)

theorem smoothedMobius_close_eps {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (suppSmoothingF : Function.support SmoothingF ⊆ Set.Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Set.Ioi (0 : ℝ), SmoothingF x / x = 1) :
    ∃ C > 0, ∀ (X : ℝ), 3 < X → ∀ (ε : ℝ), 0 < ε → ε < 1 → 2 < X * ε →
    ‖smoothedMobius SmoothingF ε X - (M X : ℂ)‖ ≤ C * ε * X := by
  obtain ⟨c₁, c₁_pos, c₁_eq, hc₁⟩ := Smooth1Properties_below suppSmoothingF mass_one
  obtain ⟨c₂, c₂_pos, c₂_eq, hc₂⟩ := Smooth1Properties_above suppSmoothingF
  have c₁_lt : c₁ < 1 := by
    rw [c₁_eq]; exact lt_trans (Real.log_two_lt_d9) (by norm_num)
  have c₂_lt : c₂ < 2 := by
    rw [c₂_eq]
    nth_rewrite 3 [← mul_one 2]
    apply mul_lt_mul'
    · rfl
    · exact lt_trans (Real.log_two_lt_d9) (by norm_num)
    · exact Real.log_nonneg (by norm_num)
    · positivity
  let C : ℝ := 6 * (3 * c₁ + c₂)
  have C_eq : C = 6 * (3 * c₁ + c₂) := rfl
  have Cpos : 0 < C := by rw [C_eq]; positivity
  refine ⟨C, Cpos, fun X X_gt ε εpos ε_lt_one X_bound => ?_⟩
  have X_gt_zero : (0 : ℝ) < X := by linarith
  have n_on_X_pos {n : ℕ} (npos : 0 < n) : 0 < (n : ℝ) / X := by
    have : (0 : ℝ) < n := by exact_mod_cast npos
    positivity
  have smooth1BddAbove (n : ℕ) (npos : 0 < n) : Smooth1 SmoothingF ε (n / X) ≤ 1 :=
    Smooth1LeOne SmoothingFnonneg mass_one εpos (n_on_X_pos npos)
  have smooth1BddBelow (n : ℕ) (npos : 0 < n) : Smooth1 SmoothingF ε (n / X) ≥ 0 :=
    Smooth1Nonneg SmoothingFnonneg (n_on_X_pos npos) εpos
  have smoothIs1 (n : ℕ) (npos : 0 < n) (n_le : (n : ℝ) ≤ X * (1 - c₁ * ε)) :
      Smooth1 SmoothingF ε (↑n / X) = 1 := by
    apply hc₁ (ε := ε) (n / X) εpos (n_on_X_pos npos)
    exact (div_le_iff₀' X_gt_zero).mpr n_le
  have smoothIs0 (n : ℕ) (n_le : (1 + c₂ * ε) ≤ (n : ℝ) / X) :
      Smooth1 SmoothingF ε (↑n / X) = 0 :=
    hc₂ (ε := ε) (n / X) ⟨εpos, ε_lt_one⟩ n_le
  have X_bound_1 : 1 ≤ X * ε * c₁ := by
    rw [c₁_eq, ← div_le_iff₀ (Real.log_pos (by norm_num))]
    have : 1 / Real.log 2 < 2 := by
      nth_rewrite 2 [← one_div_one_div 2]
      rw [one_div_lt_one_div]
      · exact lt_of_le_of_lt (by norm_num) (Real.log_two_gt_d9)
      · exact Real.log_pos (by norm_num)
      · norm_num
    exact le_of_lt (gt_trans X_bound this)
  have X_bound_2 : 1 ≤ X * ε * c₂ := by
    rw [c₂_eq, ← div_le_iff₀ (by norm_num; exact Real.log_pos (by norm_num))]
    have : 1 / (2 * Real.log 2) < 2 := by
      nth_rewrite 3 [← one_div_one_div 2]
      rw [one_div_lt_one_div, ← one_mul (1 / 2)]
      · apply mul_lt_mul
        · norm_num
        · exact le_of_lt (lt_trans (by norm_num) (Real.log_two_gt_d9))
        · norm_num
        · norm_num
      · norm_num; exact Real.log_pos (by norm_num)
      · norm_num
    exact le_of_lt (gt_trans X_bound this)
  rw [smoothedMobius_dirichlet diffSmoothingF SmoothingFnonneg suppSmoothingF mass_one X_gt
    εpos ε_lt_one]
  have hsum_real : (∑' n, (μ n : ℂ) * Smooth1 SmoothingF ε (n / X)) =
      ((∑' (n : ℕ), (μ n : ℝ) * Smooth1 SmoothingF ε (↑n / X) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    apply tsum_congr; intro n; push_cast; ring
  rw [hsum_real]
  exact smoothedMobius_close_aux SmoothingF c₁ c₁_pos c₁_lt c₂ c₂_pos c₂_lt hc₂ C C_eq ε
    εpos ε_lt_one X X_gt_zero X_gt X_bound_1 X_bound_2 smooth1BddAbove smooth1BddBelow
    smoothIs1 smoothIs0

private theorem two_lt_X_mul_mertens_eps : ∀ᶠ X in atTop, 2 < X * mertens_eps X := by
  have hvlim := Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  filter_upwards [hvlim.eventually_gt_atTop (contourEndpoint + 2), Filter.eventually_gt_atTop (1 : ℝ)]
    with X hlarge hX
  have hlarge' : contourEndpoint + 2 < Real.sqrt (Real.log X) := hlarge
  have hv := Real.sqrt_pos.mpr (Real.log_pos hX)
  have he : 1 < Real.log X - contourEndpoint * Real.sqrt (Real.log X) := by
    nlinarith [mul_pos (sub_pos.mpr hlarge') hv, Real.sq_sqrt (Real.log_nonneg hX.le),
      contourEndpoint_pos]
  calc
    (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    _ < Real.exp (Real.log X - contourEndpoint * Real.sqrt (Real.log X)) := Real.exp_lt_exp.mpr he
    _ = X * Real.exp (-contourEndpoint * Real.sqrt (Real.log X)) := by
      rw [Real.exp_sub, Real.exp_log (by linarith : 0 < X), neg_mul,
        Real.exp_neg, div_eq_mul_inv]
    _ ≤ X * mertens_eps X := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      apply le_mul_of_one_le_left (Real.exp_pos _).le
      linarith [mul_nonneg (Real.sqrt_nonneg contourWidth) (Real.sqrt_nonneg (Real.log X))]

/-- Any strict loss in the square-root coefficient absorbs the linear
prefactor, uniformly as the real cutoff tends to infinity. -/
theorem linear_prefactor_sqrtLog_isBigO (k a c : ℝ) (hk : 0 ≤ k) (hca : c < a) :
    (fun x : ℝ => x * ((1 + k * Real.sqrt (Real.log x)) *
      Real.exp (-a * Real.sqrt (Real.log x)))) =O[atTop]
      (fun x : ℝ => x * Real.exp (-c * Real.sqrt (Real.log x))) := by
  let γ := a - c
  have hγ : 0 < γ := sub_pos.mpr hca
  refine Asymptotics.isBigO_iff.mpr ⟨1 + k / γ, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with x hx
  let y := Real.sqrt (Real.log x)
  have hy : 0 ≤ y := Real.sqrt_nonneg _
  have h₁ : 1 ≤ Real.exp (γ * y) := Real.one_le_exp_iff.mpr (mul_nonneg hγ.le hy)
  have h₂ : γ * y ≤ Real.exp (γ * y) := by linarith only [Real.add_one_le_exp (γ * y)]
  have he : k / γ * (γ * y) = k * y := by field_simp [hγ.ne']
  have h₃ := mul_le_mul_of_nonneg_left h₂ (div_nonneg hk hγ.le)
  rw [he] at h₃
  have hp : 1 + k * y ≤ (1 + k / γ) * Real.exp (γ * y) := by
    nlinarith only [h₁, h₃]
  have hsum : γ * y + -a * y = -c * y := by dsimp only [γ]; ring
  change ‖x * ((1 + k * y) * Real.exp (-a * y))‖ ≤
    (1 + k / γ) * ‖x * Real.exp (-c * y)‖
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ x * (((1 + k / γ) * Real.exp (γ * y)) * Real.exp (-a * y)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le) hx
    _ = _ := by rw [mul_assoc (1 + k / γ), ← Real.exp_add, hsum]; ring

/-- The ordinary Mertens function with the coefficient given by the common zero-free
and reciprocal-ζ strip. -/
theorem classical_mertens_at_weighted_contourEndpoint :
    M =O[atTop] (fun X : ℝ => X * ((1 + Real.sqrt contourWidth * Real.sqrt (Real.log X)) *
      Real.exp (-contourEndpoint * Real.sqrt (Real.log X)))) := by
  obtain ⟨ν, hνC, hνnn, hνsupp, hνmass⟩ := SmoothExistence
  have hdiff : ContDiff ℝ 1 ν := hνC.of_le (by exact_mod_cast le_top)
  have hnn : ∀ x > 0, 0 ≤ ν x := fun x _ => hνnn x
  have hmass : ∫ x in Set.Ioi (0 : ℝ), ν x / x = 1 := by
    rw [← hνmass, MeasureTheory.integral_Ici_eq_integral_Ioi]
  have hstrip : MobiusStripInvZetaConsumerBound :=
    classical_mertens_reciprocal_rectangle.choose_spec.2.2.1
  obtain ⟨C, hcontour⟩ := smoothedMobius_bound_at_contourEndpoint
    (mobiusBoundaryBounds_of_stripInvZeta hstrip) hνsupp hnn hmass hdiff
  obtain ⟨D, _, hclose⟩ := smoothedMobius_close_eps hdiff hνsupp hnn hmass
  rw [Asymptotics.isBigO_iff]
  refine ⟨C + D, ?_⟩
  filter_upwards [hcontour, two_lt_X_mul_mertens_eps, Filter.eventually_gt_atTop (3 : ℝ), mertens_eps_mem]
    with X hC hXε hX hεmem
  obtain ⟨hε, hε1⟩ := hεmem
  have hD := hclose X hX (mertens_eps X) hε hε1 hXε
  let S := smoothedMobius ν (mertens_eps X) X
  have hM : ‖(M X : ℂ)‖ ≤ (C + D) * (X * mertens_eps X) := calc
    _ = ‖S - (S - (M X : ℂ))‖ := by rw [sub_sub_cancel]
    _ ≤ ‖S‖ + ‖S - (M X : ℂ)‖ := norm_sub_le _ _
    _ ≤ _ := add_le_add hC hD
    _ = _ := by ring
  change ‖M X‖ ≤ (C + D) * ‖X * mertens_eps X‖
  rw [Real.norm_of_nonneg (mul_nonneg (by linarith) hε.le)]
  simpa only [Complex.norm_real] using hM

/-- Every coefficient strictly below half the square root of the certified strip
width gives an unweighted estimate. -/
theorem classical_mertens_below_contourEndpoint {c : ℝ} (hc : c < contourEndpoint) :
    M =O[atTop] (fun X : ℝ => X * Real.exp (-c * Real.sqrt (Real.log X))) :=
  classical_mertens_at_weighted_contourEndpoint.trans
    (linear_prefactor_sqrtLog_isBigO _ _ _ (Real.sqrt_nonneg contourWidth) hc)

theorem classical_mertens_at_contourRate :
    M =O[atTop] (fun X : ℝ => X * Real.exp (-contourRate * Real.sqrt (Real.log X))) :=
  classical_mertens_below_contourEndpoint (by
    unfold contourRate contourEndpoint
    linarith [Real.sqrt_pos.mpr contourWidth_pos])

end RiemannResearch.NumberTheory.PrimeNumberTheorem.Quantitative.MobiusContour

namespace RiemannResearch.NumberTheory.PrimeNumberTheorem

/-- The ordinary Mertens function is O(x exp(−c √(log x))) for some c > 0. -/
theorem M_isBigO_exp_neg_sqrt_log :
    ∃ c : ℝ, 0 < c ∧ M =O[atTop] (fun x : ℝ => x * Real.exp (-c * Real.sqrt (Real.log x))) :=
  ⟨Quantitative.MobiusContour.contourRate, Quantitative.MobiusContour.contourRate_pos,
    Quantitative.MobiusContour.classical_mertens_at_contourRate⟩

/-- A square-root logarithmic estimate with a weight at least one has the
same coefficient on the whole interval starting at one. -/
private theorem M_globalize_sqrt_log (w : ℝ → ℝ) (hw : ∀ x : ℝ, 1 ≤ x → 1 ≤ w x)
    (c : ℝ) (hc : 0 < c)
    (hbig : M =O[atTop] fun x : ℝ => x * (w x * Real.exp (-c * Real.sqrt (Real.log x)))) :
    ∃ B > 0, ∀ x : ℝ, 1 ≤ x →
      |M x| ≤ B * x * (w x * Real.exp (-c * Real.sqrt (Real.log x))) := by
  obtain ⟨K, hK, hbound⟩ := hbig.exists_pos
  have ht : ∀ᶠ x : ℝ in atTop,
      |M x| ≤ K * x * (w x * Real.exp (-c * Real.sqrt (Real.log x))) := by
    filter_upwards [hbound.bound, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    have hw0 := zero_le_one.trans (hw x hx1)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (zero_le_one.trans hx1)
      (mul_nonneg hw0 (Real.exp_pos _).le)), mul_assoc] using hx
  obtain ⟨T, hT⟩ := eventually_atTop.mp ht
  let A := 2 * Real.exp (c * Real.sqrt (Real.log (max 1 T)))
  refine ⟨max K A, hK.trans_le (le_max_left _ _), fun x hx => ?_⟩
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  by_cases hTx : T ≤ x
  · exact (hT x hTx).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hx0)
      (mul_nonneg (zero_le_one.trans (hw x hx)) (Real.exp_pos _).le))
  have hnx : |M x| ≤ 2*x := by
    rw [Quantitative.MobiusContour.M_eq_sum_range]
    calc
      _ ≤ ∑ n ∈ Finset.range (⌊x⌋₊+1), |(ArithmeticFunction.moebius n : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _n ∈ Finset.range (⌊x⌋₊+1), (1 : ℝ) :=
        Finset.sum_le_sum fun n _ => by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      _ = (⌊x⌋₊ : ℝ) + 1 := by simp
      _ ≤ 2*x := by linarith [Nat.floor_le hx0]
  have hmon := Real.sqrt_le_sqrt
    (Real.log_le_log (zero_lt_one.trans_le hx) ((le_of_not_ge hTx).trans (le_max_right 1 T)))
  have hge : 1 ≤ Real.exp (c * Real.sqrt (Real.log (max 1 T))) *
      Real.exp (-c * Real.sqrt (Real.log x)) := by
    rw [← Real.exp_add, Real.one_le_exp_iff]
    linarith only [mul_le_mul_of_nonneg_left hmon hc.le]
  calc
    _ ≤ 2 * x := hnx
    _ ≤ (2 * x) * (Real.exp (c * Real.sqrt (Real.log (max 1 T))) *
          Real.exp (-c * Real.sqrt (Real.log x))) := by
      simpa using mul_le_mul_of_nonneg_left hge (show 0 ≤ 2*x by positivity)
    _ = A * x * Real.exp (-c * Real.sqrt (Real.log x)) := by dsimp only [A]; ring
    _ ≤ max K A * x * Real.exp (-c * Real.sqrt (Real.log x)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hx0)
        (Real.exp_pos _).le
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (le_mul_of_one_le_left (Real.exp_pos _).le (hw x hx))
      (mul_nonneg (hK.le.trans (le_max_left _ _)) hx0)

/-- The same positive coefficient works on the entire interval starting at
one after increasing only the multiplicative constant. -/
theorem M_sqrt_log_global_of_isBigO (c : ℝ) (hc : 0 < c)
    (hbig : M =O[atTop] fun x : ℝ => x * Real.exp (-c * Real.sqrt (Real.log x))) :
    ∃ B > 0, ∀ x : ℝ, 1 ≤ x →
      |M x| ≤ B * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  simpa only [one_mul] using M_globalize_sqrt_log (fun _ => 1) (fun _ _ => le_rfl) c hc
    (by simpa only [one_mul] using hbig)

/-- Global endpoint bound including the logarithmic factor. -/
theorem M_sqrt_log_weighted_endpoint_global :
    ∃ B > 0, ∀ x : ℝ, 1 ≤ x → |M x| ≤ B * x *
      ((1 + Real.sqrt Quantitative.MobiusContour.contourWidth * Real.sqrt (Real.log x)) *
      Real.exp (-Quantitative.MobiusContour.contourEndpoint * Real.sqrt (Real.log x))) := by
  exact M_globalize_sqrt_log
    (fun x => 1 + Real.sqrt Quantitative.MobiusContour.contourWidth * Real.sqrt (Real.log x))
    (fun x _ => le_add_of_nonneg_right (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
    _ Quantitative.MobiusContour.contourEndpoint_pos
    Quantitative.MobiusContour.classical_mertens_at_weighted_contourEndpoint

/-- The ordinary Mertens bound holds for every real cutoff starting at one. -/
theorem M_sqrt_log_global :
    ∃ c > 0, ∃ B > 0, ∀ x : ℝ, 1 ≤ x →
      |M x| ≤ B * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  obtain ⟨c, hc, h⟩ := M_isBigO_exp_neg_sqrt_log
  exact ⟨c, hc, M_sqrt_log_global_of_isBigO c hc h⟩

/-- Every positive coefficient strictly below half the square root of the
certified width works uniformly on the entire real interval starting at one. -/
theorem M_sqrt_log_global_of_lt_contourEndpoint (c : ℝ) (hc : 0 < c)
    (hca : c < Quantitative.MobiusContour.contourEndpoint) :
    ∃ B > 0, ∀ x : ℝ, 1 ≤ x →
      |M x| ≤ B * x * Real.exp (-c * Real.sqrt (Real.log x)) :=
  M_sqrt_log_global_of_isBigO c hc
    (Quantitative.MobiusContour.classical_mertens_below_contourEndpoint hca)

/-- Each strict interior coefficient also allows eventual prefactor one. -/
theorem M_sqrt_log_eventually_of_lt_contourEndpoint (c : ℝ) (hc : 0 < c)
    (hca : c < Quantitative.MobiusContour.contourEndpoint) :
    ∀ᶠ x : ℝ in atTop, |M x| ≤ x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  obtain ⟨c', hcc', hc'⟩ := exists_between hca
  obtain ⟨B, _, hM⟩ := M_sqrt_log_global_of_lt_contourEndpoint c' (hc.trans hcc') hc'
  have hy := Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  have hB := (Real.tendsto_exp_atTop.comp
    (Tendsto.const_mul_atTop (sub_pos.mpr hcc') hy)).eventually (eventually_ge_atTop B)
  filter_upwards [hB, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  let y := Real.sqrt (Real.log x)
  change B ≤ Real.exp ((c' - c) * y) at hx
  calc
    |M x| ≤ B * x * Real.exp (-c' * y) := hM x hx1
    _ ≤ Real.exp ((c' - c) * y) * x * Real.exp (-c' * y) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hx (zero_le_one.trans hx1))
        (Real.exp_pos _).le
    _ = x * Real.exp (-c * y) := by
      rw [mul_comm (Real.exp _) x, mul_assoc, ← Real.exp_add]
      congr 2
      ring

end RiemannResearch.NumberTheory.PrimeNumberTheorem
