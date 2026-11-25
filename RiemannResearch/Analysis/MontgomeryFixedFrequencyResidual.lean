/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.MontgomeryPrimeMeanSquare
import RiemannResearch.Analysis.MontgomerySharpWeilSeparator
import RiemannResearch.Analysis.MontgomerySharpPolynomialCriterion
import RiemannResearch.Analysis.MontgomeryPrimeDiagonalAsymptotic
import RiemannResearch.Analysis.MontgomeryBGSTBTransitionComponents
import RiemannResearch.Analysis.MontgomeryHorizontalTransfer
import RiemannResearch.Analysis.MontgomeryHorizontalLimit
import RiemannResearch.Analysis.MontgomeryHorizontalBessel
import RiemannResearch.Analysis.MontgomeryFormFactor
import RiemannResearch.Analysis.MontgomeryLogMeanSquare
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Signed cutoff and prime residuals at fixed Montgomery frequencies

These declarations use the positive-height complex-pair normalization of
BGSTB, corrected §3, https://arxiv.org/html/2501.14545v3#S3.E4. They retain
the signed prime cross integral and the complete cutoff residual. The raw
ordinate comparison involves the separate horizontal defect.
-/

noncomputable section
open Filter Set MeasureTheory Zeta23
open scoped Topology
namespace RiemannResearch.Analysis.MontgomeryHorizontalBessel
open MontgomeryHorizontalTransfer MontgomeryPrimeCrossIntegral

private theorem logSignalEnergy_tendsto_of_pos {α : ℝ} (hα : 0 < α) :
    Tendsto (fun T : ℝ => logSignalEnergy T (T^α) / (T * Real.log T)) atTop (𝓝 0) := by
  have h2 : 0 < 2*α := by linarith
  have hlog := (isLittleO_log_rpow_atTop (r := 2*α) h2).tendsto_div_nhds_zero
  have hi : Tendsto (fun T : ℝ => (T^(2*α))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_rpow_atTop h2)
  apply squeeze_zero_norm' _ (by simpa using hlog.add (hi.const_mul 3))
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with T hT
  have hT₁ : 1 < T := by linarith
  have hTp := zero_lt_one.trans hT₁
  have hL := Real.log_pos hT₁
  have hnn : 0 ≤ logSignalEnergy T (T^α) :=
    intervalIntegral.integral_nonneg hTp.le (fun _ _ => sq_nonneg _)
  have hw : T^(2*α) = (T^α)^2 := by rw [mul_comm, Real.rpow_mul hTp.le, Real.rpow_two]
  have hxp := Real.rpow_pos_of_pos hTp α
  have he := (abs_le.mp (MontgomeryLogMeanSquare.log_mean_square_error_le hT (T^α))).2
  change logSignalEnergy T (T^α) - T*(Real.log T)^2/(T^α)^2 ≤ _ at he
  rw [Real.norm_of_nonneg (div_nonneg hnn (mul_pos hTp hL).le), hw]
  apply (div_le_iff₀ (mul_pos hTp hL)).2
  apply (show logSignalEnergy T (T^α) ≤
    T*(Real.log T)^2/(T^α)^2 + 3*T*Real.log T/(T^α)^2 by linarith only [he]).trans_eq
  field_simp [hxp.ne'] <;> ring

private theorem primeCross_normalized_tendsto (α : ℝ) :
    Tendsto (fun T : ℝ => (crossIntegral (T^α) T).re / (T*Real.log T)) atTop (𝓝 0) := by
  let K := 4/Real.log 2 * ∑' n : ℕ, mangoldtThreeHalves n
  have hi : Tendsto (fun T : ℝ => (Real.log T)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  apply squeeze_zero_norm' _ (by simpa using hi.const_mul K)
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with T hT
  have hT₁ : 1 < T := by linarith
  have hTp := zero_lt_one.trans hT₁
  have hL := Real.log_pos hT₁
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (mul_pos hTp hL)]
  exact (div_le_div_of_nonneg_right
    (primeCross_linear_bound hT (Real.rpow_pos_of_pos hTp α)) (mul_pos hTp hL).le).trans_eq
    (by dsimp [K]; field_simp [hTp.ne', hL.ne'] <;> ring)

/-- The exact signed residual separating the complex pair statistic from the
pole, arithmetic, and cross energies on the power cutoff. -/
theorem sharpFormFactor_sub_thirdSignalResidual_eq {T : ℝ} (hT : 1 < T) (α : ℝ) :
    sharpFormFactor T α - thirdSignalResidual T (T^α) / (T*Real.log T) =
      logSignalEnergy T (T^α) / (T*Real.log T) +
      primeSignalEnergy T (T^α) / (T*Real.log T) +
      2 * ((crossIntegral (T^α) T).re / (T*Real.log T)) := by
  rw [sharpFormFactor_eq_actualComplexPairSum, thirdSignalResidual,
    Real.log_rpow (zero_lt_one.trans hT)]
  field_simp [(zero_lt_one.trans hT).ne', (Real.log_pos hT).ne', Real.pi_ne_zero] <;> ring

/-- At every interior subunit frequency the exact residual-subtracted
complex-zero form factor has the triangular limiting slope. -/
theorem sharpFormFactor_sub_thirdSignalResidual_tendsto {α : ℝ} (hα : 0 < α) (h₁ : α < 1) :
    Tendsto (fun T : ℝ => sharpFormFactor T α - thirdSignalResidual T (T^α) / (T*Real.log T))
      atTop (𝓝 α) := by
  have hh := ((logSignalEnergy_tendsto_of_pos hα).add
    (primeSignalEnergy_tendsto_subunit hα h₁)).add ((primeCross_normalized_tendsto α).const_mul 2)
  simp only [zero_add, mul_zero, add_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
  exact (sharpFormFactor_sub_thirdSignalResidual_eq hT α).symm

/-- The missing input for the complex-zero slope is exactly the normalized
signed third-signal residual. No density hypothesis occurs in the equivalence. -/
theorem sharpFormFactor_subunit_iff_thirdSignalResidual {α : ℝ} (hα : 0 < α) (h₁ : α < 1) :
    Tendsto (fun T : ℝ => sharpFormFactor T α) atTop (𝓝 α) ↔
      Tendsto (fun T : ℝ => thirdSignalResidual T (T^α) / (T*Real.log T)) atTop (𝓝 0) := by
  have hh := sharpFormFactor_sub_thirdSignalResidual_tendsto hα h₁
  constructor
  · intro h
    simpa using h.sub hh
  · intro h
    simpa using hh.add h

/-- The positive-cutoff estimate in BGSTB §3 supplies the residual bound on
the entire open subunit interval. Its arithmetic mean-square premise has
already been discharged by the weighted prime-diagonal estimate. -/
theorem sharpFormFactor_subunit_of_thirdSignalSource (hthird : PositiveCutoffThirdSignalSource)
    {α : ℝ} (hα : 0 < α) (h₁ : α < 1) :
    Tendsto (fun T : ℝ => sharpFormFactor T α) atTop (𝓝 α) := by
  apply (sharpFormFactor_subunit_iff_thirdSignalResidual hα h₁).mpr
  obtain ⟨D, hD, hd⟩ := hthird
  let A := α+1
  let B := Real.sqrt (2*A)
  have hA : 0 ≤ A := by dsimp [A]; linarith
  have hB : B^2 = 2*A := Real.sq_sqrt (by positivity)
  have hs := (logSignalEnergy_tendsto_of_pos hα).add (primeSignalEnergy_tendsto_subunit hα h₁)
  have hs' := hs.eventually (gt_mem_nhds (show 0 + α < A by dsimp [A]; linarith))
  have hi : Tendsto (fun T : ℝ => (Real.log T)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have hroot : Tendsto (fun T : ℝ => (Real.sqrt (Real.log T))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop)
  apply squeeze_zero_norm' _ (by simpa using ((hi.const_mul 4).add (hroot.const_mul B)).const_mul D)
  filter_upwards [hd, hs', eventually_gt_atTop (1 : ℝ)] with T hT hsum hT₁
  let L := Real.log T
  let x := T^α
  let E := T/x^2 + x
  let S := logSignalEnergy T x + primeSignalEnergy T x
  have hTp := zero_lt_one.trans hT₁
  have hL : 0 < L := Real.log_pos hT₁
  have hx₁ : 1 ≤ x := Real.one_le_rpow hT₁.le hα.le
  have hxp := zero_lt_one.trans_le hx₁
  have hxT : x ≤ T := (Real.rpow_le_rpow_of_exponent_le hT₁.le h₁.le).trans_eq (Real.rpow_one T)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have he : E ≤ 2*T := by
    have hp : 1 ≤ x^2 := one_le_pow₀ hx₁
    have := div_le_self hTp.le hp
    dsimp [E]; linarith
  have hsT : S ≤ A * (T*L) := by
    apply (div_le_iff₀ (mul_pos hTp hL)).mp
    simpa only [S, add_div] using hsum.le
  have hprod : S*E ≤ (T*B*Real.sqrt L)^2 := by
    calc
      S*E ≤ (A*(T*L))*(2*T) := mul_le_mul hsT he hE (by positivity)
      _ = (T*B*Real.sqrt L)^2 := by
        rw [mul_pow, mul_pow, hB, Real.sq_sqrt hL.le]
        ring
  have hbound := Real.sqrt_le_sqrt hprod
  rw [Real.sqrt_sq (mul_nonneg (mul_nonneg hTp.le (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))] at hbound
  have hsqrt : Real.sqrt T ≤ T := by
    have h := Real.sqrt_le_sqrt (show T ≤ T^2 by nlinarith only [hT₁, sq_nonneg (T-1)])
    simpa only [Real.sqrt_sq hTp.le] using h
  have hraw := hT x ⟨hx₁,hxT⟩
  change |thirdSignalResidual T x| ≤ D*(Real.sqrt T+x+E+Real.sqrt (S*E)) at hraw
  change ‖thirdSignalResidual T x/(T*L)‖ ≤ D*(4*L⁻¹ + B*(Real.sqrt L)⁻¹)
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (mul_pos hTp hL), div_le_iff₀ (mul_pos hTp hL)]
  calc
    _ ≤ D*(Real.sqrt T+x+E+Real.sqrt (S*E)) := hraw
    _ ≤ D*(4*T+T*B*Real.sqrt L) := mul_le_mul_of_nonneg_left
      (by linarith only [hsqrt,hxT,he,hbound]) hD
    _ = _ := by
      have hr : (Real.sqrt L)⁻¹ * L = Real.sqrt L := by
        field_simp [(Real.sqrt_pos.mpr hL).ne']
        nlinarith only [Real.sq_sqrt hL.le]
      calc
        _ = D*(4*(L⁻¹*L)*T + B*((Real.sqrt L)⁻¹*L)*T) := by rw [inv_mul_cancel₀ hL.ne', hr]; ring
        _ = _ := by ring

/-- The ordinary ordinate statistic on the same subunit interval follows from
the normalized cutoff residual and the actual horizontal budget. -/
theorem formFactor_subunit_of_residual_and_horizontal {α : ℝ} (hα : 0 < α) (h₁ : α < 1)
    (hR : Tendsto (fun T : ℝ => thirdSignalResidual T (T^α)/(T*Real.log T)) atTop (𝓝 0))
    (hB : Tendsto (fun T : ℝ => horizontalBudget T (α*Real.log T)/T) atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => MontgomeryFormFactor.formFactor T α) atTop (𝓝 α) :=
  raw_limit_of_budget (fun _ => α) hα.le hB ((sharpFormFactor_subunit_iff_thirdSignalResidual hα h₁).mpr hR)

/--
info: 'RiemannResearch.Analysis.MontgomeryHorizontalBessel.sharpFormFactor_subunit_iff_thirdSignalResidual'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms sharpFormFactor_subunit_iff_thirdSignalResidual

/-- At a fixed frequency, retain the signed sum of the positive-height
cutoff residual and the prime off-diagonal. -/
def normalizedThirdAndPrimeOffDiagonal (T α : ℝ) : ℝ :=
  (thirdSignalResidual T (T^α) + primeSignalEnergy T (T^α) -
    T*primeDiagonal (T^α)) / (T*Real.log T)

/-- For all positive fixed frequencies the complete signed correction leaves
the arithmetic diagonal, the pole energy, and the oscillatory cross integral. -/
theorem sharpFormFactor_sub_normalizedThirdAndPrimeOffDiagonal_eq {T : ℝ}
    (hT : 1 < T) (α : ℝ) :
    sharpFormFactor T α - normalizedThirdAndPrimeOffDiagonal T α =
      logSignalEnergy T (T^α)/(T*Real.log T) + primeDiagonal (T^α)/Real.log T +
      2*((crossIntegral (T^α) T).re/(T*Real.log T)) := by
  have he := sharpFormFactor_sub_thirdSignalResidual_eq hT α
  have hTc := (zero_lt_one.trans hT).ne'
  have hLc := (Real.log_pos hT).ne'
  unfold normalizedThirdAndPrimeOffDiagonal
  field_simp [hTc, hLc] at he ⊢
  linarith only [he]

private theorem primeDiagonal_div_log_tendsto {α : ℝ} (hα : 0 < α) :
    Tendsto (fun T : ℝ => primeDiagonal (T^α)/Real.log T) atTop (𝓝 α) := by
  have h := primeDiagonalAsymptotic_unconditional.comp (tendsto_rpow_atTop hα)
  have hi : Tendsto (fun T : ℝ => (Real.log T)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have hh := (h.mul hi).add_const α
  simp only [zero_mul, zero_add] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
  dsimp
  rw [Real.log_rpow (zero_lt_one.trans hT)]
  field_simp [(Real.log_pos hT).ne'] <;> ring

/-- The full correction to the limiting diagonal has coefficient one and
retains its sign even beyond unit support. -/
theorem sharpFormFactor_sub_normalizedThirdAndPrimeOffDiagonal_tendsto {α : ℝ}
    (hα : 0 < α) : Tendsto (fun T : ℝ => sharpFormFactor T α -
      normalizedThirdAndPrimeOffDiagonal T α) atTop (𝓝 α) := by
  have hh := ((logSignalEnergy_tendsto_of_pos hα).add (primeDiagonal_div_log_tendsto hα)).add
    ((primeCross_normalized_tendsto α).const_mul 2)
  simp only [zero_add, mul_zero, add_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
  exact (sharpFormFactor_sub_normalizedThirdAndPrimeOffDiagonal_eq hT α).symm

/-- A unit plateau for the actual complex form factor at a fixed positive
frequency requires the signed correction to tend to 1−α. -/
theorem sharpFormFactor_tendsto_one_iff_normalizedThirdAndPrimeOffDiagonal {α : ℝ}
    (hα : 0 < α) :
    Tendsto (fun T : ℝ => sharpFormFactor T α) atTop (𝓝 1) ↔
      Tendsto (fun T : ℝ => normalizedThirdAndPrimeOffDiagonal T α) atTop (𝓝 (1-α)) := by
  have hh := sharpFormFactor_sub_normalizedThirdAndPrimeOffDiagonal_tendsto hα
  constructor
  · intro h
    simpa using h.sub hh
  · intro h
    have hlim := hh.add h
    rw [show α + (1-α) = 1 by ring] at hlim
    simpa only [sub_add_cancel] using hlim

/-- For arbitrarily high fixed frequencies, allow one-sided logarithmic
growth on a cofinal set of heights. Both the coefficient and the cofinal
set may depend on the chosen frequency. -/
def CofinalThirdAndPrimeOffDiagonalLogUpper : Prop :=
  ∀ A : ℝ, ∃ α : ℝ, 1 < α ∧ A ≤ α ∧ ∃ C : ℝ, 0 ≤ C ∧
    ∃ᶠ T : ℝ in atTop, normalizedThirdAndPrimeOffDiagonal T α ≤ C * Real.log T

/-- RH is equivalent to a one-sided logarithmic envelope for the signed
cutoff-plus-prime residual along unbounded fixed frequencies. The return
to RH uses the repository's fixed-right-zero Weil separator. -/
theorem riemannHypothesis_iff_cofinalThirdAndPrimeOffDiagonalLogUpper :
    RiemannHypothesis ↔ CofinalThirdAndPrimeOffDiagonalLogUpper := by
  constructor
  · intro hRH A
    obtain ⟨C,hC,hsharp⟩ := exists_sharpIntegral_le_height_log_sq_of_riemannHypothesis hRH
    let α := max A 2
    have hα₁ : 1 < α := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_right _ _)
    have hα := zero_lt_one.trans hα₁
    refine ⟨α,hα₁,le_max_left _ _,2*Real.pi*C,by positivity,?_⟩
    apply Filter.Eventually.frequently
    filter_upwards [eventually_ge_atTop (9 : ℝ),
      (sharpFormFactor_sub_normalizedThirdAndPrimeOffDiagonal_tendsto hα).eventually
        (lt_mem_nhds hα)] with T hT hdiff
    have hT₁ : 1 < T := by linarith
    have hD : 0 < T*Real.log T/(2*Real.pi) := div_pos
      (mul_pos (zero_lt_one.trans hT₁) (Real.log_pos hT₁)) (by positivity)
    have hF : sharpFormFactor T α ≤ 2*Real.pi*C*Real.log T := by
      rw [sharpFormFactor, div_le_iff₀ hD]
      apply (hsharp T (α*Real.log T) hT).trans_eq
      field_simp [Real.pi_ne_zero] <;> ring
    linarith only [hF, hdiff]
  · intro h
    apply cofinalSharpPolynomialUpper_iff_riemannHypothesis.mp
    refine ⟨3,?_⟩
    intro A
    obtain ⟨α,hα₁,hA,C,hC,hcof⟩ := h A
    have hα := zero_lt_one.trans hα₁
    let K := C+α+1
    have hK : 0 < K := by dsimp [K]; linarith
    refine ⟨K/(2*Real.pi),by positivity,?_⟩
    intro Y
    have he := (sharpFormFactor_sub_normalizedThirdAndPrimeOffDiagonal_tendsto hα).eventually
      (gt_mem_nhds (show α < α+1 by linarith))
    obtain ⟨T,hr,hY,hT,hlog,herr⟩ := (hcof.and_eventually ((eventually_ge_atTop Y).and
      ((eventually_gt_atTop (1 : ℝ)).and ((Real.tendsto_log_atTop.eventually_ge_atTop 1).and he)))).exists
    have hTp := zero_lt_one.trans hT
    have hL := Real.log_pos hT
    have hF : sharpFormFactor T α ≤ K*Real.log T := by
      have hm := mul_le_mul_of_nonneg_left hlog (show 0 ≤ α+1 by linarith)
      dsimp [K]
      linarith only [hm, herr, hr]
    have hraw := (div_le_iff₀ (div_pos (mul_pos hTp hL) (by positivity : 0 < 2*Real.pi))).mp
      (show sharpIntegral T (α*Real.log T)/(T*Real.log T/(2*Real.pi)) ≤ K*Real.log T from hF)
    have hsq := pow_le_pow_left₀ hL.le (show Real.log T ≤ T by
      linarith only [Real.log_le_sub_one_of_pos hTp]) 2
    refine ⟨T,α,hY,hT,hA,?_⟩
    calc
      _ ≤ K*Real.log T*(T*Real.log T/(2*Real.pi)) := hraw
      _ = (K/(2*Real.pi)*T)*(Real.log T)^2 := by ring
      _ ≤ (K/(2*Real.pi)*T)*T^2 := mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = _ := by rw [show (3:ℝ)*Real.log T = Real.log T + Real.log T + Real.log T by ring,
        Real.exp_add, Real.exp_add, Real.exp_log hTp]; ring

/-- Exact cancellation to the plateau at an unbounded collection of fixed
complex-zero frequencies supplies the one-sided cofinal bound and hence RH. -/
theorem riemannHypothesis_of_unbounded_signed_plateau
    (h : ∀ A : ℝ, ∃ α : ℝ, 1 < α ∧ A ≤ α ∧
      Tendsto (fun T : ℝ => normalizedThirdAndPrimeOffDiagonal T α) atTop (𝓝 (1-α))) :
    RiemannHypothesis := by
  apply riemannHypothesis_iff_cofinalThirdAndPrimeOffDiagonalLogUpper.mpr
  intro A
  obtain ⟨α,hα,hA,hr⟩ := h A
  refine ⟨α,hα,hA,0,le_rfl,?_⟩
  apply Filter.Eventually.frequently
  filter_upwards [hr.eventually (gt_mem_nhds (show 1-α < 0 by linarith))] with T hT
  simpa only [zero_mul] using hT.le

/--
info: 'RiemannResearch.Analysis.MontgomeryHorizontalBessel.riemannHypothesis_iff_cofinalThirdAndPrimeOffDiagonalLogUpper'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms riemannHypothesis_iff_cofinalThirdAndPrimeOffDiagonalLogUpper

end RiemannResearch.Analysis.MontgomeryHorizontalBessel
