/-
Copyright (c) 2026 RiemannResearch contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.LamzouriSchwartzCutoff
import RiemannResearch.Analysis.LamzouriGapKernel285
import RiemannResearch.Analysis.GapKernelPolynomialObjective
import RiemannResearch.Analysis.GapKernelFourierObjective

/-!
# Degree-285 certificate interface and actual small gaps

The six numerical premises concern given integer polynomials and their
positive rays, their finite Fourier recurrence and a rational scalar check.
The accompanying Python certificate uses rational Bernstein subdivision and
a Gaussian objective enclosure. The original integer polynomials have a
verified instance in `LamzouriGap285OriginalReplay`. The analytic input is
the scoped compact-deletion theorem. No condition in the finite certificate mentions any zeta zero.
-/

noncomputable section
open MeasureTheory Real
namespace RiemannResearch.Analysis.LamzouriGapKernel285
open ActualZeroOrdinate GapKernelObjective GapKernelPolynomial GapKernelFourierGaussian
open GapKernelFourierRecurrence LamzouriSmallGapCriterion

def radius : ℚ := 79759777828511/100000000000000
def cutoff : ℚ := 3999999999993/7000000000000
def gap : ℚ := 392391339/500000000
private def scaleFactor : ℝ := (cutoff:ℝ)*Real.sqrt Real.pi/(radius:ℝ)

/-- Exactly the finite part of the polynomial and rational replay. -/
class Replay : Prop where
  unit_pos : 0 < ratValue fourierPolynomial 0
  input_pos (x : ℝ) : 0 ≤ x → 0 < value inputPolynomial x
  output_neg (y : ℝ) : (78/25 : ℝ) ≤ y → value fourierPolynomial y < 0
  coefficients : transport inputPolynomial = scale (2^inputPolynomial.length) fourierPolynomial
  primitive_nonneg : 0 ≤ ratValue (primitiveFrom 0 inputPolynomial) (radius^2)
  scalar : (177245385090551603/100000000000000000 : ℚ)*ratValue fourierPolynomial 0 <
    (radius/cutoff)*ratValue inputPolynomial 0 + (cutoff/radius)*
      (ratValue (primitiveFrom 0 inputPolynomial) 0 -
        ratValue (primitiveFrom 0 inputPolynomial) (radius^2)/expLower (radius^2) 32)

/-! A certificate with the same conditions for an explicit monomial pair. -/
structure PolynomialCertificate (physical frequency : List ℤ) : Prop where
  unit_pos : 0 < ratValue frequency 0
  input_pos (x : ℝ) : 0 ≤ x → 0 < value physical x
  output_neg (y : ℝ) : (78/25 : ℝ) ≤ y → value frequency y < 0
  coefficients : transport physical = scale (2^physical.length) frequency
  primitive_nonneg : 0 ≤ ratValue (primitiveFrom 0 physical) (radius^2)
  scalar : (177245385090551603/100000000000000000 : ℚ)*ratValue frequency 0 <
    (radius/cutoff)*ratValue physical 0 + (cutoff/radius)*
      (ratValue (primitiveFrom 0 physical) 0 -
        ratValue (primitiveFrom 0 physical) (radius^2)/expLower (radius^2) 32)

private theorem smooth_value (p : List ℤ) : ContDiff ℝ 2 (value p) := by
  induction p with
  | nil => exact contDiff_const
  | cons a p ih => exact contDiff_const.add (contDiff_id.mul ih)

/-- Fixed-cutoff compact deletion for any integer polynomial pair satisfying the
six finite conditions. This lets independent exact witnesses use the same
normalization and the same analytic argument. -/
theorem smallGapProportion_of_polynomialCertificate (physical frequency : List ℤ)
    (h : PolynomialCertificate physical frequency) [LamzouriCompactDeletion2026] :
    0 < smallGapProportion (392391339/500000000) := by
  have hr : (0:ℝ) < radius := by norm_num [radius]
  have ht : (0:ℝ) < cutoff := by norm_num [cutoff]
  have hs : 0 < scaleFactor := div_pos (mul_pos ht (Real.sqrt_pos.mpr Real.pi_pos)) hr
  have hq : 0 < value frequency 0 := by
    have hq' : (0:ℝ) < ((ratValue frequency 0:ℚ):ℝ) := by exact_mod_cast h.unit_pos
    simpa only [cast_ratValue,Rat.cast_zero] using hq'
  let f := normalizedTest physical frequency scaleFactor
  have hi : Integrable (model physical) := by
    simpa only [pow_zero,one_mul] using weighted_integrable physical 0
  have hfi : Integrable f := by
    apply ((hi.comp_div hs.ne').const_mul ((scaleFactor*value frequency 0)⁻¹)).congr
    exact Filter.Eventually.of_forall fun x => by simp [f,normalizedTest,div_eq_inv_mul]
  have hfc : ContDiff ℝ 2 f := by
    change ContDiff ℝ 2 (fun x : ℝ =>
      Real.exp (-Real.pi*(x/scaleFactor)^2) *
      value physical (Real.pi*(x/scaleFactor)^2) /
        (scaleFactor*value frequency 0))
    have hv := smooth_value physical
    fun_prop
  have he : Function.Even f := fun x => by simp [f,normalizedTest,model,neg_div]
  have hn (x : ℝ) : 0 ≤ f x := by
    apply div_nonneg _ (mul_pos hs hq).le
    exact mul_nonneg (Real.exp_pos _).le (h.input_pos _ (mul_nonneg Real.pi_pos.le (sq_nonneg _))).le
  have hfour (u : ℝ) : cosineTransform f u = fourierModel scaleFactor frequency u :=
    normalized_fourier_cosine hs hq h.coefficients u
  have hedge : (78/25:ℝ) ≤ Real.pi*(scaleFactor*(gap:ℝ))^2 := by
    have hπ : (314159265358979323846/100000000000000000000 : ℝ) < Real.pi :=
      lt_of_le_of_lt (by norm_num) Real.pi_gt_d20
    have h : (78/25 : ℝ) * (radius : ℝ)^2 <
        ((314159265358979323846/100000000000000000000 : ℝ) * (cutoff : ℝ) * gap)^2 := by
      norm_num [radius, cutoff, gap]
    have hcg : 0 < (cutoff : ℝ) * gap := by norm_num [cutoff, gap]
    have hsq := mul_self_le_mul_self (by norm_num [cutoff,gap] :
      0 ≤ (314159265358979323846/100000000000000000000 : ℝ) * ((cutoff : ℝ)*gap))
      (mul_le_mul_of_nonneg_right hπ.le hcg.le)
    unfold scaleFactor
    rw [mul_pow, div_pow, mul_pow, Real.sq_sqrt Real.pi_pos.le]
    field_simp [hr.ne']
    nlinarith only [h, hsq]
  have hgapcast : (gap : ℝ) = 392391339/500000000 := by norm_num [gap]
  rw [← hgapcast]
  apply smallGapProportion_pos_of_smooth_integrable_test (θ := (cutoff:ℝ))
    (by norm_num [gap]) (by norm_num [gap]) (by norm_num [cutoff]) (by norm_num [cutoff])
    hfi hfc he hn
  · rw [hfour,fourierModel_zero hq]
  · intro u hu
    rw [hfour]
    exact (fourierModel_neg_of_separation hq (by norm_num [gap]) h.output_neg hedge hu.le).le
  · have hE : 0 < expLower (radius^2) 32 := by
      unfold expLower
      apply Finset.sum_pos'
      · intro i hi
        positivity
      · exact ⟨0, by simp, by norm_num⟩
    have hobj := polynomial_objective_gt_one physical 32
      (by norm_num [radius]) (by norm_num [cutoff]) h.unit_pos h.primitive_nonneg
      hE h.scalar
    unfold objective
    change 1 < normalizedTest _ _ _ 0 + 2 * ∫ x in (0:ℝ)..(cutoff:ℝ), x * normalizedTest _ _ _ x
    unfold scaleFactor
    rw [normalizedTest_eq_objectiveTest physical frequency hr ht hq]
    simpa only [cast_ratValue,Rat.cast_zero] using hobj

theorem smallGapProportion_certified285 [h : Replay] [LamzouriCompactDeletion2026] :
    0 < smallGapProportion (392391339/500000000) :=
  smallGapProportion_of_polynomialCertificate inputPolynomial fourierPolynomial
    ⟨h.unit_pos, h.input_pos, h.output_neg, h.coefficients, h.primitive_nonneg, h.scalar⟩

end RiemannResearch.Analysis.LamzouriGapKernel285
