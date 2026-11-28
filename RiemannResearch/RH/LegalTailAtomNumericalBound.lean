import RiemannResearch.RH.LegalTailNymanProjection
import RiemannResearch.RH.BurnolZeroProduct
import RiemannResearch.RH.WeilExplicitFormula.ZetaReflect
import Mathlib.Analysis.Real.Pi.Bounds
import RiemannResearch.RH.RealZetaNonvanishing
import RiemannResearch.Analysis.ZeroCountReciprocalSquareTail

/-!
# An explicit bound for the limiting legal tail defect

Burnol, Theorem 1.2, https://arxiv.org/abs/math/9910055, gives the
projection formula. Platt and Trudgian, https://doi.org/10.1112/blms.12460,
supply critical-line verification through the cutoff. Hasanalizade, Shen
and Wong, Corollary 1.2, https://arxiv.org/abs/2107.06506, supply the
explicit counting discrepancy. These three published inputs are hypotheses
of the numerical capacity theorem.
-/

noncomputable section
open Zeta23 RiemannResearch.Analysis.ActualZeroOrdinate
open scoped BigOperators ComplexConjugate
namespace RiemannResearch.RH.Burnol

private theorem rightZero_im_ne_zero (ρ : RightZero) : (ρ : ℂ).im ≠ 0 := by
  intro h
  have he : ((ρ : ℂ).re : ℂ) = (ρ : ℂ) := Complex.ext rfl (by simpa using h.symm)
  exact riemannZeta_ofReal_ne_zero _ ρ.property.1.2.1 ρ.property.1.2.2.ne
    (by rw [he]; exact ρ.property.1.1)

/-- The positive-height representative is the zero itself in the upper
half-plane and its functional-equation mate in the lower half-plane. -/
def positiveRepresentative (ρ : RightZero) : ℂ :=
  if 0 < (ρ : ℂ).im then (ρ : ℂ) else 1 - (ρ : ℂ)

theorem positiveRepresentative_injective : Function.Injective positiveRepresentative := by
  intro x y h
  have hx := x.property.2
  have hy := y.property.2
  unfold positiveRepresentative at h
  split_ifs at h with hx' hy' hy'
  · exact Subtype.ext h
  · have he := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re] at he
    linarith
  · have he := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re] at he
    linarith
  · exact Subtype.ext (sub_right_injective h)

theorem positiveRepresentative_data (ρ : RightZero) :
    IsNontrivialZero (positiveRepresentative ρ) ∧
      (positiveRepresentative ρ).im = |(ρ : ℂ).im| ∧
      zeroMult (positiveRepresentative ρ) = zeroMult ρ := by
  unfold positiveRepresentative
  split_ifs with hp
  · exact ⟨ρ.property.1, (abs_of_pos hp).symm, rfl⟩
  · have hneg := le_of_not_gt hp
    have hc : IsNontrivialZero (conj (ρ : ℂ)) := by
      refine ⟨?_, ?_, ?_⟩
      · rw [riemannZeta_conj (rightZero_ne_one ρ), ρ.property.1.1, map_zero]
      · simpa using ρ.property.1.2.1
      · simpa using ρ.property.1.2.2
    have hz := zeta_reflect_zero _ hc
    have hm := analyticOrderAt_zeta_one_sub ρ.property.1.2.1 ρ.property.1.2.2
    refine ⟨by simpa [reflect] using hz, ?_, ?_⟩
    · simp [abs_of_nonpos hneg]
    · unfold zeroMult
      rw [hm]

/-- A bound for each squared factor, including its full analytic multiplicity. -/
theorem weightedFactorSq_defect_le_ordinate (ρ : RightZero) :
    1 - weightedFactorSq ρ ≤ (zeroMult ρ : ℝ) / (ρ : ℂ).im ^ 2 := by
  have h₁ := one_add_mul_sub_le_pow (show -1 ≤ factorSq ρ by linarith [factorSq_nonneg ρ])
    (zeroMult ρ)
  have hn := normSq_pos_of_half_lt ρ.property.2
  have hi := sq_pos_of_ne_zero (rightZero_im_ne_zero ρ)
  have hdef : 1 - factorSq ρ ≤ 1 / (ρ : ℂ).im ^ 2 := by
    rw [one_sub_factorSq (rightZero_ne_zero ρ), div_le_div_iff₀ hn hi, Complex.normSq_apply]
    have hb : 2 * (ρ : ℂ).re - 1 ≤ 1 := by linarith [ρ.property.1.2.2]
    nlinarith [mul_le_mul_of_nonneg_right hb hi.le, sq_nonneg (ρ : ℂ).re]
  calc
    _ ≤ (zeroMult ρ : ℝ) * (1 - factorSq ρ) := by unfold weightedFactorSq; linarith
    _ ≤ _ := by simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hdef (Nat.cast_nonneg _)

private theorem finite_product_loss_le (F : Finset RightZero) :
    1 - finiteProductSq F ≤ ∑ ρ ∈ F, (zeroMult ρ : ℝ) / (ρ : ℂ).im ^ 2 := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | @insert ρ F hρ ih =>
    rw [Finset.sum_insert hρ]
    have he : finiteProductSq (insert ρ F) = weightedFactorSq ρ * finiteProductSq F := by
      simp [finiteProductSq, hρ]
    rw [he]
    have hcross := mul_nonneg (sub_nonneg.mpr (weightedFactorSq_le_one ρ))
      (sub_nonneg.mpr (finiteProductSq_le_one F))
    linarith [weightedFactorSq_defect_le_ordinate ρ]

/-- From a finite-height critical-line verification and a zero-count bound,
control the entire squared product over both signs, with no factor of two. -/
theorem productSq_loss_le_reciprocalSquareTailBound {H : ℝ} (hH : 2 * Real.pi ≤ H)
    (hheight : ∀ z : ℂ, IsNontrivialZero z → 0 < z.im → z.im ≤ H → z.re = 1 / 2)
    (hcount : ∀ t ≥ H, |(Ncount 0 t : ℝ) - tailCountMain t| ≤ Real.log t) :
    1 - productSq ≤ reciprocalSquareTailBound H := by
  classical
  have hhigh (ρ : RightZero) : H < (positiveRepresentative ρ).im := by
    obtain ⟨hz, hi, _⟩ := positiveRepresentative_data ρ
    by_contra! hle
    have hr := hheight _ hz (by rw [hi]; exact abs_pos.mpr (rightZero_im_ne_zero ρ)) hle
    have hright := ρ.property.2
    unfold positiveRepresentative at hr
    split_ifs at hr
    · linarith
    · simp only [Complex.sub_re, Complex.one_re] at hr
      linarith
  suffices h : 1 - reciprocalSquareTailBound H ≤ productSq by linarith
  apply le_ciInf
  intro F
  let e : RightZero ↪ ℂ := ⟨positiveRepresentative, positiveRepresentative_injective⟩
  have hS := finite_ordinate_reciprocal_sq_le hH hcount (F.map e) (by
    intro z hz
    obtain ⟨ρ, _, rfl⟩ := Finset.mem_map.mp hz
    exact ⟨(positiveRepresentative_data ρ).1, hhigh ρ⟩)
  rw [Finset.sum_map] at hS
  change (∑ ρ ∈ F, (zeroMult (positiveRepresentative ρ) : ℝ) /
    (positiveRepresentative ρ).im ^ 2) ≤ _ at hS
  simp only [(positiveRepresentative_data _).2.1, (positiveRepresentative_data _).2.2,
    sq_abs] at hS
  linarith [finite_product_loss_le F]

end RiemannResearch.RH.Burnol

namespace RiemannResearch.RH.Pareto.PrimePowerSchur
open RiemannResearch.RH.Burnol RiemannResearch.RH.Burnol.ContinuousNyman

/-- A height cutoff and a count discrepancy bound the atom at the capacity supremum. -/
theorem legalTailAtom_le_reciprocalSquareTailBound {H : ℝ} (hH : 2 * Real.pi ≤ H)
    (hBurnol : ‖closedSpace.starProjection unitVector‖ ^ 2 = productSq)
    (hheight : ∀ z : ℂ, IsNontrivialZero z → 0 < z.im → z.im ≤ H → z.re = 1 / 2)
    (hcount : ∀ t ≥ H, |(Ncount 0 t : ℝ) - tailCountMain t| ≤ Real.log t) :
    0 ≤ 1 - (⨆ K, normalizedLegalTailMeanCapacity K) ∧
      1 - (⨆ K, normalizedLegalTailMeanCapacity K) ≤ reciprocalSquareTailBound H := by
  rw [normalizedLegalTailMeanCapacity_iSup_eq_nymanProjection, hBurnol]
  exact ⟨sub_nonneg.mpr productSq_le_one,
    productSq_loss_le_reciprocalSquareTailBound hH hheight hcount⟩

/-- Conditional on the three stated analytic inputs, the limiting weak-star
atom has mass in the indicated half-open interval. -/
theorem legalTailAtom_lt_three_halves_trillionths_of_published_inputs
    (hBurnol : ‖closedSpace.starProjection unitVector‖ ^ 2 = productSq)
    (hPT : ∀ z : ℂ, IsNontrivialZero z → 0 < z.im → z.im ≤ 3000000000000 → z.re = 1 / 2)
    (hHSW : ∀ t : ℝ, 3000000000000 ≤ t →
      |(Ncount 0 t : ℝ) - t / (2 * Real.pi) * Real.log (t / (2 * Real.pi * Real.exp 1))| ≤
        0.1038 * Real.log t + 0.2573 * Real.log (Real.log t) + 9.3675) :
    0 ≤ 1 - (⨆ K, normalizedLegalTailMeanCapacity K) ∧
      1 - (⨆ K, normalizedLegalTailMeanCapacity K) < 3 / 2000000000000 := by
  obtain ⟨h₀, hB⟩ := legalTailAtom_le_reciprocalSquareTailBound
    (by linarith [Real.pi_lt_four]) hBurnol hPT (tailCountMain_error_le_log_of_hsw hHSW)
  exact ⟨h₀, hB.trans_lt reciprocalSquareTailBound_three_trillion_lt⟩

end RiemannResearch.RH.Pareto.PrimePowerSchur
