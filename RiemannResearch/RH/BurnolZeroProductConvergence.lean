import RiemannResearch.RH.BurnolZeroProduct
import RiemannResearch.RH.WeilExplicitFormula.WeilEF.ZeroSummability
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# Positivity and logarithmic representation of the actual Burnol product

The scalar product is that in Burnol, Theorem 1.2,
https://arxiv.org/abs/math/9910055. We derive convergence from the project's
checked multiplicity-weighted inverse-square zero sum. This proves a
strictly positive scalar product without assuming RH or a projection formula.
The connection to the Balazard--Saias--Yor critical-line integral is not
asserted here; see Burnol Theorem 1.3 and Bui--Lester--Milinovich (1.1),
https://arxiv.org/abs/1306.0856, for that separate analytic identity.
-/

noncomputable section
open scoped BigOperators Topology
namespace RiemannResearch.RH.Burnol

/-- An elementary summable majorant for a single squared-factor defect. -/
theorem factorSq_defect_le_inverseSquare (ρ : RightZero) :
    1 - factorSq ρ ≤ 5 / (1 + Complex.normSq (Zeta23.gammaOf ρ)) := by
  have hd : 0 < Complex.normSq (ρ : ℂ) := normSq_pos_of_half_lt ρ.property.2
  have hg : 0 < 1 + Complex.normSq (Zeta23.gammaOf ρ) := by
    linarith [Complex.normSq_nonneg (Zeta23.gammaOf ρ)]
  have hgeom : 1 + Complex.normSq (Zeta23.gammaOf ρ) ≤
      5 * Complex.normSq (ρ : ℂ) := by
    rw [Complex.normSq_apply, Zeta23.WeilEF.gammaOf_re, Zeta23.WeilEF.gammaOf_im,
      Complex.normSq_apply]
    have hh := ρ.property.2
    nlinarith [sq_nonneg (ρ : ℂ).im, sq_nonneg ((ρ : ℂ).re - 1 / 2)]
  rw [one_sub_factorSq (rightZero_ne_zero ρ)]
  apply (div_le_div_iff₀ hd hg).2
  have hle : 2 * (ρ : ℂ).re - 1 ≤ 1 := by linarith [ρ.property.1.2.2]
  have hm := mul_le_mul_of_nonneg_right hle hg.le
  nlinarith

/-- Bernoulli's inequality controls the entire multiplicity contribution. -/
theorem weightedFactorSq_defect_le_inverseSquare (ρ : RightZero) :
    1 - weightedFactorSq ρ ≤
      5 * ((Zeta23.zeroMult ρ : ℝ) / (1 + Complex.normSq (Zeta23.gammaOf ρ))) := by
  have ha := factorSq_nonneg (ρ : ℂ)
  have hb := one_add_mul_sub_le_pow (by linarith : -1 ≤ factorSq (ρ : ℂ))
    (Zeta23.zeroMult ρ)
  calc
    1 - weightedFactorSq ρ ≤ (Zeta23.zeroMult ρ : ℝ) * (1 - factorSq ρ) := by
      unfold weightedFactorSq
      nlinarith
    _ ≤ (Zeta23.zeroMult ρ : ℝ) * (5 / (1 + Complex.normSq (Zeta23.gammaOf ρ))) :=
      mul_le_mul_of_nonneg_left (factorSq_defect_le_inverseSquare ρ) (Nat.cast_nonneg _)
    _ = 5 * ((Zeta23.zeroMult ρ : ℝ) / (1 + Complex.normSq (Zeta23.gammaOf ρ))) := by ring

/-- Summability of defects, including the actual analytic multiplicities. -/
theorem summable_weightedFactorSq_defect :
    Summable (fun ρ : RightZero => 1 - weightedFactorSq ρ) := by
  let embed : RightZero → (Zeta23.zetaZeros Zeta23.zetaSeam).carrier :=
    fun ρ => ⟨ρ, ρ.property.1⟩
  have he : Function.Injective embed := by
    intro a b h
    apply Subtype.ext
    exact congrArg (fun z : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier => (z : ℂ)) h
  have hbase : Summable (fun ρ : RightZero =>
      (Zeta23.zeroMult ρ : ℝ) / (1 + Complex.normSq (Zeta23.gammaOf ρ))) := by
    have hs := (Zeta23.WeilEF.zero_sum_inv_sq Zeta23.zetaSeam).comp_injective he
    simpa only [embed, Function.comp_def] using hs
  exact Summable.of_nonneg_of_le
    (fun ρ => sub_nonneg.mpr (weightedFactorSq_le_one ρ))
    weightedFactorSq_defect_le_inverseSquare (hbase.mul_left 5)

/-- The logarithms converge absolutely as a real indexed family. -/
theorem summable_log_weightedFactorSq :
    Summable (fun ρ : RightZero => Real.log (weightedFactorSq ρ)) := by
  have h := Real.summable_log_one_add_of_summable summable_weightedFactorSq_defect.neg
  have heq : (fun ρ : RightZero => Real.log (1 + -(1 - weightedFactorSq ρ))) =
      (fun ρ : RightZero => Real.log (weightedFactorSq ρ)) := by
    funext ρ
    congr 1
    ring
  simpa only [heq] using h

/-- Exact logarithmic representation of the canonical squared zero product. -/
theorem productSq_eq_exp_tsum_log :
    productSq = Real.exp (∑' ρ : RightZero, Real.log (weightedFactorSq ρ)) := by
  exact hasProd_weightedFactorSq.unique
    (Real.hasProd_of_hasSum_log weightedFactorSq_pos summable_log_weightedFactorSq.hasSum)

/-- Positivity is unconditional; equality to one is still equivalent to RH. -/
theorem productSq_pos : 0 < productSq := by
  rw [productSq_eq_exp_tsum_log]
  exact Real.exp_pos _

/-- The scalar zero sum appearing in the BSY formula, with multiplicities. -/
def logarithmicZeroSum : ℝ :=
  ∑' ρ : RightZero, (Zeta23.zeroMult ρ : ℝ) * Real.log ‖(ρ : ℂ) / (1 - ρ)‖

theorem log_weightedFactorSq (ρ : RightZero) :
    Real.log (weightedFactorSq ρ) =
      -2 * ((Zeta23.zeroMult ρ : ℝ) * Real.log ‖(ρ : ℂ) / (1 - ρ)‖) := by
  rw [weightedFactorSq, Real.log_pow, log_factorSq (rightZero_ne_zero ρ) (rightZero_ne_one ρ)]
  ring

theorem summable_logarithmicZeroSum :
    Summable (fun ρ : RightZero =>
      (Zeta23.zeroMult ρ : ℝ) * Real.log ‖(ρ : ℂ) / (1 - ρ)‖) := by
  have h := summable_log_weightedFactorSq.mul_left (-1 / 2)
  have heq : (fun ρ : RightZero => (-1 / 2 : ℝ) * Real.log (weightedFactorSq ρ)) =
      (fun ρ : RightZero => (Zeta23.zeroMult ρ : ℝ) * Real.log ‖(ρ : ℂ) / (1 - ρ)‖) := by
    funext ρ
    rw [log_weightedFactorSq]
    ring
  simpa only [heq] using h

theorem productSq_eq_exp_neg_two_logarithmicZeroSum :
    productSq = Real.exp (-2 * logarithmicZeroSum) := by
  rw [productSq_eq_exp_tsum_log]
  simp only [log_weightedFactorSq, tsum_mul_left, logarithmicZeroSum]

theorem logarithmicZeroSum_zero_iff_rh : logarithmicZeroSum = 0 ↔ RiemannHypothesis := by
  rw [← productSq_eq_one_iff_rh, productSq_eq_exp_neg_two_logarithmicZeroSum,
    Real.exp_eq_one_iff]
  constructor <;> intro h <;> linarith

/-- An exact scalar residual expression; its interpretation as a projection
residual requires the analytic Burnol projection theorem. -/
theorem product_defect_eq_one_sub_exp :
    1 - productSq = 1 - Real.exp (-2 * logarithmicZeroSum) := by
  rw [productSq_eq_exp_neg_two_logarithmicZeroSum]

/-- The logarithmic zero sum is nonnegative, without an RH hypothesis. -/
theorem logarithmicZeroSum_nonneg : 0 ≤ logarithmicZeroSum := by
  have h := productSq_le_one
  rw [productSq_eq_exp_neg_two_logarithmicZeroSum] at h
  have hh := Real.exp_le_one_iff.mp h
  linarith

/-- The unsquared, multiplicity-weighted factor of Burnol's Theorem 1.2. -/
def weightedFactor (ρ : RightZero) : ℝ := factor ρ ^ Zeta23.zeroMult ρ

/-- The unsquared scalar product in Burnol's projection formula. -/
def product : ℝ := Real.exp (-logarithmicZeroSum)

theorem weightedFactor_pos (ρ : RightZero) : 0 < weightedFactor ρ :=
  pow_pos (factor_pos (rightZero_ne_zero ρ) (rightZero_ne_one ρ)) _

theorem log_weightedFactor (ρ : RightZero) :
    Real.log (weightedFactor ρ) =
      -((Zeta23.zeroMult ρ : ℝ) * Real.log ‖(ρ : ℂ) / (1 - ρ)‖) := by
  have h := log_factorSq (rightZero_ne_zero ρ) (rightZero_ne_one ρ)
  rw [← factor_sq, Real.log_pow] at h
  have he : Real.log (factor ρ) = -Real.log ‖(ρ : ℂ) / (1 - ρ)‖ := by linarith
  rw [weightedFactor, Real.log_pow, he]
  ring

/-- The ordinary factors themselves have the claimed infinite product. -/
theorem hasProd_weightedFactor : HasProd weightedFactor product := by
  apply Real.hasProd_of_hasSum_log weightedFactor_pos
  simpa only [log_weightedFactor, logarithmicZeroSum] using
    summable_logarithmicZeroSum.hasSum.neg

theorem tprod_weightedFactor : (∏' ρ : RightZero, weightedFactor ρ) = product :=
  hasProd_weightedFactor.tprod_eq

theorem product_pos : 0 < product := Real.exp_pos _

theorem product_sq : product ^ 2 = productSq := by
  rw [product, pow_two, ← Real.exp_add, productSq_eq_exp_neg_two_logarithmicZeroSum]
  congr 1
  ring

theorem product_le_one : product ≤ 1 := by
  have h := productSq_le_one
  rw [← product_sq] at h
  nlinarith [product_pos]

theorem product_eq_sqrt : product = Real.sqrt productSq := by
  have h := Real.sq_sqrt productSq_nonneg
  have hp := product_sq
  nlinarith [product_pos, Real.sqrt_nonneg productSq]

theorem product_eq_one_iff_rh : product = 1 ↔ RiemannHypothesis := by
  rw [← productSq_eq_one_iff_rh, ← product_sq]
  constructor <;> intro h <;> nlinarith [product_pos]

end RiemannResearch.RH.Burnol
