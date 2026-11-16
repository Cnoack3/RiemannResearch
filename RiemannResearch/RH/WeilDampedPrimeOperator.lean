import RiemannResearch.RH.WeilDampedSynthesis
import RiemannResearch.RH.ScrewPrimePart
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# The actual separated damped prime operator

Source: user-provided prime-side factorization continuation, Priorities 1--2.
The support identity and two-exponent tail bound construct the actual
two-sided signed prime series in operator norm for sigma > 1.
Nuclear certificates are assembled separately, and positivity is not asserted.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
open Classical
namespace RiemannResearch.RH.WeilDampedSynthesis
open RiemannResearch.Analysis.SquareSummableSynthesis
open WeilDampedWeights
set_option maxHeartbeats 800000

theorem masked_columns_norm_half {σ : ℝ} (hσ : 1 < σ) (φ : L2)
    {Y : ℝ} (hY : 0 < Y) :
    ‖mask {m : ℕ | Y ≤ (m : ℝ)} (columns (by linarith : 1 / 2 < σ) φ)‖ ≤
      Y ^ (-σ / 2) * ‖columns (by linarith : 1 / 2 < σ / 2) φ‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.rpow_nonneg hY.le _) (norm_nonneg _))).mp
  have hpow : (Y ^ (-σ / 2)) ^ 2 = Y ^ (-σ) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hY.le]
    congr 1
    ring
  rw [mul_pow, hpow, columns_norm_sq]
  exact masked_columns_half_exponent hσ φ hY

theorem primePowerWeight_rpow (n : ℕ) :
    primePowerWeight n = ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  rw [primePowerWeight, Real.sqrt_eq_rpow, Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]

theorem tailSet_log {n : ℕ} (hn : 0 < n) (r : ℝ) :
    tailSet r (Real.log n) = {m : ℕ | (2 * Real.exp (-2 * r)) * (n : ℝ) ≤ (m : ℝ)} := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  ext m
  dsimp [tailSet]
  rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hnR]
  ring_nf

theorem weighted_tail_summable {σ : ℝ} (hσ : 1 < σ) (φ : L2) (r : ℝ) :
    Summable (fun n : ℕ => primePowerWeight n *
      ‖mask (tailSet r (Real.log n)) (columns (by linarith : 1 / 2 < σ) φ)‖) := by
  let c : ℝ := 2 * Real.exp (-2 * r)
  have hc : 0 < c := by dsimp [c]; positivity
  let K : ℝ := c ^ (-σ / 2) * ‖columns (by linarith : 1 / 2 < σ / 2) φ‖
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (primePowerWeight_nonneg n) (norm_nonneg _))
    (fun n => ?_) ((prime_majorant_summable hσ).mul_left K)
  by_cases hn : n = 0
  · simp [hn, primePowerWeight]
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
  rw [tailSet_log (Nat.pos_of_ne_zero hn) r]
  calc
    _ ≤ primePowerWeight n * ((c * n) ^ (-σ / 2) *
        ‖columns (by linarith : 1 / 2 < σ / 2) φ‖) :=
      mul_le_mul_of_nonneg_left
        (masked_columns_norm_half hσ φ (mul_pos hc hnR)) (primePowerWeight_nonneg n)
    _ = K * (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(σ + 1) / 2)) := by
      rw [primePowerWeight_rpow, Real.mul_rpow hc.le hnR.le]
      have he : -(σ + 1) / 2 = -(1 / 2 : ℝ) + -σ / 2 := by ring
      rw [he, Real.rpow_add hnR]
      dsimp [K]
      ring

def compression {σ : ℝ} (hσ : 1 / 2 < σ) (φ : L2) (a : ℝ) :
    Coeff ℕ →L[ℂ] Coeff ℕ :=
  (J hσ φ).adjoint.comp ((shift (-a)).toContinuousLinearMap.comp (J hσ φ))

theorem compression_localized {σ r a : ℝ} (hσ : 1 / 2 < σ) (φ : L2)
    (hφ : ∀ᵐ x : ℝ, r < |x| → φ x = 0) :
    compression hσ φ a =
      (analysis (columns hσ φ)).comp ((shift (-a)).toContinuousLinearMap.comp
        (synthesis (mask (tailSet r a) (columns hσ φ)))) := by
  rw [compression, support_projection_identity hσ φ hφ]
  rw [J, synthesis, ContinuousLinearMap.adjoint_adjoint]
  rw [ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_assoc]
  change (analysis (columns hσ φ)).comp ((shift (-a)).toContinuousLinearMap.comp
    ((synthesis (columns hσ φ)).comp (projection (tailSet r a)))) = _
  rw [synthesis_comp_projection]

theorem compression_norm_le {σ r a : ℝ} (hσ : 1 / 2 < σ) (φ : L2)
    (hφ : ∀ᵐ x : ℝ, r < |x| → φ x = 0) :
    ‖compression hσ φ a‖ ≤
      ‖columns hσ φ‖ * ‖mask (tailSet r a) (columns hσ φ)‖ := by
  rw [compression_localized hσ φ hφ]
  have ha : ‖analysis (columns hσ φ)‖ ≤ ‖columns hσ φ‖ :=
    LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _
  have hU : ‖(shift (-a)).toContinuousLinearMap‖ ≤ 1 := (shift (-a)).norm_toContinuousLinearMap_le
  calc
    _ ≤ ‖analysis (columns hσ φ)‖ *
        (‖(shift (-a)).toContinuousLinearMap‖ *
          ‖synthesis (mask (tailSet r a) (columns hσ φ))‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ ‖columns hσ φ‖ * (1 * ‖mask (tailSet r a) (columns hσ φ)‖) :=
      mul_le_mul ha (mul_le_mul hU (synthesis_norm_le _) (norm_nonneg _) zero_le_one)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by rw [one_mul]

theorem weighted_compression_norm_summable {σ r : ℝ} (hσ : 1 < σ) (φ : L2)
    (hφ : ∀ᵐ x : ℝ, r < |x| → φ x = 0) :
    Summable (fun n : ℕ => primePowerWeight n *
      ‖compression (by linarith : 1 / 2 < σ) φ (Real.log n)‖) := by
  have hs := (weighted_tail_summable hσ φ r).mul_left
    ‖columns (by linarith : 1 / 2 < σ) φ‖
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (primePowerWeight_nonneg n) (norm_nonneg _)) (fun n => ?_) hs
  calc
    _ ≤ primePowerWeight n *
        (‖columns (by linarith : 1 / 2 < σ) φ‖ *
          ‖mask (tailSet r (Real.log n)) (columns (by linarith : 1 / 2 < σ) φ)‖) :=
      mul_le_mul_of_nonneg_left (compression_norm_le _ φ hφ) (primePowerWeight_nonneg n)
    _ = _ := by ring

def primeTerm {σ : ℝ} (hσ : 1 / 2 < σ) (φ : L2) (n : ℕ) :
    Coeff ℕ →L[ℂ] Coeff ℕ :=
  (-primePowerWeight n : ℂ) •
    (compression hσ φ (Real.log n) + (compression hσ φ (Real.log n)).adjoint)

theorem primeTerm_norm_summable {σ r : ℝ} (hσ : 1 < σ) (φ : L2)
    (hφ : ∀ᵐ x : ℝ, r < |x| → φ x = 0) :
    Summable (fun n : ℕ => ‖primeTerm (by linarith : 1 / 2 < σ) φ n‖) := by
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    ((weighted_compression_norm_summable hσ φ hφ).mul_left 2)
  rw [primeTerm, norm_smul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (primePowerWeight_nonneg n)]
  have hh := norm_add_le (compression (by linarith : 1 / 2 < σ) φ (Real.log n))
    ((compression (by linarith : 1 / 2 < σ) φ (Real.log n)).adjoint)
  rw [ContinuousLinearMap.adjoint.norm_map] at hh
  nlinarith [mul_le_mul_of_nonneg_left hh (primePowerWeight_nonneg n)]

def primeOperator {σ : ℝ} (hσ : 1 / 2 < σ) (φ : L2) :
    Coeff ℕ →L[ℂ] Coeff ℕ := ∑' n, primeTerm hσ φ n

theorem primeOperator_hasSum {σ r : ℝ} (hσ : 1 < σ) (φ : L2)
    (hφ : ∀ᵐ x : ℝ, r < |x| → φ x = 0) :
    HasSum (primeTerm (by linarith : 1 / 2 < σ) φ)
      (primeOperator (by linarith : 1 / 2 < σ) φ) :=
  (primeTerm_norm_summable hσ φ hφ).of_norm.hasSum

end RiemannResearch.RH.WeilDampedSynthesis
