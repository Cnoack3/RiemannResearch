import RiemannResearch.Analysis.InfiniteWeightedCauchy
import RiemannResearch.RH.ZetaTwoOptimizerStage
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Complete resolvent recovery for the actual inverse-square optimizer

Source: independently developed continuation of the user-directed conductor
recovery problem, 9 October 2026. Infinite weighted Cauchy retains the complete
signed target pairing. Integer resolvent masses are evaluated by exact finite
telescoping, including the terminal positive remainder. The normalized result
uses the actual optimizer and screening; no arithmetic decay is assumed.
The classical digamma interpretation is NIST DLMF 5.7.6,
https://dlmf.nist.gov/5.7#E6; the proof here uses telescoping, not a digamma axiom.
-/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.ZetaTwoResolvent
open ZetaTwoProbability ZetaTwoHilbert ZetaTwoOptimizerStage
open RiemannResearch.Analysis.InfiniteWeightedCauchy

def resolventMass (t : ℝ) : ℝ :=
  ∑' k : ℕ, positiveQWeight k / (1 / (k : ℝ) + t)

theorem resolventMass_summable (t : ℝ) (ht : 0 < t) :
    Summable (fun k : ℕ => positiveQWeight k / (1 / (k : ℝ) + t)) := by
  apply Summable.of_nonneg_of_le
    (fun k => div_nonneg (positiveQWeight_nonneg k) (by positivity))
    _ (positiveQWeight_summable.div_const t)
  intro k
  apply div_le_div_of_nonneg_left (positiveQWeight_nonneg k) ht
  have hk : 0 ≤ 1 / (k : ℝ) := by positivity
  linarith

theorem targetCharge_summable (f : QHilbert) :
    Summable (fun k => positiveQWeight k * qSequence f k) := by
  apply (qSequence_product_summable f qOne).congr
  intro k
  rw [qSequence_qOne]
  by_cases hk : k = 0
  · simp [hk, positiveQWeight]
  · simp [qOneSequence, hk]

theorem targetCharge_tsum (f : QHilbert) :
    (∑' k, positiveQWeight k * qSequence f k) = inner ℝ f qOne := by
  rw [qInner_weighted]
  congr 1
  funext k
  rw [qSequence_qOne]
  by_cases hk : k = 0
  · simp [hk, positiveQWeight]
  · simp [qOneSequence, hk]

theorem regularizedEnergy_summable (f : QHilbert) (t : ℝ) :
    Summable (fun k => positiveQWeight k * (qSequence f k)^2 *
      (1 / (k : ℝ) + t)) := by
  apply ((qSequence_product_summable f (reciprocalD f)).add
    ((qSequence_square_summable f).mul_left t)).congr
  intro k
  rw [qSequence_reciprocalD]
  ring

theorem regularizedEnergy_tsum (f : QHilbert) (t : ℝ) :
    (∑' k, positiveQWeight k * (qSequence f k)^2 *
      (1 / (k : ℝ) + t)) =
      inner ℝ f (reciprocalD f) + t * ‖f‖^2 := by
  have he : (fun k => positiveQWeight k * (qSequence f k)^2 *
      (1 / (k : ℝ) + t)) =
      (fun k => positiveQWeight k * qSequence f k *
        qSequence (reciprocalD f) k +
        t * (positiveQWeight k * (qSequence f k)^2)) := by
    funext k
    rw [qSequence_reciprocalD]
    ring
  rw [he, (qSequence_product_summable f (reciprocalD f)).tsum_add
    ((qSequence_square_summable f).mul_left t), tsum_mul_left,
    ← qInner_weighted, ← qNorm_weighted_sq]

theorem exact_resolvent_cauchy (f : QHilbert) (t : ℝ) (ht : 0 < t) :
    (inner ℝ f qOne)^2 ≤
      (inner ℝ f (reciprocalD f) + t * ‖f‖^2) * resolventMass t := by
  have hc := weighted_tsum_cauchy
    (fun k => positiveQWeight k * qSequence f k)
    (fun k => positiveQWeight k * (qSequence f k)^2 * (1/(k:ℝ)+t))
    (fun k => positiveQWeight k / (1/(k:ℝ)+t))
    (targetCharge_summable f) (regularizedEnergy_summable f t)
    (resolventMass_summable t ht)
    (fun k => by have hw := positiveQWeight_nonneg k; positivity)
    (fun k => by have hw := positiveQWeight_nonneg k; positivity)
    (by
      intro k
      have hk : 0 ≤ 1/(k:ℝ) := by positivity
      have hd : 1/(k:ℝ)+t ≠ 0 := ne_of_gt (by linarith)
      apply le_of_eq
      field_simp [hd])
  rw [targetCharge_tsum, regularizedEnergy_tsum] at hc
  exact hc

def harmonic (M : ℕ) : ℝ := ∑ j ∈ Finset.range M, 1 / ((j : ℝ) + 1)
def harmonicRemainder (M N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range M, 1 / ((N : ℝ) + j + 1)
def harmonicDifference (M n : ℕ) : ℝ :=
  1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + M + 1)

theorem harmonicRemainder_step (M N : ℕ) :
    harmonicRemainder M N - harmonicRemainder M (N + 1) =
      1 / ((N : ℝ) + 1) - 1 / ((N : ℝ) + M + 1) := by
  induction M with
  | zero => simp [harmonicRemainder]
  | succ M ih =>
      simp only [harmonicRemainder, Finset.sum_range_succ, Nat.cast_add,
        Nat.cast_one] at *
      have he : (N : ℝ) + 1 + M + 1 = (N : ℝ) + (M + 1) + 1 := by ring
      rw [he]
      linarith

theorem harmonicDifference_partial (M N : ℕ) :
    (∑ n ∈ Finset.range N, harmonicDifference M n) =
      harmonic M - harmonicRemainder M N := by
  induction N with
  | zero => simp [harmonic, harmonicRemainder]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      have hs := harmonicRemainder_step M N
      unfold harmonicDifference
      linarith

theorem harmonicRemainder_tendsto_zero (M : ℕ) :
    Tendsto (harmonicRemainder M) atTop (𝓝 0) := by
  have h : Tendsto (fun N : ℕ =>
      ∑ j ∈ Finset.range M, 1 / ((N : ℝ) + j + 1)) atTop
      (𝓝 (∑ _j ∈ Finset.range M, (0 : ℝ))) := by
    apply tendsto_finsetSum
    intro j hj
    have ht := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (tendsto_add_atTop_nat j)
    simpa only [Function.comp_def, Nat.cast_add, add_assoc] using ht
  change Tendsto (fun N : ℕ =>
    ∑ j ∈ Finset.range M, 1 / ((N : ℝ) + j + 1)) atTop (𝓝 0)
  simpa only [Finset.sum_const_zero] using h

theorem harmonicDifference_nonneg (M n : ℕ) : 0 ≤ harmonicDifference M n := by
  unfold harmonicDifference
  have hpos : 0 < (n : ℝ) + 1 := by positivity
  have hle : (n : ℝ) + 1 ≤ (n : ℝ) + M + 1 := by
    linarith [Nat.cast_nonneg (α := ℝ) M]
  exact sub_nonneg.mpr (div_le_div_of_nonneg_left zero_le_one hpos hle)

theorem harmonicDifference_hasSum (M : ℕ) :
    HasSum (harmonicDifference M) (harmonic M) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (harmonicDifference_nonneg M) _).mpr
  simp_rw [harmonicDifference_partial]
  simpa using tendsto_const_nhds.sub (harmonicRemainder_tendsto_zero M)

theorem resolventMass_inv_nat (M : ℕ) (hM : 0 < M) :
    resolventMass (1/(M:ℝ)) = harmonic M / zetaTwo := by
  have hMR : 0 < (M:ℝ) := by exact_mod_cast hM
  have hs := resolventMass_summable (1/(M:ℝ)) (by positivity)
  rw [resolventMass, hs.tsum_eq_zero_add]
  have he : (fun n : ℕ => positiveQWeight (n+1) /
      (1/((n+1:ℕ):ℝ)+1/(M:ℝ))) =
      fun n : ℕ => harmonicDifference M n / zetaTwo := by
    funext n
    have hn : (n:ℝ)+1 ≠ 0 := by positivity
    have hnm : (n:ℝ)+M+1 ≠ 0 := by positivity
    unfold positiveQWeight harmonicDifference
    push_cast
    field_simp [hn, hnm, ne_of_gt hMR, ne_of_gt zetaTwo_pos]
    ring
  rw [he, tsum_div_const, (harmonicDifference_hasSum M).tsum_eq]
  simp [positiveQWeight]

theorem residual_target_inner (n : ℕ) :
    inner ℝ (residual n) qOne = error n := by
  have hp : inner ℝ (residual n) (optimizer n) = 0 := by
    rw [real_inner_comm]
    exact ((stage n).mem_orthogonal _).mp (residual_mem_orthogonal n) _
      ((stage n).starProjection_apply_mem qOne)
  have he : qOne = residual n + optimizer n := by
    unfold ZetaTwoOptimizerStage.residual
    abel
  rw [he, inner_add_right, hp, add_zero, real_inner_self_eq_norm_sq]
  rfl

theorem stage_resolvent_cauchy (n M : ℕ) (hM : 0 < M) :
    (error n)^2 ≤
      (inner ℝ (residual n) (reciprocalD (residual n)) +
        (1/(M:ℝ)) * error n) * (harmonic M / zetaTwo) := by
  have hMR : 0 < (M:ℝ) := by exact_mod_cast hM
  have hc := exact_resolvent_cauchy (residual n) (1/(M:ℝ)) (by positivity)
  rwa [residual_target_inner, resolventMass_inv_nat M hM] at hc

theorem error_le_harmonic_norm_ratio (n M : ℕ) (hM : 0 < M) :
    error n ≤ (harmonic M / zetaTwo) *
      (‖screenedResidual n‖ / ‖residual n‖ + 1 / (M : ℝ)) := by
  have hC : 0 ≤ harmonic M / zetaTwo := by
    apply div_nonneg _ zetaTwo_pos.le
    unfold harmonic
    exact Finset.sum_nonneg (fun _ _ => by positivity)
  have hnr : 0 < ‖residual n‖ := by
    have he := error_pos n
    unfold error at he
    nlinarith [norm_nonneg (residual n)]
  have hpair : inner ℝ (residual n) (reciprocalD (residual n)) ≤
      ‖residual n‖ * ‖screenedResidual n‖ := by
    rw [← residual_inner_screened]
    exact (le_abs_self _).trans (abs_real_inner_le_norm _ _)
  have hc := stage_resolvent_cauchy n M hM
  have hup : inner ℝ (residual n) (reciprocalD (residual n)) +
      (1/(M:ℝ))*error n ≤
      ‖residual n‖ * ‖screenedResidual n‖ + (1/(M:ℝ))*error n := by
    linarith [hpair]
  have hu := mul_le_mul_of_nonneg_right hup hC
  have hprod : (‖residual n‖ * ‖screenedResidual n‖ +
      (1/(M:ℝ))*error n) * (harmonic M / zetaTwo) =
      error n * ((harmonic M / zetaTwo) *
        (‖screenedResidual n‖ / ‖residual n‖ + 1/(M:ℝ))) := by
    unfold error
    have hMR : 0 < (M : ℝ) := by exact_mod_cast hM
    field_simp [ne_of_gt hnr, ne_of_gt hMR, ne_of_gt zetaTwo_pos] <;> ring
  rw [hprod] at hu
  have hmul : error n * error n ≤ error n *
      ((harmonic M / zetaTwo) *
        (‖screenedResidual n‖ / ‖residual n‖ + 1/(M:ℝ))) := by
    simpa only [pow_two] using hc.trans hu
  by_contra h
  have hlt := mul_lt_mul_of_pos_left (lt_of_not_ge h) (error_pos n)
  exact (not_lt_of_ge hmul) hlt

theorem norm_ratio_eq_sqrt_secondMoment (n : ℕ) :
    ‖screenedResidual n‖ / ‖residual n‖ = Real.sqrt (secondMoment n) := by
  rw [secondMoment, error, Real.sqrt_div (sq_nonneg ‖screenedResidual n‖),
    Real.sqrt_sq (norm_nonneg (screenedResidual n)),
    Real.sqrt_sq (norm_nonneg (residual n))]

theorem error_le_harmonic_secondMoment (n M : ℕ) (hM : 0 < M) :
    error n ≤ (harmonic M / zetaTwo) *
      (Real.sqrt (secondMoment n) + 1 / (M : ℝ)) := by
  simpa only [norm_ratio_eq_sqrt_secondMoment] using
    error_le_harmonic_norm_ratio n M hM

theorem error_le_harmonic_complete_correction (n M : ℕ) (hM : 0 < M) :
    error n ≤ (harmonic M / zetaTwo) *
      (Real.sqrt ((quarticFloor n + weightedMismatch n - screening n) / error n) +
        1 / (M : ℝ)) := by
  have hc := error_le_harmonic_secondMoment n M hM
  rw [secondMoment, screenedResidual_energy_exact, signedCorrection,
    ← add_sub_assoc] at hc
  exact hc

end RiemannResearch.RH.ZetaTwoResolvent
