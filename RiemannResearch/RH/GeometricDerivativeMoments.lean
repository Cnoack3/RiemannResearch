import RiemannResearch.RH.DerivativeSignedCorrection

/-!
# Exact head-separated geometric moments of derivative correction rows

At every finite order the first physical site and complete signed remainder
are retained.  The remainder is bounded uniformly in the coefficient dimension
by actual Hilbert norms, never by coefficient l1 mass.
-/

noncomputable section
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto.GeometricMoments

private theorem multiplier_square_summable (b : ℕ → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hb : ∀ k, |b k| ≤ C) (f : ThresholdHilbert) :
    Summable (fun k => positiveWeight k * (b k * hilbertSequence f k)^2) := by
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (positiveWeight_nonneg k) (sq_nonneg _)) _
    ((hilbertSequence_square_summable f).mul_left (C^2))
  intro k
  have hsq : (b k)^2 ≤ C^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (b k)) hC).2 (hb k)
  have hm := mul_le_mul_of_nonneg_right hsq
    (mul_nonneg (positiveWeight_nonneg k) (sq_nonneg (hilbertSequence f k)))
  nlinarith

private def physicalMultiplier (b : ℕ → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hb : ∀ k, |b k| ≤ C) (f : ThresholdHilbert) : ThresholdHilbert :=
  sequenceHilbert (fun k => b k * hilbertSequence f k)
    (multiplier_square_summable b C hC hb f)

private theorem physicalMultiplier_sequence (b : ℕ → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hb : ∀ k, |b k| ≤ C) (f : ThresholdHilbert) :
    hilbertSequence (physicalMultiplier b C hC hb f) =
      fun k => b k * hilbertSequence f k := by
  apply hilbertSequence_sequenceHilbert
  simp

private theorem physicalMultiplier_norm_le (b : ℕ → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hb : ∀ k, |b k| ≤ C) (f : ThresholdHilbert) :
    ‖physicalMultiplier b C hC hb f‖ ≤ C * ‖f‖ := by
  have hs : ‖physicalMultiplier b C hC hb f‖^2 ≤ C^2 * ‖f‖^2 := by
    rw [hilbert_norm_weighted_sq, physicalMultiplier_sequence,
      hilbert_norm_weighted_sq, ← tsum_mul_left]
    apply Summable.tsum_le_tsum _ (multiplier_square_summable b C hC hb f)
      ((hilbertSequence_square_summable f).mul_left (C^2))
    intro k
    have hsq : (b k)^2 ≤ C^2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (b k)) hC).2 (hb k)
    have hm := mul_le_mul_of_nonneg_right hsq
      (mul_nonneg (positiveWeight_nonneg k) (sq_nonneg (hilbertSequence f k)))
    nlinarith
  nlinarith [norm_nonneg (physicalMultiplier b C hC hb f), norm_nonneg f,
    mul_nonneg hC (norm_nonneg f)]

def tailPowerMultiplier (M k : ℕ) : ℝ :=
  if 2 ≤ k then (1 / (k : ℝ))^M else 0

theorem tailPowerMultiplier_nonneg (M k : ℕ) : 0 ≤ tailPowerMultiplier M k := by
  unfold tailPowerMultiplier
  split_ifs <;> positivity

theorem tailPowerMultiplier_bound (M k : ℕ) :
    |tailPowerMultiplier M k| ≤ (1 / 2 : ℝ)^M := by
  rw [abs_of_nonneg (tailPowerMultiplier_nonneg M k)]
  unfold tailPowerMultiplier
  split_ifs with hk
  · apply pow_le_pow_left₀ (by positivity)
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (by exact_mod_cast hk)
  · positivity

def tailPower (M : ℕ) (f : ThresholdHilbert) : ThresholdHilbert :=
  physicalMultiplier (tailPowerMultiplier M) ((1 / 2 : ℝ)^M)
    (by positivity) (tailPowerMultiplier_bound M) f

theorem tailPower_sequence (M : ℕ) (f : ThresholdHilbert) :
    hilbertSequence (tailPower M f) =
      fun k => tailPowerMultiplier M k * hilbertSequence f k :=
  physicalMultiplier_sequence _ _ _ _ _

theorem tailPower_norm_le (M : ℕ) (f : ThresholdHilbert) :
    ‖tailPower M f‖ ≤ (1 / 2 : ℝ)^M * ‖f‖ :=
  physicalMultiplier_norm_le _ _ _ _ _

theorem tailPower_add (M : ℕ) (f g : ThresholdHilbert) :
    tailPower M (f + g) = tailPower M f + tailPower M g := by
  apply hilbertSequence_injective
  rw [tailPower_sequence, hilbertSequence_add, hilbertSequence_add,
    tailPower_sequence, tailPower_sequence]
  funext k
  simp only [Pi.add_apply]
  ring

theorem tailPower_smul (M : ℕ) (a : ℝ) (f : ThresholdHilbert) :
    tailPower M (a • f) = a • tailPower M f := by
  apply hilbertSequence_injective
  rw [tailPower_sequence, hilbertSequence_smul, hilbertSequence_smul,
    tailPower_sequence]
  funext k
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

def tailPowerLinear (M : ℕ) : ThresholdHilbert →ₗ[ℝ] ThresholdHilbert where
  toFun := tailPower M
  map_add' := tailPower_add M
  map_smul' := tailPower_smul M

theorem tailPower_fintype_sum {ι : Type*} [Fintype ι] (M : ℕ)
    (f : ι → ThresholdHilbert) : tailPower M (∑ i, f i) = ∑ i, tailPower M (f i) :=
  map_sum (tailPowerLinear M) f Finset.univ

theorem tailPower_zero (f : ThresholdHilbert) :
    tailPower 0 f = f - hilbertSequence f 1 • hilbertAtom 1 (by decide) := by
  apply hilbertSequence_injective
  rw [tailPower_sequence, hilbertSequence_sub, hilbertSequence_smul,
    hilbertAtom_sequence]
  funext k
  by_cases hk : 2 ≤ k
  · have hk1 : k ≠ 1 := by omega
    simp [tailPowerMultiplier, hk, hk1]
  · have hk01 : k = 0 ∨ k = 1 := by omega
    rcases hk01 with rfl | rfl <;> simp [tailPowerMultiplier]

/-- The jth moment is the complete inverse-power sum starting at physical site 2. -/
def geometricMoment (j : ℕ) (f g : ThresholdHilbert) : ℝ :=
  inner ℝ f (tailPower j g + tailPower (j + 1) g)

theorem geometricMoment_linearCombination {ι : Type*} [Fintype ι]
    (j : ℕ) (f : ThresholdHilbert) (v : ι → ThresholdHilbert) (a : ι → ℝ) :
    geometricMoment j f (Fintype.linearCombination ℝ v a) =
      ∑ i, a i * geometricMoment j f (v i) := by
  rw [Fintype.linearCombination_apply, geometricMoment,
    tailPower_fintype_sum, tailPower_fintype_sum,
    ← Finset.sum_add_distrib, inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [tailPower_smul, tailPower_smul, ← smul_add, real_inner_smul_right]
  rfl

def signedRemainder (M : ℕ) (f g : ThresholdHilbert) : ℝ :=
  inner ℝ f (tailPower M g)

theorem geometricMoment_eq_tsum (j : ℕ) (f g : ThresholdHilbert) :
    geometricMoment j f g = ∑' k : ℕ, if 2 ≤ k then
      hilbertSequence f k * hilbertSequence g k / (k : ℝ)^(j + 2) else 0 := by
  rw [geometricMoment, hilbert_inner_weighted, hilbertSequence_add,
    tailPower_sequence, tailPower_sequence]
  unfold paretoInner
  apply tsum_congr
  intro k
  by_cases hk : 2 ≤ k
  · have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
    have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
    simp only [Pi.add_apply, tailPowerMultiplier, if_pos hk, positiveWeight,
      div_pow, one_pow, pow_add, pow_one]
    field_simp
  · simp [Pi.add_apply, tailPowerMultiplier, hk]

theorem signedRemainder_bound (M : ℕ) (f g : ThresholdHilbert) :
    |signedRemainder M f g| ≤ (1 / 2 : ℝ)^M * (‖f‖ * ‖g‖) := by
  exact (abs_real_inner_le_norm f (tailPower M g)).trans (by
    have h := mul_le_mul_of_nonneg_left (tailPower_norm_le M g) (norm_nonneg f)
    nlinarith)

theorem squareRemainder_nonneg (M : ℕ) (f : ThresholdHilbert) :
    0 ≤ signedRemainder M f f := by
  rw [signedRemainder, hilbert_inner_weighted, tailPower_sequence]
  unfold paretoInner
  apply tsum_nonneg
  intro k
  have h := mul_nonneg (mul_nonneg (positiveWeight_nonneg k)
    (tailPowerMultiplier_nonneg M k)) (sq_nonneg (hilbertSequence f k))
  nlinarith

/-- Exact finite Abel-compatible geometric expansion; neither boundary nor remainder is omitted. -/
theorem inner_eq_head_moments_remainder (M : ℕ) (f g : ThresholdHilbert) :
    inner ℝ f g = hilbertSequence f 1 * hilbertSequence g 1 / 2 +
      (∑ j ∈ Finset.range M, (-1 : ℝ)^j * geometricMoment j f g) +
      (-1 : ℝ)^M * signedRemainder M f g := by
  induction M with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, add_zero,
        pow_zero, one_mul, signedRemainder, tailPower_zero,
        inner_sub_right, real_inner_smul_right]
      have he := hilbertAtom_inner 1 (by decide) f
      rw [real_inner_comm] at he
      have hw : positiveWeight 1 = (1 / 2 : ℝ) := by norm_num [positiveWeight]
      rw [hw] at he
      rw [he]
      ring
  | succ M ih =>
      rw [Finset.sum_range_succ]
      simp only [geometricMoment, inner_add_right, signedRemainder,
        pow_succ] at ih ⊢
      linarith

/-- Every discarded piece of the square expansion remains an explicit nonnegative square remainder. -/
theorem norm_sq_eq_head_moments_remainder (M : ℕ) (f : ThresholdHilbert) :
    ‖f‖^2 = (hilbertSequence f 1)^2 / 2 +
      (∑ j ∈ Finset.range M, (-1 : ℝ)^j * geometricMoment j f f) +
      (-1 : ℝ)^M * signedRemainder M f f := by
  simpa only [real_inner_self_eq_norm_sq, ← pow_two] using
    inner_eq_head_moments_remainder M f f

open CoefficientStabilization.DerivativeCompatibility
open CoefficientStabilization.GramMobiusCorrection

/-- Boundedness comes from the already established strong correction limit, without RH. -/
theorem correction_derivative_uniform_norm_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ n, ‖hilbertDifference (correctionSynthesis n)‖ ≤ C := by
  obtain ⟨C, hC⟩ :=
    (Metric.isBounded_range_of_tendsto _ derivative_correction_tendsto).exists_norm_le
  refine ⟨max C 1, lt_of_lt_of_le (by norm_num) (le_max_right C 1), ?_⟩
  intro n
  exact (hC _ ⟨n, rfl⟩).trans (le_max_left C 1)

def correctionMomentCore (M n i : ℕ) : ℝ :=
  hilbertSequence (derivativeAtom i) 1 *
      hilbertSequence (hilbertDifference (correctionSynthesis n)) 1 / 2 +
    ∑ j ∈ Finset.range M, (-1 : ℝ)^j *
      geometricMoment j (derivativeAtom i) (hilbertDifference (correctionSynthesis n))

/-- The actual signed inverse-Gram correction, with no growing-sum limit interchange. -/
theorem signedCorrectionRow_eq_momentCore (M n i : ℕ) :
    signedCorrectionRow n i = correctionMomentCore M n i +
      (-1 : ℝ)^M * signedRemainder M (derivativeAtom i)
        (hilbertDifference (correctionSynthesis n)) := by
  rw [signedCorrectionRow_eq_pairing]
  exact inner_eq_head_moments_remainder M _ _

/-- The finite moment expansion has a geometric error controlled by the full vector norm. -/
theorem signedCorrectionRow_momentCore_bound (M n i : ℕ) :
    |signedCorrectionRow n i - correctionMomentCore M n i| ≤
      (1 / 2 : ℝ)^M * (‖derivativeAtom i‖ *
        ‖hilbertDifference (correctionSynthesis n)‖) := by
  rw [signedCorrectionRow_eq_momentCore M n i, add_sub_cancel_left, abs_mul,
    abs_pow, abs_neg, abs_one, one_pow, one_mul]
  exact signedRemainder_bound M _ _

/-- In particular, any bounded family of actual corrections has a uniform geometric error. -/
theorem signedCorrectionRow_momentCore_uniform (C : ℝ)
    (hC : ∀ n, ‖hilbertDifference (correctionSynthesis n)‖ ≤ C) (M n i : ℕ) :
    |signedCorrectionRow n i - correctionMomentCore M n i| ≤
      (1 / 2 : ℝ)^M * (‖derivativeAtom i‖ * C) := by
  exact (signedCorrectionRow_momentCore_bound M n i).trans
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (hC n) (norm_nonneg _)) (by positivity))

/-- A single dimension-independent constant controls every finite expansion order. -/
theorem signedCorrectionRow_momentCore_uniform_exists :
    ∃ C : ℝ, 0 < C ∧ ∀ M n i,
      |signedCorrectionRow n i - correctionMomentCore M n i| ≤
        (1 / 2 : ℝ)^M * (‖derivativeAtom i‖ * C) := by
  obtain ⟨C, hC, hb⟩ := correction_derivative_uniform_norm_bound
  exact ⟨C, hC, signedCorrectionRow_momentCore_uniform C hb⟩

/-- Explicit remaining arithmetic provider.  M is fixed before each cofinal n-set;
the complete finite signed moment core is combined before taking its absolute value. -/
theorem riemannHypothesis_of_cofinal_momentCore_budget
    (h : ∀ i : ℕ, ∀ ε : ℝ, 0 < ε → ∃ M : ℕ,
      ∃ᶠ n : ℕ in Filter.atTop,
        |correctionMomentCore M n i| +
          (1 / 2 : ℝ)^M * (‖derivativeAtom i‖ *
            ‖hilbertDifference (correctionSynthesis n)‖) < ε) : RiemannHypothesis := by
  apply riemannHypothesis_of_cofinal_signedCorrectionRow
  intro i ε hε
  obtain ⟨M, hM⟩ := h i ε hε
  apply hM.mono
  intro n hn
  have hb := signedCorrectionRow_momentCore_bound M n i
  have ht := abs_add_le (signedCorrectionRow n i - correctionMomentCore M n i)
    (correctionMomentCore M n i)
  have he : signedCorrectionRow n i - correctionMomentCore M n i +
      correctionMomentCore M n i = signedCorrectionRow n i := by ring
  rw [he] at ht
  linarith

end RiemannResearch.RH.Pareto.GeometricMoments
