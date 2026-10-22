import RiemannResearch.RH.DerivativeCRT
import RiemannResearch.RH.GeometricDerivativeMoments
import RiemannResearch.RH.FiniteDyadicDefect

/-!
# Uniform Möbius aggregation of the signed derivative correction rows

Source: user-directed continuation from 41b7faf6, reusing the later checked
DerivativeSignedCorrection/CRT, ReciprocalGramCorrection, and FiniteDyadicDefect
identities. The finite Möbius synthesis and Hilbert continuity supply the
proof strategy; no mathematical novelty claim is made.

The complete signed aggregate reconstructs half the reciprocal correction
with an actual Hilbert-pairing remainder, uniformly in the optimization
dimension. Any test cutoff tending to infinity gives the same exact limit.
The full Abel endpoints, CRT intersections, signed cross term, and square
remainders remain explicit.

The single one-sided cofinal arithmetic estimate at the end is equivalent
to all fixed mismatches vanishing. It is a CONDITIONAL RESEARCH REDUCTION:
no provider of that estimate, and no unconditional RH proof, is asserted.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.DerivativeCompatibility
open GramMobiusCorrection
open RiemannResearch.Analysis.SignedAbel

/-- Negative Möbius-weighted sum of complete signed correction rows. -/
def mobiusRowAggregate (m n : ℕ) : ℝ :=
  -(∑ i : Fin m, mobiusVector m i * signedCorrectionRow n i.val)

/-- The entire raw-derivative test error against the actual correction. -/
def mobiusRowRemainder (m n : ℕ) : ℝ :=
  inner ℝ (rawMobiusDerivativeResidual (m + 1))
    (hilbertDifference (correctionSynthesis n))

theorem correctionReciprocalMoment_eq_reciprocalCorrection (n : ℕ) :
    correctionReciprocalMoment n = reciprocalCorrection n := by
  unfold correctionReciprocalMoment reciprocalCorrection dotProduct
    TailCapacity.reciprocalSource
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem correctionReciprocalMoment_half (n : ℕ) :
    correctionReciprocalMoment n / 2 =
      inner ℝ (hilbertAtom 1 (by decide)) (hilbertDifference (correctionSynthesis n)) := by
  rw [derivative_correction_synthesis, Fintype.linearCombination_apply, inner_sum]
  simp only [real_inner_smul_right, derivativeFamily]
  unfold correctionReciprocalMoment
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  rw [real_inner_comm, derivativeAtom_inner_target]
  ring

/-- Exact reconstruction before taking absolute values or limits. -/
theorem mobiusRowAggregate_exact (m n : ℕ) :
    correctionReciprocalMoment n / 2 =
      mobiusRowAggregate m n + mobiusRowRemainder m n := by
  unfold mobiusRowRemainder
  rw [rawMobiusDerivativeResidual_eq_mobiusResidual, mobiusResidual, map_add,
    hilbertDifference_hilbertOne, derivative_mobius_synthesis,
    Fintype.linearCombination_apply, inner_add_left, sum_inner,
    ← correctionReciprocalMoment_half]
  simp only [real_inner_smul_left, derivativeFamily, ← signedCorrectionRow_eq_pairing]
  unfold mobiusRowAggregate
  ring

/-- The signed cross term and the full square remainder are retained. -/
theorem mobiusRowAggregate_square (m n : ℕ) :
    (correctionReciprocalMoment n / 2)^2 =
      (mobiusRowAggregate m n)^2 +
        2 * mobiusRowAggregate m n * mobiusRowRemainder m n +
        (mobiusRowRemainder m n)^2 := by
  rw [mobiusRowAggregate_exact]
  ring

theorem mobiusRowRemainder_bound (m n : ℕ) :
    |mobiusRowRemainder m n| ≤
      ‖rawMobiusDerivativeResidual (m + 1)‖ *
        ‖hilbertDifference (correctionSynthesis n)‖ :=
  abs_real_inner_le_norm _ _

/-- One unconditional constant controls both independent finite dimensions. -/
theorem mobiusRowAggregate_uniform_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ m n,
      |correctionReciprocalMoment n / 2 - mobiusRowAggregate m n| ≤
        C * ‖rawMobiusDerivativeResidual (m + 1)‖ := by
  obtain ⟨C, hC, hb⟩ := GeometricMoments.correction_derivative_uniform_norm_bound
  refine ⟨C, hC, ?_⟩
  intro m n
  rw [mobiusRowAggregate_exact, add_sub_cancel_left]
  exact (mobiusRowRemainder_bound m n).trans (by
    have h := mul_le_mul_of_nonneg_left (hb n)
      (norm_nonneg (rawMobiusDerivativeResidual (m + 1)))
    nlinarith)

theorem mobiusRowRemainder_tendsto_zero (m : ℕ → ℕ)
    (hm : Tendsto m atTop atTop) :
    Tendsto (fun n => mobiusRowRemainder (m n) n) atTop (𝓝 0) := by
  have hr := rawMobiusDerivativeResidual_tendsto_zero.comp
    ((tendsto_add_atTop_nat 1).comp hm)
  simpa only [Function.comp_def, mobiusRowRemainder, inner_zero_left] using
    hr.inner (𝕜 := ℝ) derivative_correction_tendsto

/-- No relative growth condition on the test and optimization cutoffs is needed. -/
theorem mobiusRowAggregate_tendsto (m : ℕ → ℕ) (hm : Tendsto m atTop atTop) :
    Tendsto (fun n => mobiusRowAggregate (m n) n) atTop
      (𝓝 (-hilbertSequence limitResidual 1 / 2)) := by
  have he (n : ℕ) : mobiusRowAggregate (m n) n =
      reciprocalCorrection n / 2 - mobiusRowRemainder (m n) n := by
    have h := mobiusRowAggregate_exact (m n) n
    rw [correctionReciprocalMoment_eq_reciprocalCorrection] at h
    linarith
  simpa only [he, sub_zero] using
    (reciprocalCorrection_tendsto.div_const 2).sub (mobiusRowRemainder_tendsto_zero m hm)

theorem mobiusRowAggregate_tendsto_full_remainder (m : ℕ → ℕ)
    (hm : Tendsto m atTop atTop) :
    Tendsto (fun n => mobiusRowAggregate (m n) n) atTop
      (𝓝 (-((2 - Real.sqrt 2) * limitEnergy +
        (Real.sqrt 2 / 2) *
          ‖limitResidual - (Real.sqrt 2 / 2) • doubleDilation limitResidual‖^2) / 2)) := by
  simpa only [firstCoordinate_eq_energy_add_dyadicRemainder] using
    mobiusRowAggregate_tendsto m hm

/-- Exact equivalence; the cofinal arithmetic lower-bound provider remains open. -/
theorem mobiusRowAggregate_cofinal_iff_residual_zero (m : ℕ → ℕ)
    (hm : Tendsto m atTop atTop) :
    (∀ ε : ℝ, 0 < ε →
      ∃ᶠ n : ℕ in atTop, -ε < mobiusRowAggregate (m n) n) ↔
        limitResidual = 0 := by
  constructor
  · intro h
    apply firstCoordinate_zero_iff_residual_zero.mp
    by_contra hz
    have hp : 0 < hilbertSequence limitResidual 1 :=
      lt_of_le_of_ne firstCoordinate_nonneg (Ne.symm hz)
    have he : ∀ᶠ n : ℕ in atTop, mobiusRowAggregate (m n) n <
        -(hilbertSequence limitResidual 1 / 4) :=
      (mobiusRowAggregate_tendsto m hm).eventually_lt_const (by linarith)
    obtain ⟨n, hn, hn'⟩ :=
      ((h (hilbertSequence limitResidual 1 / 4) (by positivity)).and_eventually he).exists
    linarith
  · intro h ε hε
    have ht := mobiusRowAggregate_tendsto m hm
    have hz := firstCoordinate_zero_iff_residual_zero.mpr h
    rw [hz] at ht
    exact (ht.eventually_const_lt (by linarith)).frequently

theorem mobiusRowAggregate_cofinal_iff_fixedMismatch (m : ℕ → ℕ)
    (hm : Tendsto m atTop atTop) :
    (∀ ε : ℝ, 0 < ε →
      ∃ᶠ n : ℕ in atTop, -ε < mobiusRowAggregate (m n) n) ↔
        ∀ i : ℕ, Tendsto (fun n => fixedMismatch n i) atTop (𝓝 0) :=
  (mobiusRowAggregate_cofinal_iff_residual_zero m hm).trans
    fixedMismatch_limits_iff_residual_zero.symm

/-- CONDITIONAL RESEARCH REDUCTION: only a one-sided cofinal bound is required. -/
theorem riemannHypothesis_of_cofinal_mobiusRowAggregate
    (h : ∀ ε : ℝ, 0 < ε →
      ∃ᶠ n : ℕ in atTop, -ε < mobiusRowAggregate n n) : RiemannHypothesis := by
  apply riemannHypothesis_of_fixedMismatch_limits
  exact (mobiusRowAggregate_cofinal_iff_fixedMismatch id tendsto_id).mp h

/-- Both the Abel endpoint and every signed interior summand are retained. -/
theorem mobiusRowAggregate_eq_abel (m n : ℕ) :
    mobiusRowAggregate m n =
      -(∑ i : Fin m, mobiusVector m i *
        (primitive (correctionCoefficient n) n * derivativeRowKernel i.val n -
          ∑ k ∈ Finset.range n,
            primitive (correctionCoefficient n) (k + 1) *
              difference (derivativeRowKernel i.val) k)) := by
  simp only [mobiusRowAggregate, signedCorrectionRow_eq_abel]

/-- The same aggregate uses the complete CRT intersections. -/
theorem mobiusRowAggregate_eq_crt (m n : ℕ) :
    mobiusRowAggregate m n =
      -(∑ i : Fin m, mobiusVector m i * correctionCRTRow n i.val) := by
  simp only [mobiusRowAggregate, signedCorrectionRow_eq_crt]

/-- The reconstruction error is uniformly small in the optimization stage;
the test cutoff may be chosen before n, without an inverse-Gram norm bound. -/
theorem mobiusRowAggregate_uniform_approximation :
    ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ m ≥ M, ∀ n : ℕ,
      |correctionReciprocalMoment n / 2 - mobiusRowAggregate m n| < ε := by
  intro ε hε
  obtain ⟨C, hC, hb⟩ := mobiusRowAggregate_uniform_bound
  have ht : Tendsto (fun m => C * ‖rawMobiusDerivativeResidual (m + 1)‖)
      atTop (𝓝 0) := by
    simpa using
      (rawMobiusDerivativeResidual_norm_tendsto_zero.comp
        (tendsto_add_atTop_nat 1)).const_mul C
  obtain ⟨M, hM⟩ := eventually_atTop.1 (ht.eventually_lt_const hε)
  exact ⟨M, fun m hm n => (hb m n).trans_lt (hM m hm)⟩

/-- All limiting derivative tests are quantitatively controlled by the single
first-coordinate obstruction. The exact dyadic square is recorded in the
aggregate limit theorem; this inequality only uses its lower-energy bound. -/
theorem limiting_derivative_test_sq_le_firstCoordinate (f : ThresholdHilbert) :
    |inner ℝ f (hilbertDifference limitResidual)|^2 ≤
      (4 + 2 * Real.sqrt 2) * ‖f‖^2 * hilbertSequence limitResidual 1 := by
  have hl : (2 - Real.sqrt 2) * limitEnergy ≤ hilbertSequence limitResidual 1 := by
    linarith [firstCoordinate_energy_bounds.1]
  have hc : (2 + Real.sqrt 2) * (2 - Real.sqrt 2) = 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have he := mul_le_mul_of_nonneg_left hl
    (show 0 ≤ 2 + Real.sqrt 2 by positivity)
  rw [← mul_assoc, hc] at he
  have hd : ‖hilbertDifference limitResidual‖^2 ≤
      (4 + 2 * Real.sqrt 2) * hilbertSequence limitResidual 1 := by
    linarith [limiting_mismatch_bounds.2]
  have hs := (sq_le_sq₀ (abs_nonneg _) (by positivity)).2
    (abs_real_inner_le_norm f (hilbertDifference limitResidual))
  have hm := mul_le_mul_of_nonneg_left hd (sq_nonneg ‖f‖)
  nlinarith

/-- A direct finite arithmetic condition on the actual inverse-Gram vector.
Only one signed scalar is tested, and only from below along cofinal stages. -/
theorem cofinal_mobius_gram_iff_fixedMismatch :
    (∀ ε : ℝ, 0 < ε → ∃ᶠ n : ℕ in atTop,
      -(∑ i : Fin n, (ArithmeticFunction.moebius (i.val + 2) : ℝ) *
        (∑ j : Fin n, correctionVector n j *
          inner ℝ (derivativeAtom i.val) (derivativeAtom j.val))) > -ε) ↔
        ∀ i : ℕ, Tendsto (fun n => fixedMismatch n i) atTop (𝓝 0) := by
  simpa only [mobiusRowAggregate, mobiusVector, signedCorrectionRow, id_eq] using
    mobiusRowAggregate_cofinal_iff_fixedMismatch id tendsto_id

/-- Endpoint plus the entire signed harmonic-weighted primitive sum. -/
def reciprocalCorrectionAbel (n : ℕ) : ℝ :=
  primitive (correctionCoefficient n) n / ((n + 2 : ℕ) : ℝ) +
    ∑ k ∈ Finset.range n, primitive (correctionCoefficient n) (k + 1) /
      (((k + 2 : ℕ) : ℝ) * ((k + 3 : ℕ) : ℝ))

private theorem reciprocal_kernel_difference (k : ℕ) :
    difference (fun j => 1 / ((j + 2 : ℕ) : ℝ)) k =
      -(1 / (((k + 2 : ℕ) : ℝ) * ((k + 3 : ℕ) : ℝ))) := by
  unfold difference
  have h2 : (k : ℝ) + 2 ≠ 0 := by positivity
  have h3 : (k : ℝ) + 3 ≠ 0 := by positivity
  push_cast
  field_simp [h2, h3]
  ring

theorem reciprocalCorrectionAbel_eq_moment (n : ℕ) :
    reciprocalCorrectionAbel n = correctionReciprocalMoment n := by
  have he : correctionReciprocalMoment n =
      ∑ j ∈ Finset.range n, correctionCoefficient n j *
        (1 / ((j + 2 : ℕ) : ℝ)) := by
    rw [← Fin.sum_univ_eq_sum_range]
    unfold correctionReciprocalMoment
    apply Finset.sum_congr rfl
    intro j hj
    simp [correctionCoefficient]
    ring
  rw [he, sum_eq_value]
  unfold value reciprocalCorrectionAbel
  simp_rw [reciprocal_kernel_difference]
  simp only [mul_neg, Finset.sum_neg_distrib, sub_neg_eq_add]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro k hk
    ring

theorem mobiusRowAggregate_reciprocalAbel_exact (m n : ℕ) :
    reciprocalCorrectionAbel n / 2 =
      mobiusRowAggregate m n + mobiusRowRemainder m n := by
  rw [reciprocalCorrectionAbel_eq_moment]
  exact mobiusRowAggregate_exact m n

/-- A finite residual square remains, even after the exact CRT cancellations. -/
theorem mobiusRowAggregate_finite_dyadic_exact (m n : ℕ) :
    2 * mobiusRowAggregate m n + finiteDyadicSquare n -
      mobiusReciprocalSum (n + 1) + 2 * mobiusRowRemainder m n =
        finiteDyadicDefect n := by
  have h := reciprocalCorrection_add_dyadicSquare_sub_mobius n
  rw [← correctionReciprocalMoment_eq_reciprocalCorrection] at h
  have he := mobiusRowAggregate_exact m n
  linarith

/-- Exact signed diagonal balance with both complete dyadic squares. -/
theorem mobiusRowAggregate_doubleStage_full_remainders (m b : ℕ) :
    2 * mobiusRowAggregate m (doubleStage b) =
      mobiusReciprocalSum (doubleStage b + 1) -
        (2 - Real.sqrt 2) * energy (doubleStage b) -
        (Real.sqrt 2 / 2) * finiteDyadicResidualRemainder (doubleStage b) +
        (Real.sqrt 2 / 2) *
          (energy b - energy (doubleStage (doubleStage b)) -
            finiteDyadicIncrementRemainder b) -
        2 * mobiusRowRemainder m (doubleStage b) := by
  have h := mobiusRowAggregate_finite_dyadic_exact m (doubleStage b)
  rw [finiteDyadicSquare_eq_energy_add_remainder,
    finiteDyadicDefect_eq_energy_drop_sub_remainder] at h
  linarith

theorem derivative_correction_finite_norm_bound (n : ℕ) :
    ‖hilbertDifference (correctionSynthesis n)‖ ≤
      ‖rawMobiusDerivativeResidual (n + 1)‖ +
        2 * ‖projectionResidual n‖ := by
  rw [derivative_correction_exact]
  change ‖rawMobiusDerivativeResidual (n + 1) -
    hilbertDifference (projectionResidual n)‖ ≤ _
  exact (norm_sub_le _ _).trans
    (add_le_add_right (hilbertDifference_norm_le (projectionResidual n)) _)

/-- A fully finite estimate about the negative residual square, retaining its center. -/
theorem mobiusRowAggregate_doubleStage_centered_bound (m b : ℕ) :
    |mobiusRowAggregate m (doubleStage b) +
        finiteDyadicSquare (doubleStage b) / 2 -
        mobiusReciprocalSum (doubleStage b + 1) / 2| ≤
      (Real.sqrt 2 / 4) * (energy b - energy (doubleStage (doubleStage b))) +
        ‖rawMobiusDerivativeResidual (m + 1)‖ *
          (‖rawMobiusDerivativeResidual (doubleStage b + 1)‖ +
            2 * ‖projectionResidual (doubleStage b)‖) := by
  have he : mobiusRowAggregate m (doubleStage b) +
      finiteDyadicSquare (doubleStage b) / 2 -
      mobiusReciprocalSum (doubleStage b + 1) / 2 =
      finiteDyadicDefect (doubleStage b) / 2 - mobiusRowRemainder m (doubleStage b) := by
    linarith [mobiusRowAggregate_finite_dyadic_exact m (doubleStage b)]
  rw [he]
  have hd := finiteDyadicDefect_two_gap_abs b
  have hu := (mobiusRowRemainder_bound m (doubleStage b)).trans
    (mul_le_mul_of_nonneg_left (derivative_correction_finite_norm_bound (doubleStage b))
      (norm_nonneg _))
  have ha := abs_sub (finiteDyadicDefect (doubleStage b) / 2)
    (mobiusRowRemainder m (doubleStage b))
  rw [abs_div, show |(2 : ℝ)| = 2 by norm_num] at ha
  linarith


/-- One-sided lower estimate for the signed aggregate, with the residual square retained. -/
theorem mobiusRowAggregate_doubleStage_lower_bound (m b : ℕ) :
    -finiteDyadicSquare (doubleStage b) / 2 +
        mobiusReciprocalSum (doubleStage b + 1) / 2 -
        (Real.sqrt 2 / 4) * (energy b - energy (doubleStage (doubleStage b))) -
        ‖rawMobiusDerivativeResidual (m + 1)‖ *
          (‖rawMobiusDerivativeResidual (doubleStage b + 1)‖ +
            2 * ‖projectionResidual (doubleStage b)‖) ≤
      mobiusRowAggregate m (doubleStage b) := by
  have h := (abs_le.mp (mobiusRowAggregate_doubleStage_centered_bound m b)).1
  linarith

/-- Complete cancellation occurs before the absolute value in the dyadic budget. -/
theorem mobiusRowAggregate_centered_dyadic_budget (m : ℕ → ℕ) (b K : ℕ) :
    (∑ k ∈ Finset.range K,
      |2 * mobiusRowAggregate (m k) (dyadicStage b (k + 1)) +
        finiteDyadicSquare (dyadicStage b (k + 1)) -
        mobiusReciprocalSum (dyadicStage b (k + 1) + 1) +
        2 * mobiusRowRemainder (m k) (dyadicStage b (k + 1))|) ≤
      (Real.sqrt 2 / 2) *
        (energy b + energy (doubleStage b) - energy (dyadicStage b K) -
          energy (dyadicStage b (K + 1))) := by
  simp_rw [mobiusRowAggregate_finite_dyadic_exact]
  exact finiteDyadicDefect_sum_abs_le b K

/-- CONDITIONAL RESEARCH REDUCTION: the endpoint and signed sum are tested together. -/
theorem reciprocalCorrectionAbel_cofinal_iff_residual_zero :
    (∀ ε : ℝ, 0 < ε → ∃ᶠ n : ℕ in atTop,
      -ε < reciprocalCorrectionAbel n) ↔ limitResidual = 0 := by
  have ht : Tendsto reciprocalCorrectionAbel atTop
      (𝓝 (-hilbertSequence limitResidual 1)) := by
    have he : reciprocalCorrectionAbel = reciprocalCorrection := by
      funext n
      rw [reciprocalCorrectionAbel_eq_moment,
        correctionReciprocalMoment_eq_reciprocalCorrection]
    simpa only [he] using reciprocalCorrection_tendsto
  constructor
  · intro h
    apply firstCoordinate_zero_iff_residual_zero.mp
    by_contra hz
    have hp : 0 < hilbertSequence limitResidual 1 :=
      lt_of_le_of_ne firstCoordinate_nonneg (Ne.symm hz)
    have he : ∀ᶠ n : ℕ in atTop, reciprocalCorrectionAbel n <
        -(hilbertSequence limitResidual 1 / 2) :=
      ht.eventually_lt_const (by linarith)
    obtain ⟨n, hn, hn'⟩ :=
      ((h (hilbertSequence limitResidual 1 / 2) (by positivity)).and_eventually he).exists
    linarith
  · intro hz ε hε
    rw [firstCoordinate_zero_iff_residual_zero.mpr hz, neg_zero] at ht
    exact (ht.eventually_const_lt (by linarith)).frequently

theorem riemannHypothesis_of_cofinal_reciprocalCorrectionAbel
    (h : ∀ ε : ℝ, 0 < ε → ∃ᶠ n : ℕ in atTop,
      -ε < reciprocalCorrectionAbel n) : RiemannHypothesis := by
  apply riemannHypothesis_of_fixedMismatch_limits
  exact fixedMismatch_limits_iff_residual_zero.mpr
    (reciprocalCorrectionAbel_cofinal_iff_residual_zero.mp h)

end RiemannResearch.RH.Pareto.CoefficientStabilization.DerivativeCompatibility
