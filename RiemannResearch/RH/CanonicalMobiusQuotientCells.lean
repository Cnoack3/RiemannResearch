import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import RiemannResearch.NumberTheory.MobiusReciprocalSum
import RiemannResearch.RH.CanonicalMobiusConditionalHead
import RiemannResearch.RH.CanonicalMobiusFullEnergy
import RiemannResearch.RH.ParetoDilation
import RiemannResearch.RH.ThresholdHilbertMean
import RiemannResearch.RH.ThresholdHilbertSpace
import RiemannResearch.RH.CanonicalMobiusWindowCancellation
import RiemannResearch.RH.CanonicalMobiusSignedAverages
import Mathlib.Tactic.Ring
/-!
# Exact arithmetic on common quotient cells

Source: independently developed from the exact finite Möbius floor-tail identity
in `CanonicalMobiusWindowCancellation`, in response to the user's October 14, 2026
request for arithmetic control of covariance when both cutoffs move.

Write M(n) = ∑ d ≤ n, μ(d), b(Y) = (Y + 1) S(Y) - M(Y), and
H(q,n) = ∑ k ≤ q, M(⌊n/k⌋). The exact residual is H(q,n) + q b(Y), where
q = ⌊n/(Y + 1)⌋. On a common quotient cell, every normalized signed average
therefore has the same nonconstant profile H(q,n); its coefficients change only
the constant term. The cell energy is exactly the weighted variance of H plus
a mean-square term. The full norm equality retains the entire complementary
infinite sum. No signed term or remaining energy is discarded.

These are unconditional finite arithmetic identities and a resulting lower
bound, not a uniform covariance upper bound or an RH proof. The necessary
arithmetic upper estimate for the retained Mertens-profile variance and the
complement remains open. Common cells can be empty for widely separated
cutoffs, so these results do not exclude general cofinal signed averages.
Taking Y = p - 1 specializes to the canonical prime-cutoff family.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
/-- The cutoff-dependent constant after exact floor-tail cancellation. -/
noncomputable def mobiusCellOffset (Y : ℕ) : ℝ :=
  ((Y + 1 : ℕ) : ℝ) * mobiusReciprocalSum Y -
    ∑ d ∈ Finset.Icc 1 Y, (ArithmeticFunction.moebius d : ℝ)
/-- The common arithmetic profile on a cell of fixed quotient. -/
noncomputable def mobiusQuotientProfile (q n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 q, ∑ d ∈ Finset.Icc 1 (n / k), (ArithmeticFunction.moebius d : ℝ)
/-- The complete exact residual identity, including the reciprocal Möbius correction. -/
theorem canonicalMobiusResidual_quotient_identity (Y n : ℕ) (hn : 0 < n) :
    1 - canonicalMobiusHead Y n =
      mobiusQuotientProfile (n / (Y + 1)) n + ((n / (Y + 1) : ℕ) : ℝ) * mobiusCellOffset Y := by
  by_cases hYn : Y ≤ n
  · have ht := finite_mobius_floor_tail_identity Y n hn hYn
    rw [canonicalMobiusHead_floor_expansion]
    unfold mobiusQuotientProfile mobiusCellOffset
    rw [Finset.sum_sub_distrib] at ht
    simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul] at ht
    linarith
  · have hnY : n ≤ Y := (lt_of_not_ge hYn).le
    have hq : n / (Y + 1) = 0 := Nat.div_eq_of_lt (Nat.lt_succ_of_le hnY)
    rw [canonicalMobiusHead_exact Y n hn hnY, hq]
    simp [mobiusQuotientProfile]

/-- The signed two-cutoff product on a common quotient cell; both correction terms remain. -/
theorem canonicalMobiusResidual_quotient_product (Y Z q n : ℕ) (hn : 0 < n)
    (hY : n / (Y + 1) = q) (hZ : n / (Z + 1) = q) :
    (1 - canonicalMobiusHead Y n) * (1 - canonicalMobiusHead Z n) =
      mobiusQuotientProfile q n ^ 2 +
      (q : ℝ) * (mobiusCellOffset Y + mobiusCellOffset Z) * mobiusQuotientProfile q n +
      (q : ℝ) ^ 2 * mobiusCellOffset Y * mobiusCellOffset Z := by
  rw [canonicalMobiusResidual_quotient_identity Y n hn,
    canonicalMobiusResidual_quotient_identity Z n hn, hY, hZ]
  ring

/-- Normalized signed averaging changes only the constant on a common quotient cell. -/
theorem signedMobiusAverage_quotient_cell (s : Finset ℕ) (a : ℕ → ℝ)
    (q n : ℕ) (hn : 0 < n) (hsum : ∑ Y ∈ s, a Y = 1)
    (hcell : ∀ Y ∈ s, n / (Y + 1) = q) :
    1 - hilbertSequence (signedMobiusAverage s a) n =
      mobiusQuotientProfile q n + (q : ℝ) * (∑ Y ∈ s, a Y * mobiusCellOffset Y) := by
  rw [signedMobiusAverage_sequence]
  calc
    1 - ∑ Y ∈ s, a Y * canonicalMobiusHead Y n =
        ∑ Y ∈ s, a Y * (1 - canonicalMobiusHead Y n) := by
      simp_rw [mul_sub, mul_one]
      rw [Finset.sum_sub_distrib, hsum]
    _ = ∑ Y ∈ s, a Y * (mobiusQuotientProfile q n + (q : ℝ) * mobiusCellOffset Y) := by
      apply Finset.sum_congr rfl
      intro Y hY
      rw [canonicalMobiusResidual_quotient_identity Y n hn, hcell Y hY]
    _ = _ := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, hsum, one_mul]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro Y hY
      ring

/-- The mean for the actual Pareto weights on a finite set. -/
noncomputable def mobiusQuotientMean (t : Finset ℕ) (q : ℕ) : ℝ :=
  (∑ n ∈ t, positiveWeight n * mobiusQuotientProfile q n) /
    ∑ n ∈ t, positiveWeight n

/-- Unnormalized variance for the actual Pareto weights, not a flat-period variance. -/
noncomputable def mobiusQuotientVariance (t : Finset ℕ) (q : ℕ) : ℝ :=
  ∑ n ∈ t, positiveWeight n * (mobiusQuotientProfile q n - mobiusQuotientMean t q) ^ 2

/-- Exact completion of the square for the arithmetic profile and its constant correction. -/
theorem mobiusQuotientProfile_translation_energy (t : Finset ℕ) (q : ℕ) (b : ℝ)
    (hW : (∑ n ∈ t, positiveWeight n) ≠ 0) :
    (∑ n ∈ t, positiveWeight n * (mobiusQuotientProfile q n + b) ^ 2) =
      mobiusQuotientVariance t q +
      (∑ n ∈ t, positiveWeight n) * (mobiusQuotientMean t q + b) ^ 2 := by
  have hm : (∑ n ∈ t, positiveWeight n) * mobiusQuotientMean t q =
      ∑ n ∈ t, positiveWeight n * mobiusQuotientProfile q n := by
    unfold mobiusQuotientMean
    exact mul_div_cancel₀ _ hW
  have hc : (∑ n ∈ t, positiveWeight n *
      (mobiusQuotientProfile q n - mobiusQuotientMean t q)) = 0 := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
    linarith
  calc
    _ = ∑ n ∈ t, (positiveWeight n *
        (mobiusQuotientProfile q n - mobiusQuotientMean t q) ^ 2 +
        (2 * (mobiusQuotientMean t q + b)) * (positiveWeight n *
          (mobiusQuotientProfile q n - mobiusQuotientMean t q)) +
        positiveWeight n * (mobiusQuotientMean t q + b) ^ 2) := by
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
        hc, ← Finset.sum_mul]
      simp [mobiusQuotientVariance]

/-- The complete cell energy, retaining its mean-square correction. -/
theorem signedMobiusAverage_quotient_cell_energy (s t : Finset ℕ) (a : ℕ → ℝ)
    (q : ℕ) (hsum : ∑ Y ∈ s, a Y = 1)
    (ht : ∀ n ∈ t, 0 < n) (hcell : ∀ n ∈ t, ∀ Y ∈ s, n / (Y + 1) = q)
    (hW : (∑ n ∈ t, positiveWeight n) ≠ 0) :
    (∑ n ∈ t, positiveWeight n * (1 - hilbertSequence (signedMobiusAverage s a) n) ^ 2) =
      mobiusQuotientVariance t q + (∑ n ∈ t, positiveWeight n) *
        (mobiusQuotientMean t q + (q : ℝ) * (∑ Y ∈ s, a Y * mobiusCellOffset Y)) ^ 2 := by
  calc
    _ = ∑ n ∈ t, positiveWeight n *
        (mobiusQuotientProfile q n + (q : ℝ) * (∑ Y ∈ s, a Y * mobiusCellOffset Y)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [signedMobiusAverage_quotient_cell s a q n (ht n hn) hsum (hcell n hn)]
    _ = _ := mobiusQuotientProfile_translation_energy t q _ hW


/-- Concrete interval inequalities guarantee a common quotient. -/
private theorem quotient_cell_of_mem_Ico (s : Finset ℕ) (q L U n : ℕ)
    (hbounds : ∀ Y ∈ s, q * (Y + 1) ≤ L ∧ U ≤ (q + 1) * (Y + 1))
    (hn : n ∈ Finset.Ico L U) : ∀ Y ∈ s, n / (Y + 1) = q := by
  intro Y hY
  obtain ⟨hL, hU⟩ := hbounds Y hY
  obtain ⟨hnL, hnU⟩ := Finset.mem_Ico.mp hn
  have hlo : q ≤ n / (Y + 1) := (Nat.le_div_iff_mul_le (Nat.succ_pos Y)).2
    (hL.trans hnL)
  have hhi : n / (Y + 1) < q + 1 := (Nat.div_lt_iff_lt_mul (Nat.succ_pos Y)).2
    (by simpa [Nat.mul_comm] using hnU.trans_le hU)
  exact Nat.le_antisymm (Nat.lt_succ_iff.mp hhi) hlo

/-- The full norm is the arithmetic cell variance, the mean square, and the entire complement. -/
theorem signedMobiusAverage_quotient_full_energy (s t : Finset ℕ) (a : ℕ → ℝ)
    (q : ℕ) (hsum : ∑ Y ∈ s, a Y = 1)
    (ht : ∀ n ∈ t, 0 < n) (hcell : ∀ n ∈ t, ∀ Y ∈ s, n / (Y + 1) = q)
    (hW : (∑ n ∈ t, positiveWeight n) ≠ 0) :
    ‖hilbertOne - signedMobiusAverage s a‖ ^ 2 =
      mobiusQuotientVariance t q + (∑ n ∈ t, positiveWeight n) *
        (mobiusQuotientMean t q + (q : ℝ) * (∑ Y ∈ s, a Y * mobiusCellOffset Y)) ^ 2 +
      ∑' n : {n : ℕ // n ∉ t}, positiveWeight n.val *
        (hilbertSequence (hilbertOne - signedMobiusAverage s a) n.val) ^ 2 := by
  rw [hilbert_norm_weighted_sq,
    ← (hilbertSequence_square_summable
      (hilbertOne - signedMobiusAverage s a)).sum_add_tsum_subtype_compl t]
  congr 1
  rw [← signedMobiusAverage_quotient_cell_energy s t a q hsum ht hcell hW]
  apply Finset.sum_congr rfl
  intro n hn
  have he : hilbertSequence (hilbertOne - signedMobiusAverage s a) n =
      1 - hilbertSequence (signedMobiusAverage s a) n := by
    change (hilbertSequenceLinear (hilbertOne - signedMobiusAverage s a)) n = _
    rw [map_sub]
    change hilbertSequence hilbertOne n - hilbertSequence (signedMobiusAverage s a) n = _
    rw [hilbertOne_sequence]
    simp [zeroAnchor, Nat.ne_of_gt (ht n hn)]
  rw [he]

/-- The exact split gives a local constraint; it supplies no uniform upper estimate. -/
theorem mobiusQuotientVariance_le_signedMobiusAverage_energy
    (s t : Finset ℕ) (a : ℕ → ℝ) (q : ℕ) (hsum : ∑ Y ∈ s, a Y = 1)
    (ht : ∀ n ∈ t, 0 < n) (hcell : ∀ n ∈ t, ∀ Y ∈ s, n / (Y + 1) = q)
    (hW : (∑ n ∈ t, positiveWeight n) ≠ 0) :
    mobiusQuotientVariance t q ≤ ‖hilbertOne - signedMobiusAverage s a‖ ^ 2 := by
  rw [signedMobiusAverage_quotient_full_energy s t a q hsum ht hcell hW]
  have hm : 0 ≤ (∑ n ∈ t, positiveWeight n) *
      (mobiusQuotientMean t q + (q : ℝ) * (∑ Y ∈ s, a Y * mobiusCellOffset Y)) ^ 2 :=
    mul_nonneg (Finset.sum_nonneg (fun n hn => positiveWeight_nonneg n)) (sq_nonneg _)
  have hr : 0 ≤ ∑' n : {n : ℕ // n ∉ t}, positiveWeight n.val *
      (hilbertSequence (hilbertOne - signedMobiusAverage s a) n.val) ^ 2 :=
    tsum_nonneg (fun n => mul_nonneg (positiveWeight_nonneg _) (sq_nonneg _))
  linarith


/-- The first quotient profile is the ordinary Mertens partial sum. -/
@[simp] theorem mobiusQuotientProfile_one (n : ℕ) :
    mobiusQuotientProfile 1 n =
      ∑ d ∈ Finset.Icc 1 n, (ArithmeticFunction.moebius d : ℝ) := by
  simp [mobiusQuotientProfile]

/-- A concrete nonempty common interval gives the full exact energy split, with no
nonzero-mass or analytic hypothesis left to supply. -/
theorem signedMobiusAverage_quotient_interval_full_energy
    (s : Finset ℕ) (a : ℕ → ℝ) (q L U : ℕ) (hL : 0 < L) (hLU : L < U)
    (hsum : ∑ Y ∈ s, a Y = 1)
    (hbounds : ∀ Y ∈ s, q * (Y + 1) ≤ L ∧ U ≤ (q + 1) * (Y + 1)) :
    ‖hilbertOne - signedMobiusAverage s a‖ ^ 2 =
      mobiusQuotientVariance (Finset.Ico L U) q +
      (1 / (L : ℝ) - 1 / (U : ℝ)) *
        (mobiusQuotientMean (Finset.Ico L U) q +
          (q : ℝ) * (∑ Y ∈ s, a Y * mobiusCellOffset Y)) ^ 2 +
      ∑' n : {n : ℕ // n ∉ Finset.Ico L U}, positiveWeight n.val *
        (hilbertSequence (hilbertOne - signedMobiusAverage s a) n.val) ^ 2 := by
  have ht : ∀ n ∈ Finset.Ico L U, 0 < n := fun n hn =>
    hL.trans_le (Finset.mem_Ico.mp hn).1
  have hW : 0 < ∑ n ∈ Finset.Ico L U, positiveWeight n := by
    apply Finset.sum_pos
    · intro n hn
      have hn0 := ht n hn
      unfold positiveWeight
      positivity
    · exact Finset.nonempty_Ico.mpr hLU
  have h := signedMobiusAverage_quotient_full_energy s (Finset.Ico L U) a q hsum ht
    (fun n hn => quotient_cell_of_mem_Ico s q L U n hbounds hn) hW.ne'
  rw [positiveWeight_interval L U hL hLU.le] at h
  exact h

end RiemannResearch.RH.Pareto
