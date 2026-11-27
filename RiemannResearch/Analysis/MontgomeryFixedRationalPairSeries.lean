import RiemannResearch.Analysis.ActualPrimeTorusFMZInterpolation
import RiemannResearch.Analysis.ActualZeroLoglogRate
import RiemannResearch.Analysis.ActualZeroTriangularIntegral
import RiemannResearch.Analysis.MontgomeryAllPairWordRounding
import RiemannResearch.Analysis.MontgomeryHeightCutoff
import RiemannResearch.Analysis.MontgomeryMacroscopicGapSecondTerm
import RiemannResearch.Analysis.FinitePrimeModeCoefficients
import RiemannResearch.Analysis.ThreePrimeGapParseval
import Mathlib.Analysis.Normed.Group.Tannery

/-! # Height-normalized all-pair Fourier limits on fixed rational frequencies

The exact measured collision atom is removed before taking a squared-Fourier
limit. A weighted absolute-summability bound allows countably many fixed
signed rational frequencies. The limiting coefficients are the squares of
the one-point FMZ main terms. At a fixed prime-power frequency the same
strict positive-gap cosine sum diverges on the PCC normalization.

Source: the Mellin prime-orbit handoff, section 5, together with the
repository's actual-zero FMZ and local Cauchy-mass estimates.
-/

noncomputable section
open Filter Zeta23
open scoped Topology
namespace RiemannResearch.Analysis.MontgomeryAllPairWordRounding
open ActualZeroOrdinate ActualZeroCollisionCertificate OrdinateCollisionCertificate
open MontgomeryPositiveGap MontgomeryLocalMass MontgomeryPoisson PrimePhaseTorus

/-- All equal-ordinate ordered pairs contribute negligibly on the height-square scale. -/
theorem actualCollision_div_height_sq_tendsto :
    Tendsto (fun T : ℝ => (actualCollision T : ℝ) / T^2) atTop (𝓝 0) := by
  obtain ⟨A,hA,hcount⟩ := exists_count_le_height_log
  obtain ⟨B,hB,hrow⟩ := exists_actual_cauchy_row_bound
  have h := MontgomeryHeightCutoff.log_sq_div_height_tendsto_zero.const_mul (2*A*B)
  apply squeeze_zero' (Eventually.of_forall fun T => div_nonneg (Nat.cast_nonneg _) (sq_nonneg T))
    _ (by simpa only [mul_zero] using h)
  filter_upwards [eventually_ge_atTop (9 : ℝ)] with T ht
  have hT : 0 < T := by linarith
  have hl : Real.log (T+3) ≤ 2*Real.log T := by
    have he : T+3 ≤ T^2 := by nlinarith [sq_nonneg (T-3)]
    simpa only [Real.log_pow, Nat.cast_ofNat] using Real.log_le_log (by linarith) he
  have hcoll := collision_le_kernelEnergy (copyOrdinate T) cauchyWeight cauchyWeight_nonneg
    (by norm_num [cauchyWeight])
  have hb : (actualCollision T : ℝ) ≤ (Ncount 0 T : ℝ) * (B * Real.log (T+3)) := by
    apply hcoll.trans
    apply (Finset.sum_le_sum fun i _ => hrow T hT.le (copyOrdinate T i)).trans_eq
    simp only [Finset.sum_const, Finset.card_univ, card_copies, nsmul_eq_mul]
  have hlog : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  calc
    _ ≤ ((A*T*Real.log T) * (B*(2*Real.log T))) / T^2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      exact hb.trans (mul_le_mul (hcount T ht) (mul_le_mul_of_nonneg_left hl hB.le)
        (mul_nonneg hB.le (Real.log_nonneg (by linarith))) (by positivity))
    _ = _ := by field_simp [hT.ne']

/-- Cosine of the physical gap, summed over every strictly positive pair
with multiplicity, with the two possible orientations accounted for. -/
def positivePairCosine (T u : ℝ) : ℝ :=
  2 * positiveTestSum (copyOrdinate T) (fun d => Real.cos (d*u))

theorem positivePairCosine_eq_square_sub_collision (T u : ℝ) :
    positivePairCosine T u = ‖ordinateSum T u‖^2 - (actualCollision T : ℝ) := by
  rw [positivePairCosine, ← normSq_sub_collision, actual_occurrenceAmplitude,
    Complex.normSq_eq_norm_sq]
  rfl

private theorem heightSquareMode (T u : ℝ) :
    positivePairCosine T u / T^2 =
      ‖ordinateSum T u / (T : ℂ)‖ ^ 2 - (actualCollision T : ℝ) / T^2 := by
  rw [positivePairCosine_eq_square_sub_collision, sub_div, norm_div, div_pow,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- Every fixed nonzero rational mode has a collision-subtracted squared main term. -/
theorem positivePairCosine_rational_div_height_sq {n m : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hnm : n ≠ m) :
    Tendsto (fun T : ℝ => positivePairCosine T (Real.log ((n : ℝ)/m)) / T^2)
      atTop (𝓝 (‖rationalFMZMain n m‖^2)) := by
  have h := ((tendsto_centeredRationalOrdinate_div hn hm).norm.pow 2).sub
    actualCollision_div_height_sq_tendsto
  simpa only [heightSquareMode, centeredRationalOrdinate, if_neg hnm, sub_zero] using h

/-- Tannery's theorem passes the actual all-rank signed pair statistic
through a countably infinite dictionary of fixed nonzero rational modes. -/
theorem weighted_positivePairCosine_rational_series {ι : Type*} [Countable ι]
    (n m : ι → ℕ) (a : ι → ℝ) (hn : ∀ i, 1 ≤ n i) (hm : ∀ i, 1 ≤ m i)
    (hne : ∀ i, n i ≠ m i)
    (ha : Summable (fun i => |a i| * (fmzLogWeight (rationalModeWeight (n i) (m i))) ^ 2)) :
    Tendsto (fun T : ℝ => ∑' i, a i *
      (positivePairCosine T (Real.log ((n i : ℝ) / m i)) / T^2)) atTop
      (𝓝 (∑' i, a i * ‖rationalFMZMain (n i) (m i)‖^2)) := by
  let W := fun i => fmzLogWeight (rationalModeWeight (n i) (m i))
  obtain ⟨K,hK,hbound⟩ := eventually_centeredRationalOrdinate_logWeight
  have hmajor := ha.mul_left ((K+1)^2+1)
  apply tendsto_tsum_of_dominated_convergence hmajor
      (fun i => (positivePairCosine_rational_div_height_sq (hn i) (hm i) (hne i)).const_mul _)
  filter_upwards [hbound, actualCollision_div_height_sq_tendsto.eventually_lt_const
    (by norm_num : (0 : ℝ) < 1)] with T hT hC i
  have hw : 1 ≤ rationalModeWeight (n i) (m i) := by
    unfold rationalModeWeight; linarith only [abs_nonneg (Real.log (n i) + Real.log (m i))]
  have hw' : rationalModeWeight (n i) (m i) ≤ W i := by
    dsimp only [W, fmzLogWeight]
    exact le_mul_of_one_le_right (by linarith) (by linarith [Real.log_nonneg hw])
  have hW := hw.trans hw'
  have hu : ‖ordinateSum T (Real.log ((n i : ℝ) / m i)) / (T : ℂ)‖ ≤ (K+1)*W i := by
    have e := norm_add_le
      (centeredRationalOrdinate T (n i) (m i)/(T:ℂ) - rationalFMZMain (n i) (m i))
      (rationalFMZMain (n i) (m i))
    rw [sub_add_cancel] at e
    have h := e.trans (add_le_add (hT _ _ (hn i) (hm i))
      ((rationalFMZMain_norm_le_weight _ _ (hn i) (hm i)).trans hw'))
    simpa only [centeredRationalOrdinate, if_neg (hne i), sub_zero, add_mul, one_mul, W] using h
  have hs := pow_le_pow_left₀ (norm_nonneg _) hu 2
  have hnn : 0 ≤ (actualCollision T : ℝ) / T^2 := div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  have hab : |positivePairCosine T (Real.log ((n i : ℝ) / m i)) / T^2| ≤
      ((K+1)^2+1) * W i ^ 2 := by
    rw [heightSquareMode]
    apply abs_le.mpr
    have ht : 1 ≤ W i ^ 2 := one_le_pow₀ hW
    rw [mul_pow] at hs
    constructor <;> nlinarith only [hs, hC, hnn, ht, sq_nonneg (K+1),
      mul_nonneg (sq_nonneg (K+1)) (sq_nonneg (W i)), sq_nonneg (‖ordinateSum T
        (Real.log ((n i : ℝ) / m i)) / (T : ℂ)‖)]
  rw [Real.norm_eq_abs, abs_mul]
  exact (mul_le_mul_of_nonneg_left hab (abs_nonneg _)).trans_eq (by dsimp only [W]; ring)

/-- For a fixed prime-power frequency, count normalization for ordinary PCC
makes the collision-subtracted physical cosine sum diverge. -/
theorem positivePairCosine_primePower_div_unfoldedCutoff {p r : ℕ} (hp : p.Prime) (hr : 0 < r) :
    Tendsto (fun T : ℝ => positivePairCosine T (Real.log ((p^r : ℕ) : ℝ)) /
      unfoldedCutoff T) atTop atTop := by
  have hpow : IsPrimePow (p^r) := ⟨p,r,hp.prime,hr,rfl⟩
  have hmode := positivePairCosine_rational_div_height_sq (n := p^r) (m := 1)
    hpow.one_lt.le (by norm_num) hpow.one_lt.ne'
  have hmain : 0 < ‖rationalFMZMain (p^r) 1‖^2 := by
    rw [rationalFMZMain_prime_pow hp hr]
    have hl := Real.log_pos (show (1:ℝ) < p by exact_mod_cast hp.one_lt)
    have hs := Real.sqrt_pos.mpr (show (0:ℝ) < p by exact_mod_cast hp.pos)
    apply pow_pos (norm_pos_iff.mpr _)
    apply mul_ne_zero
    · apply neg_ne_zero.mpr
      apply div_ne_zero
      · exact Complex.ofReal_ne_zero.mpr hl.ne'
      · exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    · exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (inv_ne_zero hs.ne'))
  have hz : Tendsto (fun T : ℝ => Real.log T/T) atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨Real.log_div_self_tendsto_zero,?_⟩
    filter_upwards [eventually_gt_atTop (1:ℝ)] with T ht
    exact div_pos (Real.log_pos ht) (zero_lt_one.trans ht)
  have hg := (tendsto_inv_nhdsGT_zero.comp hz).const_mul_atTop (by positivity : 0 < 2*Real.pi)
  apply (hmode.pos_mul_atTop hmain hg).congr'
  filter_upwards [eventually_gt_atTop (1:ℝ)] with T ht
  simp only [Function.comp_apply, Nat.cast_one, div_one, unfoldedCutoff]
  have hT : T ≠ 0 := (zero_lt_one.trans ht).ne'
  have hL : Real.log T ≠ 0 := (Real.log_pos ht).ne'
  field_simp [hT,hL]

end RiemannResearch.Analysis.MontgomeryAllPairWordRounding

namespace RiemannResearch.Analysis.ActualInfinitePrimeTorus
open ActualZeroOrdinate PrimePhaseTorus

/-- Every nontrivial character of the two ratio angles has at least two
nonzero prime exponents, even when one ratio order vanishes. Its FMZ main
term is exactly zero. This arithmetic statement also holds for moving orders. -/
theorem two_ratio_word_FMZ_zero {p q r : Nat.Primes}
    (hpq : (p : ℕ) < q) (hqr : (q : ℕ) < r) {a b : ℤ} (hne : a ≠ 0 ∨ b ≠ 0) :
    let w := ratioWord p q a ++ ratioWord q r b
    rationalFMZMain (wordNumerator w) (wordDenominator w) = 0 := by
  intro w
  have hp : (p : ℕ) ∈ wordPrimes w := by simp [w, ratioWord, wordPrimes]
  have hq : (q : ℕ) ∈ wordPrimes w := by simp [w, ratioWord, wordPrimes]
  have hr : (r : ℕ) ∈ wordPrimes w := by simp [w, ratioWord, wordPrimes]
  have ep : wordMode w p = -a := by
    simp [w, ratioWord, wordMode, hpq.ne, (hpq.trans hqr).ne]
  have eq : wordMode w q = a-b := by
    simp [w, ratioWord, wordMode, hpq.ne', hqr.ne, sub_eq_add_neg]
  have er : wordMode w r = b := by
    simp [w, ratioWord, wordMode, hqr.ne', (hpq.trans hqr).ne']
  unfold wordNumerator wordDenominator
  by_cases ha : a = 0
  · have hb : b ≠ 0 := hne.resolve_left (not_not_intro ha)
    apply rationalFMZMain_prime_eq_zero_of_two_nonzero _ _ (wordPrimes_prime w) hq hr hqr.ne
    · simpa [eq, ha] using hb
    · simpa [er] using hb
  · by_cases hb : b = 0
    · apply rationalFMZMain_prime_eq_zero_of_two_nonzero _ _ (wordPrimes_prime w) hp hq hpq.ne
      · simpa [ep] using ha
      · simpa [eq, hb] using ha
    · apply rationalFMZMain_prime_eq_zero_of_two_nonzero _ _ (wordPrimes_prime w)
        hp hr (hpq.trans hqr).ne
      · simpa [ep] using ha
      · simpa [er] using hb

end RiemannResearch.Analysis.ActualInfinitePrimeTorus
