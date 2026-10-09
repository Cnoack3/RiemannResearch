import RiemannResearch.RH.ReciprocalRadicalFourCertificate
import RiemannResearch.RH.ZetaTwoConductorFiveBound
import RiemannResearch.RH.ZetaTwoReciprocalObstruction

/-!
# Target-only reciprocal improvement from actual radical compatibility

Source: independently developed exact signed normal equations, 9 October 2026.
The actual target residual is orthogonal to the permanent four-site dual.
Its resulting site-four identity is used only on this residual. The full
screened image is never assumed to satisfy radical compatibility.
Every tail and optimizer correction remains complete.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.ZetaTwoRadicalFourBound
open ZetaTwoProbability ZetaTwoHilbert ZetaTwoOptimizerStage
open ZetaTwoReciprocalBound ReciprocalInfiniteCertificate
open ReciprocalRadicalFourCertificate
open RiemannResearch.Analysis.InfiniteWeightedCauchy

def signedPair (w : ℕ → ℝ) (f : QHilbert) (i : ℕ) : ℝ :=
  w (i + 5) * qSequence f (i + 5) / ((i + 5 : ℕ) : ℝ) ^ 2

theorem linearRow_pair_summable (a b c : ℝ) (f : QHilbert) :
    Summable (signedPair (linearRow a b c) f) := by
  have hs2 := (summable_nat_add_iff 5).mpr (residueCharge_summable 2 (by norm_num) f)
  have hs3 := (summable_nat_add_iff 5).mpr (residueCharge_summable 3 (by norm_num) f)
  have hs5 := (summable_nat_add_iff 5).mpr (residueCharge_summable 5 (by norm_num) f)
  exact (((hs2.mul_left a).add (hs3.mul_left b)).add (hs5.mul_left c)).congr
    (fun i => by unfold signedPair linearRow residueCharge; ring)

theorem linearRow_pair_tsum (a b c : ℝ) (f : QHilbert) :
    (∑' i : ℕ, signedPair (linearRow a b c) f i) =
      a * (∑' i : ℕ, residueCharge 2 f (i + 5)) +
      b * (∑' i : ℕ, residueCharge 3 f (i + 5)) +
      c * (∑' i : ℕ, residueCharge 5 f (i + 5)) := by
  have hs2 := (summable_nat_add_iff 5).mpr (residueCharge_summable 2 (by norm_num) f)
  have hs3 := (summable_nat_add_iff 5).mpr (residueCharge_summable 3 (by norm_num) f)
  have hs5 := (summable_nat_add_iff 5).mpr (residueCharge_summable 5 (by norm_num) f)
  rw [← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left,
    ← (hs2.mul_left a).tsum_add (hs3.mul_left b),
    ← ((hs2.mul_left a).add (hs3.mul_left b)).tsum_add (hs5.mul_left c)]
  apply tsum_congr
  intro i
  unfold signedPair linearRow residueCharge
  ring

/-- All three recovery rows are full signed normal-equation consequences. -/
theorem radical_signed_normal_equations (f : QHilbert)
    (h2 : inner ℝ (qResidue 2) f = 0) (h3 : inner ℝ (qResidue 3) f = 0)
    (h5 : inner ℝ (qResidue 5) f = 0)
    (h4 : qSequence f 4 = -qSequence f 1 + qSequence f 2 + qSequence f 3) :
    qSequence f 1 + qSequence f 2 / 223 + qSequence f 3 / 223 =
        ∑' i : ℕ, signedPair transformedOne f i ∧
      qSequence f 2 - 14 * qSequence f 3 / 209 =
        ∑' i : ℕ, signedPair transformedTwo f i ∧
      qSequence f 3 = ∑' i : ℕ, signedPair transformedThree f i := by
  have he2 := (residueCharge_summable 2 (by norm_num) f).sum_add_tsum_nat_add 5
  have he3 := (residueCharge_summable 3 (by norm_num) f).sum_add_tsum_nat_add 5
  have he5 := (residueCharge_summable 5 (by norm_num) f).sum_add_tsum_nat_add 5
  have hh2 : (∑ k ∈ Finset.range 5, residueCharge 2 f k) =
      qSequence f 1 + qSequence f 3 / 9 := by
    norm_num only [residueCharge, Finset.sum_range_succ, Finset.sum_range_zero, qSequence_zero]
    ring
  have hh3 : (∑ k ∈ Finset.range 5, residueCharge 3 f k) =
      qSequence f 1 + qSequence f 2 / 2 + qSequence f 4 / 16 := by
    norm_num only [residueCharge, Finset.sum_range_succ, Finset.sum_range_zero, qSequence_zero]
    ring
  have hh5 : (∑ k ∈ Finset.range 5, residueCharge 5 f k) =
      qSequence f 1 + qSequence f 2 / 2 + qSequence f 3 / 3 + qSequence f 4 / 4 := by
    norm_num only [residueCharge, Finset.sum_range_succ, Finset.sum_range_zero, qSequence_zero]
    ring
  rw [hh2, residueCharge_tsum 2 (by norm_num) f, h2] at he2
  rw [hh3, residueCharge_tsum 3 (by norm_num) f, h3, h4] at he3
  rw [hh5, residueCharge_tsum 5 (by norm_num) f, h5, h4] at he5
  refine ⟨?_, ?_, ?_⟩
  · change _ = ∑' i : ℕ, signedPair (linearRow (-200 / 223) (-176 / 669) (128 / 669)) f i
    rw [linearRow_pair_tsum]
    linarith
  · change _ = ∑' i : ℕ, signedPair (linearRow (347 / 209) (-368 / 209) (-8 / 627)) f i
    rw [linearRow_pair_tsum]
    linarith
  · change _ = ∑' i : ℕ, signedPair (linearRow (-9 / 10) (12 / 5) (-9 / 5)) f i
    rw [linearRow_pair_tsum]
    linarith

def radicalTailEnergy (f : QHilbert) : ℝ :=
  ∑' i : ℕ, gap (31 / 100) (i + 5) * rawSquare f (i + 5)

theorem radicalTail_summable (f : QHilbert) :
    Summable (fun i : ℕ => gap (31 / 100) (i + 5) * rawSquare f (i + 5)) := by
  have hs := ((summable_nat_add_iff 5).mpr (rawSquare_summable f)).mul_left (31 / 100 : ℝ)
  apply Summable.of_nonneg_of_le
    (fun i => mul_nonneg (gap_five_pos _ (by omega)).le
      (by unfold rawSquare; positivity)) _ hs
  intro i
  apply mul_le_mul_of_nonneg_right _ (by unfold rawSquare; positivity)
  unfold gap
  have : (0 : ℝ) ≤ 1 / ((i + 5 : ℕ) : ℝ) := by positivity
  linarith

theorem radicalTail_nonneg (f : QHilbert) : 0 ≤ radicalTailEnergy f := by
  apply tsum_nonneg
  intro i
  exact mul_nonneg (gap_five_pos _ (by omega)).le (by unfold rawSquare; positivity)

private theorem rawReciprocal_summable (f : QHilbert) :
    Summable (fun k : ℕ => rawSquare f k / (k : ℝ)) := by
  apply Summable.of_nonneg_of_le (fun k => by unfold rawSquare; positivity)
    _ (rawSquare_summable f)
  intro k
  by_cases hk : k = 0
  · simp [hk, rawSquare]
  · have hkr : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
    simpa using div_le_self (show 0 ≤ rawSquare f k by unfold rawSquare; positivity) hkr

/-- Complete signed gap identity with the site-four correction retained. -/
theorem radical_gap_exact (f : QHilbert)
    (h4 : qSequence f 4 = -qSequence f 1 + qSequence f 2 + qSequence f 3) :
    zetaTwo * ((31 / 100 : ℝ) * ‖f‖ ^ 2 - inner ℝ f (reciprocalD f)) =
      radicalTailEnergy f - headForm (qSequence f 1) (qSequence f 2) (qSequence f 3) +
      (1 / 100 : ℝ) * headNorm (qSequence f 1) (qSequence f 2) (qSequence f 3) := by
  have hs := ((rawSquare_summable f).mul_left (31 / 100 : ℝ)).sub (rawReciprocal_summable f)
  have he := hs.sum_add_tsum_nat_add 5
  have hhead : (∑ k ∈ Finset.range 5,
      ((31 / 100 : ℝ) * rawSquare f k - rawSquare f k / (k : ℝ))) =
      -headForm (qSequence f 1) (qSequence f 2) (qSequence f 3) +
      (1 / 100 : ℝ) * headNorm (qSequence f 1) (qSequence f 2) (qSequence f 3) := by
    norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, rawSquare, qSequence_zero]
    rw [h4]
    unfold headForm headNorm
    ring
  have htail : (∑' i : ℕ, ((31 / 100 : ℝ) * rawSquare f (i + 5) -
      rawSquare f (i + 5) / ((i + 5 : ℕ) : ℝ))) = radicalTailEnergy f := by
    apply tsum_congr
    intro i
    unfold gap
    ring
  rw [hhead, htail, ((rawSquare_summable f).mul_left (31 / 100 : ℝ)).tsum_sub
    (rawReciprocal_summable f), tsum_mul_left, rawSquare_tsum, rawReciprocal_tsum] at he
  linarith

def componentGram (d : ℝ) (w : ℕ → ℝ) (k : ℕ) : ℝ :=
  d * (w k) ^ 2 / ((k : ℝ) ^ 2 * gap (31 / 100) k)

theorem weightedRow_cauchy (d : ℝ) (hd : 0 ≤ d) (w : ℕ → ℝ)
    (f : QHilbert) (v : ℝ) (hsigned : Summable (signedPair w f))
    (hnormal : v = ∑' i : ℕ, signedPair w f i)
    (hbound : ∀ k : ℕ, 5 ≤ k → componentGram d w k ≤ traceTerm k) :
    d * v ^ 2 ≤ radicalTailEnergy f * (∑' i : ℕ, componentGram d w (i + 5)) := by
  have hgram : Summable (fun i : ℕ => componentGram d w (i + 5)) := by
    apply Summable.of_nonneg_of_le
      (fun i => div_nonneg (mul_nonneg hd (sq_nonneg _))
        (mul_nonneg (sq_nonneg _) (gap_five_pos _ (by omega)).le)) _ trace_summable
    intro i
    exact hbound _ (by omega)
  have hpair : Summable (fun i : ℕ => Real.sqrt d * w (i + 5) *
      qSequence f (i + 5) / ((i + 5 : ℕ) : ℝ) ^ 2) :=
    (hsigned.mul_left (Real.sqrt d)).congr (fun i => by unfold signedPair; ring)
  have hsum : (∑' i : ℕ, Real.sqrt d * w (i + 5) *
      qSequence f (i + 5) / ((i + 5 : ℕ) : ℝ) ^ 2) = Real.sqrt d * v := by
    rw [hnormal, ← tsum_mul_left]
    apply tsum_congr
    intro i
    unfold signedPair
    ring
  have hcs := weighted_tsum_cauchy
    (fun i : ℕ => Real.sqrt d * w (i + 5) * qSequence f (i + 5) /
      ((i + 5 : ℕ) : ℝ) ^ 2)
    (fun i : ℕ => gap (31 / 100) (i + 5) * rawSquare f (i + 5))
    (fun i : ℕ => componentGram d w (i + 5))
    hpair (radicalTail_summable f) hgram
    (fun i => mul_nonneg (gap_five_pos _ (by omega)).le (by unfold rawSquare; positivity))
    (fun i => div_nonneg (mul_nonneg hd (sq_nonneg _))
      (mul_nonneg (sq_nonneg _) (gap_five_pos _ (by omega)).le))
    (fun i => by
      have hk : (((i + 5 : ℕ) : ℝ)) ≠ 0 := by positivity
      have hg := ne_of_gt (gap_five_pos (i + 5) (by omega))
      apply le_of_eq
      unfold rawSquare componentGram
      field_simp [hk, hg]
      rw [Real.sq_sqrt hd]
      ring)
  rw [hsum, mul_pow, Real.sq_sqrt hd] at hcs
  exact hcs

theorem radical_headForm_le_tail (f : QHilbert)
    (h2 : inner ℝ (qResidue 2) f = 0) (h3 : inner ℝ (qResidue 3) f = 0)
    (h5 : inner ℝ (qResidue 5) f = 0)
    (h4 : qSequence f 4 = -qSequence f 1 + qSequence f 2 + qSequence f 3) :
    headForm (qSequence f 1) (qSequence f 2) (qSequence f 3) ≤
      (1259351 / 1264260 : ℝ) * radicalTailEnergy f := by
  have hn := radical_signed_normal_equations f h2 h3 h5 h4
  have hc1 (k : ℕ) (hk : 5 ≤ k) :
      componentGram (223 / 320) transformedOne k ≤ traceTerm k := by
    unfold componentGram traceTerm
    apply div_le_div_of_nonneg_right _
      (mul_nonneg (sq_nonneg _) (gap_five_pos k hk).le)
    rw [traceNumerator_transformed]
    nlinarith [sq_nonneg (transformedTwo k), sq_nonneg (transformedThree k)]
  have hc2 (k : ℕ) (hk : 5 ≤ k) :
      componentGram (209 / 4460) transformedTwo k ≤ traceTerm k := by
    unfold componentGram traceTerm
    apply div_le_div_of_nonneg_right _
      (mul_nonneg (sq_nonneg _) (gap_five_pos k hk).le)
    rw [traceNumerator_transformed]
    nlinarith [sq_nonneg (transformedOne k), sq_nonneg (transformedThree k)]
  have hc3 (k : ℕ) (hk : 5 ≤ k) :
      componentGram (2 / 5643) transformedThree k ≤ traceTerm k := by
    unfold componentGram traceTerm
    apply div_le_div_of_nonneg_right _
      (mul_nonneg (sq_nonneg _) (gap_five_pos k hk).le)
    rw [traceNumerator_transformed]
    nlinarith [sq_nonneg (transformedOne k), sq_nonneg (transformedTwo k)]
  have hs1 : Summable (signedPair transformedOne f) := linearRow_pair_summable _ _ _ f
  have hs2 : Summable (signedPair transformedTwo f) := linearRow_pair_summable _ _ _ f
  have hs3 : Summable (signedPair transformedThree f) := linearRow_pair_summable _ _ _ f
  have h1 := weightedRow_cauchy (223 / 320) (by norm_num) transformedOne f _ hs1 hn.1 hc1
  have h2' := weightedRow_cauchy (209 / 4460) (by norm_num) transformedTwo f _ hs2 hn.2.1 hc2
  have h3' := weightedRow_cauchy (2 / 5643) (by norm_num) transformedThree f _ hs3 hn.2.2 hc3
  have hgs1 : Summable (fun i : ℕ => componentGram (223 / 320) transformedOne (i + 5)) := by
    refine Summable.of_nonneg_of_le
      (fun i => show 0 ≤ componentGram (223 / 320) transformedOne (i + 5) from
        div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
          (mul_nonneg (sq_nonneg _) (gap_five_pos (i + 5) (by omega)).le))
      (fun i => hc1 (i + 5) (by omega)) trace_summable
  have hgs2 : Summable (fun i : ℕ => componentGram (209 / 4460) transformedTwo (i + 5)) := by
    refine Summable.of_nonneg_of_le
      (fun i => show 0 ≤ componentGram (209 / 4460) transformedTwo (i + 5) from
        div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
          (mul_nonneg (sq_nonneg _) (gap_five_pos (i + 5) (by omega)).le))
      (fun i => hc2 (i + 5) (by omega)) trace_summable
  have hgs3 : Summable (fun i : ℕ => componentGram (2 / 5643) transformedThree (i + 5)) := by
    refine Summable.of_nonneg_of_le
      (fun i => show 0 ≤ componentGram (2 / 5643) transformedThree (i + 5) from
        div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
          (mul_nonneg (sq_nonneg _) (gap_five_pos (i + 5) (by omega)).le))
      (fun i => hc3 (i + 5) (by omega)) trace_summable
  have hsum : (∑' i : ℕ, componentGram (223 / 320) transformedOne (i + 5)) +
      (∑' i : ℕ, componentGram (209 / 4460) transformedTwo (i + 5)) +
      (∑' i : ℕ, componentGram (2 / 5643) transformedThree (i + 5)) =
      ∑' i : ℕ, traceTerm (i + 5) := by
    rw [← hgs1.tsum_add hgs2, ← (hgs1.add hgs2).tsum_add hgs3]
    apply tsum_congr
    intro i
    unfold componentGram traceTerm
    rw [traceNumerator_transformed]
    ring
  have hsumBound := mul_le_mul_of_nonneg_left complete_trace_le (radicalTail_nonneg f)
  rw [← hsum] at hsumBound
  unfold headForm
  nlinarith

/-- This bound requires the four-site target identity only for its input. -/
theorem radical_firstMoment_le (f : QHilbert)
    (h2 : inner ℝ (qResidue 2) f = 0) (h3 : inner ℝ (qResidue 3) f = 0)
    (h5 : inner ℝ (qResidue 5) f = 0)
    (h4 : qSequence f 4 = -qSequence f 1 + qSequence f 2 + qSequence f 3) :
    inner ℝ f (reciprocalD f) ≤ (31 / 100 : ℝ) * ‖f‖ ^ 2 := by
  have he := radical_gap_exact f h4
  have hJ := radical_headForm_le_tail f h2 h3 h5 h4
  have ht := radicalTail_nonneg f
  have hh := headNorm_nonneg (qSequence f 1) (qSequence f 2) (qSequence f 3)
  have hz : 0 ≤ zetaTwo * ((31 / 100 : ℝ) * ‖f‖ ^ 2 -
      inner ℝ f (reciprocalD f)) := by nlinarith
  have hgap := (mul_nonneg_iff_of_pos_left zetaTwo_pos).mp hz
  linarith

/-- The complete norm split retains all four head sites and all tail sites. -/
theorem radical_norm_exact (f : QHilbert)
    (h4 : qSequence f 4 = -qSequence f 1 + qSequence f 2 + qSequence f 3) :
    zetaTwo * ‖f‖ ^ 2 =
      headNorm (qSequence f 1) (qSequence f 2) (qSequence f 3) +
      (∑' i : ℕ, rawSquare f (i + 5)) := by
  have he := (rawSquare_summable f).sum_add_tsum_nat_add 5
  have hh : (∑ k ∈ Finset.range 5, rawSquare f k) =
      headNorm (qSequence f 1) (qSequence f 2) (qSequence f 3) := by
    norm_num only [rawSquare, Finset.sum_range_succ, Finset.sum_range_zero, qSequence_zero]
    rw [h4]
    unfold headNorm
    ring
  rw [hh, rawSquare_tsum] at he
  exact he.symm

theorem radicalTail_controls_rawTail (f : QHilbert) :
    (11 / 100 : ℝ) * (∑' i : ℕ, rawSquare f (i + 5)) ≤ radicalTailEnergy f := by
  have hs := (summable_nat_add_iff 5).mpr (rawSquare_summable f)
  rw [← tsum_mul_left]
  apply Summable.tsum_le_tsum _ (hs.mul_left (11 / 100 : ℝ)) (radicalTail_summable f)
  intro i
  have hg := gap_lower (31 / 100) 5 (i + 5) (by norm_num) (by omega)
  norm_num [gap] at hg
  have hp := mul_le_mul_of_nonneg_right hg
    (show 0 ≤ rawSquare f (i + 5) by unfold rawSquare; positivity)
  simpa only [gap, Nat.cast_add, Nat.cast_ofNat, one_div] using hp

/-- Retaining both the strict tail margin and the head margin sharpens 31/100. -/
theorem radical_firstMoment_le_margin (f : QHilbert)
    (h2 : inner ℝ (qResidue 2) f = 0) (h3 : inner ℝ (qResidue 3) f = 0)
    (h5 : inner ℝ (qResidue 5) f = 0)
    (h4 : qSequence f 4 = -qSequence f 1 + qSequence f 2 + qSequence f 3) :
    inner ℝ f (reciprocalD f) ≤ (39138061 / 126426000 : ℝ) * ‖f‖ ^ 2 := by
  have he := radical_gap_exact f h4
  have hJ := radical_headForm_le_tail f h2 h3 h5 h4
  have ht := radicalTail_controls_rawTail f
  have hn := radical_norm_exact f h4
  have hh := headNorm_nonneg (qSequence f 1) (qSequence f 2) (qSequence f 3)
  have hz : 0 ≤ zetaTwo * ((39138061 / 126426000 : ℝ) * ‖f‖ ^ 2 -
      inner ℝ f (reciprocalD f)) := by nlinarith
  have hgap := (mul_nonneg_iff_of_pos_left zetaTwo_pos).mp hz
  linarith

theorem residual_four_identity (n : ℕ) :
    qSequence (residual n) 4 = -qSequence (residual n) 1 +
      qSequence (residual n) 2 + qSequence (residual n) 3 := by
  have h := ZetaTwoReciprocalObstruction.fourWitness_inner_residual n
  rw [ZetaTwoReciprocalObstruction.inner_fourWitness,
    ZetaTwoConductorFour.fullPair_eq_rawInner] at h
  have hh := congrArg (fun t : ℝ => t * zetaTwo) h
  rw [div_mul_cancel₀ _ (ne_of_gt zetaTwo_pos), zero_mul] at hh
  norm_num only [ZetaTwoConductorFour.rawInner, ZetaTwoConductorFour.witness,
    Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.val_zero, Fin.val_succ] at hh
  linarith

/-- Actual target-only improvement below the permanent universal floor. -/
theorem residual_firstMoment_le (n : ℕ) (hn : 4 ≤ n) :
    inner ℝ (residual n) (reciprocalD (residual n)) ≤
      (31 / 100 : ℝ) * error n := by
  have hg := stage_contains_two_three n (by omega)
  have hg5 := ZetaTwoConductorFiveBound.stage_contains_five n hn
  exact radical_firstMoment_le (residual n)
    (((stage n).mem_orthogonal _).mp (residual_mem_orthogonal n) _ hg.1)
    (((stage n).mem_orthogonal _).mp (residual_mem_orthogonal n) _ hg.2)
    (((stage n).mem_orthogonal _).mp (residual_mem_orthogonal n) _ hg5)
    (residual_four_identity n)

theorem residual_firstMoment_normalized_le (n : ℕ) (hn : 4 ≤ n) :
    inner ℝ (residual n) (reciprocalD (residual n)) / error n ≤ (31 / 100 : ℝ) := by
  exact (div_le_iff₀ (error_pos n)).mpr (residual_firstMoment_le n hn)

theorem residual_firstMoment_le_margin (n : ℕ) (hn : 4 ≤ n) :
    inner ℝ (residual n) (reciprocalD (residual n)) ≤
      (39138061 / 126426000 : ℝ) * error n := by
  have hg := stage_contains_two_three n (by omega)
  have hg5 := ZetaTwoConductorFiveBound.stage_contains_five n hn
  exact radical_firstMoment_le_margin (residual n)
    (((stage n).mem_orthogonal _).mp (residual_mem_orthogonal n) _ hg.1)
    (((stage n).mem_orthogonal _).mp (residual_mem_orthogonal n) _ hg.2)
    (((stage n).mem_orthogonal _).mp (residual_mem_orthogonal n) _ hg5)
    (residual_four_identity n)

theorem residual_firstMoment_normalized_le_margin (n : ℕ) (hn : 4 ≤ n) :
    inner ℝ (residual n) (reciprocalD (residual n)) / error n ≤
      (39138061 / 126426000 : ℝ) := by
  exact (div_le_iff₀ (error_pos n)).mpr (residual_firstMoment_le_margin n hn)

theorem target_cap_below_permanent_floor : (31 / 100 : ℝ) < 1337 / 3979 := by norm_num

end RiemannResearch.RH.ZetaTwoRadicalFourBound
