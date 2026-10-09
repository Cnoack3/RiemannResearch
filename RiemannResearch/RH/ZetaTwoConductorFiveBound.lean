import RiemannResearch.RH.ReciprocalConductorFiveCertificate
import RiemannResearch.RH.ZetaTwoReciprocalBound

/-!
# A stronger actual reciprocal bound after conductor five enters the stage

Source: independently developed exact signed recovery rows in
`ReciprocalConductorFiveCertificate`. Orthogonality at conductors three and
five supplies a complete zero tail charge, since their residues agree at
sites one and two. Adding this charge to both recovery rows improves the
first-moment cap to 3/8 and the actual screened second moment to 9/64.
Retaining the strict tail remainder further improves these caps to
10745/28906 and its square.
No moment cap or asymptotic arithmetic saving is assumed.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.ZetaTwoConductorFiveBound
open ZetaTwoHilbert ZetaTwoOptimizerStage ZetaTwoProbability
open ZetaTwoReciprocalBound ReciprocalHeadCertificate ReciprocalInfiniteCertificate
open ReciprocalConductorFiveCertificate (weightOneFive weightTwoFive fiveCharge fiveGramTerm)

theorem five_signed_charge_summable (f : QHilbert) :
    Summable (fun i : ℕ => weightOneFive (i + 3) * qSequence f (i + 3) /
      ((i + 3 : ℕ) : ℝ) ^ 2) ∧
    Summable (fun i : ℕ => weightTwoFive (i + 3) * qSequence f (i + 3) /
      ((i + 3 : ℕ) : ℝ) ^ 2) := by
  have h3 := (summable_nat_add_iff 3).mpr (residueCharge_summable 3 (by norm_num) f)
  have h5 := (summable_nat_add_iff 3).mpr (residueCharge_summable 5 (by norm_num) f)
  have hs := signed_charge_summable f
  constructor
  · exact (hs.1.sub ((h3.sub h5).div_const 5)).congr
      (fun i => by unfold weightOne weightOneFive residueCharge; ring)
  · exact (hs.2.add (h3.sub h5)).congr
      (fun i => by unfold weightTwo weightTwoFive residueCharge; ring)

/-- Exact additional signed zero charge, including every site from three on. -/
theorem three_five_tail_charge_zero (f : QHilbert)
    (h3 : inner ℝ (qResidue 3) f = 0) (h5 : inner ℝ (qResidue 5) f = 0) :
    (∑' i : ℕ, (residueCharge 3 f (i + 3) - residueCharge 5 f (i + 3))) = 0 := by
  have hs3 := residueCharge_summable 3 (by norm_num) f
  have hs5 := residueCharge_summable 5 (by norm_num) f
  have he3 := hs3.sum_add_tsum_nat_add 3
  have he5 := hs5.sum_add_tsum_nat_add 3
  have hh3 : (∑ k ∈ Finset.range 3, residueCharge 3 f k) =
      qSequence f 1 + qSequence f 2 / 2 := by
    norm_num [residueCharge, Finset.sum_range_succ]
    ring
  have hh5 : (∑ k ∈ Finset.range 3, residueCharge 5 f k) =
      qSequence f 1 + qSequence f 2 / 2 := by
    norm_num [residueCharge, Finset.sum_range_succ]
    ring
  rw [hh3, residueCharge_tsum 3 (by norm_num) f, h3] at he3
  rw [hh5, residueCharge_tsum 5 (by norm_num) f, h5] at he5
  rw [((summable_nat_add_iff 3).mpr hs3).tsum_sub ((summable_nat_add_iff 3).mpr hs5)]
  linarith

theorem five_signed_normal_equations (f : QHilbert)
    (h2 : inner ℝ (qResidue 2) f = 0) (h3 : inner ℝ (qResidue 3) f = 0)
    (h5 : inner ℝ (qResidue 5) f = 0) :
    qSequence f 1 = ∑' i : ℕ, weightOneFive (i + 3) * qSequence f (i + 3) /
      ((i + 3 : ℕ) : ℝ) ^ 2 ∧
    qSequence f 2 = ∑' i : ℕ, weightTwoFive (i + 3) * qSequence f (i + 3) /
      ((i + 3 : ℕ) : ℝ) ^ 2 := by
  have hs3 := (summable_nat_add_iff 3).mpr (residueCharge_summable 3 (by norm_num) f)
  have hs5 := (summable_nat_add_iff 3).mpr (residueCharge_summable 5 (by norm_num) f)
  have hs := signed_charge_summable f
  have hn := signed_normal_equations f h2 h3
  have hz := three_five_tail_charge_zero f h3 h5
  constructor
  · calc
      _ = (∑' i : ℕ, weightOne (i + 3) * qSequence f (i + 3) /
          ((i + 3 : ℕ) : ℝ) ^ 2) -
          (∑' i : ℕ, (residueCharge 3 f (i + 3) - residueCharge 5 f (i + 3))) / 5 := by
        rw [hz, hn.1]
        ring
      _ = _ := by
        rw [← tsum_div_const, ← hs.1.tsum_sub ((hs3.sub hs5).div_const 5)]
        apply tsum_congr
        intro i
        unfold weightOne weightOneFive residueCharge
        ring
  · calc
      _ = (∑' i : ℕ, weightTwo (i + 3) * qSequence f (i + 3) /
          ((i + 3 : ℕ) : ℝ) ^ 2) +
          (∑' i : ℕ, (residueCharge 3 f (i + 3) - residueCharge 5 f (i + 3))) := by
        rw [hz, hn.2]
        ring
      _ = _ := by
        rw [← hs.2.tsum_add (hs3.sub hs5)]
        apply tsum_congr
        intro i
        unfold weightTwo weightTwoFive residueCharge
        ring

theorem conductorFive_headEnergy_le_tail (f : QHilbert)
    (h2 : inner ℝ (qResidue 2) f = 0) (h3 : inner ℝ (qResidue 3) f = 0)
    (h5 : inner ℝ (qResidue 5) f = 0) :
    headEnergy (3 / 8) f ≤ (3329 / 3708 : ℝ) * tailEnergy (3 / 8) f := by
  have hcoeff (x y : ℝ) (k : ℕ) :
      recoveryGramTerm (3 / 8) weightOneFive weightTwoFive x y k = fiveGramTerm x y k := by
    norm_num [recoveryGramTerm, recoveryCharge, fiveGramTerm, fiveCharge]
  exact headEnergy_le_tail (3 / 8) (3329 / 3708) weightOneFive weightTwoFive
    (by norm_num) (by norm_num) (by norm_num)
    (fun x y => by simp_rw [hcoeff]; exact ReciprocalConductorFiveCertificate.fiveGram_summable x y)
    (fun x y => by simp_rw [hcoeff]; exact ReciprocalConductorFiveCertificate.five_complete_gram_le x y)
    f (five_signed_charge_summable f) (five_signed_normal_equations f h2 h3 h5)

theorem conductorFive_firstMoment_remainder (f : QHilbert)
    (h2 : inner ℝ (qResidue 2) f = 0) (h3 : inner ℝ (qResidue 3) f = 0)
    (h5 : inner ℝ (qResidue 5) f = 0) :
    (379 / 3708 : ℝ) * tailEnergy (3 / 8) f ≤
      zetaTwo * ((3 / 8 : ℝ) * ‖f‖ ^ 2 - inner ℝ f (reciprocalD f)) := by
  rw [reciprocal_gap_exact]
  have hJ := conductorFive_headEnergy_le_tail f h2 h3 h5
  linarith

theorem conductorFive_firstMoment_le (f : QHilbert)
    (h2 : inner ℝ (qResidue 2) f = 0) (h3 : inner ℝ (qResidue 3) f = 0)
    (h5 : inner ℝ (qResidue 5) f = 0) :
    inner ℝ f (reciprocalD f) ≤ (3 / 8 : ℝ) * ‖f‖ ^ 2 := by
  have hJ := conductorFive_headEnergy_le_tail f h2 h3 h5
  have ht := tailEnergy_nonneg (3 / 8) (by norm_num) f
  have he := reciprocal_gap_exact (3 / 8) f
  nlinarith [zetaTwo_pos]

/-- The full norm is controlled by the retained positive tail; its two head
coordinates are accounted for by the same signed recovery certificate. -/
theorem conductorFive_tail_controls_norm (f : QHilbert)
    (h2 : inner ℝ (qResidue 2) f = 0) (h3 : inner ℝ (qResidue 3) f = 0)
    (h5 : inner ℝ (qResidue 5) f = 0) :
    zetaTwo * ‖f‖ ^ 2 ≤ (28906 / 927 : ℝ) * tailEnergy (3 / 8) f := by
  have hraw := (rawSquare_summable f).sum_add_tsum_nat_add 3
  have hh : (∑ k ∈ Finset.range 3, rawSquare f k) =
      (qSequence f 1) ^ 2 + (qSequence f 2) ^ 2 / 4 := by
    norm_num [rawSquare, Finset.sum_range_succ]
  rw [hh, rawSquare_tsum] at hraw
  have hsTail := (summable_nat_add_iff 3).mpr (rawSquare_summable f)
  have htail : (∑' i : ℕ, rawSquare f (i + 3)) / 24 ≤ tailEnergy (3 / 8) f := by
    rw [← tsum_div_const]
    apply Summable.tsum_le_tsum _ (hsTail.div_const 24)
      (tailEnergy_summable (3 / 8) (by norm_num) f)
    intro i
    have hm := gap_lower (3 / 8) 3 (i + 3) (by norm_num) (by omega)
    norm_num [gap] at hm
    have he : (1 / 24 : ℝ) ≤ gap (3 / 8) (i + 3) := by
      simpa [gap] using hm
    have hn : 0 ≤ rawSquare f (i + 3) := by unfold rawSquare; positivity
    have hp := mul_le_mul_of_nonneg_right he hn
    linarith
  have hhead : ((qSequence f 1) ^ 2 + (qSequence f 2) ^ 2 / 4) / 8 ≤
      headEnergy (3 / 8) f := by
    unfold headEnergy
    nlinarith [sq_nonneg (qSequence f 1)]
  have hJ := conductorFive_headEnergy_le_tail f h2 h3 h5
  nlinarith

/-- The positive remainder improves the threshold itself, without changing
the finite head or discarding any arithmetic tail or correction square. -/
theorem conductorFive_firstMoment_le_margin (f : QHilbert)
    (h2 : inner ℝ (qResidue 2) f = 0) (h3 : inner ℝ (qResidue 3) f = 0)
    (h5 : inner ℝ (qResidue 5) f = 0) :
    inner ℝ f (reciprocalD f) ≤ (10745 / 28906 : ℝ) * ‖f‖ ^ 2 := by
  have hnorm := conductorFive_tail_controls_norm f h2 h3 h5
  have hrem := conductorFive_firstMoment_remainder f h2 h3 h5
  have hp : 0 ≤ zetaTwo * ((10745 / 28906 : ℝ) * ‖f‖ ^ 2 -
      inner ℝ f (reciprocalD f)) := by nlinarith
  have hh := (mul_nonneg_iff_of_pos_left zetaTwo_pos).mp hp
  linarith

theorem stage_contains_five (n : ℕ) (hn : 4 ≤ n) : qResidue 5 ∈ stage n := by
  unfold stage RiemannResearch.Analysis.ExhaustiveWalk.walkSpan
  apply Submodule.subset_span
  refine ⟨⟨3, by omega⟩, ?_⟩
  simp [squarefreeAtom, Nat.prime_five.squarefree]

/-- A genuinely conductor-dependent improvement for the same actual optimizer. -/
theorem screenedResidual_sq_le (n : ℕ) (hn : 4 ≤ n) :
    ‖screenedResidual n‖ ^ 2 ≤ (9 / 64 : ℝ) * error n := by
  have hg := stage_contains_two_three n (by omega)
  have hg5 := stage_contains_five n hn
  have h := screened_bound_of_firstMoment (3 / 8) (by norm_num) (stage n)
    (fun f hf => conductorFive_firstMoment_le f
      (((stage n).mem_orthogonal _).mp hf _ hg.1)
      (((stage n).mem_orthogonal _).mp hf _ hg.2)
      (((stage n).mem_orthogonal _).mp hf _ hg5)) (residual n) (residual_mem_orthogonal n)
  norm_num only [show (3 / 8 : ℝ) ^ 2 = 9 / 64 by norm_num] at h
  exact h

theorem secondMoment_bounds (n : ℕ) (hn : 4 ≤ n) :
    0 ≤ secondMoment n ∧ secondMoment n ≤ (9 / 64 : ℝ) := by
  constructor
  · exact div_nonneg (sq_nonneg _) (error_pos n).le
  · unfold secondMoment
    exact (div_le_iff₀ (error_pos n)).mpr (screenedResidual_sq_le n hn)

theorem screenedResidual_sq_le_margin (n : ℕ) (hn : 4 ≤ n) :
    ‖screenedResidual n‖ ^ 2 ≤ (10745 / 28906 : ℝ) ^ 2 * error n := by
  have hg := stage_contains_two_three n (by omega)
  have hg5 := stage_contains_five n hn
  exact screened_bound_of_firstMoment (10745 / 28906) (by norm_num) (stage n)
    (fun f hf => conductorFive_firstMoment_le_margin f
      (((stage n).mem_orthogonal _).mp hf _ hg.1)
      (((stage n).mem_orthogonal _).mp hf _ hg.2)
      (((stage n).mem_orthogonal _).mp hf _ hg5)) (residual n) (residual_mem_orthogonal n)

theorem secondMoment_le_margin (n : ℕ) (hn : 4 ≤ n) :
    secondMoment n ≤ (10745 / 28906 : ℝ) ^ 2 := by
  unfold secondMoment
  exact (div_le_iff₀ (error_pos n)).mpr (screenedResidual_sq_le_margin n hn)

theorem margin_cap_lt_three_eighths_sq : (10745 / 28906 : ℝ) ^ 2 < 9 / 64 := by norm_num

theorem conductorFive_cap_lt_two_constraint_cap : (9 / 64 : ℝ) < 11449 / 62500 := by norm_num

/-- Both correction squares and the entire quartic floor remain in this bound. -/
theorem signedCorrection_le (n : ℕ) (hn : 4 ≤ n) :
    signedCorrection n ≤ (10745 / 28906 : ℝ) ^ 2 * error n - quarticFloor n := by
  have he := screenedResidual_energy_exact n
  have hb := screenedResidual_sq_le_margin n hn
  linarith

theorem positiveCorrection_normalized_bounds (n : ℕ) (hn : 4 ≤ n) :
    0 ≤ max (signedCorrection n) 0 / error n ∧
      max (signedCorrection n) 0 / error n ≤ (10745 / 28906 : ℝ) ^ 2 := by
  constructor
  · exact div_nonneg (le_max_right _ _) (error_pos n).le
  · apply (div_le_iff₀ (error_pos n)).mpr
    apply max_le
    · have hb := signedCorrection_le n hn
      have hfloor : 0 ≤ quarticFloor n := sq_nonneg _
      linarith
    · exact mul_nonneg (by norm_num) (error_pos n).le

end RiemannResearch.RH.ZetaTwoConductorFiveBound
