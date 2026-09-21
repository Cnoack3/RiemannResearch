import RiemannResearch.RH.ComplexTailCoercivity
import RiemannResearch.RH.MellinModeResiduePairing
import RiemannResearch.RH.MellinModeEnergyBounds
import RiemannResearch.Analysis.WeightedComplexPairing

set_option autoImplicit false

/-!
# Exact tail Cauchy inequality forced by a zeta zero

Source: user-provided Mellin certificate argument. The pairing is complex
linear, so its Cauchy estimate does not assume positivity of the coefficients.
All vectors below are actual vectors of the complexified Pareto Hilbert space.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity

open RiemannResearch.Analysis.Cesaro
open RiemannResearch.RH.Pareto.SpectralObstruction

private theorem tailAtom_physical_tail (i k : ℕ) :
    hilbertSequence (tailAtom i) (k + 2) =
      ArithmeticCumulative.residueFraction (i + 2) (k + 2) := by
  change hilbertSequenceLinear
    (residueAtom i - anchoredEvaluationCLM 1 (residueAtom i) • paretoPointHilbert 0)
    (k + 2) = _
  rw [map_sub, map_smul]
  change hilbertSequence (residueAtom i) (k + 2) -
    anchoredEvaluationCLM 1 (residueAtom i) *
      hilbertSequence (paretoPointHilbert 0) (k + 2) = _
  rw [residueAtom, normalizedResidueHilbert_sequence, hilbertSequence_paretoPoint]
  simp [paretoPointSequence, show k + 2 ≠ 1 by omega]

private theorem tailAtom_array_tail (i k : ℕ) :
    (tailAtom i (k + 1) : ℂ) =
      (Real.sqrt (paretoWeight (k + 1)) : ℂ) *
        normalizedResidueCoordinate (i + 2) (k + 1) := by
  have hdiv : tailAtom i (k + 1) / Real.sqrt (paretoWeight (k + 1)) =
      ArithmeticCumulative.residueFraction (i + 2) (k + 2) := by
    simpa only [show k + 2 = (k + 1) + 1 by omega, hilbertSequence_succ] using
      tailAtom_physical_tail i k
  have hreal : tailAtom i (k + 1) = Real.sqrt (paretoWeight (k + 1)) *
      ArithmeticCumulative.residueFraction (i + 2) (k + 2) := by
    have h := (div_eq_iff
      (ne_of_gt (Real.sqrt_pos.mpr (paretoWeight_pos (k + 1))))).mp hdiv
    simpa only [mul_comm] using h
  rw [hreal, Complex.ofReal_mul, normalizedResidueCoordinate_eq_residueFraction]

/-- The same finite complex tail combination, in its actual weighted `lp` coordinates. -/
theorem complexTailCombination_tail_coordinate (n : ℕ) (c : Fin n → ℂ) (k : ℕ) :
    complexTailCombination n c (k + 1) =
      (Real.sqrt (paretoWeight (k + 1)) : ℂ) *
        ∑ i : Fin n, c i * normalizedResidueCoordinate (i.val + 2) (k + 1) := by
  simp only [complexTailCombination, Fintype.linearCombination_apply,
    lp.coeFn_sum, lp.coeFn_smul, Finset.sum_apply, Pi.smul_apply,
    realHilbertComplexify_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [tailAtom_array_tail]
  ring

/-- The raw Mellin mode with the square-root Pareto weight absorbed. The
index starts at physical site two, so the entire removed head is excluded. -/
def mellinTailWeightedCoordinate (s : ℂ) (k : ℕ) : ℂ :=
  (Real.sqrt (paretoWeight (k + 1)) : ℂ) * mellinMode s (k + 1)

theorem mellinTailWeightedCoordinate_norm_sq (s : ℂ) (k : ℕ) :
    ‖mellinTailWeightedCoordinate s k‖ ^ 2 =
      paretoWeight (k + 1) * ‖mellinMode s (k + 1)‖ ^ 2 := by
  rw [mellinTailWeightedCoordinate, norm_mul, mul_pow, Complex.norm_real,
    Real.norm_eq_abs, sq_abs, Real.sq_sqrt (paretoWeight_pos (k + 1)).le]

private theorem mellin_zero_residue_tail_hasSum
    (s : ℂ) (hs : 0 < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s = 0)
    (d : ℕ) (hd : 2 ≤ d) :
    HasSum (fun k => (paretoWeight (k + 1) : ℂ) * mellinMode s (k + 1) *
      normalizedResidueCoordinate d (k + 1))
      (-(1 - (2 : ℂ) ^ (-s)) * (1 / (d : ℂ))) := by
  have hfull : HasSum (fun k => (paretoWeight k : ℂ) * mellinMode s k *
      normalizedResidueCoordinate d k) 0 := by
    simpa only [hz, mul_zero] using mellinMode_residue_hasSum s hs hs1 d hd
  have ht := (hasSum_nat_add_iff' 1).mpr hfull
  have hhead : (paretoWeight 0 : ℂ) * mellinMode s 0 *
      normalizedResidueCoordinate d 0 =
      (1 - (2 : ℂ) ^ (-s)) * (1 / (d : ℂ)) := by
    rw [weighted_mellinMode_eq]
    norm_num [mellinFirst, normalizedResidueCoordinate,
      Nat.mod_eq_of_lt (show 1 < d by omega)]
  simpa only [Finset.sum_range_one, hhead, zero_sub, neg_mul] using ht

/-- Every finite complex legal tail has the same exact zero-mode pairing. -/
theorem mellin_zero_complexTail_hasSum
    (s : ℂ) (hs : 0 < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s = 0)
    (n : ℕ) (c : Fin n → ℂ) :
    HasSum (fun k => mellinTailWeightedCoordinate s k *
      complexTailCombination n c (k + 1))
      (-(1 - (2 : ℂ) ^ (-s)) * complexReciprocalSource n c) := by
  have hsum : HasSum
      (fun k => ∑ i : Fin n, c i *
        ((paretoWeight (k + 1) : ℂ) * mellinMode s (k + 1) *
          normalizedResidueCoordinate (i.val + 2) (k + 1)))
      (∑ i : Fin n, c i * (-(1 - (2 : ℂ) ^ (-s)) *
        (1 / ((i.val + 2 : ℕ) : ℂ)))) := by
    apply hasSum_sum
    intro i hi
    exact (mellin_zero_residue_tail_hasSum s hs hs1 hz (i.val + 2) (by omega)).mul_left (c i)
  have hfun : (fun k => mellinTailWeightedCoordinate s k *
      complexTailCombination n c (k + 1)) =
      (fun k => ∑ i : Fin n, c i *
        ((paretoWeight (k + 1) : ℂ) * mellinMode s (k + 1) *
          normalizedResidueCoordinate (i.val + 2) (k + 1))) := by
    funext k
    simp only [complexTailCombination_tail_coordinate, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hsq : (Real.sqrt (paretoWeight (k + 1)) : ℂ) *
        (Real.sqrt (paretoWeight (k + 1)) : ℂ) = (paretoWeight (k + 1) : ℂ) := by
      exact_mod_cast Real.mul_self_sqrt (paretoWeight_pos (k + 1)).le
    dsimp [mellinTailWeightedCoordinate]
    calc
      _ = ((Real.sqrt (paretoWeight (k + 1)) : ℂ) *
          (Real.sqrt (paretoWeight (k + 1)) : ℂ)) *
          (c i * mellinMode s (k + 1) *
            normalizedResidueCoordinate (i.val + 2) (k + 1)) := by ring
      _ = _ := by rw [hsq]; ring
  have hval : (∑ i : Fin n, c i * (-(1 - (2 : ℂ) ^ (-s)) *
      (1 / ((i.val + 2 : ℕ) : ℂ)))) =
      -(1 - (2 : ℂ) ^ (-s)) * complexReciprocalSource n c := by
    rw [complexReciprocalSource, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [reciprocalSource, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_natCast]
    ring
  rw [hfun, ← hval]
  exact hsum

/-- The exact full signed Cauchy obstruction from one right-half-strip zero.
The entire tail energy appears, with no absolute-value replacement of the
arithmetic source and no finite-support estimate substituted for the limit. -/
theorem mellin_zero_tail_cauchy
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s = 0)
    (n : ℕ) (c : Fin n → ℂ) :
    ‖1 - (2 : ℂ) ^ (-s)‖ ^ 2 * ‖complexReciprocalSource n c‖ ^ 2 ≤
      (∑' k : ℕ, paretoWeight (k + 1) * ‖mellinMode s (k + 1)‖ ^ 2) *
        ‖complexTailCombination n c‖ ^ 2 := by
  let f := complexTailCombination n c
  have hb : Summable (fun k => ‖mellinTailWeightedCoordinate s k‖ ^ 2) := by
    simp_rw [mellinTailWeightedCoordinate_norm_sq]
    exact (summable_nat_add_iff 1).mpr (mellinMode_energy_summable s hs)
  have hf : Summable (fun k => ‖f k‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      Memℓp.summable (show 0 < (2 : ENNReal).toReal by norm_num) f.property
  have hft : Summable (fun k => ‖f (k + 1)‖ ^ 2) := (summable_nat_add_iff 1).mpr hf
  have htail : (∑' k, ‖f (k + 1)‖ ^ 2) ≤ ‖f‖ ^ 2 := by
    rw [complexHilbert_norm_sq, hf.tsum_eq_zero_add]
    exact le_add_of_nonneg_left (sq_nonneg _)
  have hcs := RiemannResearch.Analysis.WeightedPairing.pairing_norm_sq_le
    (fun _ => (1 : ℝ)) (fun _ => by norm_num)
    (mellinTailWeightedCoordinate s) (fun k => f (k + 1))
    (by simpa only [div_one] using hb) (by simpa only [one_mul] using hft)
  simp only [div_one, one_mul] at hcs
  have hpair := mellin_zero_complexTail_hasSum s (by linarith) hs1 hz n c
  change ‖∑' k, mellinTailWeightedCoordinate s k *
    complexTailCombination n c (k + 1)‖ ^ 2 ≤ _ at hcs
  rw [hpair.tsum_eq, norm_mul, norm_neg, mul_pow] at hcs
  simp_rw [mellinTailWeightedCoordinate_norm_sq] at hcs
  exact hcs.trans (mul_le_mul_of_nonneg_left htail
    (tsum_nonneg (fun k => mul_nonneg (paretoWeight_pos (k + 1)).le (sq_nonneg _))))

end RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
