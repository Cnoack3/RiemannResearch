/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.RationalInterval
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ArithmeticCumulativeBasic
import RiemannResearch.RH.ParetoDilation
import RiemannResearch.Analysis.ParetoProgressionCertificates
import RiemannResearch.RH.ParetoPeriodicRegrouping
import RiemannResearch.RH.QResidueMoments
import RiemannResearch.RH.ZetaTwoParetoTransfer
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! Complete actual P Gram and first-moment rational interval entries. -/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QPeriodicParetoGram
open ZetaTwoHilbert ZetaTwoParetoTransfer ArithmeticCumulative
open RiemannResearch RatInterval
open RiemannResearch.Analysis.ParetoProgressionCertificates

/-- Exact rational physical value of a legal residue atom. -/
def rationalResidue (d n : ℕ) : ℚ := ((n % d : ℕ) : ℚ)/(d : ℚ)

theorem rationalResidue_cast (d n : ℕ) :
    ((rationalResidue d n : ℚ) : ℝ) = residueFraction d n := by
  norm_num [rationalResidue, residueFraction]

private theorem residue_bound (d k : ℕ) : |residueFraction d k| ≤ 1 := by
  by_cases hd : d = 0
  · simp [hd, residueFraction]
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
    unfold residueFraction
    rw [abs_of_nonneg (by positivity)]
    apply (div_le_iff₀ hdR).mpr
    simpa only [one_mul] using (show ((k % d : ℕ) : ℝ) ≤ (d : ℝ) by
      exact_mod_cast (Nat.mod_lt k hdpos).le)

/-- The P inner product of the actual Q residue vectors reencoded with the
same physical sequences is a finite sum of complete P progression masses. -/
theorem paretoGram_eq_weighted (d e : ℕ) (hd : 0 < d) (he : 0 < e) :
    inner ℝ (toPareto (qResidue d)) (toPareto (qResidue e)) =
      ∑ r : Fin (Nat.lcm d e),
        Pareto.progressionWeight (Nat.lcm d e) (r.val+1) *
          (residueFraction d (r.val+1)*residueFraction e (r.val+1)) := by
  rw [Pareto.hilbert_inner_weighted, toPareto_sequence, toPareto_sequence,
    qSequence_qResidue, qSequence_qResidue]
  exact Pareto.periodic_paretoInner_mixed (Nat.lcm d e) (Nat.lcm_pos hd he)
    (residueFraction d) (residueFraction e) (residue_bound d) (residue_bound e)
    (residueFraction_period_of_dvd d _ (Nat.dvd_lcm_left d e))
    (residueFraction_period_of_dvd e _ (Nat.dvd_lcm_right d e))

/-- Complete P first moment, including every physical site. -/
theorem paretoMean_eq_weighted (d : ℕ) (hd : 0 < d) :
    inner ℝ (toPareto qOne) (toPareto (qResidue d)) =
      ∑ r : Fin d, Pareto.progressionWeight d (r.val+1)*residueFraction d (r.val+1) := by
  rw [Pareto.hilbert_inner_weighted, toPareto_sequence, toPareto_sequence,
    qSequence_qOne, qSequence_qResidue]
  have he : Pareto.paretoInner qOneSequence (residueFraction d) =
      Pareto.paretoMean (residueFraction d) := by
    unfold Pareto.paretoInner Pareto.paretoMean
    apply tsum_congr
    intro k
    by_cases hk : k = 0 <;> simp [qOneSequence, hk, Pareto.positiveWeight]
  rw [he]
  exact Pareto.periodic_paretoMean d hd (residueFraction d) (residue_bound d)
    (residueFraction_period_of_dvd d d (dvd_refl d))

def paretoGramInterval (d e K : ℕ) : RatInterval :=
  RatInterval.sum Finset.univ (fun r : Fin (Nat.lcm d e) =>
    RatInterval.mul
      (paretoProgressionInterval ((r.val+1 : ℕ) : ℚ) ((Nat.lcm d e : ℕ) : ℚ) K)
      (RatInterval.point (rationalResidue d (r.val+1)*rationalResidue e (r.val+1))))

theorem paretoGramInterval_contains (d e K : ℕ) (hd : 0 < d) (he : 0 < e)
    (hK : 1 ≤ K) :
    (paretoGramInterval d e K).Contains
      (inner ℝ (toPareto (qResidue d)) (toPareto (qResidue e))) := by
  rw [paretoGram_eq_weighted d e hd he]
  unfold paretoGramInterval
  apply RatInterval.contains_sum
  intro r hr
  have hm := paretoProgressionInterval_contains ((r.val+1 : ℕ) : ℚ)
    ((Nat.lcm d e : ℕ) : ℚ) K (by positivity)
    (by exact_mod_cast Nat.lcm_pos hd he) hK
  have hm' : (paretoProgressionInterval ((r.val+1 : ℕ) : ℚ)
      ((Nat.lcm d e : ℕ) : ℚ) K).Contains
      (Pareto.progressionWeight (Nat.lcm d e) (r.val+1)) := by
    simpa only [Rat.cast_natCast, paretoProgression_eq_progressionWeight] using hm
  simpa only [Rat.cast_mul, rationalResidue_cast] using
    RatInterval.contains_mul hm' (RatInterval.contains_point
      (rationalResidue d (r.val+1)*rationalResidue e (r.val+1)))

def paretoMeanInterval (d K : ℕ) : RatInterval :=
  RatInterval.sum Finset.univ (fun r : Fin d =>
    RatInterval.mul
      (paretoProgressionInterval ((r.val+1 : ℕ) : ℚ) (d : ℚ) K)
      (RatInterval.point (rationalResidue d (r.val+1))))

theorem paretoMeanInterval_contains (d K : ℕ) (hd : 0 < d) (hK : 1 ≤ K) :
    (paretoMeanInterval d K).Contains
      (inner ℝ (toPareto qOne) (toPareto (qResidue d))) := by
  rw [paretoMean_eq_weighted d hd]
  unfold paretoMeanInterval
  apply RatInterval.contains_sum
  intro r hr
  have hm := paretoProgressionInterval_contains ((r.val+1 : ℕ) : ℚ)
    (d : ℚ) K (by positivity) (by exact_mod_cast hd) hK
  have hm' : (paretoProgressionInterval ((r.val+1 : ℕ) : ℚ) (d : ℚ) K).Contains
      (Pareto.progressionWeight d (r.val+1)) := by
    simpa only [Rat.cast_natCast, paretoProgression_eq_progressionWeight] using hm
  simpa only [rationalResidue_cast] using
    RatInterval.contains_mul hm' (RatInterval.contains_point (rationalResidue d (r.val+1)))

end RiemannResearch.RH.QPeriodicParetoGram
