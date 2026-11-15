/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.RationalInterval
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.QResidueMoments
import RiemannResearch.RH.ParetoPeriodicRegrouping
import RiemannResearch.Analysis.ReciprocalProgressionCertificates
import RiemannResearch.RH.QPeriodicParetoGram
import RiemannResearch.RH.QShiftedReciprocal
import Mathlib.Analysis.SumOverResidueClass
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Complete actual shifted-reciprocal Gram entries, before Q normalization. -/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QPeriodicReciprocalGram
open ZetaTwoHilbert ZetaTwoProbability ArithmeticCumulative QPeriodicParetoGram
open RiemannResearch RatInterval
open RiemannResearch.Analysis.ParetoProgressionCertificates

/-- Exact residue regrouping of the actual reciprocal Hilbert inner product.
Only periodicity is assumed: the actual Hilbert vectors supply summability. -/
theorem reciprocal_inner_eq_periodic (L : ℕ) (hL : 0 < L) (f g : QHilbert)
    (hpf : ∀ k, qSequence f (k+L) = qSequence f k)
    (hpg : ∀ k, qSequence g (k+L) = qSequence g k) :
    zetaTwo*inner ℝ (QShiftedReciprocal.B f) (QShiftedReciprocal.B g) =
      ∑ r : Fin L, reciprocalProgression ((r.val+1 : ℕ) : ℝ) (L : ℝ)*
        (qSequence f (r.val+1)*qSequence g (r.val+1)) := by
  letI : NeZero L := ⟨Nat.ne_of_gt hL⟩
  let F : ℕ → ℝ := fun k => zetaTwo*(positiveQWeight (k+1)*
    qSequence (QShiftedReciprocal.B f) (k+1)*
      qSequence (QShiftedReciprocal.B g) (k+1))
  have hsall := (qSequence_product_summable
    (QShiftedReciprocal.B f) (QShiftedReciprocal.B g)).mul_left zetaTwo
  have hs : Summable F :=
    hsall.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  calc
    zetaTwo*inner ℝ (QShiftedReciprocal.B f) (QShiftedReciprocal.B g) = ∑' k, F k := by
      rw [qInner_weighted, ← tsum_mul_left, hsall.tsum_eq_zero_add]
      simp only [qSequence_zero, mul_zero, zero_add]
      <;> rfl
    _ = ∑ r : Fin L, ∑' j : ℕ, F (r.val+L*j) := by
      cases L with
      | zero => omega
      | succ n => exact Nat.sumByResidueClasses hs (n+1)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r hr
      have he (j : ℕ) : F (r.val+L*j) =
          (1/(((r.val+1 : ℕ) : ℝ)+(L:ℝ)*(j:ℝ))^2 /
            ((((r.val+1 : ℕ) : ℝ)+(L:ℝ)*(j:ℝ))+1)^2)*
            (qSequence f (r.val+1)*qSequence g (r.val+1)) := by
        dsimp only [F]
        have hn : r.val+L*j+1 = r.val+1+L*j := by omega
        rw [hn, QShiftedReciprocal.qSequence_B, QShiftedReciprocal.qSequence_B,
          Pareto.periodic_add_mul L (qSequence f) hpf,
          Pareto.periodic_add_mul L (qSequence g) hpg]
        unfold positiveQWeight
        push_cast
        field_simp [ne_of_gt zetaTwo_pos]
        <;> ring
      simp_rw [he]
      rw [tsum_mul_right]
      unfold reciprocalProgression
      congr 1
      apply tsum_congr
      intro j
      exact div_div _ _ _

/-- The report's complete raw J entry is the actual reciprocal Gram entry. -/
theorem reciprocalGram_eq_weighted (d e : ℕ) (hd : 0 < d) (he : 0 < e) :
    zetaTwo*inner ℝ (QShiftedReciprocal.B (qResidue d))
      (QShiftedReciprocal.B (qResidue e)) =
      ∑ r : Fin (Nat.lcm d e),
        reciprocalProgression ((r.val+1 : ℕ) : ℝ) ((Nat.lcm d e : ℕ) : ℝ)*
          (residueFraction d (r.val+1)*residueFraction e (r.val+1)) := by
  have h := reciprocal_inner_eq_periodic (Nat.lcm d e) (Nat.lcm_pos hd he)
    (qResidue d) (qResidue e)
    (by simpa only [qSequence_qResidue] using
      residueFraction_period_of_dvd d _ (Nat.dvd_lcm_left d e))
    (by simpa only [qSequence_qResidue] using
      residueFraction_period_of_dvd e _ (Nat.dvd_lcm_right d e))
  simpa only [qSequence_qResidue] using h

def reciprocalGramInterval (d e K : ℕ) : RatInterval :=
  RatInterval.sum Finset.univ (fun r : Fin (Nat.lcm d e) =>
    RatInterval.mul
      (reciprocalProgressionInterval ((r.val+1 : ℕ) : ℚ) ((Nat.lcm d e : ℕ) : ℚ) K)
      (RatInterval.point (rationalResidue d (r.val+1)*rationalResidue e (r.val+1))))

theorem reciprocalGramInterval_contains (d e K : ℕ) (hd : 0 < d) (he : 0 < e)
    (hK : 1 ≤ K) :
    (reciprocalGramInterval d e K).Contains
      (zetaTwo*inner ℝ (QShiftedReciprocal.B (qResidue d))
        (QShiftedReciprocal.B (qResidue e))) := by
  rw [reciprocalGram_eq_weighted d e hd he]
  unfold reciprocalGramInterval
  apply RatInterval.contains_sum
  intro r hr
  have hm := reciprocalProgressionInterval_contains ((r.val+1 : ℕ) : ℚ)
    ((Nat.lcm d e : ℕ) : ℚ) K (by positivity)
    (by exact_mod_cast Nat.lcm_pos hd he) hK
  simpa only [Rat.cast_natCast, Rat.cast_mul, rationalResidue_cast] using
    RatInterval.contains_mul hm (RatInterval.contains_point
      (rationalResidue d (r.val+1)*rationalResidue e (r.val+1)))

end RiemannResearch.RH.QPeriodicReciprocalGram
