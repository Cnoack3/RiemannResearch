import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoPolygammaResidues
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact residue moments in the actual inverse-square Hilbert space

Source: user-provided Q-residue Gram computation, 13 October 2026.
The trigamma progression identity is the existing checked theorem in
`ZetaTwoPolygammaResidues` (DLMF 5.15.1). These results specialize that
identity to the actual `qResidue` vectors and keep the entire infinite tail.
The representative `L` is the zero residue class, whose residue factors
vanish; there is no finite truncation of the physical positive integers.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.ZetaTwoHilbert
open RiemannResearch.RH.ZetaTwoProbability
open RiemannResearch.RH.ArithmeticCumulative
open RiemannResearch.RH.CRTBlock

/-- Any actual Hilbert inner product is the literal inverse-square mean. -/
theorem qInner_eq_inversePowerMean (f g : QHilbert) :
    inner ℝ f g = inversePowerMean 0 (fun k => qSequence f k * qSequence g k) := by
  rw [qInner_weighted, (qSequence_product_summable f g).tsum_eq_zero_add]
  simp only [qSequence_zero, mul_zero, zero_add]
  unfold inversePowerMean
  apply tsum_congr
  intro k
  unfold positiveQWeight
  ring

/-- Actual first moment of a residue atom, before periodic regrouping. -/
theorem qResidue_mean_eq_inversePowerMean (d : ℕ) :
    inner ℝ qOne (qResidue d) = inversePowerMean 0 (residueFraction d) := by
  rw [qInner_eq_inversePowerMean, qSequence_qOne, qSequence_qResidue]
  unfold inversePowerMean
  apply tsum_congr
  intro k
  simp [qOneSequence]

/-- Actual mixed second moment, before periodic regrouping. -/
theorem qResidue_gram_eq_inversePowerMean (d e : ℕ) :
    inner ℝ (qResidue d) (qResidue e) =
      inversePowerMean 0 (fun k => residueFraction d k * residueFraction e k) := by
  rw [qInner_eq_inversePowerMean, qSequence_qResidue, qSequence_qResidue]

private theorem residue_abs_bound (d k : ℕ) : |residueFraction d k| ≤ 1 := by
  by_cases hd : d = 0
  · simp [hd, residueFraction]
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
    unfold residueFraction
    rw [abs_of_nonneg (by positivity)]
    apply (div_le_iff₀ hdR).mpr
    simpa only [one_mul] using (show ((k % d : ℕ) : ℝ) ≤ (d : ℝ) by
      exact_mod_cast (Nat.mod_lt k hdpos).le)

/-- Every multiple of a conductor is an exact period of its residue atom. -/
theorem residueFraction_period_of_dvd (d L : ℕ) (hdL : d ∣ L) (k : ℕ) :
    residueFraction d (k + L) = residueFraction d k := by
  rcases hdL with ⟨m, rfl⟩
  simp [residueFraction, Nat.add_mod, Nat.mul_mod]

/-- Exact finite trigamma representation of any bounded periodic Q-mean. -/
theorem inversePowerMean_zero_eq_trigamma (L : ℕ) (hL : 0 < L)
    (f : ℕ → ℝ) {C : ℝ} (hf : ∀ k, |f k| ≤ C)
    (hp : ∀ k, f (k + L) = f k) :
    inversePowerMean 0 f =
      ∑ r : Fin L, trigamma (((r.val + 1 : ℕ) : ℝ) / L) /
        (zetaTwo * (L : ℝ)^2) * f (r.val + 1) := by
  rw [periodic_inversePowerMean 0 L hL f hf hp]
  apply Finset.sum_congr rfl
  intro r _
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  rw [residueSquareWeight_eq_trigamma hLr (by positivity)]
  simp only [Nat.cast_add, Nat.cast_one]

/-- First moment of the actual residue atom as a finite trigamma sum. -/
theorem qResidue_mean_eq_trigamma (d : ℕ) (hd : 0 < d) :
    inner ℝ qOne (qResidue d) =
      ∑ r : Fin d, trigamma (((r.val + 1 : ℕ) : ℝ) / d) /
        (zetaTwo * (d : ℝ)^2) * residueFraction d (r.val + 1) := by
  rw [qResidue_mean_eq_inversePowerMean]
  exact inversePowerMean_zero_eq_trigamma d hd (residueFraction d)
    (residue_abs_bound d) (residueFraction_period_of_dvd d d (dvd_refl d))

/-- Every Gram entry is a finite sum over the complete lcm period. -/
theorem qResidue_gram_eq_trigamma (d e : ℕ) (hd : 0 < d) (he : 0 < e) :
    inner ℝ (qResidue d) (qResidue e) =
      ∑ r : Fin (Nat.lcm d e),
        trigamma (((r.val + 1 : ℕ) : ℝ) / Nat.lcm d e) /
          (zetaTwo * (Nat.lcm d e : ℝ)^2) *
        (residueFraction d (r.val + 1) * residueFraction e (r.val + 1)) := by
  rw [qResidue_gram_eq_inversePowerMean]
  apply inversePowerMean_zero_eq_trigamma (Nat.lcm d e) (Nat.lcm_pos hd he)
  · exact RiemannResearch.RH.Pareto.bounded_product
      (residue_abs_bound d) (residue_abs_bound e)
  · intro k
    rw [residueFraction_period_of_dvd d _ (Nat.dvd_lcm_left d e),
      residueFraction_period_of_dvd e _ (Nat.dvd_lcm_right d e)]

/-- Twisted residue first moment, useful for conditioning on prime divisibility. -/
def qTwistedResidueMean (d k : ℕ) : ℝ :=
  inversePowerMean 0 (fun n => residueFraction d (k * n))

/-- The untwisted first moment is the actual target pairing. -/
theorem qTwistedResidueMean_one (d : ℕ) :
    qTwistedResidueMean d 1 = inner ℝ qOne (qResidue d) := by
  rw [qResidue_mean_eq_inversePowerMean]
  simp [qTwistedResidueMean]

/-- Only the dilation's residue class matters; prime congruence classes may
therefore be grouped before a divisibility-coordinate calculation. -/
theorem qTwistedResidueMean_eq_of_mod_eq (d k l : ℕ) (hkl : k % d = l % d) :
    qTwistedResidueMean d k = qTwistedResidueMean d l := by
  unfold qTwistedResidueMean inversePowerMean
  apply tsum_congr
  intro n
  have hprod : (k * (n + 1)) % d = (l * (n + 1)) % d := by
    rw [Nat.mul_mod k (n + 1) d, Nat.mul_mod l (n + 1) d, hkl]
  simp only [residueFraction, hprod]

/-- A twisted first moment is still a finite sum with period `d`. -/
theorem qTwistedResidueMean_eq_trigamma (d k : ℕ) (hd : 0 < d) :
    qTwistedResidueMean d k =
      ∑ r : Fin d, trigamma (((r.val + 1 : ℕ) : ℝ) / d) /
        (zetaTwo * (d : ℝ)^2) * residueFraction d (k * (r.val + 1)) := by
  apply inversePowerMean_zero_eq_trigamma d hd
  · intro n
    exact residue_abs_bound d (k * n)
  · intro n
    simp [residueFraction, Nat.mul_add, Nat.add_mod, Nat.mul_mod]

/-- If the conductor divides the dilation, the twisted atom vanishes exactly. -/
theorem qTwistedResidueMean_eq_zero_of_dvd (d k : ℕ) (hdk : d ∣ k) :
    qTwistedResidueMean d k = 0 := by
  have hz (n : ℕ) : residueFraction d (k * n) = 0 := by
    have hmod : (k * n) % d = 0 :=
      Nat.mod_eq_zero_of_dvd (hdk.trans (dvd_mul_right k n))
    simp [residueFraction, hmod]
  simp [qTwistedResidueMean, inversePowerMean, hz]

/-- The first divisibility difference at a prime conductor is minus the mean.
The same identity holds for every natural conductor. -/
theorem qTwistedResidueMean_self_difference (d : ℕ) :
    qTwistedResidueMean d d - qTwistedResidueMean d 1 =
      -inner ℝ qOne (qResidue d) := by
  rw [qTwistedResidueMean_eq_zero_of_dvd d d (dvd_refl d),
    qTwistedResidueMean_one]
  ring

/-- The next prime-power divisibility difference vanishes exactly. -/
theorem qTwistedResidueMean_square_difference (d : ℕ) :
    qTwistedResidueMean d (d * d) - qTwistedResidueMean d d = 0 := by
  rw [qTwistedResidueMean_eq_zero_of_dvd d (d * d) (dvd_mul_right d d),
    qTwistedResidueMean_eq_zero_of_dvd d d (dvd_refl d)]
  ring

end RiemannResearch.RH.ZetaTwoHilbert
