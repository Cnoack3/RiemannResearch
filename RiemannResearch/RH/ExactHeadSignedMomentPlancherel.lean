import RiemannResearch.RH.ExactHeadSignedMomentBounds
import RiemannResearch.RH.ExactHeadAtomReturnMoments
import RiemannResearch.RH.ExactHeadGcdAtoms
import RiemannResearch.RH.RamanujanFinitePlancherel
import RiemannResearch.Analysis.FiniteProfileEnergy
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Complete Ramanujan coordinates of the signed three-label moment

The corrected finite Plancherel identity is applied to the upper prefix
scores, not to the full optimizer scores (which vanish on upper atoms).
The conductor-one term is retained. The estimates contain the actual
prefix-score energy; no decay or inverse-Gram estimate is inferred.
Source for the transform: audited A1--A2 manuscript, section 8;
https://drive.google.com/file/d/1DHIp4gGwApIL1V6nHwV4HDxuOAFdijwG/view.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.ExactHeadSignedMomentPlancherel
open RiemannResearch.Analysis.FiniteProfileEnergy
open RiemannResearch.RH.ExactHeadGcdAtoms
open RiemannResearch.RH.ExactHeadAtomReturnMoments
open RiemannResearch.RH.ExactHeadSignedMomentBounds
open RiemannResearch.RH.Pareto.RamanujanFinitePlancherel

def upperPrefixScore (P x Y : ℕ) (w h : ℕ → ℝ) (g : ℕ) : ℝ :=
  if x < g then prefixMoment P Y w h g else 0

def tripleAtomCoefficient (p q r g : ℕ) : ℝ :=
  (p : ℝ) * ((r : ℝ) - q) * (if p ∣ g then 1 else 0) -
  (q : ℝ) * ((r : ℝ) - p) * (if q ∣ g then 1 else 0) +
  (r : ℝ) * ((q : ℝ) - p) * (if r ∣ g then 1 else 0)

/-- Only activated upper atoms are charged in the dual score cost. -/
def activeTripleCoefficient (x Y p q r g : ℕ) : ℝ :=
  if x < g ∧ g ≤ Y then tripleAtomCoefficient p q r g else 0

theorem activatedMoment_eq_upperPrefixScore (P x Y p : ℕ) (w h : ℕ → ℝ) :
    activatedMoment P x Y p w h =
      ∑ g ∈ P.divisors, (if p ∣ g then (1 : ℝ) else 0) *
        upperPrefixScore P x Y w h g := by
  rw [← upperDivisorSignal_prefix, upperDivisorSignal, prefix_pairing_synthesis]
  simp only [upperDivisors, Finset.sum_filter, upperPrefixScore]
  apply Finset.sum_congr rfl
  intro g hg
  split_ifs <;> ring

theorem tripleMoment_eq_raw_divisor_sum (P x Y p q r : ℕ) (w h : ℕ → ℝ) :
    tripleMoment P x Y p q r w h =
      ∑ g ∈ P.divisors, tripleAtomCoefficient p q r g * upperPrefixScore P x Y w h g := by
  unfold tripleMoment
  rw [activatedMoment_eq_upperPrefixScore, activatedMoment_eq_upperPrefixScore,
    activatedMoment_eq_upperPrefixScore]
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro g hg
  unfold tripleAtomCoefficient
  ring

theorem tripleMoment_eq_divisor_sum (P x Y p q r : ℕ) (w h : ℕ → ℝ) :
    tripleMoment P x Y p q r w h =
      ∑ g ∈ P.divisors, activeTripleCoefficient x Y p q r g * upperPrefixScore P x Y w h g := by
  rw [tripleMoment_eq_raw_divisor_sum]
  apply Finset.sum_congr rfl
  intro g hg
  by_cases ha : x < g ∧ g ≤ Y
  · simp [activeTripleCoefficient, ha]
  · have hz : upperPrefixScore P x Y w h g = 0 := by
      by_cases hx : x < g
      · have hY : Y < g := by omega
        simp [upperPrefixScore, hx, prefixMoment_zero_above_cutoff P Y g w h hY]
      · simp [upperPrefixScore, hx]
    simp [hz]


theorem tripleMoment_eq_totient_pairing (P x Y p q r : ℕ) (w h : ℕ → ℝ) :
    tripleMoment P x Y p q r w h =
      pairing P.divisors (fun g => (g.totient : ℝ)) (upperPrefixScore P x Y w h)
        (fun g => activeTripleCoefficient x Y p q r g / (g.totient : ℝ)) := by
  rw [tripleMoment_eq_divisor_sum]
  unfold pairing
  apply Finset.sum_congr rfl
  intro g hg
  have ht : (g.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_mem_divisors hg)).ne'
  field_simp
  <;> ring

/-- All conductors, including one, participate in this signed identity. -/
theorem tripleMoment_eq_conductor_pairing (P x Y p q r : ℕ) (w h : ℕ → ℝ)
    (hP : Squarefree P) :
    tripleMoment P x Y p q r w h =
      (P.totient : ℝ) / P *
      ∑ a ∈ P.divisors,
        transform P (upperPrefixScore P x Y w h) a *
        transform P (fun g => activeTripleCoefficient x Y p q r g / (g.totient : ℝ)) a /
          (a.totient : ℝ) := by
  rw [polarized_plancherel P hP]
  change _ = (P.totient : ℝ) / P * ((P : ℝ) / P.totient *
    pairing P.divisors (fun g => (g.totient : ℝ)) (upperPrefixScore P x Y w h)
      (fun g => activeTripleCoefficient x Y p q r g / (g.totient : ℝ)))
  rw [← tripleMoment_eq_totient_pairing]
  have hp0 : (P : ℝ) ≠ 0 := by exact_mod_cast hP.ne_zero
  have ht0 : (P.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hP.ne_zero)).ne'
  field_simp

/-- The signed atom coefficients are combined before squaring. -/
theorem tripleMoment_sq_le_score_energy (P x Y p q r : ℕ) (w h : ℕ → ℝ) :
    tripleMoment P x Y p q r w h ^ 2 ≤
      (∑ g ∈ P.divisors, (g.totient : ℝ) * upperPrefixScore P x Y w h g ^ 2) *
      (∑ g ∈ P.divisors, activeTripleCoefficient x Y p q r g ^ 2 / (g.totient : ℝ)) := by
  rw [tripleMoment_eq_totient_pairing]
  have he : energy P.divisors (fun g => (g.totient : ℝ))
      (fun g => activeTripleCoefficient x Y p q r g / (g.totient : ℝ)) =
      ∑ g ∈ P.divisors, activeTripleCoefficient x Y p q r g ^ 2 / (g.totient : ℝ) := by
    unfold energy
    apply Finset.sum_congr rfl
    intro g hg
    have ht : (g.totient : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_mem_divisors hg)).ne'
    field_simp
  have hh := pairing_sq_le P.divisors (fun g => (g.totient : ℝ))
    (upperPrefixScore P x Y w h)
    (fun g => activeTripleCoefficient x Y p q r g / (g.totient : ℝ))
    (fun g _ => Nat.cast_nonneg _)
  rw [he] at hh
  exact hh

/-- The exact remainder behind the score-energy bound; no sign is discarded. -/
theorem tripleMoment_score_gram_identity (P x Y p q r : ℕ) (w h : ℕ → ℝ) :
    energy P.divisors (fun g => (g.totient : ℝ)) (upperPrefixScore P x Y w h) *
      energy P.divisors (fun g => (g.totient : ℝ))
        (fun g => activeTripleCoefficient x Y p q r g / (g.totient : ℝ)) -
      tripleMoment P x Y p q r w h ^ 2 =
    (∑ g ∈ P.divisors, ∑ k ∈ P.divisors,
      (g.totient : ℝ) * k.totient *
      (upperPrefixScore P x Y w h g * (activeTripleCoefficient x Y p q r k / k.totient) -
       upperPrefixScore P x Y w h k * (activeTripleCoefficient x Y p q r g / g.totient))^2) / 2 := by
  rw [tripleMoment_eq_totient_pairing]
  exact gram_identity _ _ _ _

end RiemannResearch.RH.ExactHeadSignedMomentPlancherel
