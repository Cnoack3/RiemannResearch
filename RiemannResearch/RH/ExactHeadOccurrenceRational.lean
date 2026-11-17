import RiemannResearch.RH.ExactHeadOccurrenceEnclosures
import Mathlib.Data.Rat.BigOperators
import Mathlib.Tactic.NormNum

/-!
# Rational replay of complete occurrence means and energies

Source: the exact canonical occurrence formula and the proved elementary
Pareto progression intervals. Every endpoint test is finite rational
arithmetic. Soundness concerns the actual infinite progression weights.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.ExactHeadOccurrenceProjection
open RiemannResearch
open RiemannResearch.Analysis.FiniteProfileEnergy
open RiemannResearch.Analysis.FiniteWeightedVariance
open RiemannResearch.RH.ExactHeadGcdAtoms
open ExactHeadAtomOptimizer

/-- Exact rational coprime-count target; no subtraction is truncated in the naturals. -/
def rationalTarget (P r : ℕ) : ℚ :=
  (((Finset.Icc 1 r).filter (fun n => Nat.gcd n P = 1)).card : ℚ) - 1

theorem rationalTarget_cast (P r : ℕ) :
    (rationalTarget P r : ℝ) = target P r := by
  simp [rationalTarget, target, atom]

/-- Two rational centered-sum tests for one block, including every progression tail. -/
def blockMeanCertificate (P K a b : ℕ) (lo hi : ℚ) : Prop :=
  (0 : ℚ) ≤ ∑ r ∈ Finset.Ico a b,
    min ((elementaryProgressionInterval P r K).lo * (rationalTarget P r - lo))
      ((elementaryProgressionInterval P r K).hi * (rationalTarget P r - lo)) ∧
  (∑ r ∈ Finset.Ico a b,
    max ((elementaryProgressionInterval P r K).lo * (rationalTarget P r - hi))
      ((elementaryProgressionInterval P r K).hi * (rationalTarget P r - hi))) ≤ 0

instance (P K a b : ℕ) (lo hi : ℚ) : Decidable (blockMeanCertificate P K a b lo hi) :=
  by unfold blockMeanCertificate; infer_instance

theorem blockMeanCertificate_sound (P x K a b : ℕ)
    (ha : a ∈ freePositions P x) (hab : a < b) (hbP : b ≤ P)
    (hb : b ∈ freePositions P x ∨ b = P)
    (hgap : ∀ n ∈ freePositions P x, a < n → n < b → False)
    (lo hi : ℚ) (hc : blockMeanCertificate P K a b lo hi) :
    (lo : ℝ) ≤ fit P x (occurrenceCoefficients P x) a ∧
      fit P x (occurrenceCoefficients P x) a ≤ (hi : ℝ) := by
  have ha1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).1
  have hP : 0 < P := by omega
  apply occurrence_block_fit_enclosure P x a b ha hab hbP hb hgap
    (fun r => ((elementaryProgressionInterval P r K).lo : ℝ))
    (fun r => ((elementaryProgressionInterval P r K).hi : ℝ))
  · intro r hr
    exact elementaryProgressionInterval_contains P r K hP
      (by have := Finset.mem_Ico.mp hr; omega)
  · have h : (0 : ℝ) ≤ ((∑ r ∈ Finset.Ico a b,
        min ((elementaryProgressionInterval P r K).lo * (rationalTarget P r - lo))
          ((elementaryProgressionInterval P r K).hi * (rationalTarget P r - lo)) : ℚ) : ℝ) := by
      exact_mod_cast hc.1
    simpa only [Rat.cast_sum, Rat.cast_min, Rat.cast_mul, Rat.cast_sub, rationalTarget_cast] using h
  · have h : ((∑ r ∈ Finset.Ico a b,
        max ((elementaryProgressionInterval P r K).lo * (rationalTarget P r - hi))
          ((elementaryProgressionInterval P r K).hi * (rationalTarget P r - hi)) : ℚ) : ℝ) ≤ 0 := by
      exact_mod_cast hc.2
    simpa only [Rat.cast_sum, Rat.cast_max, Rat.cast_mul, Rat.cast_sub, rationalTarget_cast] using h

theorem elementaryProgressionInterval_lower_pos (P r K : ℕ) (hP : 0 < P) (hr : 0 < r) :
    0 < (elementaryProgressionInterval P r K).lo := by
  dsimp [elementaryProgressionInterval]
  have hp : (0 : ℚ) < P := by exact_mod_cast hP
  have hrr : (0 : ℚ) < r := by exact_mod_cast hr
  have hs : (0 : ℚ) ≤ ∑ j ∈ Finset.range K,
      1 / (((r : ℚ) + P * j) * ((r : ℚ) + P * j + 1)) :=
    Finset.sum_nonneg (fun j hj => by positivity)
  positivity

/-- Exact rational version of the canonical weighted energy formula. -/
def rationalOccurrenceEnergy (P x : ℕ) (w : ℕ → ℚ) : ℚ :=
  (∑ r ∈ Finset.Ico 1 (occurrenceBoundary P x 0), w r * rationalTarget P r ^ 2) +
  ∑ i ∈ Finset.range (freePositions P x).card,
    let s := Finset.Ico (occurrenceBoundary P x i) (occurrenceBoundary P x (i+1))
    let m := (∑ r ∈ s, w r * rationalTarget P r) / (∑ r ∈ s, w r)
    ∑ r ∈ s, w r * (rationalTarget P r - m)^2

theorem rationalOccurrenceEnergy_cast (P x : ℕ) (w : ℕ → ℚ) :
    (rationalOccurrenceEnergy P x w : ℝ) =
      occurrenceWeightEnergy P x (fun r => (w r : ℝ)) := by
  simp only [rationalOccurrenceEnergy, occurrenceWeightEnergy, energy, variance, mean,
    RiemannResearch.Analysis.FiniteWeightedVariance.mass, Rat.cast_add,
    Rat.cast_sum, Rat.cast_mul, Rat.cast_pow, Rat.cast_sub, Rat.cast_div, rationalTarget_cast]

/-- Completely finite rational bounds for the true minimum; no numerical solver is trusted. -/
theorem rationalOccurrenceEnergy_enclosure (P x K : ℕ) (hP : 0 < P) :
    (rationalOccurrenceEnergy P x
      (fun r => (elementaryProgressionInterval P r K).lo) : ℝ)
        ≤ occurrenceEnergy P x ∧
      occurrenceEnergy P x ≤
        (rationalOccurrenceEnergy P x
          (fun r => (elementaryProgressionInterval P r K).hi) : ℝ) := by
  simp only [rationalOccurrenceEnergy_cast]
  apply occurrenceEnergy_weight_enclosure P x hP
  · intro r hr
    exact_mod_cast elementaryProgressionInterval_lower_pos P r K hP (Finset.mem_Icc.mp hr).1
  · intro r hr
    exact elementaryProgressionInterval_contains P r K hP (Finset.mem_Icc.mp hr).1

/-- A computable sorted-list representation of every canonical boundary. -/
theorem occurrenceBoundary_eq_sorted (P x i : ℕ) :
    occurrenceBoundary P x i = ((freePositions P x).sort (· ≤ ·)).getD i P := by
  by_cases hi : i < (freePositions P x).card
  · simp only [occurrenceBoundary, dif_pos hi, Finset.orderEmbOfFin_apply]
    exact List.getElem_eq_getD P
  · simp [occurrenceBoundary, hi, List.getD_eq_getElem?_getD]

end RiemannResearch.RH.Pareto.ExactHeadOccurrenceProjection
