import RiemannResearch.Probability.DeterminantalProcess
import Mathlib.Data.Finset.Interval

/-!
# Increasing deterministic DPPs can leave a permanent hole

Source: the user-provided DPP conversation, 2026-09-20. This checks every
correlation determinant for the counterexample {1,...,n}, with site 0 always
absent. It records why increasing cardinality and nested coupling alone do
not prove the arithmetic first-site criterion. Sites use zero-based indices.
-/

noncomputable section
open MeasureTheory Matrix
open scoped Classical BigOperators
namespace RiemannResearch.Probability.DPP

variable {α Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

def deterministicKernel (A : Set α) (i j : α) : ℝ :=
  if i = j then (if i ∈ A then 1 else 0) else 0

theorem deterministic_isDPP (A : Set α) :
    IsDPP μ (fun _ => A) (deterministicKernel A) := by
  constructor
  · intro i
    by_cases hi : i ∈ A <;> simp [hi]
  · intro n e
    have hmat : Matrix.of (fun i j : Fin n => deterministicKernel A (e i) (e j)) =
        Matrix.diagonal (fun i : Fin n => if e i ∈ A then (1 : ℝ) else 0) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [deterministicKernel]
      · simp [deterministicKernel, Matrix.diagonal, hij]
    rw [hmat, Matrix.det_diagonal]
    by_cases ha : ∀ i : Fin n, e i ∈ A
    · simp [ha]
    · obtain ⟨i, hi⟩ := not_forall.mp ha
      have he : {ω : Ω | ∀ j : Fin n, e j ∈ A} = ∅ := by
        ext ω
        simp [show ¬ ∀ j : Fin n, e j ∈ A from fun h => hi (h i)]
      rw [he]
      simp only [Measure.real, measure_empty, ENNReal.toReal_zero]
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [hi]

/-- Stage n occupies exactly n sites, while the first site 0 is never occupied. -/
def omittedFirstStage (n : ℕ) : Finset ℕ := Finset.Icc 1 n

theorem omittedFirstStage_card (n : ℕ) : (omittedFirstStage n).card = n := by
  simp [omittedFirstStage, Nat.card_Icc]

theorem omittedFirstStage_mono : Monotone omittedFirstStage := by
  intro n m hnm k hk
  simp only [omittedFirstStage, Finset.mem_Icc] at hk ⊢
  exact ⟨hk.1, hk.2.trans hnm⟩

theorem omittedFirstStage_vacancy (n : ℕ) :
    μ.real {_ω : Ω | 0 ∉ omittedFirstStage n} = 1 := by
  simp [omittedFirstStage]

theorem omittedFirstStage_isDPP (n : ℕ) :
    IsDPP μ (fun _ => (omittedFirstStage n : Set ℕ))
      (deterministicKernel (omittedFirstStage n : Set ℕ)) :=
  deterministic_isDPP μ _

end RiemannResearch.Probability.DPP
