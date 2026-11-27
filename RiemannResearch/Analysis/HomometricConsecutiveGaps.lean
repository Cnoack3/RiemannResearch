import RiemannResearch.Analysis.OrdinateTriangularIntegral
import Mathlib.Data.Fin.VecNotation

/-!
# All-frequency Fourier power and consecutive gaps

Bloom's six-point example (JCT A 22 (1977), 378–379,
https://doi.org/10.1016/0097-3165(77)90013-9) supplies the two simple
configurations below. The repeated-height example is the sum and the
translated difference of two copies of the set {0, 1, 3}, with occurrences.
Both examples use the same Fourier power as the ordinate collision tests.
-/

namespace RiemannResearch.Analysis.HomometricConsecutiveGaps

open OrdinateCollisionCertificate
open scoped BigOperators

/-- All signed differences of occurrence labels, including the diagonal. -/
def signedDifferences {n : ℕ} (x : Fin n → ℤ) : Multiset ℤ :=
  (Finset.univ : Finset (Fin n × Fin n)).val.map (fun ij => x ij.1 - x ij.2)

/-- The squared Fourier amplitude of an integer configuration. -/
noncomputable def fourierPower {n : ℕ} (x : Fin n → ℤ) (u : ℝ) : ℝ :=
  Complex.normSq (occurrenceAmplitude (fun i => (x i : ℝ)) u)

private theorem sum_test {n : ℕ} (x : Fin n → ℤ) (f : ℤ → ℝ) :
    ((signedDifferences x).map f).sum = ∑ i, ∑ j, f (x i - x j) := by
  rw [signedDifferences, Multiset.map_map]
  change (∑ ij : Fin n × Fin n, f (x ij.1 - x ij.2)) = _
  rw [Fintype.sum_prod_type]

/-- Equality of the signed difference multisets implies equality of physical
Fourier power at every real frequency. -/
theorem fourierPower_eq_of_signedDifferences_eq {m n : ℕ} {x : Fin m → ℤ} {y : Fin n → ℤ}
    (h : signedDifferences x = signedDifferences y) : fourierPower x = fourierPower y := by
  funext u
  have hsum := congrArg (fun s : Multiset ℤ =>
    (s.map (fun d : ℤ => Real.cos ((d : ℝ) * u))).sum) h
  simpa only [fourierPower, occurrenceAmplitude_normSq, sum_test, Int.cast_sub] using hsum

/-- Ordered sums and ordered differences of two real samples have identical
power. In the expanded energy, interchange the two indices of the second sample. -/
theorem sum_difference_power {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x : ι → ℝ) (y : κ → ℝ) (u : ℝ) :
    Complex.normSq (occurrenceAmplitude (fun ij : ι × κ => x ij.1 + y ij.2) u) =
      Complex.normSq (occurrenceAmplitude (fun ij : ι × κ => x ij.1 - y ij.2) u) := by
  simp only [occurrenceAmplitude_normSq, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = ∑ k, ∑ j, ∑ l, Real.cos ((x i + y j - (x k + y l)) * u) := Finset.sum_comm
    _ = ∑ k, ∑ j, ∑ l, Real.cos ((x i - y j - (x k - y l)) * u) := by
      apply Finset.sum_congr rfl
      intro k _
      calc
        _ = ∑ j, ∑ l, Real.cos ((x i + y l - (x k + y j)) * u) := Finset.sum_comm
        _ = _ := by
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro l _
          congr 1
          ring
    _ = _ := Finset.sum_comm

/-- For a nondecreasing list these are the interior consecutive gaps at most
the stated width. The comparison includes zero. -/
def adjacentCount {n : ℕ} (x : Fin (n + 1) → ℤ) (width : ℤ) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => x i.succ - x i.castSucc ≤ width)).card

def bloomA : Fin 6 → ℤ := ![0, 1, 4, 10, 12, 17]
def bloomB : Fin 6 → ℤ := ![0, 1, 8, 11, 13, 17]

theorem bloom_signedDifferences : signedDifferences bloomA = signedDifferences bloomB := by decide

theorem bloom_fourierPower : fourierPower bloomA = fourierPower bloomB :=
  fourierPower_eq_of_signedDifferences_eq bloom_signedDifferences

theorem bloom_adjacentCounts : adjacentCount bloomA 4 = 3 ∧ adjacentCount bloomB 4 = 4 := by decide

def sumSample : Fin 9 → ℤ := ![0, 1, 1, 2, 3, 3, 4, 4, 6]
def differenceSample : Fin 9 → ℤ := ![0, 1, 2, 3, 3, 3, 4, 5, 6]

theorem tied_signedDifferences :
    signedDifferences sumSample = signedDifferences differenceSample := by
  decide

theorem tied_fourierPower : fourierPower sumSample = fourierPower differenceSample :=
  fourierPower_eq_of_signedDifferences_eq tied_signedDifferences

theorem tied_adjacentCounts :
    adjacentCount sumSample 0 = 3 ∧ adjacentCount differenceSample 0 = 2 := by
  decide

/-- Even when both endpoints and the number of occurrences are given implicitly
by restricting the domain, power cannot determine either of these counts. -/
theorem no_power_rule_for_bloom :
    ¬ ∃ F : (ℝ → ℝ) → ℕ, ∀ x : Fin 6 → ℤ, Monotone x → x 0 = 0 → x 5 = 17 →
      F (fourierPower x) = adjacentCount x 4 := by
  rintro ⟨F, h⟩
  have hA := h bloomA (by decide) rfl rfl
  have hB := h bloomB (by decide) rfl rfl
  rw [bloom_fourierPower, bloom_adjacentCounts.1] at hA
  rw [bloom_adjacentCounts.2] at hB
  omega

/-- Counting exact ties from Fourier power fails even on sorted nine-term
samples anchored at zero and ending at six. -/
theorem no_power_rule_for_ties :
    ¬ ∃ F : (ℝ → ℝ) → ℕ, ∀ x : Fin 9 → ℤ, Monotone x → x 0 = 0 → x 8 = 6 →
      F (fourierPower x) = adjacentCount x 0 := by
  rintro ⟨F, h⟩
  have hA := h sumSample (by decide) rfl rfl
  have hB := h differenceSample (by decide) rfl rfl
  rw [tied_fourierPower, tied_adjacentCounts.1] at hA
  rw [tied_adjacentCounts.2] at hB
  omega

end RiemannResearch.Analysis.HomometricConsecutiveGaps
