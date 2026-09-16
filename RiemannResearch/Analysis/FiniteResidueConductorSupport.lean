import RiemannResearch.Analysis.FiniteResidueCharge
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Tauto

/-!
# Exact support count for two-seed residue charges

Source: user-provided `RH_Coupled_Residual_Corrections_2026-09-16.md`,
Section 9, for the conductor set and inclusion--exclusion formula.

The finite conductor count and the resulting moment ceiling are algebraic.
No Taylor expansion, Laplace identification, or Bernoulli nonvanishing theorem
is assumed or claimed here.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.FiniteResidueCharge

/-- Conductors obtained by multiplying the indices `1,...,M` by `d`. -/
def dilatedConductors (d M : ℕ) : Finset ℕ :=
  (Finset.Icc 1 M).image (fun m => d * m)

/-- The complete possible conductor set after expanding binary and ternary
legal generators. The formal conductor `1` is retained. -/
def conductorSet (M : ℕ) : Finset ℕ :=
  Finset.Icc 1 M ∪ dilatedConductors 2 M ∪ dilatedConductors 3 M

theorem card_dilatedConductors (d M : ℕ) (hd : 0 < d) :
    (dilatedConductors d M).card = M := by
  unfold dilatedConductors
  rw [Finset.card_image_of_injective _ (fun _ _ h => mul_left_cancel₀ (Nat.ne_of_gt hd) h)]
  simp

private theorem base_inter_binary (M : ℕ) :
    Finset.Icc 1 M ∩ dilatedConductors 2 M = dilatedConductors 2 (M / 2) := by
  ext n
  simp only [dilatedConductors, Finset.mem_inter, Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨hn, m, hm, hnm⟩
    exact ⟨m, ⟨hm.1, by omega⟩, hnm⟩
  · rintro ⟨m, hm, hnm⟩
    exact ⟨⟨by omega, by omega⟩, m, ⟨hm.1, by omega⟩, hnm⟩

private theorem base_inter_ternary (M : ℕ) :
    Finset.Icc 1 M ∩ dilatedConductors 3 M = dilatedConductors 3 (M / 3) := by
  ext n
  simp only [dilatedConductors, Finset.mem_inter, Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨hn, m, hm, hnm⟩
    exact ⟨m, ⟨hm.1, by omega⟩, hnm⟩
  · rintro ⟨m, hm, hnm⟩
    exact ⟨⟨by omega, by omega⟩, m, ⟨hm.1, by omega⟩, hnm⟩

private theorem binary_inter_ternary (M : ℕ) :
    dilatedConductors 2 M ∩ dilatedConductors 3 M =
      dilatedConductors 6 (M / 3) := by
  ext n
  simp only [dilatedConductors, Finset.mem_inter, Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨a, ha, hna⟩, b, hb, hnb⟩
    exact ⟨a / 3, ⟨by omega, by omega⟩, by omega⟩
  · rintro ⟨m, hm, hnm⟩
    exact ⟨⟨3 * m, ⟨by omega, by omega⟩, by omega⟩,
      2 * m, ⟨by omega, by omega⟩, by omega⟩

private theorem triple_inter (M : ℕ) :
    (Finset.Icc 1 M ∩ dilatedConductors 2 M) ∩ dilatedConductors 3 M =
      dilatedConductors 6 (M / 6) := by
  ext n
  simp only [dilatedConductors, Finset.mem_inter, Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hn, a, ha, hna⟩, b, hb, hnb⟩
    exact ⟨a / 3, ⟨by omega, by omega⟩, by omega⟩
  · rintro ⟨m, hm, hnm⟩
    exact ⟨⟨⟨by omega, by omega⟩,
      3 * m, ⟨by omega, by omega⟩, by omega⟩,
      2 * m, ⟨by omega, by omega⟩, by omega⟩

/-- Inclusion--exclusion in a subtraction-free form. -/
theorem conductorSet_card_identity (M : ℕ) :
    (conductorSet M).card + M / 2 + 2 * (M / 3) = 3 * M + M / 6 := by
  let A := Finset.Icc 1 M
  let B := dilatedConductors 2 M
  let C := dilatedConductors 3 M
  have hAB := Finset.card_union_add_card_inter A B
  have hABC := Finset.card_union_add_card_inter (A ∪ B) C
  have hACBC := Finset.card_union_add_card_inter (A ∩ C) (B ∩ C)
  have hdist : (A ∪ B) ∩ C = (A ∩ C) ∪ (B ∩ C) := by
    ext n
    simp only [Finset.mem_inter, Finset.mem_union]
    tauto
  have hcross : (A ∩ C) ∩ (B ∩ C) = (A ∩ B) ∩ C := by
    ext n
    simp only [Finset.mem_inter]
    tauto
  rw [hdist] at hABC
  rw [hcross] at hACBC
  have hA : A.card = M := by simp [A]
  have hB : B.card = M := card_dilatedConductors 2 M (by omega)
  have hC : C.card = M := card_dilatedConductors 3 M (by omega)
  have hABcard : (A ∩ B).card = M / 2 := by
    rw [show A ∩ B = dilatedConductors 2 (M / 2) from base_inter_binary M]
    exact card_dilatedConductors 2 (M / 2) (by omega)
  have hACcard : (A ∩ C).card = M / 3 := by
    rw [show A ∩ C = dilatedConductors 3 (M / 3) from base_inter_ternary M]
    exact card_dilatedConductors 3 (M / 3) (by omega)
  have hBCcard : (B ∩ C).card = M / 3 := by
    rw [show B ∩ C = dilatedConductors 6 (M / 3) from binary_inter_ternary M]
    exact card_dilatedConductors 6 (M / 3) (by omega)
  have hABCcard : ((A ∩ B) ∩ C).card = M / 6 := by
    rw [show (A ∩ B) ∩ C = dilatedConductors 6 (M / 6) from triple_inter M]
    exact card_dilatedConductors 6 (M / 6) (by omega)
  have hfull : (A ∪ B ∪ C).card = (conductorSet M).card := rfl
  omega

/-- The exact conductor count, including all coincidences between conductors. -/
theorem conductorSet_card (M : ℕ) :
    (conductorSet M).card = 3 * M - M / 2 - 2 * (M / 3) + M / 6 := by
  have h := conductorSet_card_identity M
  omega

/-- A uniform linear support bound independent of the common period. -/
theorem conductorSet_card_le (M : ℕ) : (conductorSet M).card ≤ 2 * M + 1 := by
  have h := conductorSet_card_identity M
  omega

/-- The first nonzero even charge on any actual two-seed conductor support
has odd order at most `4*M-1`. The statement is about moments; the separate
analytic identification with the order of a Laplace transform is not used. -/
theorem actual_support_moment_index_bound (M : ℕ) (S : Finset ℕ)
    (hS : S ⊆ conductorSet M) (b : S → ℝ)
    (hzero : ∑ i, b i = 0)
    (ha : constantTerm b (fun i : S => ((i : ℕ) : ℝ)) = 0) :
    ∃ j, moment b (fun i : S => ((i : ℕ) : ℝ)) (j + 1) ≠ 0 ∧
      2 * j + 1 ≤ 4 * M - 1 := by
  classical
  have hne : S.Nonempty := by
    by_contra hn
    have hempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    subst S
    simp [constantTerm] at ha
  have hs : 0 < Fintype.card S := by
    simpa using Finset.card_pos.mpr hne
  have hsize : Fintype.card S ≤ 2 * M + 1 := by
    simpa using (Finset.card_le_card hS).trans (conductorSet_card_le M)
  have hinj : Function.Injective (fun i : S => (((i : ℕ) : ℝ)) ^ 2) := by
    intro i j hij
    apply Subtype.ext
    exact Nat.cast_injective ((sq_eq_sq₀ (Nat.cast_nonneg _) (Nat.cast_nonneg _)).mp hij)
  exact moment_index_bound b _ M hinj hs hsize hzero ha

end RiemannResearch.Analysis.FiniteResidueCharge
