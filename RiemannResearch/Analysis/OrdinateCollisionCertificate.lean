import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Finite collision certificates for ordinate samples

Every occurrence is retained, so distinct labels may have the same ordinate.
The positive sinc-squared kernel dominates the exact ordered collision count.
The certificate is a finite sum statement; identifying it with a triangular
Fourier integral is an additional analytic theorem, not an assumption here.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace RiemannResearch.Analysis.OrdinateCollisionCertificate

variable {ι : Type*}

def multiplicityCount (s : Finset ι) (M : ι → ℕ) : ℕ := ∑ i ∈ s, M i

def multiplicityCollision (s : Finset ι) (M : ι → ℕ) : ℕ := ∑ i ∈ s, (M i) ^ 2

def multiplicityExcess (s : Finset ι) (M : ι → ℕ) : ℕ :=
  ∑ i ∈ s, M i * (M i - 1)

theorem multiplicity_square_decomposition (n : ℕ) :
    n ^ 2 = n + n * (n - 1) := by
  cases n with
  | zero => norm_num
  | succ n =>
      simp only [Nat.succ_sub_one]
      ring

theorem multiplicityCollision_eq_count_add_excess (s : Finset ι) (M : ι → ℕ) :
    multiplicityCollision s M = multiplicityCount s M + multiplicityExcess s M := by
  unfold multiplicityCollision multiplicityCount multiplicityExcess
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => multiplicity_square_decomposition (M i))

theorem multiplicityExcess_even (s : Finset ι) (M : ι → ℕ) :
    Even (multiplicityExcess s M) := by
  classical
  unfold multiplicityExcess
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi hs =>
      rw [Finset.sum_insert hi]
      exact (Nat.even_mul_pred_self (M i)).add hs

theorem multiplicityCollision_sub_count_even (s : Finset ι) (M : ι → ℕ) :
    Even (multiplicityCollision s M - multiplicityCount s M) := by
  rw [multiplicityCollision_eq_count_add_excess, Nat.add_sub_cancel_left]
  exact multiplicityExcess_even s M

theorem two_le_multiplicityExcess (s : Finset ι) (M : ι → ℕ)
    {i : ι} (hi : i ∈ s) (hM : 2 ≤ M i) : 2 ≤ multiplicityExcess s M := by
  have hcost : 2 ≤ M i * (M i - 1) := by
    calc
      2 = 2 * (2 - 1) := by norm_num
      _ ≤ M i * (M i - 1) :=
        Nat.mul_le_mul hM (Nat.sub_le_sub_right hM 1)
  exact hcost.trans (Finset.single_le_sum
    (f := fun j => M j * (M j - 1)) (fun j _ => Nat.zero_le _) hi)

/-- A dominating real energy below `N + 2` rules out every multiplicity above one. -/
theorem multiplicity_certificate (s : Finset ι) (M : ι → ℕ) (energy : ℝ)
    (hdom : (multiplicityCollision s M : ℝ) ≤ energy)
    (hsmall : energy < (multiplicityCount s M : ℝ) + 2) :
    ∀ i ∈ s, M i ≤ 1 := by
  intro i hi
  by_contra h
  have hM : 2 ≤ M i := by omega
  have hx := two_le_multiplicityExcess s M hi hM
  have hc := multiplicityCollision_eq_count_add_excess s M
  have hgap : multiplicityCount s M + 2 ≤ multiplicityCollision s M := by omega
  have hgapR : (multiplicityCount s M : ℝ) + 2 ≤
      (multiplicityCollision s M : ℝ) := by exact_mod_cast hgap
  linarith

section Occurrences

variable [Fintype ι]

/-- Ordered same-ordinate pairs, including identical occurrences. -/
def occurrenceCollision (frequency : ι → ℝ) : ℕ := by
  classical
  exact ∑ i, ∑ j, if frequency i = frequency j then 1 else 0

/-- Ordered same-ordinate pairs of distinct occurrence labels. -/
def occurrenceExcess (frequency : ι → ℝ) : ℕ := by
  classical
  exact ∑ i, ∑ j, if i ≠ j ∧ frequency i = frequency j then 1 else 0

theorem occurrenceCollision_eq_card_add_excess (frequency : ι → ℝ) :
    occurrenceCollision frequency = Fintype.card ι + occurrenceExcess frequency := by
  classical
  have hp : ∀ i j : ι,
      (if frequency i = frequency j then (1 : ℕ) else 0) =
      (if i = j then 1 else 0) +
      (if i ≠ j ∧ frequency i = frequency j then 1 else 0) := by
    intro i j
    by_cases hij : i = j
    · simp [hij]
    · by_cases hf : frequency i = frequency j <;> simp [hij, hf]
  unfold occurrenceCollision occurrenceExcess
  simp_rw [hp, Finset.sum_add_distrib]
  simp

theorem one_le_collision_row (frequency : ι → ℝ) {i j : ι}
    (hij : i ≠ j) (hf : frequency i = frequency j) :
    1 ≤ ∑ k, if i ≠ k ∧ frequency i = frequency k then (1 : ℕ) else 0 := by
  classical
  have h := Finset.single_le_sum
    (fun k (_ : k ∈ Finset.univ) =>
      Nat.zero_le (if i ≠ k ∧ frequency i = frequency k then (1 : ℕ) else 0))
    (Finset.mem_univ j)
  simpa [hij, hf] using h

/-- One collision supplies two ordered distinct-occurrence collisions. -/
theorem two_le_occurrenceExcess (frequency : ι → ℝ) {i j : ι}
    (hij : i ≠ j) (hf : frequency i = frequency j) :
    2 ≤ occurrenceExcess frequency := by
  classical
  let row : ι → ℕ := fun a =>
    ∑ b, if a ≠ b ∧ frequency a = frequency b then 1 else 0
  have hi : 1 ≤ row i := one_le_collision_row frequency hij hf
  have hj : 1 ≤ row j := one_le_collision_row frequency hij.symm hf.symm
  have hs : row i + row j ≤ occurrenceExcess frequency := by
    calc
      row i + row j = ∑ k ∈ ({i, j} : Finset ι), row k := by simp [hij]
      _ ≤ ∑ k, row k := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ = occurrenceExcess frequency := rfl
  omega

/-- Each selected occurrence with a distinct companion injects one unit into the excess. -/
theorem selected_count_le_occurrenceExcess (frequency : ι → ℝ) (selected : Finset ι)
    (hcompanion : ∀ i ∈ selected, ∃ j, i ≠ j ∧ frequency i = frequency j) :
    selected.card ≤ occurrenceExcess frequency := by
  classical
  calc
    selected.card = ∑ i ∈ selected, (1 : ℕ) := by simp
    _ ≤ ∑ i ∈ selected,
        ∑ j, if i ≠ j ∧ frequency i = frequency j then (1 : ℕ) else 0 := by
      apply Finset.sum_le_sum
      intro i hi
      obtain ⟨j, hij, hf⟩ := hcompanion i hi
      exact one_le_collision_row frequency hij hf
    _ ≤ ∑ i, ∑ j,
        if i ≠ j ∧ frequency i = frequency j then (1 : ℕ) else 0 :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = occurrenceExcess frequency := rfl

def kernelEnergy (frequency : ι → ℝ) (K : ℝ → ℝ) : ℝ :=
  ∑ i, ∑ j, K (frequency i - frequency j)

theorem collision_le_kernelEnergy (frequency : ι → ℝ) (K : ℝ → ℝ)
    (hK : ∀ x, 0 ≤ K x) (hzero : K 0 = 1) :
    (occurrenceCollision frequency : ℝ) ≤ kernelEnergy frequency K := by
  classical
  unfold occurrenceCollision kernelEnergy
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  by_cases hf : frequency i = frequency j
  · simp [hf, hzero]
  · simpa [hf] using hK (frequency i - frequency j)

/-- All off-line occurrences have a reflected companion, so this applies to their count. -/
theorem selected_count_le_kernel_excess (frequency : ι → ℝ) (K : ℝ → ℝ)
    (hK : ∀ x, 0 ≤ K x) (hzero : K 0 = 1) (selected : Finset ι)
    (hcompanion : ∀ i ∈ selected, ∃ j, i ≠ j ∧ frequency i = frequency j) :
    (selected.card : ℝ) ≤ kernelEnergy frequency K - Fintype.card ι := by
  have hs := selected_count_le_occurrenceExcess frequency selected hcompanion
  have hsR : (selected.card : ℝ) ≤ (occurrenceExcess frequency : ℝ) := by
    exact_mod_cast hs
  have hc := occurrenceCollision_eq_card_add_excess frequency
  have hcR : (occurrenceCollision frequency : ℝ) =
      (Fintype.card ι : ℝ) + (occurrenceExcess frequency : ℝ) := by
    exact_mod_cast hc
  have hd := collision_le_kernelEnergy frequency K hK hzero
  linarith

theorem kernel_certificate (frequency : ι → ℝ) (K : ℝ → ℝ)
    (hK : ∀ x, 0 ≤ K x) (hzero : K 0 = 1)
    (hsmall : kernelEnergy frequency K < (Fintype.card ι : ℝ) + 2) :
    Function.Injective frequency := by
  intro i j hf
  by_contra hij
  have hx := two_le_occurrenceExcess frequency hij hf
  have hc := occurrenceCollision_eq_card_add_excess frequency
  have hgap : Fintype.card ι + 2 ≤ occurrenceCollision frequency := by omega
  have hgapR : (Fintype.card ι : ℝ) + 2 ≤ (occurrenceCollision frequency : ℝ) := by
    exact_mod_cast hgap
  have hd := collision_le_kernelEnergy frequency K hK hzero
  linarith

def sincSquared (R v : ℝ) : ℝ := (Real.sinc (R * v / 2)) ^ 2

theorem sincSquared_nonneg (R v : ℝ) : 0 ≤ sincSquared R v := sq_nonneg _

@[simp] theorem sincSquared_zero (R : ℝ) : sincSquared R 0 = 1 := by
  simp [sincSquared]

def sincEnergy (frequency : ι → ℝ) (R : ℝ) : ℝ :=
  kernelEnergy frequency (sincSquared R)

theorem collision_le_sincEnergy (frequency : ι → ℝ) (R : ℝ) :
    (occurrenceCollision frequency : ℝ) ≤ sincEnergy frequency R :=
  collision_le_kernelEnergy frequency (sincSquared R)
    (sincSquared_nonneg R) (sincSquared_zero R)

/-- A fully finite, explicit sinc-squared certificate; no Fourier limit is assumed. -/
theorem sinc_certificate (frequency : ι → ℝ) (R : ℝ)
    (hsmall : sincEnergy frequency R < (Fintype.card ι : ℝ) + 2) :
    Function.Injective frequency :=
  kernel_certificate frequency (sincSquared R)
    (sincSquared_nonneg R) (sincSquared_zero R) hsmall

end Occurrences
end RiemannResearch.Analysis.OrdinateCollisionCertificate
