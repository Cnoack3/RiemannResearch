import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.SplitIfs

/-!
Source: user-supplied `Zeta_Zero_Harmonic_Analysis_20261011 (1)(1).md`, Sections 7 and 12.
These finite deductions make no publication-priority claim.

# Finite collision certificates and an exact adapted sine filter

This development is independent of the analytic zeta-zero inputs. For any finite
multiset represented by an occurrence type, collision excess is zero exactly
when the sampling map is injective, and otherwise is at least two. A
nonnegative pair kernel taking value one on collisions gives the sharp
strict certificate `energy < card + 2`.

The adapted finite sine product annihilates all nonzero sampled gaps, giving
an exact collision filter. Its compactly supported Fourier weight is explained
in the research continuation; no Fourier integral theorem is asserted here.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.FiniteCollisionCertificates

variable {ι β : Type*} [Fintype ι]

/-- Ordered distinct-occurrence pairs sharing the same sampled value. -/
def collisionExcess (f : ι → β) : ℝ := by
  classical
  exact ∑ i, ∑ j, if i ≠ j ∧ f i = f j then 1 else 0

/-- Ordered collision pairs, including identical-occurrence pairs. -/
def collisionCount (f : ι → β) : ℝ := by
  classical
  exact ∑ i, ∑ j, if f i = f j then 1 else 0

theorem collisionExcess_nonneg (f : ι → β) : 0 ≤ collisionExcess f := by
  classical
  exact Finset.sum_nonneg (fun i hi => Finset.sum_nonneg (fun j hj => by
    split_ifs <;> norm_num))

theorem collisionCount_eq_card_add_excess (f : ι → β) :
    collisionCount f = (Fintype.card ι : ℝ) + collisionExcess f := by
  classical
  calc
    collisionCount f = ∑ i, ∑ j,
        ((if i = j then (1 : ℝ) else 0) +
          (if i ≠ j ∧ f i = f j then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hij : i = j
      · simp [hij]
      · by_cases hf : f i = f j <;> simp [hij, hf]
    _ = (Fintype.card ι : ℝ) + collisionExcess f := by
      simp [collisionExcess, Finset.sum_add_distrib]

theorem collisionExcess_eq_zero_of_injective (f : ι → β)
    (hf : Function.Injective f) : collisionExcess f = 0 := by
  classical
  unfold collisionExcess
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  have h : ¬(i ≠ j ∧ f i = f j) := by
    rintro ⟨hne, heq⟩
    exact hne (hf heq)
  simp [h]

/-- The constant two is forced by the two orientations of one collision. -/
theorem two_le_collisionExcess_of_not_injective (f : ι → β)
    (hf : ¬Function.Injective f) : 2 ≤ collisionExcess f := by
  classical
  change ¬(∀ i j, f i = f j → i = j) at hf
  push Not at hf
  obtain ⟨i, j, hij, hne⟩ := hf
  let row : ι → ℝ := fun a => ∑ b, if a ≠ b ∧ f a = f b then 1 else 0
  have hrow : ∀ a, 0 ≤ row a := fun a =>
    Finset.sum_nonneg (fun b hb => by split_ifs <;> norm_num)
  have hi : 1 ≤ row i := by
    have h := Finset.single_le_sum
      (s := Finset.univ)
      (f := fun b => if i ≠ b ∧ f i = f b then (1 : ℝ) else 0)
      (fun b hb => by split_ifs <;> norm_num) (Finset.mem_univ j)
    simpa [row, hne, hij] using h
  have hj : 1 ≤ row j := by
    have h := Finset.single_le_sum
      (s := Finset.univ)
      (f := fun b => if j ≠ b ∧ f j = f b then (1 : ℝ) else 0)
      (fun b hb => by split_ifs <;> norm_num) (Finset.mem_univ i)
    simpa [row, Ne.symm hne, hij.symm] using h
  have hsubset : ({i, j} : Finset ι) ⊆ Finset.univ := Finset.subset_univ _
  have hsum : (∑ a ∈ ({i, j} : Finset ι), row a) ≤ ∑ a, row a :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun a ha hnot => hrow a)
  have htwo : 2 ≤ ∑ a ∈ ({i, j} : Finset ι), row a := by
    have htwo' : (2 : ℝ) ≤ row i + row j := by linarith
    simpa [hne] using htwo'
  exact htwo.trans hsum

theorem collisionExcess_eq_zero_iff (f : ι → β) :
    collisionExcess f = 0 ↔ Function.Injective f := by
  constructor
  · intro h
    by_contra hf
    have htwo := two_le_collisionExcess_of_not_injective f hf
    rw [h] at htwo
    norm_num at htwo
  · exact collisionExcess_eq_zero_of_injective f

theorem collisionExcess_zero_or_ge_two (f : ι → β) :
    collisionExcess f = 0 ∨ 2 ≤ collisionExcess f := by
  classical
  by_cases hf : Function.Injective f
  · exact Or.inl (collisionExcess_eq_zero_of_injective f hf)
  · exact Or.inr (two_le_collisionExcess_of_not_injective f hf)

theorem collisionCount_lt_card_add_two_iff (f : ι → β) :
    collisionCount f < (Fintype.card ι : ℝ) + 2 ↔ Function.Injective f := by
  rw [collisionCount_eq_card_add_excess]
  constructor
  · intro h
    by_contra hf
    have htwo := two_le_collisionExcess_of_not_injective f hf
    linarith
  · intro hf
    rw [collisionExcess_eq_zero_of_injective f hf]
    linarith

/-- A general nonnegative pair kernel dominates exact collisions. -/
theorem kernelEnergy_ge_collisionCount (f : ι → β) (K : ι → ι → ℝ)
    (hK : ∀ i j, 0 ≤ K i j)
    (heq : ∀ i j, f i = f j → K i j = 1) :
    collisionCount f ≤ ∑ i, ∑ j, K i j := by
  classical
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  by_cases hf : f i = f j
  · simp [hf, heq i j hf]
  · simp only [if_neg hf]
    exact hK i j

/-- Sharp finite-energy certificate, valid for an arbitrary occurrence map. -/
theorem injective_of_kernelEnergy_lt_card_add_two
    (f : ι → β) (K : ι → ι → ℝ)
    (hK : ∀ i j, 0 ≤ K i j)
    (heq : ∀ i j, f i = f j → K i j = 1)
    (hcert : (∑ i, ∑ j, K i j) < (Fintype.card ι : ℝ) + 2) :
    Function.Injective f := by
  by_contra hf
  have htwo := two_le_collisionExcess_of_not_injective f hf
  have hle := kernelEnergy_ge_collisionCount f K hK heq
  rw [collisionCount_eq_card_add_excess] at hle
  linarith

/-- Directly computable normalized sine, including its removable endpoint. -/
def normalizedSine (x : ℝ) : ℝ := if x = 0 then 1 else Real.sin x / x

@[simp] theorem normalizedSine_zero : normalizedSine 0 = 1 := by
  simp [normalizedSine]

@[simp] theorem normalizedSine_pi : normalizedSine Real.pi = 0 := by
  simp [normalizedSine, Real.pi_ne_zero]

theorem normalizedSine_neg (x : ℝ) :
    normalizedSine (-x) = normalizedSine x := by
  by_cases hx : x = 0
  · simp [hx]
  · simp [normalizedSine, hx, Real.sin_neg]

/-- Target-adapted product annihilating the specified positive gaps. -/
def gapKernel (D : Finset ℝ) (v : ℝ) : ℝ :=
  ∏ d ∈ D, normalizedSine (Real.pi * v / d) ^ 2

theorem gapKernel_nonneg (D : Finset ℝ) (v : ℝ) : 0 ≤ gapKernel D v :=
  Finset.prod_nonneg (fun d hd => sq_nonneg _)

@[simp] theorem gapKernel_zero (D : Finset ℝ) : gapKernel D 0 = 1 := by
  simp [gapKernel]

theorem gapKernel_neg (D : Finset ℝ) (v : ℝ) :
    gapKernel D (-v) = gapKernel D v := by
  unfold gapKernel
  apply Finset.prod_congr rfl
  intro d hd
  rw [mul_neg, neg_div, normalizedSine_neg]

theorem gapKernel_eq_zero_of_mem (D : Finset ℝ) {d : ℝ}
    (hd : d ∈ D) (hne : d ≠ 0) : gapKernel D d = 0 := by
  have harg : Real.pi * d / d = Real.pi := by
    rw [mul_div_cancel_right₀ _ hne]
  apply Finset.prod_eq_zero hd
  simp [harg]

theorem gapKernel_eq_zero_of_abs_mem (D : Finset ℝ) {v : ℝ}
    (hv : v ≠ 0) (hD : |v| ∈ D) : gapKernel D v = 0 := by
  by_cases hnonneg : 0 ≤ v
  · rw [abs_of_nonneg hnonneg] at hD
    exact gapKernel_eq_zero_of_mem D hD hv
  · have hneg : v < 0 := lt_of_not_ge hnonneg
    rw [abs_of_neg hneg] at hD
    have h := gapKernel_eq_zero_of_mem D hD (neg_ne_zero.mpr hv)
    rwa [gapKernel_neg] at h

/-- Exact collision count from a finite sine product, without a limit. -/
theorem gapKernelEnergy_eq_collisionCount
    (f : ι → ℝ) (D : Finset ℝ)
    (hD : ∀ i j, f i ≠ f j → |f i - f j| ∈ D) :
    (∑ i, ∑ j, gapKernel D (f i - f j)) = collisionCount f := by
  classical
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hf : f i = f j
  · simp [hf]
  · simp only [if_neg hf]
    exact gapKernel_eq_zero_of_abs_mem D (sub_ne_zero.mpr hf) (hD i j hf)

/-- The adapted finite filter is a necessary and sufficient sharp certificate. -/
theorem gapKernel_certificate_iff_injective
    (f : ι → ℝ) (D : Finset ℝ)
    (hD : ∀ i j, f i ≠ f j → |f i - f j| ∈ D) :
    (∑ i, ∑ j, gapKernel D (f i - f j)) < (Fintype.card ι : ℝ) + 2 ↔
      Function.Injective f := by
  rw [gapKernelEnergy_eq_collisionCount f D hD, collisionCount_eq_card_add_excess]
  constructor
  · intro h
    by_contra hf
    have htwo := two_le_collisionExcess_of_not_injective f hf
    linarith
  · intro hf
    rw [collisionExcess_eq_zero_of_injective f hf]
    linarith

/-- The finite set of all positive absolute differences among sampled values. -/
def sampleGaps (f : ι → ℝ) : Finset ℝ := by
  classical
  exact ((Finset.univ.product Finset.univ).image
    (fun ij : ι × ι => |f ij.1 - f ij.2|)).erase 0

theorem abs_sub_mem_sampleGaps (f : ι → ℝ) (i j : ι)
    (hij : f i ≠ f j) : |f i - f j| ∈ sampleGaps f := by
  classical
  apply Finset.mem_erase.mpr
  refine ⟨ne_of_gt (abs_pos.mpr (sub_ne_zero.mpr hij)), ?_⟩
  exact Finset.mem_image.mpr ⟨(i, j), by simp, rfl⟩

theorem sampleGapKernelEnergy_eq_collisionCount (f : ι → ℝ) :
    (∑ i, ∑ j, gapKernel (sampleGaps f) (f i - f j)) = collisionCount f :=
  gapKernelEnergy_eq_collisionCount f (sampleGaps f) (abs_sub_mem_sampleGaps f)

end RiemannResearch.Analysis.FiniteCollisionCertificates
