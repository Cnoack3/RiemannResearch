import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Exact finite kernel energy

Source: elementary finite weighted-variance expansion, developed while
reviewing Michel Balazard, arXiv:1812.04309, Propositions 6--7.
That paper supplies the RH application and dual-system terminology, not
a claimed source for this general algebraic identity.

The exact equality retains the entire variance remainder. The concrete
triangular-dual application is explained in
RH/BalazardTriangularResearch20261019.md; its overlap identification is
not a formal theorem of this module.
-/

open scoped BigOperators
noncomputable section
namespace RiemannResearch.Analysis
theorem finite_kernel_variance_identity
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (ℓ : ι → κ → ℝ) (p : ι → ℝ) (q : κ → ℝ)
    (a : ι → ℝ) (x : κ → ℝ)
    (hrow : ∀ i, ∑ j, ℓ i j = p i)
    (hcol : ∀ j, ∑ i, ℓ i j = q j)
    (hmean : ∀ i, ∑ j, ℓ i j * x j = p i * a i) :
    (∑ j, q j * x j ^ 2) =
      (∑ i, p i * a i ^ 2) + ∑ i, ∑ j, ℓ i j * (x j - a i) ^ 2 := by
  classical
  have hrowVar (i : ι) :
      (∑ j, ℓ i j * (x j - a i) ^ 2) =
        (∑ j, ℓ i j * x j ^ 2) - p i * a i ^ 2 := by
    calc
      _ = ∑ j, (ℓ i j * x j ^ 2 -
            (2 * a i) * (ℓ i j * x j) + a i ^ 2 * ℓ i j) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = (∑ j, ℓ i j * x j ^ 2) -
          (2 * a i) * (∑ j, ℓ i j * x j) +
          a i ^ 2 * (∑ j, ℓ i j) := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
      _ = (∑ j, ℓ i j * x j ^ 2) - p i * a i ^ 2 := by
        rw [hmean i, hrow i]
        ring
  have hcolVar :
      (∑ i, ∑ j, ℓ i j * x j ^ 2) = ∑ j, q j * x j ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← Finset.sum_mul, hcol j]
  have htotal :
      (∑ i, ∑ j, ℓ i j * (x j - a i) ^ 2) =
        (∑ j, q j * x j ^ 2) - ∑ i, p i * a i ^ 2 := by
    simp_rw [hrowVar]
    rw [Finset.sum_sub_distrib, hcolVar]
  linarith

theorem finite_kernel_energy_le
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (ℓ : ι → κ → ℝ) (p : ι → ℝ) (q : κ → ℝ)
    (a : ι → ℝ) (x : κ → ℝ)
    (hℓ : ∀ i j, 0 ≤ ℓ i j)
    (hrow : ∀ i, ∑ j, ℓ i j = p i)
    (hcol : ∀ j, ∑ i, ℓ i j = q j)
    (hmean : ∀ i, ∑ j, ℓ i j * x j = p i * a i) :
    (∑ i, p i * a i ^ 2) ≤ ∑ j, q j * x j ^ 2 := by
  classical
  have hid := finite_kernel_variance_identity ℓ p q a x hrow hcol hmean
  have hnonneg : 0 ≤ ∑ i, ∑ j, ℓ i j * (x j - a i) ^ 2 := by
    apply Finset.sum_nonneg
    intro i hi
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (hℓ i j) (sq_nonneg (x j - a i))
  linarith
end RiemannResearch.Analysis
