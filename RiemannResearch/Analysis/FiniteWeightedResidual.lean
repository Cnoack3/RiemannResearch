import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Weighted residuals with a fixed coordinate

The finite normal-equation identity used by the Ramanujan LCM zero certificate.
The distinguished class is the zero residue. Complex Mellin observations are
represented by their real and imaginary rows.

Source: Full-Conductor RH Projection Machinery, Section 15.3 (minimum-energy
zero-coordinate certificate). The identity here separates a fixed residue
class before forming the observation Gram.
-/

open scoped BigOperators

namespace RiemannResearch.Analysis.FiniteWeightedResidual

/-- A solved observation Gram on the complement of a distinguished class gives
an exact residual energy with that class's mass and the orthogonal remainder. -/
theorem energy_eq_fixedClass_add_certificate_add_remainder
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (o : ι) (w r : ι → ℝ) (row : κ → ι → ℝ) (a y : κ → ℝ)
    (hr0 : r o = 1)
    (hobs : ∀ k, ∑ i ∈ Finset.univ.erase o, w i * row k i * r i = y k)
    (hnormal : ∀ k,
      ∑ l, (∑ i ∈ Finset.univ.erase o, w i * row l i * row k i) * a l = y k) :
    let z : ι → ℝ := fun i => ∑ k, a k * row k i
    (∑ i, w i * (r i)^2) =
      w o + (∑ k, y k * a k) + ∑ i ∈ Finset.univ.erase o, w i * (r i - z i)^2 := by
  let s := Finset.univ.erase o
  let z : ι → ℝ := fun i => ∑ k, a k * row k i
  change (∑ i, w i * (r i)^2) =
    w o + (∑ k, y k * a k) + ∑ i ∈ s, w i * (r i - z i)^2
  have hpair (g : ι → ℝ) :
      (∑ i ∈ s, w i * z i * g i) = ∑ k, (∑ i ∈ s, w i * row k i * g i) * a k := by
    calc
      _ = ∑ i ∈ s, ∑ k, (w i * row k i * g i) * a k := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp only [z]
        rw [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = _ := by
        rw [Finset.sum_comm]
        simp only [Finset.sum_mul]
  have hm (k : κ) : (∑ i ∈ s, w i * row k i * z i) = y k := by
    calc
      _ = ∑ i ∈ s, w i * z i * row k i := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := (hpair (row k)).trans (hnormal k)
  have hcross : (∑ i ∈ s, w i * z i * (r i - z i)) = 0 := by
    rw [hpair (fun i => r i - z i)]
    apply Finset.sum_eq_zero
    intro k _
    change (∑ i ∈ s, w i * row k i * (r i - z i)) * a k = 0
    simp only [mul_sub, Finset.sum_sub_distrib]
    have hobs' : (∑ i ∈ s, w i * row k i * r i) = y k := hobs k
    rw [hobs', hm k, sub_self, zero_mul]
  have henergy : (∑ i ∈ s, w i * (z i)^2) = ∑ k, y k * a k := by
    simpa only [pow_two, ← mul_assoc, hm] using hpair z
  have hs :
      (∑ i ∈ s, w i * (r i)^2) =
        (∑ k, y k * a k) + ∑ i ∈ s, w i * (r i - z i)^2 := by
    calc
      _ = ∑ i ∈ s, (w i * (z i)^2 + w i * (r i - z i)^2 +
          2 * (w i * z i * (r i - z i))) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hcross, henergy]
        simp
  calc
    _ = (∑ i ∈ s, w i * (r i)^2) + w o * (r o)^2 :=
      (Finset.sum_erase_add _ _ (Finset.mem_univ o)).symm
    _ = _ := by rw [hs, hr0, one_pow, mul_one]; ring

end RiemannResearch.Analysis.FiniteWeightedResidual
