/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Moving a subgroup conjugator into a kernel

Suppose a subgroup contains an element whose image cancels the image of a
chosen conjugator. Multiplying the conjugator on the right by that element
does not change the conjugated subgroup, but moves the conjugator into the
kernel. For an index-two determinant map, an odd root reflection performs
exactly this correction.
-/

namespace RiemannResearch.GroupTheory

/-- `ConjugateSubgroupBy g H K` says that conjugation by `g` carries `H` to
`K`, expressed without choosing a particular subgroup-conjugation API. -/
def ConjugateSubgroupBy {G : Type*} [Group G]
    (g : G) (H K : Subgroup G) : Prop :=
  ∀ x, x ∈ K ↔ g⁻¹ * x * g ∈ H

private theorem mem_inner_conjugate_iff
    {G : Type*} [Group G] {H : Subgroup G} {r x : G}
    (hr : r ∈ H) :
    r⁻¹ * x * r ∈ H ↔ x ∈ H := by
  constructor
  · intro hx
    have hmem := H.mul_mem (H.mul_mem hr hx) (H.inv_mem hr)
    simpa [mul_assoc] using hmem
  · intro hx
    exact H.mul_mem (H.mul_mem (H.inv_mem hr) hx) hr

/-- Right multiplication by an element of the source subgroup does not
change the subgroup produced by a conjugator. -/
theorem conjugateSubgroupBy_mul_right_iff
    {G : Type*} [Group G] {H K : Subgroup G} {g r : G}
    (hr : r ∈ H) :
    ConjugateSubgroupBy (g * r) H K ↔ ConjugateSubgroupBy g H K := by
  have hmem (x : G) :
      (g * r)⁻¹ * x * (g * r) ∈ H ↔ g⁻¹ * x * g ∈ H := by
    simpa [mul_assoc] using
      (mem_inner_conjugate_iff (H := H) (r := r) (x := g⁻¹ * x * g) hr)
  constructor
  · intro h x
    exact (h x).trans (hmem x)
  · intro h x
    exact (h x).trans (hmem x).symm

/-- If an element of the source subgroup cancels the image of a conjugator,
the same subgroup conjugacy has a conjugator in the homomorphism kernel. -/
theorem exists_mem_ker_conjugator
    {G A : Type*} [Group G] [Group A]
    (φ : G →* A) {H K : Subgroup G} {g r : G}
    (hr : r ∈ H) (hcancel : φ g * φ r = 1)
    (hconj : ConjugateSubgroupBy g H K) :
    ∃ q : G, q ∈ φ.ker ∧ ConjugateSubgroupBy q H K := by
  refine ⟨g * r, ?_, ?_⟩
  · change φ (g * r) = 1
    simpa using hcancel
  · exact (conjugateSubgroupBy_mul_right_iff hr).2 hconj


/-- A simultaneous pointwise conjugator can be moved into a homomorphism
kernel by left multiplication with a centralizer element whose image cancels
the original conjugator's image.  For the A11 certificate, the homomorphism is
the sign map and both cancelling elements are odd permutations. -/
theorem exists_mem_ker_pointwiseConjugator
    {Γ G A : Type*} [Group Γ] [Group G] [Group A]
    (φ : G →* A) (ρX ρY : Γ →* G) {g c : G}
    (hcentral : ∀ σ : Γ, c * ρX σ = ρX σ * c)
    (hcancel : φ c * φ g = 1)
    (hconj : ∀ σ : Γ, ρY σ = g⁻¹ * ρX σ * g) :
    ∃ q : G, q ∈ φ.ker ∧
      ∀ σ : Γ, ρY σ = q⁻¹ * ρX σ * q := by
  refine ⟨c * g, ?_, ?_⟩
  · change φ (c * g) = 1
    simpa using hcancel
  · intro σ
    rw [hconj]
    have hc : c⁻¹ * ρX σ * c = ρX σ := by
      calc
        c⁻¹ * ρX σ * c = c⁻¹ * (ρX σ * c) := by
          simp only [mul_assoc]
        _ = c⁻¹ * (c * ρX σ) := by rw [← hcentral σ]
        _ = ρX σ := by simp
    calc
      g⁻¹ * ρX σ * g =
          g⁻¹ * (c⁻¹ * ρX σ * c) * g := by rw [hc]
      _ = (c * g)⁻¹ * ρX σ * (c * g) := by
        simp only [mul_inv_rev, mul_assoc]

end RiemannResearch.GroupTheory
