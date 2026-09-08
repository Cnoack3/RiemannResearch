import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Tactic.NoncommRing

/-!
# Exact noncommutative compression and perturbation identities

Source: user-provided `RH_Two_Seed_Threshold.tex`, September 8, 2026,
Section 11.2 and 11.4. These are algebraic identities applicable to the
paper's bounded operators. They retain all ordered products and do not
assert that an ordered product defect is positive or compact.
-/

namespace Ring

variable {A : Type*} [Ring A]

/-- The exact ordered-product defect created by an idempotent compression. -/
theorem compression_product_defect (P B C : A) (hP : P * P = P) :
    P * B * C * P - (P * B * P) * (P * C * P) =
      P * B * (1 - P) * C * P := by
  calc
    _ = P * B * C * P - P * B * (P * P) * C * P := by noncomm_ring
    _ = _ := by rw [hP]; noncomm_ring

/-- First-order telescoping of two products; no commutativity is used. -/
theorem product_difference_exact (U₁ U₂ L₁ L₂ : A) :
    U₁ * U₂ - L₁ * L₂ = U₁ * (U₂ - L₂) + (U₁ - L₁) * L₂ := by
  noncomm_ring

/-- The compact-comparison cocycle is algebraic; compactness of the factors
is a separate analytic obligation. The index monoid is unrestricted. -/
theorem hom_difference_cocycle {M : Type*} [Monoid M]
    (U L : M →* A) (m n : M) :
    U (m * n) - L (m * n) =
      U m * (U n - L n) + (U m - L m) * L n := by
  simp only [map_mul]
  noncomm_ring

end Ring

namespace StarRing

variable {A : Type*} [Ring A] [StarRing A]

/-- The full squared compression defect, before invoking any order structure.
This is an exact identity for each operator, including finite combinations. -/
theorem compression_square_defect (P B : A) (hP : P * P = P)
    (hPstar : star P = P) :
    P * star B * B * P - star (P * B * P) * (P * B * P) =
      P * star B * (1 - P) * B * P := by
  simp only [star_mul, hPstar]
  calc
    _ = P * star B * B * P - (P * star B * P) * (P * B * P) := by
      noncomm_ring
    _ = _ := Ring.compression_product_defect P (star B) B hP

/-- For a self-adjoint idempotent, the defect is exactly the square of the
omitted component. Positivity follows in an appropriate ordered star algebra. -/
theorem compression_square_defect_factorization (P B : A) (hP : P * P = P)
    (hPstar : star P = P) :
    P * star B * (1 - P) * B * P =
      star ((1 - P) * B * P) * ((1 - P) * B * P) := by
  have hc : (1 - P) * (1 - P) = 1 - P := by
    calc
      _ = 1 - P - P + P * P := by noncomm_ring
      _ = _ := by rw [hP]; noncomm_ring
  simp only [star_mul, star_sub, star_one, hPstar]
  calc
    _ = P * star B * ((1 - P) * (1 - P)) * B * P := by rw [hc]
    _ = _ := by noncomm_ring

end StarRing



/-!
The following expands every mixed term in the paper's
finite coefficient-dependent projection defect. The family `B i` may
already include its scalar coefficient.
-/

open scoped BigOperators

namespace StarRing

variable {A : Type*} [Ring A] [StarRing A]

theorem compression_finite_gram {ι : Type*} (s : Finset ι) (P : A) (B : ι → A) :
    P * star (∑ i ∈ s, B i) * (1 - P) * (∑ j ∈ s, B j) * P =
      ∑ i ∈ s, ∑ j ∈ s, P * star (B i) * (1 - P) * B j * P := by
  simp only [star_sum, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

theorem compression_square_defect_finite_gram {ι : Type*} (s : Finset ι)
    (P : A) (hP : P * P = P) (hPstar : star P = P) (B : ι → A) :
    P * star (∑ i ∈ s, B i) * (∑ i ∈ s, B i) * P -
        star (P * (∑ i ∈ s, B i) * P) * (P * (∑ i ∈ s, B i) * P) =
      ∑ i ∈ s, ∑ j ∈ s, P * star (B i) * (1 - P) * B j * P := by
  rw [compression_square_defect P _ hP hPstar]
  exact compression_finite_gram s P B

end StarRing
