/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.RationalInterval

/-!
# Sound finite rational quadratic-form certificates

Source: the complete-Q/P Gram computations in the user's 7 November 2026
canonical and reciprocal-head reviews. Every matrix and vector entry must
already have a proved enclosure; all signed cross terms are retained.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RatInterval
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def bilinear (A : ι → κ → RatInterval) (x : ι → RatInterval)
    (y : κ → RatInterval) : RatInterval :=
  sum Finset.univ (fun i => sum Finset.univ
    (fun j => mul (mul (x i) (A i j)) (y j)))

theorem bilinear_contains
    (AI : ι → κ → RatInterval) (xI : ι → RatInterval) (yI : κ → RatInterval)
    (A : ι → κ → ℝ) (x : ι → ℝ) (y : κ → ℝ)
    (hA : ∀ i j, (AI i j).Contains (A i j))
    (hx : ∀ i, (xI i).Contains (x i)) (hy : ∀ j, (yI j).Contains (y j)) :
    (bilinear AI xI yI).Contains (∑ i, ∑ j, x i * A i j * y j) := by
  apply contains_sum
  intro i _
  apply contains_sum
  intro j _
  exact contains_mul (contains_mul (hx i) (hA i j)) (hy j)

def quadratic (A : ι → ι → RatInterval) (x : ι → RatInterval) : RatInterval :=
  bilinear A x x

theorem quadratic_contains
    (AI : ι → ι → RatInterval) (xI : ι → RatInterval)
    (A : ι → ι → ℝ) (x : ι → ℝ)
    (hA : ∀ i j, (AI i j).Contains (A i j))
    (hx : ∀ i, (xI i).Contains (x i)) :
    (quadratic AI xI).Contains (∑ i, ∑ j, x i * A i j * x j) :=
  bilinear_contains AI xI xI A x x hA hx hx

def linearForm (b : ι → RatInterval) (x : ι → RatInterval) : RatInterval :=
  sum Finset.univ (fun i => mul (b i) (x i))

theorem linearForm_contains
    (bI xI : ι → RatInterval) (b x : ι → ℝ)
    (hb : ∀ i, (bI i).Contains (b i)) (hx : ∀ i, (xI i).Contains (x i)) :
    (linearForm bI xI).Contains (∑ i, b i * x i) :=
  contains_sum _ _ _ (fun i _ => contains_mul (hb i) (hx i))

/-- The full signed approximation-error quadratic, before any square roots.
This includes the target norm and every mixed target/dictionary pairing. -/
def squaredError (targetNorm : RatInterval) (b : ι → RatInterval)
    (A : ι → ι → RatInterval) (x : ι → RatInterval) : RatInterval :=
  add (sub targetNorm (mul (point 2) (linearForm b x))) (quadratic A x)

theorem squaredError_contains
    (nI : RatInterval) (bI xI : ι → RatInterval) (AI : ι → ι → RatInterval)
    (n : ℝ) (b x : ι → ℝ) (A : ι → ι → ℝ)
    (hn : nI.Contains n) (hb : ∀ i, (bI i).Contains (b i))
    (hA : ∀ i j, (AI i j).Contains (A i j))
    (hx : ∀ i, (xI i).Contains (x i)) :
    (squaredError nI bI AI xI).Contains
      (n - 2 * (∑ i, b i * x i) + ∑ i, ∑ j, x i * A i j * x j) :=
  contains_add (contains_sub hn
    (contains_mul (contains_point 2) (linearForm_contains bI xI b x hb hx)))
    (quadratic_contains AI xI A x hA hx)

end RiemannResearch.RatInterval
