/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.NumberTheory.SquarefreeCumulantTower
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Ring.Subring.Defs
/-!
# Compatible restrictions and the infinite projective squarefree algebra
All finite subsets are represented by Boolean masks in a sufficiently large
labeled finite stage. Restrictions are actual ring maps, compose by
intersection, and commute with both cumulant transforms.
The countable prefix tower is cofinal for an enumeration of the primes.
Its inverse limit is a subring of the product, with an explicit universal
property. Logarithm and exponential act levelwise on compatible normalized
coordinates. No analytic convergence is assumed.
Source: user-provided infinite-CRT and cumulant-completion request, 17 October 2026.
-/
noncomputable section
namespace RiemannResearch.NumberTheory.SquarefreeCumulantLimit
open SquarefreeCumulantTower

/-- Scalar extension of a ring map, followed by X ↦ e X. -/
def dualMap {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (e : S) :
    TrivSqZeroExt R R →+* TrivSqZeroExt S S where
  toFun x := (f x.fst, e*f x.snd)
  map_one' := by apply TrivSqZeroExt.ext <;> simp
  map_zero' := by apply TrivSqZeroExt.ext <;> simp
  map_add' x y := by
    apply TrivSqZeroExt.ext
    · change f (x.fst+y.fst) = f x.fst+f y.fst
      exact map_add f _ _
    · change e*f (x.snd+y.snd) = e*f x.snd+e*f y.snd
      rw [map_add, mul_add]
  map_mul' x y := by
    apply TrivSqZeroExt.ext
    · change f (x.fst*y.fst) = f x.fst*f y.fst
      exact map_mul f _ _
    · change e*f (x.fst*y.snd+x.snd*y.fst) =
        f x.fst*(e*f y.snd)+(e*f x.snd)*f y.fst
      rw [map_add, map_mul, map_mul]
      ring

/-- Retain precisely the selected variables; deleted variables are set to zero. -/
def restrictAlgebra : (n : ℕ) → Index n → Algebra n →+* Algebra n
  | 0, _ => RingHom.id ℝ
  | n+1, (b,s) => dualMap (restrictAlgebra n s) (if b then 1 else 0)
def restrictCoordinates : (n : ℕ) → Index n → Coordinates n → Coordinates n
  | 0, _, x => x
  | n+1, (b,s), x => (restrictCoordinates n s x.1,
      (if b then 1 else 0)*restrictAlgebra n s x.2)

theorem restrictCoordinates_add : ∀ (n : ℕ) (s : Index n) (x y : Coordinates n),
    restrictCoordinates n s (x+y) =
      restrictCoordinates n s x+restrictCoordinates n s y := by
  intro n
  induction n with
  | zero => intro s x y; rfl
  | succ n ih =>
    rintro ⟨b,s⟩ x y
    apply Prod.ext
    · exact ih s x.1 y.1
    · change (if b then 1 else 0)*restrictAlgebra n s (x.2+y.2) = _
      rw [map_add, mul_add]
      rfl

theorem restrictCoordinates_neg : ∀ (n : ℕ) (s : Index n) (x : Coordinates n),
    restrictCoordinates n s (-x) = -restrictCoordinates n s x := by
  intro n
  induction n with
  | zero => intro s x; rfl
  | succ n ih =>
    rintro ⟨b,s⟩ x
    apply Prod.ext
    · exact ih s x.1
    · change (if b then 1 else 0)*restrictAlgebra n s (-x.2) = _
      rw [map_neg, mul_neg]
      rfl

theorem moment_restrict : ∀ (n : ℕ) (s : Index n) (x : Coordinates n),
    moment n (restrictCoordinates n s x) = restrictAlgebra n s (moment n x) := by
  intro n
  induction n with
  | zero => intro s x; rfl
  | succ n ih =>
    rintro ⟨b,s⟩ x
    apply TrivSqZeroExt.ext
    · exact ih s x.1
    · rfl

theorem exponential_restrict : ∀ (n : ℕ) (s : Index n) (x : Coordinates n),
    exponential n (restrictCoordinates n s x) =
      restrictAlgebra n s (exponential n x) := by
  intro n
  induction n with
  | zero => intro s x; rfl
  | succ n ih =>
    rintro ⟨b,s⟩ x
    apply TrivSqZeroExt.ext
    · exact ih s x.1
    · change exponential n (restrictCoordinates n s x.1) *
        ((if b then 1 else 0)*restrictAlgebra n s x.2) =
          (if b then 1 else 0)*restrictAlgebra n s (exponential n x.1*x.2)
      rw [ih, map_mul]
      ring

theorem expStar_restrict : ∀ (n : ℕ) (s : Index n) (x : Coordinates n),
    expStar n (restrictCoordinates n s x) =
      restrictCoordinates n s (expStar n x) := by
  intro n
  induction n with
  | zero => intro s x; rfl
  | succ n ih =>
    rintro ⟨b,s⟩ x
    apply Prod.ext
    · exact ih s x.1
    · change exponential n (restrictCoordinates n s x.1) *
        ((if b then 1 else 0)*restrictAlgebra n s x.2) =
          (if b then 1 else 0)*restrictAlgebra n s (exponential n x.1*x.2)
      rw [exponential_restrict, map_mul]
      ring

theorem logStar_restrict (n : ℕ) (s : Index n) (x : Coordinates n) :
    logStar n (restrictCoordinates n s x) =
      restrictCoordinates n s (logStar n x) := by
  have h := expStar_restrict n s (logStar n x)
  rw [expStar_logStar] at h
  rw [← h, logStar_expStar]

theorem star_restrict (n : ℕ) (s : Index n) (x y : Coordinates n) :
    restrictCoordinates n s (star n x y) =
      star n (restrictCoordinates n s x) (restrictCoordinates n s y) := by
  apply moment_injective n
  rw [moment_restrict, moment_star, map_mul, moment_star,
    moment_restrict, moment_restrict]

def intersection : (n : ℕ) → Index n → Index n → Index n
  | 0, _, _ => ()
  | n+1, (b,s), (c,t) => (b && c, intersection n s t)
theorem restrictAlgebra_comp : ∀ (n : ℕ) (s t : Index n) (x : Algebra n),
    restrictAlgebra n s (restrictAlgebra n t x) =
      restrictAlgebra n (intersection n s t) x := by
  intro n
  induction n with
  | zero => intro s t x; rfl
  | succ n ih =>
    rintro ⟨b,s⟩ ⟨c,t⟩ x
    apply TrivSqZeroExt.ext
    · exact ih s t x.fst
    · change (if b then 1 else 0)*restrictAlgebra n s
          ((if c then 1 else 0)*restrictAlgebra n t x.snd) =
            (if b && c then 1 else 0)*restrictAlgebra n (intersection n s t) x.snd
      cases b <;> cases c <;> simp [ih]

theorem restrictCoordinates_comp (n : ℕ) (s t : Index n) (x : Coordinates n) :
    restrictCoordinates n s (restrictCoordinates n t x) =
      restrictCoordinates n (intersection n s t) x := by
  apply moment_injective n
  rw [moment_restrict, moment_restrict, restrictAlgebra_comp, moment_restrict]

/-- The genuine inverse-limit ring, with prefix restrictions X_n ↦ 0. -/
def projectiveAlgebra : Subring ((n : ℕ) → Algebra n) where
  carrier := {x | ∀ n, dropAlgebra n (x (n + 1)) = x n}
  one_mem' := by intro n; rfl
  zero_mem' := by intro n; rfl
  add_mem' := by
    intro x y hx hy n
    change dropAlgebra n (x (n + 1)+y (n + 1)) = x n+y n
    rw [map_add, hx, hy]
  mul_mem' := by
    intro x y hx hy n
    change dropAlgebra n (x (n + 1)*y (n + 1)) = x n*y n
    rw [map_mul, hx, hy]
  neg_mem' := by
    intro x hx n
    change dropAlgebra n (-x (n + 1)) = -x n
    rw [map_neg, hx]
abbrev Completion := projectiveAlgebra

def projectiveCoordinates : AddSubgroup ((n : ℕ) → Coordinates n) where
  carrier := {x | ∀ n, (x (n + 1)).1 = x n}
  zero_mem' := by intro n; rfl
  add_mem' := by
    intro x y hx hy n
    change (x (n + 1)).1+(y (n + 1)).1 = x n+y n
    rw [hx, hy]
  neg_mem' := by
    intro x hx n
    change -(x (n + 1)).1 = -x n
    rw [hx]
abbrev CompletedCoordinates := projectiveCoordinates

def evaluation (n : ℕ) : Completion →+* Algebra n where
  toFun x := x.val n
  map_one' := rfl
  map_zero' := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- Universal property of the projective-limit ring. -/
def lift {R : Type} [CommRing R] (f : (n : ℕ) → R →+* Algebra n)
    (h : ∀ n, (dropAlgebra n).comp (f (n + 1)) = f n) : R →+* Completion where
  toFun r := ⟨fun n => f n r, fun n => congrArg (fun g : R →+* Algebra n => g r) (h n)⟩
  map_one' := by apply Subtype.ext; funext n; exact map_one (f n)
  map_zero' := by apply Subtype.ext; funext n; exact map_zero (f n)
  map_add' x y := by apply Subtype.ext; funext n; exact map_add (f n) x y
  map_mul' x y := by apply Subtype.ext; funext n; exact map_mul (f n) x y

theorem lift_unique {R : Type} [CommRing R] (f g : R →+* Completion)
    (h : ∀ n, (evaluation n).comp f = (evaluation n).comp g) : f = g := by
  apply RingHom.ext
  intro r
  apply Subtype.ext
  funext n
  exact congrArg (fun k : R →+* Algebra n => k r) (h n)

def expStarLimit (x : CompletedCoordinates) : CompletedCoordinates :=
  ⟨fun n => expStar n (x.val n), by
    intro n
    change expStar n ((x.val (n + 1)).1) = expStar n (x.val n)
    rw [x.property n]⟩
def logStarLimit (x : CompletedCoordinates) : CompletedCoordinates :=
  ⟨fun n => logStar n (x.val n), by
    intro n
    change logStar n ((x.val (n + 1)).1) = logStar n (x.val n)
    rw [x.property n]⟩
def starLimit (x y : CompletedCoordinates) : CompletedCoordinates :=
  ⟨fun n => star n (x.val n) (y.val n), by
    intro n
    change star n ((x.val (n + 1)).1) ((y.val (n + 1)).1) = _
    rw [x.property n, y.property n]⟩
def momentLimit (x : CompletedCoordinates) : Completion :=
  ⟨fun n => moment n (x.val n), by
    intro n
    change moment n ((x.val (n + 1)).1) = _
    rw [x.property n]⟩
@[simp] theorem logStarLimit_expStarLimit (x : CompletedCoordinates) :
    logStarLimit (expStarLimit x) = x := by
  apply Subtype.ext
  funext n
  exact logStar_expStar n _
@[simp] theorem expStarLimit_logStarLimit (x : CompletedCoordinates) :
    expStarLimit (logStarLimit x) = x := by
  apply Subtype.ext
  funext n
  exact expStar_logStar n _
theorem expStarLimit_add (x y : CompletedCoordinates) :
    expStarLimit (x+y) = starLimit (expStarLimit x) (expStarLimit y) := by
  apply Subtype.ext
  funext n
  exact expStar_add n _ _
theorem logStarLimit_star (x y : CompletedCoordinates) :
    logStarLimit (starLimit x y) = logStarLimit x+logStarLimit y := by
  apply Subtype.ext
  funext n
  exact logStar_star n _ _
theorem momentLimit_star (x y : CompletedCoordinates) :
    momentLimit (starLimit x y) = momentLimit x*momentLimit y := by
  apply Subtype.ext
  funext n
  exact moment_star n _ _
def completedLogExpEquiv : CompletedCoordinates ≃ CompletedCoordinates where
  toFun := expStarLimit
  invFun := logStarLimit
  left_inv := logStarLimit_expStarLimit
  right_inv := expStarLimit_logStarLimit

/-- A compatible family with arbitrarily assigned singleton moments. -/
def singletonArray (p : ℕ → ℝ) : (n : ℕ) → Algebra n
  | 0 => 1
  | n+1 => (singletonArray p n, scalar n (p n))
def singletonCompletion (p : ℕ → ℝ) : Completion :=
  ⟨singletonArray p, fun _ => rfl⟩
theorem singletonArray_augmentation (p : ℕ → ℝ) : ∀ n,
    augmentation n (singletonArray p n) = 1 := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => exact ih
def singletonCoordinates (p : ℕ → ℝ) : CompletedCoordinates :=
  ⟨fun n => coordinatesOf n (singletonArray p n), fun _ => rfl⟩
theorem singletonCoordinates_moment (p : ℕ → ℝ) :
    momentLimit (singletonCoordinates p) = singletonCompletion p := by
  apply Subtype.ext
  funext n
  exact moment_coordinatesOf n _ (singletonArray_augmentation p n)

/-- A finite polynomial viewed at every level of the projective system. -/
def truncatedFamily (x : Completion) (N : ℕ) : (n : ℕ) → Algebra n
  | 0 => x.val 0
  | n+1 => if n < N then x.val (n+1) else (truncatedFamily x N n, 0)
theorem truncatedFamily_eq (x : Completion) (N n : ℕ) (h : n ≤ N) :
    truncatedFamily x N n = x.val n := by
  cases n with
  | zero => rfl
  | succ n => exact if_pos (Nat.lt_of_succ_le h)
def finiteApproximation (x : Completion) (N : ℕ) : Completion :=
  ⟨truncatedFamily x N, by
    intro n
    by_cases h : n < N
    · calc
        dropAlgebra n (truncatedFamily x N (n+1)) =
            dropAlgebra n (x.val (n+1)) :=
          congrArg (dropAlgebra n) (truncatedFamily_eq x N (n+1) (Nat.succ_le_of_lt h))
        _ = x.val n := x.property n
        _ = truncatedFamily x N n := (truncatedFamily_eq x N n (Nat.le_of_lt h)).symm
    · exact congrArg (dropAlgebra n)
        (if_neg h : truncatedFamily x N (n+1) =
          ((truncatedFamily x N n, 0) : Algebra (n+1)))⟩
/-- Every formal element is eventually exactly correct at each finite stage. -/
theorem finiteApproximation_stabilizes (x : Completion) (n N : ℕ) (h : n ≤ N) :
    evaluation n (finiteApproximation x N) = evaluation n x :=
  truncatedFamily_eq x N n h

end RiemannResearch.NumberTheory.SquarefreeCumulantLimit
