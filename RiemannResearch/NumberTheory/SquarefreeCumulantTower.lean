/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.NumberTheory.SquarefreeCumulantPair
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
/-!
# All-order squarefree convolution cumulants
An n-variable algebra is built by adjoining one central square-zero variable
at each step. Its Boolean coefficients have the actual disjoint-subset
convolution product. Coordinates suppress the constant term; moments have
augmentation one. Exponential and logarithm use the exact dual-number
recursions exp(a + X b) = exp(a) (1 + X b) and
log(u + X v) = log(u) + X exp(-log(u)) v.
Source: user-provided log/exp lattice proposal, 16-17 October 2026.
Mathlib's TrivSqZeroExt.Basic supplies the standard square-zero extension.
The two-prime specialization reuses SquarefreeCumulantPair.
No physical norm or floor-dilation multiplication is identified with this ring.
-/
noncomputable section
namespace RiemannResearch.NumberTheory.SquarefreeCumulantTower
@[reducible] def Algebra : ℕ → Type
  | 0 => ℝ
  | n+1 => TrivSqZeroExt (Algebra n) (Algebra n)
@[instance_reducible] private def nextRing (R : Type) [CommRing R] :
    CommRing (TrivSqZeroExt R R) := inferInstance
@[instance_reducible] def algebraRing : (n : ℕ) → CommRing (Algebra n)
  | 0 => inferInstanceAs (CommRing ℝ)
  | n+1 => @nextRing (Algebra n) (algebraRing n)
attribute [instance] algebraRing
@[reducible] def Coordinates : ℕ → Type
  | 0 => Fin 0 → ℝ
  | n+1 => Coordinates n × Algebra n
@[instance_reducible] private def productGroup (V W : Type) [AddCommGroup V] [AddCommGroup W] :
    AddCommGroup (V × W) := inferInstance
@[instance_reducible] def coordinateGroup : (n : ℕ) → AddCommGroup (Coordinates n)
  | 0 => inferInstanceAs (AddCommGroup (Fin 0 → ℝ))
  | n+1 => @productGroup (Coordinates n) (Algebra n)
      (coordinateGroup n) (algebraRing n).toAddCommGroup
attribute [instance] coordinateGroup

@[simp] theorem snd_mul (n : ℕ) (x y : Algebra (n + 1)) :
    (x*y).snd = x.fst*y.snd+x.snd*y.fst := by
  exact TrivSqZeroExt.snd_mul x y

def moment : (n : ℕ) → Coordinates n → Algebra n
  | 0, _ => 1
  | n+1, x => (moment n x.1, x.2)
def exponential : (n : ℕ) → Coordinates n → Algebra n
  | 0, _ => 1
  | n+1, x => (exponential n x.1, exponential n x.1 * x.2)

theorem exponential_add : ∀ (n : ℕ) (x y : Coordinates n),
    exponential n (x+y) = exponential n x * exponential n y := by
  intro n
  induction n with
  | zero => intro x y; simp [exponential]
  | succ n ih =>
    intro x y
    apply TrivSqZeroExt.ext
    · change exponential n (x.1+y.1) = exponential n x.1 * exponential n y.1
      exact ih _ _
    · change exponential n (x.1+y.1)*(x.2+y.2) =
        exponential n x.1*(exponential n y.1*y.2) +
          (exponential n x.1*x.2)*exponential n y.1
      rw [ih]
      ring

@[simp] theorem exponential_zero : ∀ n, exponential n 0 = 1 := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    apply TrivSqZeroExt.ext
    · change exponential n 0 = 1
      exact ih
    · change exponential n 0 * 0 = 0
      exact mul_zero _

theorem exponential_neg_mul (n : ℕ) (x : Coordinates n) :
    exponential n (-x) * exponential n x = 1 := by
  rw [← exponential_add, neg_add_cancel, exponential_zero]
theorem exponential_mul_neg (n : ℕ) (x : Coordinates n) :
    exponential n x * exponential n (-x) = 1 := by
  rw [mul_comm, exponential_neg_mul]

def expStar : (n : ℕ) → Coordinates n → Coordinates n
  | 0, x => x
  | n+1, x => (expStar n x.1, exponential n x.1*x.2)
def logStar : (n : ℕ) → Coordinates n → Coordinates n
  | 0, x => x
  | n+1, x => (logStar n x.1, exponential n (-logStar n x.1)*x.2)

@[simp] theorem moment_expStar : ∀ (n : ℕ) (x : Coordinates n),
    moment n (expStar n x) = exponential n x := by
  intro n
  induction n with
  | zero => intro x; rfl
  | succ n ih =>
    intro x
    apply TrivSqZeroExt.ext
    · exact ih _
    · rfl

@[simp] theorem logStar_expStar : ∀ (n : ℕ) (x : Coordinates n),
    logStar n (expStar n x) = x := by
  intro n
  induction n with
  | zero => intro x; rfl
  | succ n ih =>
    intro x
    apply Prod.ext
    · exact ih _
    · change exponential n (-logStar n (expStar n x.1)) *
        (exponential n x.1*x.2) = x.2
      rw [ih, ← mul_assoc, exponential_neg_mul, one_mul]

@[simp] theorem expStar_logStar : ∀ (n : ℕ) (x : Coordinates n),
    expStar n (logStar n x) = x := by
  intro n
  induction n with
  | zero => intro x; rfl
  | succ n ih =>
    intro x
    apply Prod.ext
    · exact ih _
    · change exponential n (logStar n x.1) *
        (exponential n (-logStar n x.1)*x.2) = x.2
      rw [← mul_assoc, exponential_mul_neg, one_mul]

def star : (n : ℕ) → Coordinates n → Coordinates n → Coordinates n
  | 0, x, _ => x
  | n+1, x, y => (star n x.1 y.1, moment n x.1*y.2+x.2*moment n y.1)

theorem expStar_add : ∀ (n : ℕ) (x y : Coordinates n),
    expStar n (x+y) = star n (expStar n x) (expStar n y) := by
  intro n
  induction n with
  | zero =>
    intro x y
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    intro x y
    apply Prod.ext
    · exact ih _ _
    · change exponential n (x.1+y.1)*(x.2+y.2) =
        moment n (expStar n x.1)*(exponential n y.1*y.2) +
          (exponential n x.1*x.2)*moment n (expStar n y.1)
      rw [exponential_add, moment_expStar, moment_expStar]
      ring

theorem logStar_star (n : ℕ) (x y : Coordinates n) :
    logStar n (star n x y) = logStar n x+logStar n y := by
  have h := expStar_add n (logStar n x) (logStar n y)
  rw [expStar_logStar, expStar_logStar] at h
  rw [← h, logStar_expStar]

def logExpEquiv (n : ℕ) : Coordinates n ≃ Coordinates n where
  toFun := expStar n
  invFun := logStar n
  left_inv := logStar_expStar n
  right_inv := expStar_logStar n

theorem moment_star : ∀ (n : ℕ) (x y : Coordinates n),
    moment n (star n x y) = moment n x * moment n y := by
  intro n
  induction n with
  | zero => intro x y; simp [moment]
  | succ n ih =>
    intro x y
    apply TrivSqZeroExt.ext
    · exact ih _ _
    · rfl

theorem moment_injective : ∀ n, Function.Injective (moment n) := by
  intro n
  induction n with
  | zero =>
    intro x y h
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    intro x y h
    apply Prod.ext
    · exact ih (congrArg TrivSqZeroExt.fst h)
    · exact congrArg (fun z : Algebra (n + 1) => z.snd) h

theorem star_assoc (n : ℕ) (x y z : Coordinates n) :
    star n (star n x y) z = star n x (star n y z) := by
  apply moment_injective n
  simp only [moment_star, mul_assoc]
theorem star_comm (n : ℕ) (x y : Coordinates n) :
    star n x y = star n y x := by
  apply moment_injective n
  simp only [moment_star, mul_comm]

def dropAlgebra (n : ℕ) : Algebra (n + 1) →+* Algebra n where
  toFun := TrivSqZeroExt.fst
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
def augmentation : (n : ℕ) → Algebra n →+* ℝ
  | 0 => RingHom.id ℝ
  | n+1 => (augmentation n).comp (dropAlgebra n)

theorem power_snd (n k : ℕ) (x : Algebra (n + 1)) :
    (x^(k+1)).snd = (k+1 : Algebra n)*x.fst^k*x.snd := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, snd_mul, ih, TrivSqZeroExt.fst_pow]
    push_cast
    ring

theorem augmentation_nilpotent : ∀ (n : ℕ) (x : Algebra n),
    augmentation n x = 0 → x^(n + 1) = 0 := by
  intro n
  induction n with
  | zero => intro x hx; simpa [augmentation] using hx
  | succ n ih =>
    intro x hx
    have h := ih x.fst hx
    apply TrivSqZeroExt.ext
    · change (x^(n+1+1)).fst = 0
      rw [TrivSqZeroExt.fst_pow, pow_succ, h, zero_mul]
    · rw [power_snd, h, mul_zero, zero_mul]
      rfl

@[simp] theorem augmentation_exponential : ∀ (n : ℕ) (x : Coordinates n),
    augmentation n (exponential n x) = 1 := by
  intro n
  induction n with
  | zero => intro x; rfl
  | succ n ih => intro x; exact ih x.1

def fromPair (x : RiemannResearch.NumberTheory.SquarefreeCumulantPair.Coordinates) :
    Coordinates 2 := ((fun i => Fin.elim0 i, x.1), (x.2.1, x.2.2))
theorem expStar_pair (x : RiemannResearch.NumberTheory.SquarefreeCumulantPair.Coordinates) :
    expStar 2 (fromPair x) =
      fromPair (RiemannResearch.NumberTheory.SquarefreeCumulantPair.expStar x) := by
  rcases x with ⟨a,b,c⟩
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · exact one_mul a
  · apply TrivSqZeroExt.ext
    · change dropAlgebra 0 ((exponential 1 (fromPair (a,b,c)).1) *
          (fromPair (a,b,c)).2) = _
      rw [map_mul]
      change 1*b = b
      exact one_mul b
    · change ((exponential 1 (fromPair (a,b,c)).1) * (fromPair (a,b,c)).2).snd = _
      rw [snd_mul]
      change 1*c+(1*a)*b = c+a*b
      ring
theorem logStar_pair (x : RiemannResearch.NumberTheory.SquarefreeCumulantPair.Coordinates) :
    logStar 2 (fromPair x) =
      fromPair (RiemannResearch.NumberTheory.SquarefreeCumulantPair.logStar x) := by
  have h := expStar_pair (RiemannResearch.NumberTheory.SquarefreeCumulantPair.logStar x)
  rw [RiemannResearch.NumberTheory.SquarefreeCumulantPair.expStar_logStar] at h
  rw [← h, logStar_expStar]


/-- A Boolean choice for each variable, encoded recursively. -/
@[reducible] def Index : ℕ → Type
  | 0 => Unit
  | n+1 => Bool × Index n
@[instance_reducible] private def nextFintype (I : Type) [Fintype I] :
    Fintype (Bool × I) := inferInstance
@[instance_reducible] def indexFintype : (n : ℕ) → Fintype (Index n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n+1 => @nextFintype (Index n) (indexFintype n)
attribute [instance] indexFintype
def coefficient : (n : ℕ) → Algebra n → Index n → ℝ
  | 0, a, _ => a
  | n+1, a, (b,s) => if b then coefficient n a.snd s else coefficient n a.fst s
def assemble : (n : ℕ) → (Index n → ℝ) → Algebra n
  | 0, a => a ()
  | n+1, a => (assemble n (fun s => a (false,s)), assemble n (fun s => a (true,s)))
@[simp] theorem coefficient_assemble : ∀ (n : ℕ) (a : Index n → ℝ) (s : Index n),
    coefficient n (assemble n a) s = a s := by
  intro n
  induction n with
  | zero => intro a s; cases s; rfl
  | succ n ih =>
    rintro a ⟨b,s⟩
    cases b <;> simp [coefficient, assemble, ih]
@[simp] theorem assemble_coefficient : ∀ (n : ℕ) (a : Algebra n),
    assemble n (coefficient n a) = a := by
  intro n
  induction n with
  | zero => intro a; rfl
  | succ n ih =>
    intro a
    apply TrivSqZeroExt.ext <;> simpa [assemble, coefficient] using ih _
def coefficientEquiv (n : ℕ) : Algebra n ≃ (Index n → ℝ) where
  toFun := coefficient n
  invFun := assemble n
  left_inv := assemble_coefficient n
  right_inv a := funext (coefficient_assemble n a)
theorem coefficient_add : ∀ (n : ℕ) (a b : Algebra n) (s : Index n),
    coefficient n (a+b) s = coefficient n a s+coefficient n b s := by
  intro n
  induction n with
  | zero => intro a b s; rfl
  | succ n ih =>
    rintro a b ⟨e,s⟩
    cases e <;> exact ih _ _ s
/-- The actual disjoint-subset convolution, recursively split at the last variable. -/
def convolution : (n : ℕ) → (Index n → ℝ) → (Index n → ℝ) → Index n → ℝ
  | 0, a, b, _ => a ()*b ()
  | n+1, a, b, (false,s) =>
      convolution n (fun t => a (false,t)) (fun t => b (false,t)) s
  | n+1, a, b, (true,s) =>
      convolution n (fun t => a (false,t)) (fun t => b (true,t)) s+
      convolution n (fun t => a (true,t)) (fun t => b (false,t)) s
theorem coefficient_mul : ∀ (n : ℕ) (a b : Algebra n) (s : Index n),
    coefficient n (a*b) s =
      convolution n (coefficient n a) (coefficient n b) s := by
  intro n
  induction n with
  | zero => intro a b s; rfl
  | succ n ih =>
    rintro a b ⟨e,s⟩
    cases e
    · exact ih a.fst b.fst s
    · change coefficient n ((a*b).snd) s = _
      rw [snd_mul, coefficient_add, ih, ih]
      rfl


@[simp] theorem augmentation_moment : ∀ (n : ℕ) (x : Coordinates n),
    augmentation n (moment n x) = 1 := by
  intro n
  induction n with
  | zero => intro x; rfl
  | succ n ih => intro x; exact ih x.1

def coordinatesOf : (n : ℕ) → Algebra n → Coordinates n
  | 0, _ => fun i => Fin.elim0 i
  | n+1, a => (coordinatesOf n a.fst, a.snd)
@[simp] theorem coordinatesOf_moment : ∀ (n : ℕ) (x : Coordinates n),
    coordinatesOf n (moment n x) = x := by
  intro n
  induction n with
  | zero => intro x; funext i; exact Fin.elim0 i
  | succ n ih => intro x; exact Prod.ext (ih _) rfl
theorem moment_coordinatesOf : ∀ (n : ℕ) (a : Algebra n),
    augmentation n a = 1 → moment n (coordinatesOf n a) = a := by
  intro n
  induction n with
  | zero => intro a ha; exact ha.symm
  | succ n ih =>
    intro a ha
    exact TrivSqZeroExt.ext (ih a.fst ha) rfl


/-- The empty subset and scalar embedding. -/
def emptyIndex : (n : ℕ) → Index n
  | 0 => ()
  | n+1 => (false, emptyIndex n)
@[instance_reducible] private def nextDecidableEq (I : Type) [DecidableEq I] :
    DecidableEq (Bool × I) := inferInstance
@[instance_reducible] def indexDecidableEq : (n : ℕ) → DecidableEq (Index n)
  | 0 => inferInstanceAs (DecidableEq Unit)
  | n+1 => @nextDecidableEq (Index n) (indexDecidableEq n)
attribute [instance] indexDecidableEq
def scalar : (n : ℕ) → ℝ → Algebra n
  | 0, r => r
  | n+1, r => (scalar n r, 0)
@[simp] theorem coefficient_zero : ∀ (n : ℕ) (s : Index n),
    coefficient n 0 s = 0 := by
  intro n
  induction n with
  | zero => intro s; rfl
  | succ n ih => rintro ⟨b,s⟩; cases b <;> exact ih s
@[simp] theorem coefficient_scalar : ∀ (n : ℕ) (r : ℝ) (s : Index n),
    coefficient n (scalar n r) s = if s = emptyIndex n then r else 0 := by
  intro n
  induction n with
  | zero => intro r s; cases s; simp [coefficient, scalar, emptyIndex]
  | succ n ih =>
    rintro r ⟨b,s⟩
    cases b <;> simp [coefficient, scalar, emptyIndex, ih]
theorem coefficient_empty : ∀ (n : ℕ) (a : Algebra n),
    coefficient n a (emptyIndex n) = augmentation n a := by
  intro n
  induction n with
  | zero => intro a; rfl
  | succ n ih => intro a; exact ih a.fst

end RiemannResearch.NumberTheory.SquarefreeCumulantTower
