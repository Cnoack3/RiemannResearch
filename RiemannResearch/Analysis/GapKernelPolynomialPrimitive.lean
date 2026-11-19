import RiemannResearch.Analysis.GapKernelPolynomial
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exact primitive for Gaussian polynomial moment certificates

Coefficients are ordered from constant to highest degree. The recursive
integer primitive satisfies H-H'=P without any division, so evaluations
at rational cutoffs can be replayed by the Lean kernel.
-/

namespace RiemannResearch.Analysis.GapKernelObjective
open GapKernelPolynomial

def indexed : ℕ → List ℤ → List ℤ
  | _, [] => []
  | k, a :: p => (k : ℤ) * a :: indexed (k+1) p

theorem indexed_succ (p : List ℤ) (x : ℝ) (k : ℕ) :
    value (indexed (k+1) p) x = value (indexed k p) x + value p x := by
  induction p generalizing k with
  | nil => simp [indexed, value]
  | cons a p ih =>
    simp only [indexed, value, Int.cast_mul, Int.cast_add, Int.cast_one, Int.cast_natCast, Nat.cast_add, Nat.cast_one]
    rw [ih (k+1)]
    ring

theorem value_hasDerivAt (p : List ℤ) (x : ℝ) :
    HasDerivAt (value p) (value (indexed 1 p.tail) x) x := by
  induction p with
  | nil => simpa [value, indexed] using (hasDerivAt_const x (0 : ℝ))
  | cons a p ih =>
    change HasDerivAt (fun y : ℝ => (a : ℝ) + y * value p y) (value (indexed 1 p) x) x
    have h := ((hasDerivAt_id x).mul ih).const_add (a : ℝ)
    have hid : value (indexed 1 p) x = value p x + x * value (indexed 1 p.tail) x := by
      calc
        _ = value (indexed 0 p) x + value p x := indexed_succ p x 0
        _ = _ := by cases p <;> simp [indexed, value] <;> ring
    simpa only [hid, Pi.mul_apply, id_eq, one_mul, add_comm, mul_comm] using h

def primitiveFrom : ℕ → List ℤ → List ℤ
  | _, [] => []
  | k, a :: p =>
      let h := primitiveFrom (k+1) p
      (a + (k+1 : ℕ) * h.headD 0 : ℤ) :: h

theorem primitiveFrom_eq (p : List ℤ) (x : ℝ) (k : ℕ) :
    value (primitiveFrom k p) x = value p x + value (indexed (k+1) (primitiveFrom k p).tail) x := by
  induction p generalizing k with
  | nil => simp [primitiveFrom, indexed, value]
  | cons a p ih =>
    have ht := ih (k+1)
    cases he : primitiveFrom (k+1) p with
    | nil =>
      rw [he] at ht
      simp [indexed, value] at ht
      simp [primitiveFrom, he, indexed, value, ht]
    | cons b bs =>
      rw [he] at ht
      simp only [value, List.tail_cons] at ht
      simp only [primitiveFrom, he, value, indexed, List.headD_cons, List.tail_cons,
        Int.cast_add, Int.cast_mul, Int.cast_natCast]
      linear_combination x * ht

theorem primitive_hasDerivAt (p : List ℤ) (y : ℝ) :
    HasDerivAt (value (primitiveFrom 0 p)) (value (primitiveFrom 0 p) y - value p y) y := by
  have he := primitiveFrom_eq p y 0
  convert value_hasDerivAt (primitiveFrom 0 p) y using 1 <;> linarith

def ratValue : List ℤ → ℚ → ℚ
  | [], _ => 0
  | a :: p, x => a + x * ratValue p x

theorem cast_ratValue (p : List ℤ) (x : ℚ) : (ratValue p x : ℝ) = value p (x : ℝ) := by
  induction p with
  | nil => simp [ratValue, value]
  | cons a p ih => simp [ratValue, value, ih]

end RiemannResearch.Analysis.GapKernelObjective
