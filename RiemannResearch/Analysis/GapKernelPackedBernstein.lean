/-
Copyright (c) 2026 RiemannResearch contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.GapKernelBernsteinRay

/-!
# Exact integer packing for Bernstein subdivision

A single Horner evaluation at a power of two encodes every shifted
coefficient. A bound on their total absolute mass makes signed digit
decoding exact. The fast checker computes the same Boolean as ordinary
Bernstein subdivision, including the test on the unbounded piece.
-/

namespace RiemannResearch.Analysis.GapKernelPolynomial

private def mass : List ℤ → ℤ
  | [] => 0
  | a :: p => |a| + mass p

private theorem mass_nonneg (p : List ℤ) : 0 ≤ mass p := by
  induction p with
  | nil => rfl
  | cons a p ih => exact add_nonneg (abs_nonneg a) ih

private theorem mass_add_le (p q : List ℤ) : mass (add p q) ≤ mass p + mass q := by
  induction p generalizing q with
  | nil => simp [mass, add]
  | cons a p ih =>
    cases q with
    | nil => simp [mass, add]
    | cons b q =>
      simp only [add, mass]
      linarith only [abs_add_le a b, ih q]

private theorem mass_scale_two (p : List ℤ) : mass (scale 2 p) = 2 * mass p := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    change |2 * a| + mass (scale 2 p) = 2 * (|a| + mass p)
    rw [abs_mul, ih, abs_of_pos (by decide : (0 : ℤ) < 2)]
    ring

private def rightBound : List ℤ → ℤ
  | [] => 0
  | a :: p => |a| + 3 * rightBound p

private theorem mass_right_le (p : List ℤ) : mass (bernsteinRight p) ≤ rightBound p := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    let q := bernsteinRight p
    have h := mass_add_le [a] (add q (0 :: scale 2 q))
    have h' := mass_add_le q (0 :: scale 2 q)
    change mass (add [a] (add q (0 :: scale 2 q))) ≤ |a| + 3 * rightBound p
    simp only [mass, abs_zero, zero_add, add_zero, mass_scale_two] at h h'
    change mass q ≤ rightBound p at ih
    linarith only [h,h',ih]

private theorem length_add (p q : List ℤ) : (add p q).length = max p.length q.length := by
  induction p generalizing q with
  | nil => simp [add]
  | cons a p ih =>
    cases q with
    | nil => simp [add]
    | cons b q => simp only [add, List.length_cons, ih]; omega

private theorem length_right (p : List ℤ) : (bernsteinRight p).length = p.length := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [bernsteinRight, length_add, List.length_cons, List.length_nil,
      scale, List.length_map, ih]
    omega

private def evalInt (base : ℤ) : List ℤ → ℤ
  | [] => 0
  | a :: p => a + base * evalInt base p

private theorem cast_evalInt (p : List ℤ) (base : ℤ) :
    (evalInt base p : ℝ) = value p base := by
  induction p with
  | nil => simp [evalInt, value]
  | cons a p ih => simp only [evalInt, value, Int.cast_add, Int.cast_mul, ih]

private theorem evalInt_right (p : List ℤ) (base : ℤ) :
    evalInt base (bernsteinRight p) = evalInt (1 + 2 * base) p := by
  apply (Int.cast_injective (α := ℝ))
  simp only [cast_evalInt, value_bernsteinRight, Int.cast_add, Int.cast_mul,
    Int.cast_one, Int.cast_ofNat]

private def digits (half : ℤ) : ℕ → ℤ → List ℤ
  | 0, _ => []
  | n+1, z =>
    let a := (z + half) % (2 * half) - half
    a :: digits half n ((z - a) / (2 * half))

private theorem digits_eval (p : List ℤ) {b : ℤ} (h : mass p < b) :
    digits b p.length (evalInt (2 * b) p) = p := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    have hp := mass_nonneg p
    have ha := abs_nonneg a
    change |a| + mass p < b at h
    have hlo := neg_abs_le a
    have hhi := le_abs_self a
    have hb : 2 * b ≠ 0 := by omega
    let z := evalInt (2 * b) p
    have hrem : (a + 2 * b * z + b) % (2 * b) = a + b := by
      rw [show a + 2 * b * z + b = a + b + (2 * b) * z by ring,
        Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]
    change ((a + 2 * b * z + b) % (2 * b) - b) ::
      digits b p.length ((a + 2 * b * z - ((a + 2 * b * z + b) % (2 * b) - b)) /
        (2 * b)) = a :: p
    rw [hrem, add_sub_cancel_right, add_sub_cancel_left, Int.mul_ediv_cancel_left _ hb]
    exact congrArg (List.cons a) (ih (by omega))

/-- Recover every coefficient of P(1+2x) from one integer evaluation.
The ordinary shift is a total fallback when the supplied radix is small. -/
def packedBernsteinRight (p : List ℤ) : List ℤ :=
  let bound := rightBound p
  let half := (2 : ℤ) ^ (bound.toNat.log2 + 1)
  if bound < half then digits half p.length (evalInt (1 + 2 * (2 * half)) p)
  else bernsteinRight p

theorem packedBernsteinRight_eq (p : List ℤ) : packedBernsteinRight p = bernsteinRight p := by
  dsimp only [packedBernsteinRight]
  split
  next h =>
    rw [← evalInt_right, ← length_right p]
    exact digits_eval _ ((mass_right_le p).trans_lt h)
  next => rfl

/-- Validate a proposed shifted row by comparing one packed integer per side.
The strict mass bounds make that comparison injective on both rows. -/
def certifyBernsteinRight (p q : List ℤ) : Bool :=
  let b := (2 : ℤ) ^ ((max (rightBound p) (mass q)).toNat.log2 + 1)
  decide (rightBound p < b ∧ mass q < b ∧ p.length = q.length ∧
    evalInt (1 + 2 * (2 * b)) p = evalInt (2 * b) q)

theorem certifyBernsteinRight_sound (p q : List ℤ) (h : certifyBernsteinRight p q = true) :
    bernsteinRight p = q := by
  let b := (2 : ℤ) ^ ((max (rightBound p) (mass q)).toNat.log2 + 1)
  change decide (rightBound p < b ∧ mass q < b ∧ p.length = q.length ∧
    evalInt (1 + 2 * (2 * b)) p = evalInt (2 * b) q) = true at h
  rcases of_decide_eq_true h with ⟨hp, hq, hn, he⟩
  rw [← evalInt_right] at he
  calc
    _ = digits b (bernsteinRight p).length (evalInt (2 * b) (bernsteinRight p)) :=
      (digits_eval _ ((mass_right_le p).trans_lt hp)).symm
    _ = digits b q.length (evalInt (2 * b) q) := by rw [length_right, hn, he]
    _ = _ := digits_eval _ hq

/-- The original sign test, with exact signed digit packing at each split. -/
def checkPackedRay : ℕ → List ℤ → Bool
  | 0, p => checkRay p
  | n+1, p => checkRay p || (decide (0 < p.headD 0) &&
      (checkPackedRay n (packedBernsteinRight p.reverse).reverse &&
       checkPackedRay n (packedBernsteinRight p)))

theorem checkPackedRay_eq (n : ℕ) (p : List ℤ) :
    checkPackedRay n p = checkBernsteinRay n p := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih => simp only [checkPackedRay, checkBernsteinRay, ih, packedBernsteinRight_eq]

end RiemannResearch.Analysis.GapKernelPolynomial
