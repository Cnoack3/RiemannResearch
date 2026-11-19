/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A sound integer-polynomial sign certificate for the small-gap Fourier kernel

Coefficients are in increasing degree order. Exact shifts and rescalings
prove positivity on a bounded interval by subdivision. Translating the
remaining ray makes it possible to verify the unbounded tail from its
ordinary power coefficients. The certificate is checked in the kernel.
-/
namespace RiemannResearch.Analysis.GapKernelPolynomial

def value : List ℤ → ℝ → ℝ
  | [], _ => 0
  | a :: p, x => a + x * value p x

def add : List ℤ → List ℤ → List ℤ
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: add p q

def scale (a : ℤ) (p : List ℤ) : List ℤ := p.map (a * ·)

theorem value_add (p q : List ℤ) (x : ℝ) :
    value (add p q) x = value p x + value q x := by
  induction p generalizing q with
  | nil => simp [add, value]
  | cons a p ih =>
    cases q with
    | nil => simp [add, value]
    | cons b q => simp [add, value, ih]; ring

theorem value_scale (a : ℤ) (p : List ℤ) (x : ℝ) :
    value (scale a p) x = a * value p x := by
  induction p with
  | nil => simp [value, scale]
  | cons b p ih =>
    change ((a*b : ℤ) : ℝ) + x * value (scale a p) x = a * (b + x * value p x)
    rw [Int.cast_mul, ih]
    ring

/-- P(a+x) in ordinary monomial coordinates. -/
def shift (a : ℤ) : List ℤ → List ℤ
  | [] => []
  | b :: p =>
    let q := shift a p
    add [b] (add (scale a q) (0 :: q))

theorem value_shift (p : List ℤ) (a : ℤ) (x : ℝ) :
    value (shift a p) x = value p (a + x) := by
  induction p with
  | nil => simp [shift, value]
  | cons b p ih =>
    simp only [shift, value_add, value_scale, value,
      Int.cast_zero, mul_zero, add_zero, zero_add, ih]
    ring

/-- P(dx) in ordinary monomial coordinates. -/
def inputScale (d : ℤ) : List ℤ → List ℤ
  | [] => []
  | a :: p => a :: scale d (inputScale d p)

theorem value_inputScale (p : List ℤ) (d : ℤ) (x : ℝ) :
    value (inputScale d p) x = value p (d * x) := by
  induction p with
  | nil => rfl
  | cons a p ih => simp only [inputScale, value, value_scale, ih]; ring

/-- Clearing denominators for P(x/d). The uniform positive multiplier is d^length. -/
def clearScale (d : ℤ) : List ℤ → List ℤ
  | [] => []
  | a :: p => d ^ (p.length + 1) * a :: clearScale d p

theorem value_clearScale (p : List ℤ) (d : ℤ) (x : ℝ) :
    value (clearScale d p) (d * x) = (d : ℝ) ^ p.length * value p x := by
  induction p with
  | nil => simp [clearScale, value]
  | cons a p ih =>
    simp only [clearScale, value, ih, List.length_cons, Int.cast_mul, Int.cast_pow, pow_succ]
    ring

/-- A lower bound for Horner evaluation on [0,1]. -/
def unitLower : List ℤ → ℤ
  | [] => 0
  | a :: p => a + min 0 (unitLower p)

theorem unitLower_le (p : List ℤ) {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1) :
    (unitLower p : ℝ) ≤ value p x := by
  induction p with
  | nil => simp [unitLower, value]
  | cons a p ih =>
    simp only [unitLower, Int.cast_add, value, add_le_add_iff_left]
    rcases le_total 0 (unitLower p) with h | h
    · rw [min_eq_left h, Int.cast_zero]
      have h' : 0 ≤ (unitLower p : ℝ) := by exact_mod_cast h
      exact mul_nonneg hx (h'.trans ih)
    · rw [min_eq_right h]
      have hn : (unitLower p : ℝ) ≤ 0 := by exact_mod_cast h
      calc
        _ = 1 * (unitLower p : ℝ) := (one_mul _).symm
        _ ≤ x * (unitLower p : ℝ) := mul_le_mul_of_nonpos_right hx' hn
        _ ≤ x * value p x := mul_le_mul_of_nonneg_left ih hx

def checkUnit : ℕ → List ℤ → Bool
  | 0, p => decide (0 < unitLower p)
  | n + 1, p =>
    decide (0 < unitLower p) ||
      let left := clearScale 2 p
      checkUnit n left && checkUnit n (shift 1 left)

theorem checkUnit_sound (n : ℕ) (p : List ℤ) {x : ℝ}
    (h : checkUnit n p = true) (hx : 0 ≤ x) (hx' : x ≤ 1) : 0 < value p x := by
  induction n generalizing p x with
  | zero =>
    have hl : 0 < unitLower p := by simpa [checkUnit] using h
    exact (Int.cast_pos.mpr hl).trans_le (unitLower_le p hx hx')
  | succ n ih =>
    simp only [checkUnit, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with h | ⟨hl, hr⟩
    · exact (Int.cast_pos.mpr h).trans_le (unitLower_le p hx hx')
    · have hscale : value (clearScale 2 p) (2*x) = (2 : ℝ)^p.length * value p x := by
        simpa using value_clearScale p 2 x
      apply (mul_pos_iff_of_pos_left (show (0 : ℝ) < 2^p.length by positivity)).mp
      rw [← hscale]
      by_cases hm : 2*x ≤ 1
      · exact ih _ hl (by linarith) hm
      · have hright := ih _ (x := 2*x-1) hr (by linarith) (by linarith)
        rw [value_shift] at hright
        simpa only [Int.cast_one, show 1+(2*x-1)=2*x by ring] using hright

theorem nonnegative_value (p : List ℤ) {x : ℝ} (hx : 0 ≤ x)
    (h : p.all (fun a => decide (0 ≤ a)) = true) : 0 ≤ value p x := by
  induction p with
  | nil => simp [value]
  | cons a p ih =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    have ha : (0 : ℝ) ≤ a := by exact_mod_cast h.1
    exact add_nonneg ha (mul_nonneg hx (ih h.2))

def checkRay (p : List ℤ) : Bool :=
  decide (0 < p.headD 0) && p.all (fun a => decide (0 ≤ a))

theorem checkRay_sound (p : List ℤ) {x : ℝ} (hx : 0 ≤ x) (h : checkRay p = true) :
    0 < value p x := by
  cases p with
  | nil => simp [checkRay] at h
  | cons a p =>
    simp only [checkRay, List.headD_cons, Bool.and_eq_true, List.all_cons, decide_eq_true_eq] at h
    have ha : (0 : ℤ) < a := of_decide_eq_true h.1
    exact add_pos_of_pos_of_nonneg (Int.cast_pos.mpr ha) (mul_nonneg hx (nonnegative_value p hx h.2.2))

/-- Cover [0,R] by subdivision and [R,infinity) by translating the ray. -/
def checkHalfLine (fuel : ℕ) (R : ℤ) (p : List ℤ) : Bool :=
  checkUnit fuel (inputScale R p) && checkRay (shift R p)

theorem checkHalfLine_sound (fuel : ℕ) {R : ℤ} (hR : 0 < R) (p : List ℤ) {x : ℝ}
    (hx : 0 ≤ x) (h : checkHalfLine fuel R p = true) : 0 < value p x := by
  simp only [checkHalfLine, Bool.and_eq_true] at h
  have hR' : 0 < (R : ℝ) := Int.cast_pos.mpr hR
  rcases le_total x (R : ℝ) with hle | hge
  · have hpos := checkUnit_sound fuel _ h.1 (div_nonneg hx hR'.le) ((div_le_one hR').mpr hle)
    rw [value_inputScale, show (R : ℝ) * (x / R) = x by field_simp] at hpos
    exact hpos
  · have hpos := checkRay_sound _ (sub_nonneg.mpr hge) h.2
    rwa [value_shift, add_sub_cancel] at hpos

end RiemannResearch.Analysis.GapKernelPolynomial
