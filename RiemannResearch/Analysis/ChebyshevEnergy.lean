/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
/-!
# Chebyshev semi-iteration with exact Hilbert energy
Source: the user-directed displacement continuation, 4 November 2026.
The classical polynomial recurrence is documented in NIST DLMF 3.11.7:
https://dlmf.nist.gov/3.11.E7 . The source supports the recurrence.
The proof below uses a conserved quadratic energy for a symmetric contraction;
no spectral theorem or positivity assumption on the displacement is needed.
The concrete RH consumer is QSquarefreeChebyshev.
-/
noncomputable section
namespace RiemannResearch.Analysis.ChebyshevEnergy
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
def pairEnergy (C : E →L[ℝ] E) (x y : E) : ℝ :=
  inner ℝ x x + inner ℝ y y - 2 * inner ℝ (C x) y
theorem pairEnergy_step (C : E →L[ℝ] E)
    (hs : ∀ x y, inner ℝ (C x) y = inner ℝ x (C y)) (x y : E) :
    pairEnergy C ((2 : ℝ) • C x - y) x = pairEnergy C x y := by
  have h1 := hs (C x) x
  have h2 : inner ℝ (C y) x = inner ℝ (C x) y := by
    rw [hs, real_inner_comm]
  simp only [pairEnergy, inner_sub_left, inner_sub_right,
    inner_smul_left, inner_smul_right, map_sub, map_smul,
    conj_trivial, h1, h2]
  rw [real_inner_comm y (C x)]
  ring

def secondKind (C : E →L[ℝ] E) (d : E) : ℕ → E
  | 0 => 0
  | 1 => d
  | n + 2 => (2 : ℝ) • C (secondKind C d (n + 1)) - secondKind C d n

theorem secondKind_energy (C : E →L[ℝ] E)
    (hs : ∀ x y, inner ℝ (C x) y = inner ℝ x (C y)) (d : E) (n : ℕ) :
    pairEnergy C (secondKind C d (n + 1)) (secondKind C d n) = ‖d‖ ^ 2 := by
  induction n with
  | zero => simp [secondKind, pairEnergy]
  | succ n ih =>
    change pairEnergy C ((2 : ℝ) • C (secondKind C d (n + 1)) -
      secondKind C d n) (secondKind C d (n + 1)) = _
    rw [pairEnergy_step C hs, ih]

def firstKind (C : E →L[ℝ] E) (d : E) (n : ℕ) : E :=
  secondKind C d (n + 1) - C (secondKind C d n)

theorem exact_energy (C : E →L[ℝ] E)
    (hs : ∀ x y, inner ℝ (C x) y = inner ℝ x (C y)) (d : E) (n : ℕ) :
    ‖firstKind C d n‖ ^ 2 + ‖secondKind C d n‖ ^ 2 -
      ‖C (secondKind C d n)‖ ^ 2 = ‖d‖ ^ 2 := by
  have h := secondKind_energy C hs d n
  rw [firstKind, ← real_inner_self_eq_norm_sq,
    ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right]
  have hc := real_inner_comm (C (secondKind C d n)) (secondKind C d (n + 1))
  unfold pairEnergy at h
  rw [hs] at h
  linarith

theorem firstKind_norm_le (C : E →L[ℝ] E)
    (hs : ∀ x y, inner ℝ (C x) y = inner ℝ x (C y))
    (hc : ∀ x, ‖C x‖ ≤ ‖x‖) (d : E) (n : ℕ) :
    ‖firstKind C d n‖ ≤ ‖d‖ := by
  have he := exact_energy C hs d n
  have h := hc (secondKind C d n)
  nlinarith [norm_nonneg (C (secondKind C d n)), norm_nonneg (secondKind C d n),
    norm_nonneg (firstKind C d n), norm_nonneg d]

theorem firstKind_zero (C : E →L[ℝ] E) (d : E) : firstKind C d 0 = d := by
  simp [firstKind, secondKind]
theorem firstKind_one (C : E →L[ℝ] E) (d : E) : firstKind C d 1 = C d := by
  simp [firstKind, secondKind]
  module
theorem firstKind_recurrence (C : E →L[ℝ] E) (d : E) (n : ℕ) :
    firstKind C d (n + 2) =
      (2 : ℝ) • C (firstKind C d (n + 1)) - firstKind C d n := by
  simp only [firstKind, secondKind, map_sub, map_smul]
  module

def denominator : ℕ → ℝ
  | 0 => 1
  | 1 => 3
  | n + 2 => 6 * denominator (n + 1) - denominator n

theorem denominator_growth (n : ℕ) :
    0 < denominator n ∧ 3 * denominator n ≤ denominator (n + 1) := by
  induction n with
  | zero => norm_num [denominator]
  | succ n ih =>
    constructor
    · linarith [ih.1, ih.2]
    · change 3 * denominator (n + 1) ≤ 6 * denominator (n + 1) - denominator n
      nlinarith [ih.1, ih.2]

theorem denominator_pos (n : ℕ) : 0 < denominator n :=
  (denominator_growth n).1

theorem denominator_ratio_le (n : ℕ) :
    denominator (n + 1) ≤ 6 * denominator n := by
  cases n with
  | zero => norm_num [denominator]
  | succ n =>
    change 6 * denominator (n + 1) - denominator n ≤ 6 * denominator (n + 1)
    linarith [denominator_pos n]

theorem denominator_ge_pow (n : ℕ) : (3 : ℝ) ^ n ≤ denominator n := by
  induction n with
  | zero => norm_num [denominator]
  | succ n ih =>
    calc
      (3 : ℝ) ^ (n + 1) = 3 * 3 ^ n := by rw [pow_succ]; ring
      _ ≤ 3 * denominator n := by linarith
      _ ≤ denominator (n + 1) := (denominator_growth n).2

def numerator (C : E →L[ℝ] E) (b : E) : ℕ → E
  | 0 => 0
  | 1 => (4 : ℝ) • b
  | n + 2 => (2 : ℝ) • C (numerator C b (n + 1)) - numerator C b n +
      (8 * denominator (n + 1)) • b

theorem numerator_exact_remainder (C : E →L[ℝ] E) (b d : E)
    (heq : C d = (3 : ℝ) • d - (4 : ℝ) • b) (n : ℕ) :
    denominator n • d - numerator C b n = firstKind C d n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [denominator, numerator, firstKind_zero]
  | one => simpa [denominator, numerator, firstKind_one] using heq.symm
  | more n ih0 ih1 =>
    rw [firstKind_recurrence, ← ih1, ← ih0]
    simp only [denominator, numerator, map_sub, map_smul, heq]
    module

def approximant (C : E →L[ℝ] E) (b : E) (n : ℕ) : E :=
  (denominator n)⁻¹ • numerator C b n

theorem approximant_error (C : E →L[ℝ] E) (b d : E)
    (heq : C d = (3 : ℝ) • d - (4 : ℝ) • b) (n : ℕ) :
    d - approximant C b n = (denominator n)⁻¹ • firstKind C d n := by
  rw [← numerator_exact_remainder C b d heq n, smul_sub, smul_smul,
    inv_mul_cancel₀ (ne_of_gt (denominator_pos n)), one_smul]
  rfl

theorem approximant_error_norm_le (C : E →L[ℝ] E)
    (hs : ∀ x y, inner ℝ (C x) y = inner ℝ x (C y))
    (hc : ∀ x, ‖C x‖ ≤ ‖x‖) (b d : E)
    (heq : C d = (3 : ℝ) • d - (4 : ℝ) • b) (n : ℕ) :
    ‖d - approximant C b n‖ ≤ ‖d‖ / denominator n := by
  rw [approximant_error C b d heq, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (denominator_pos n)), div_eq_mul_inv, mul_comm]
  exact mul_le_mul_of_nonneg_right (firstKind_norm_le C hs hc d n)
    (inv_nonneg.mpr (denominator_pos n).le)

end RiemannResearch.Analysis.ChebyshevEnergy
