/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.PrimePhaseCRT
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Recovering a complex point from prime-logarithm projections

Source (motivation and geometric notation): *Modular Phase Reconstruction of
Zeta Zeros from Pole Lattices*, pp. 1-3,
https://drive.google.com/file/d/1opJNKzINIeBMDA_k6mr1jEtfW26_-2Cj/view.
We define the projected point directly by the entire exponential
exp(-log(p) * z). These statements do not assert meromorphy of a sum over zeros.

Two distinct prime projections determine every complex point, extending
the real-ordinate injection. A single nontrivial integer base determines the
real part from its radius. The exact signed log-radius identity is retained
before the absolute-error formula. No RH or simplicity premise is used.
-/

noncomputable section
namespace RiemannResearch.Analysis.PrimeLogProjection
open RiemannResearch.RH.PrimePhaseCRT

def projection (p : ℕ) (z : ℂ) : ℂ :=
  Complex.exp (-(Real.log (p : ℝ) : ℂ) * z)

theorem norm_projection (p : ℕ) (z : ℂ) :
    ‖projection p z‖ = Real.exp (-Real.log p * z.re) := by
  rw [projection, Complex.norm_exp]
  congr 1
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, neg_zero, zero_mul, sub_zero]

theorem log_norm_projection (p : ℕ) (z : ℂ) :
    Real.log ‖projection p z‖ = -Real.log p * z.re := by
  rw [norm_projection, Real.log_exp]

theorem re_from_log_radius {p : ℕ} (hp : 1 < p) (z : ℂ) :
    z.re = -Real.log ‖projection p z‖ / Real.log p := by
  have hl : Real.log (p : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hp)).ne'
  rw [log_norm_projection]
  field_simp

theorem norm_projection_eq_iff {p : ℕ} (hp : 1 < p) (z : ℂ) (b : ℝ) :
    ‖projection p z‖ = Real.exp (-Real.log p * b) ↔ z.re = b := by
  rw [norm_projection, Real.exp_injective.eq_iff]
  have hl : Real.log (p : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hp)).ne'
  constructor
  · intro h
    exact (mul_left_cancel₀ (neg_ne_zero.mpr hl)) h
  · intro h
    rw [h]

theorem log_relative_radius (p : ℕ) (z : ℂ) (b : ℝ) :
    Real.log (‖projection p z‖ / Real.exp (-Real.log p * b)) =
      -Real.log p * (z.re - b) := by
  rw [norm_projection, Real.log_div (Real.exp_ne_zero _) (Real.exp_ne_zero _),
    Real.log_exp, Real.log_exp]
  ring

theorem horizontal_error_eq {p : ℕ} (hp : 1 < p) (z : ℂ) (b : ℝ) :
    |z.re - b| =
      |Real.log (‖projection p z‖ / Real.exp (-Real.log p * b))| / Real.log p := by
  have hl : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp)
  rw [log_relative_radius, abs_mul, abs_neg, abs_of_pos hl]
  field_simp

theorem two_prime_projection_injective {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) :
    Function.Injective (fun z : ℂ => (projection p z, projection q z)) := by
  intro z w h
  have he_p := congrArg Prod.fst h
  have he_q := congrArg Prod.snd h
  obtain ⟨a,ha⟩ := Complex.exp_eq_exp_iff_exists_int.mp he_p
  obtain ⟨b,hb⟩ := Complex.exp_eq_exp_iff_exists_int.mp he_q
  have hlp : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hlq : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq.one_lt)
  have hr := congrArg Complex.re ha
  have hi := congrArg Complex.im ha
  have hj := congrArg Complex.im hb
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.intCast_re, Complex.intCast_im,
    show (2 : ℂ).re = 2 from rfl, show (2 : ℂ).im = 0 from rfl,
    Complex.I_re, Complex.I_im, neg_zero, zero_mul, mul_zero, sub_zero,
    add_zero, zero_add, mul_one] at hr hi hj
  have hrel : (a : ℝ) * Real.log q = (b : ℝ) * Real.log p := by
    have hc : ((a : ℝ) * Real.log q - (b : ℝ) * Real.log p) * (2 * Real.pi) = 0 := by
      nlinarith [congrArg (fun x : ℝ => x * Real.log q) hi,
        congrArg (fun x : ℝ => x * Real.log p) hj]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hc).resolve_right
      (mul_ne_zero (by norm_num) Real.pi_ne_zero))
  obtain ⟨ha0,hb0⟩ := intPrimeLogRelation hp hq hpq hrel
  apply Complex.ext
  · nlinarith
  · simp only [ha0, Int.cast_zero, zero_mul, add_zero] at hi
    nlinarith

end RiemannResearch.Analysis.PrimeLogProjection
