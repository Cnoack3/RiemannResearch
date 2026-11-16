/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.HurwitzUniformStripBounds
import RiemannResearch.Analysis.ConreyBaluyotEstermannHurwitzGrowth
import RiemannResearch.Analysis.ConreyBaluyotEstermannMellinKernel
import RiemannResearch.Analysis.DampedGammaStripBounds
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Actual Estermann and Mellin bounds uniform after an explicit modulus factor

The complete finite Hurwitz identity is bounded using the actual uniform
Hurwitz provider. The displayed power of K accounts for all modulus
dependence; the remaining constants are independent of K, numerator class,
and individual shifts in the given real interval.

The Mellin bound retains fixed positive damping. Its Gamma recurrence order
is chosen for the given left edge, so the tail theorem does not require a > -1.
The shifted Hurwitz arguments must still have real part greater than -1.
No assertion uniform as damping approaches the boundary, no uniform mollified
moment, and no Selberg-density conclusion follows from these bounds alone.

Sources: NIST DLMF 25.11.6 (Euler--Maclaurin input),
https://dlmf.nist.gov/25.11.E6;
Baluyot, On the Zeros of Riemann's Zeta-function (2017), equation (3.1.7)
and Lemma 3.1.3, pp. 95--97 (finite identity and contour setting),
https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320.
-/

open Complex Set
noncomputable section

namespace RiemannResearch.Analysis.ConreyBaluyot
open HurwitzUniformStripBounds
open scoped BigOperators

/-- The exponent displaying all dependence on the positive modulus. -/
def uniformModulusExponent (a b A B : ℝ) : ℝ :=
  -2 * a - 2 * A + 2 * (parameterExponent (b + B) + 1)

/-- An explicit bound uniform over all positive moduli, numerator classes and
shifts with real part in [A,B]. The imaginary shifts enter only the threshold. -/
theorem norm_estermann_uniform_modulus_bound {K : ℕ} [NeZero K]
    (h : ZMod K) {a b A B r t : ℝ} {α β : ℂ}
    (ha : -1 < a + A) (hα : α.re ∈ Icc A B) (hβ : β.re ∈ Icc A B)
    (hr : r ∈ Icc a b)
    (ht : max (2 * (1 + |α.im|)) (2 * (1 + |β.im|)) ≤ |t|) :
    ‖estermann h ((r : ℂ) + t * I + α) ((r : ℂ) + t * I + β)‖ ≤
      ((9 / 4 : ℝ) * stripConstant (a + A) (b + B)) ^ 2 *
        (K : ℝ) ^ uniformModulusExponent a b A B * |t| ^ 4 := by
  let C : ℝ := (9 / 4 : ℝ) * stripConstant (a + A) (b + B)
  let p : ℝ := parameterExponent (b + B)
  have hK : 0 < (K : ℝ) := Nat.cast_pos.mpr (NeZero.pos K)
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast NeZero.pos K
  have hC : 0 ≤ C := mul_nonneg (by norm_num) (stripConstant_pos ha).le
  have hbasic := norm_estermann_shifted_le_of_hurwitz_polynomial_bounds h α β 2 2
    (fun _ : ZMod K => C * (K : ℝ) ^ p) (fun _ : ZMod K => C * (K : ℝ) ^ p)
    (fun j x hx y hy =>
      norm_hurwitzZeta_rational_uniform_shift_bound j ha hα hx
        ((le_max_left _ _).trans hy))
    (fun j x hx y hy =>
      norm_hurwitzZeta_rational_uniform_shift_bound j ha hβ hx
        ((le_max_right _ _).trans hy)) r hr t ht
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul,
    Nat.reduceAdd] at hbasic
  have hpower : (K : ℝ) ^ (-2 * a - α.re - β.re) ≤
      (K : ℝ) ^ (-2 * a - 2 * A) :=
    Real.rpow_le_rpow_of_exponent_le hK1 (by linarith [hα.1, hβ.1])
  have hfac : (K : ℝ) ^ (-2 * a - 2 * A + 2 * (p + 1)) =
      (K : ℝ) ^ (-2 * a - 2 * A) * ((K : ℝ) * (K : ℝ) ^ p) ^ 2 := by
    rw [Real.rpow_add hK, show 2 * (p + 1) = (p + 1) * 2 by ring,
      Real.rpow_mul hK.le, Real.rpow_two, Real.rpow_add hK, Real.rpow_one]
    ring
  change ‖estermann h _ _‖ ≤ C ^ 2 *
    (K : ℝ) ^ (-2 * a - 2 * A + 2 * (p + 1)) * |t| ^ 4
  refine hbasic.trans ?_
  calc
    _ ≤ ((K : ℝ) ^ (-2 * a - 2 * A) *
        ((K : ℝ) * (C * (K : ℝ) ^ p)) *
        ((K : ℝ) * (C * (K : ℝ) ^ p))) * |t| ^ 4 := by
      gcongr
    _ = _ := by rw [hfac]; ring


/-- After factoring the displayed power of K, one Cauchy-tail constant works for
all positive moduli, all numerator classes and all shifts in the real interval.
The real strip may start arbitrarily far left; the Gamma recurrence order is
chosen large enough. Positive damping remains fixed. -/
theorem exists_estermannMellinKernel_uniform_modulus_tail {lam : ℂ}
    (hlam : 0 < lam.re) {a b A B : ℝ} (ha : -1 < a + A) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (K : ℕ) [NeZero K], ∀ (h : ZMod K) (α β : ℂ),
      α.re ∈ Icc A B → β.re ∈ Icc A B →
      ∀ r ∈ Icc a b, ∀ t : ℝ,
      max (2 * (1 + |α.im|)) (2 * (1 + |β.im|)) ≤ |t| →
      ‖estermannMellinKernel h α β lam ((r : ℂ) + t * I)‖ ≤
        D * (K : ℝ) ^ uniformModulusExponent a b A B * (1 + t ^ 2)⁻¹ := by
  obtain ⟨n, hn⟩ := exists_nat_gt (-a)
  have hn6 : 0 < a + ((n + 6 : ℕ) : ℝ) := by
    simp only [Nat.cast_add, Nat.cast_ofNat]
    linarith
  obtain ⟨M, hM, hgamma⟩ :=
    Complex.exists_gamma_mul_cpow_neg_strip_pow_bound hlam (b := b) (n + 6) hn6
  let C : ℝ := ((9 / 4 : ℝ) * stripConstant (a + A) (b + B)) ^ 2
  have hC : 0 ≤ C := sq_nonneg _
  refine ⟨2 * M * C, by positivity, ?_⟩
  intro K inst h α β hα hβ r hr t ht
  have htα := (le_max_left (2 * (1 + |α.im|)) (2 * (1 + |β.im|))).trans ht
  have ht1 : 1 ≤ |t| := by linarith [abs_nonneg α.im]
  have ht0 : t ≠ 0 := by intro he; norm_num [he] at ht1
  have hg :
      ‖Gamma ((r : ℂ) + t * I) * lam ^ (-((r : ℂ) + t * I))‖ * |t| ^ 6 ≤ M :=
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ ht1 (by omega : 6 ≤ n + 6)) (norm_nonneg _)).trans
        (hgamma r hr t ht0)
  have hE := norm_estermann_uniform_modulus_bound h ha hα hβ hr ht
  have hsq : 1 + t ^ 2 ≤ 2 * |t| ^ 2 := by nlinarith [sq_abs t]
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity : 0 < 1 + t ^ 2)).mpr
  simp only [estermannMellinKernel, norm_mul]
  calc
    _ ≤ (‖Gamma ((r : ℂ) + t * I)‖ * ‖lam ^ (-((r : ℂ) + t * I))‖) *
        (C * (K : ℝ) ^ uniformModulusExponent a b A B * |t| ^ 4) *
          (2 * |t| ^ 2) := by gcongr
    _ = 2 * C * (K : ℝ) ^ uniformModulusExponent a b A B *
        (‖Gamma ((r : ℂ) + t * I) * lam ^ (-((r : ℂ) + t * I))‖ * |t| ^ 6) := by
      rw [norm_mul]
      ring
    _ ≤ 2 * C * (K : ℝ) ^ uniformModulusExponent a b A B * M :=
      mul_le_mul_of_nonneg_left hg (by positivity)
    _ = _ := by ring

/-- info: 'RiemannResearch.Analysis.ConreyBaluyot.norm_estermann_uniform_modulus_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_estermann_uniform_modulus_bound

/-- info: 'RiemannResearch.Analysis.ConreyBaluyot.exists_estermannMellinKernel_uniform_modulus_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_estermannMellinKernel_uniform_modulus_tail

end RiemannResearch.Analysis.ConreyBaluyot
