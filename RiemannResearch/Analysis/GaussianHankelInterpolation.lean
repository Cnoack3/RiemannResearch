/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ConjugatePairHankel
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
Constructive finite real interpolation and exact infinite contamination budgets.

This module does not assume or prove the analytic vanishing-tail provider.  It
separates that obligation from finite interpolation.  The real polynomial uses
quadratic factors, so the finite set itself need not be closed under conjugation.
Nodes are distinct elements of a finite set; analytic multiplicities belong in
the weight function, not in repeated factors.

Source: user-provided Gaussian interpolation argument. Polynomial negative-witness
strategy also appears in Bickel, Pascoe and Sargent, Zero-free regions near a line,
Section 1 (https://arxiv.org/abs/2108.04807); the quadratic construction and sharp
infinite budget below are independently developed adaptations.

The full sum below is over complex nodes.  A zero spectrum can be embedded by
giving weight zero to nodes outside its carrier, or the generic real-tail
lemmas can be used directly on the carrier subtype.
-/

noncomputable section

namespace RiemannResearch.Analysis.GaussianHankelInterpolation

open scoped BigOperators Topology Polynomial
open Filter Polynomial
open RiemannResearch.Analysis.ConjugatePairHankel

/-- Evaluation of a real polynomial at a complex node. -/
def evalC (p : ℝ[X]) (z : ℂ) : ℂ := p.eval₂ Complex.ofRealHom z

/-- A real quadratic whose complex roots are a node and its conjugate. -/
def conjugateQuadratic (z : ℂ) : ℝ[X] :=
  (X - C z.re) ^ 2 + C (z.im ^ 2)

theorem conjugateQuadratic_eval (z u : ℂ) :
    evalC (conjugateQuadratic z) u = (u - z) * (u - (starRingEnd ℂ) z) := by
  simp only [evalC, conjugateQuadratic, Polynomial.eval₂_add,
    Polynomial.eval₂_pow, Polynomial.eval₂_sub, Polynomial.eval₂_X,
    Polynomial.eval₂_C, Complex.ofRealHom_eq_coe]
  apply Complex.ext <;>
    simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.conj_re, Complex.conj_im] <;> ring

theorem conjugateQuadratic_eval_self (z : ℂ) :
    evalC (conjugateQuadratic z) z = 0 := by
  simp [conjugateQuadratic_eval]

theorem conjugateQuadratic_eval_ne_zero {z u : ℂ}
    (hu : u ≠ z) (huc : u ≠ (starRingEnd ℂ) z) :
    evalC (conjugateQuadratic z) u ≠ 0 := by
  rw [conjugateQuadratic_eval]
  exact mul_ne_zero (sub_ne_zero.mpr hu) (sub_ne_zero.mpr huc)

/-- A product over distinct unwanted nodes.  Conjugate factors may be redundant. -/
noncomputable def annihilator (s : Finset ℂ) : ℝ[X] :=
  ∏ z ∈ s, conjugateQuadratic z

theorem annihilator_eval (s : Finset ℂ) (u : ℂ) :
    evalC (annihilator s) u = ∏ z ∈ s, evalC (conjugateQuadratic z) u := by
  exact Polynomial.eval₂_finsetProd Complex.ofRealHom s conjugateQuadratic u

theorem annihilator_eval_zero {s : Finset ℂ} {u : ℂ} (hu : u ∈ s) :
    evalC (annihilator s) u = 0 := by
  classical
  rw [annihilator_eval]
  exact Finset.prod_eq_zero hu (conjugateQuadratic_eval_self u)

theorem annihilator_eval_ne_zero {s : Finset ℂ} {u : ℂ}
    (hs : ∀ z ∈ s, z ≠ u ∧ z ≠ (starRingEnd ℂ) u) :
    evalC (annihilator s) u ≠ 0 := by
  classical
  rw [annihilator_eval]
  apply Finset.prod_ne_zero_iff.mpr
  intro z hz
  have hzu := (hs z hz).1
  have hzc := (hs z hz).2
  apply conjugateQuadratic_eval_ne_zero (Ne.symm hzu)
  intro h
  apply hzc
  simpa using (congrArg (starRingEnd ℂ) h).symm

/-- The unique real affine polynomial assigning `ξ` at a nonreal node `z`. -/
def affineAt (z ξ : ℂ) : ℝ[X] :=
  C (ξ.im / z.im) * X + C (ξ.re - (ξ.im / z.im) * z.re)

theorem affineAt_eval {z : ℂ} (hz : z.im ≠ 0) (ξ : ℂ) :
    evalC (affineAt z ξ) z = ξ := by
  simp only [evalC, affineAt, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Complex.ofRealHom_eq_coe]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero]
    exact div_mul_cancel₀ ξ.im hz

theorem evalC_star (p : ℝ[X]) (z : ℂ) :
    evalC p ((starRingEnd ℂ) z) = (starRingEnd ℂ) (evalC p z) := by
  have hh : Polynomial.eval₂RingHom Complex.ofRealHom ((starRingEnd ℂ) z) =
      (starRingEnd ℂ).comp (Polynomial.eval₂RingHom Complex.ofRealHom z) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp
    · simp
  exact congrArg (fun h : ℝ[X] →+* ℂ => h p) hh

/-- Explicit real interpolant after annihilating a finite set of other nodes. -/
noncomputable def interpolant (s : Finset ℂ) (z ξ : ℂ) : ℝ[X] :=
  affineAt z (ξ / evalC (annihilator s) z) * annihilator s

theorem interpolant_eval {s : Finset ℂ} {z : ℂ} (hz : z.im ≠ 0)
    (hs : ∀ u ∈ s, u ≠ z ∧ u ≠ (starRingEnd ℂ) z) (ξ : ℂ) :
    evalC (interpolant s z ξ) z = ξ := by
  simp only [evalC, interpolant, Polynomial.eval₂_mul]
  change evalC (affineAt z (ξ / evalC (annihilator s) z)) z *
    evalC (annihilator s) z = ξ
  rw [affineAt_eval hz]
  exact div_mul_cancel₀ ξ (annihilator_eval_ne_zero hs)

theorem interpolant_eval_star {s : Finset ℂ} {z : ℂ} (hz : z.im ≠ 0)
    (hs : ∀ u ∈ s, u ≠ z ∧ u ≠ (starRingEnd ℂ) z) (ξ : ℂ) :
    evalC (interpolant s z ξ) ((starRingEnd ℂ) z) = (starRingEnd ℂ) ξ := by
  rw [evalC_star, interpolant_eval hz hs]

theorem interpolant_eval_zero {s : Finset ℂ} {u : ℂ} (hu : u ∈ s)
    (z ξ : ℂ) : evalC (interpolant s z ξ) u = 0 := by
  simp only [evalC, interpolant, Polynomial.eval₂_mul]
  change evalC (affineAt z (ξ / evalC (annihilator s) z)) u *
    evalC (annihilator s) u = 0
  rw [annihilator_eval_zero hu, mul_zero]

/-- Arbitrary assignment at one nonreal pair with exact zeros at the finite remainder. -/
theorem exists_real_interpolant {s : Finset ℂ} {z : ℂ} (hz : z.im ≠ 0)
    (hs : ∀ u ∈ s, u ≠ z ∧ u ≠ (starRingEnd ℂ) z) (ξ : ℂ) :
    ∃ p : ℝ[X], evalC p z = ξ ∧ evalC p ((starRingEnd ℂ) z) = (starRingEnd ℂ) ξ ∧
      ∀ u ∈ s, evalC p u = 0 := by
  refine ⟨interpolant s z ξ, interpolant_eval hz hs ξ,
    interpolant_eval_star hz hs ξ, ?_⟩
  intro u hu
  exact interpolant_eval_zero hu z ξ

/-- The real contribution of one weighted node to a polynomial square form. -/
def squareTerm (w : ℂ → ℂ) (p : ℝ[X]) (z : ℂ) : ℝ :=
  (w z * (evalC p z) ^ 2).re

/-- Positive absolute-complex envelope used by Gaussian counting estimates. -/
def absoluteSquareTerm (w : ℂ → ℂ) (p : ℝ[X]) (z : ℂ) : ℝ :=
  ‖w z‖ * ‖evalC p z‖ ^ 2

theorem norm_squareTerm_le_absoluteSquareTerm (w : ℂ → ℂ) (p : ℝ[X]) (z : ℂ) :
    ‖squareTerm w p z‖ ≤ absoluteSquareTerm w p z := by
  calc
    ‖squareTerm w p z‖ = |(w z * (evalC p z) ^ 2).re| := by
      rw [squareTerm, Real.norm_eq_abs]
    _ ≤ ‖w z * (evalC p z) ^ 2‖ := Complex.abs_re_le_norm _
    _ = absoluteSquareTerm w p z := by rw [norm_mul, norm_pow, absoluteSquareTerm]

theorem squareTerm_le_absoluteSquareTerm (w : ℂ → ℂ) (p : ℝ[X]) (z : ℂ) :
    squareTerm w p z ≤ absoluteSquareTerm w p z := by
  calc
    squareTerm w p z ≤ |squareTerm w p z| := le_abs_self _
    _ = ‖squareTerm w p z‖ := (Real.norm_eq_abs _).symm
    _ ≤ absoluteSquareTerm w p z := norm_squareTerm_le_absoluteSquareTerm w p z

theorem summable_squareTerm_of_absoluteSquareTerm (w : ℂ → ℂ) (p : ℝ[X])
    (h : Summable (absoluteSquareTerm w p)) : Summable (squareTerm w p) :=
  h.of_norm_bounded (norm_squareTerm_le_absoluteSquareTerm w p)

/-- Full infinite polynomial-square positivity; ordinary Hankel identification is separate. -/
def PolynomialSquareNonneg (w : ℂ → ℂ) : Prop :=
  ∀ p : ℝ[X], 0 ≤ ∑' z : ℂ, squareTerm w p z

/-- Every nonzero complex weight admits a strictly negative square value. -/
theorem exists_negative_pair_value {v z : ℂ} (hv : v ≠ 0) (hz : z.im ≠ 0) :
    ∃ ξ : ℂ, 2 * (v * ξ ^ 2).re < 0 := by
  obtain ⟨x, y, hxy⟩ := pairMoment_negative_witness hv hz
  refine ⟨(x : ℂ) + (y : ℂ) * z, ?_⟩
  have heq : 2 * (v * ((x : ℂ) + (y : ℂ) * z) ^ 2).re =
      pairMoment v z 0 * x ^ 2 + 2 * pairMoment v z 1 * x * y +
        pairMoment v z 2 * y ^ 2 := by
    simp only [pairMoment, pow_zero, pow_one, mul_one, pow_two,
      Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  rwa [heq]

/-- A finite sum supported at exactly two distinct selected indices. -/
theorem sum_eq_pair_of_vanish {α : Type*} (s : Finset α) (q : α → ℝ)
    {a b : α} (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b)
    (hzero : ∀ x ∈ s, x ≠ a → x ≠ b → q x = 0) :
    (∑ x ∈ s, q x) = q a + q b := by
  classical
  have hsub : ({a, b} : Finset α) ⊆ s := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  have heq : (∑ x ∈ ({a, b} : Finset α), q x) = ∑ x ∈ s, q x := by
    apply Finset.sum_subset hsub
    intro x hx hnot
    apply hzero x hx
    · intro h
      apply hnot
      simp [h]
    · intro h
      apply hnot
      simp [h]
  rw [← heq]
  simp [hab]

/-- Exact finite energy: all other nodes, including their full multiplicities, vanish. -/
theorem core_square_eq_pair (w : ℂ → ℂ) (s : Finset ℂ) (p : ℝ[X])
    {z ξ : ℂ} (hz : z.im ≠ 0) (hzin : z ∈ s) (hzcin : (starRingEnd ℂ) z ∈ s)
    (hw : w ((starRingEnd ℂ) z) = (starRingEnd ℂ) (w z))
    (hp : evalC p z = ξ) (hpc : evalC p ((starRingEnd ℂ) z) = (starRingEnd ℂ) ξ)
    (hzero : ∀ u ∈ s, u ≠ z → u ≠ (starRingEnd ℂ) z → evalC p u = 0) :
    (∑ u ∈ s, squareTerm w p u) = 2 * (w z * ξ ^ 2).re := by
  have hne : z ≠ (starRingEnd ℂ) z := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.conj_im] at hi
    apply hz
    linarith
  rw [sum_eq_pair_of_vanish s (squareTerm w p) hzin hzcin hne]
  · simp only [squareTerm, hp, hpc, hw, pow_two,
      Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  · intro u hu huz huc
    simp [squareTerm, hzero u hu huz huc]

/--
Every nonreal target pair with nonzero conjugate weights is detectable in any
finite cutoff containing it.  No sign hypothesis on other weights and no
conjugation symmetry of the cutoff are needed.
-/
theorem exists_finite_negative_square (w : ℂ → ℂ) (s : Finset ℂ) {z : ℂ}
    (hz : z.im ≠ 0) (hzin : z ∈ s) (hzcin : (starRingEnd ℂ) z ∈ s)
    (hw : w ((starRingEnd ℂ) z) = (starRingEnd ℂ) (w z)) (hw0 : w z ≠ 0) :
    ∃ p : ℝ[X], (∑ u ∈ s, squareTerm w p u) < 0 := by
  classical
  obtain ⟨ξ, hξ⟩ := exists_negative_pair_value hw0 hz
  let t := (s.erase z).erase ((starRingEnd ℂ) z)
  have ht : ∀ u ∈ t, u ≠ z ∧ u ≠ (starRingEnd ℂ) z := by
    intro u hu
    simp only [t, Finset.mem_erase] at hu
    exact ⟨hu.2.1, hu.1⟩
  obtain ⟨p, hp, hpc, hpzero⟩ := exists_real_interpolant hz ht ξ
  refine ⟨p, ?_⟩
  have hzero : ∀ u ∈ s, u ≠ z → u ≠ (starRingEnd ℂ) z → evalC p u = 0 := by
    intro u hu huz huc
    apply hpzero u
    simp only [t, Finset.mem_erase]
    exact ⟨huc, huz, hu⟩
  rwa [core_square_eq_pair w s p hz hzin hzcin hw hp hpc hzero]

/-- The sharp scalar tail condition.  No norm or entrywise estimate is required. -/
theorem tsum_negative_of_tail_lt_neg_core {α : Type*} (q : α → ℝ)
    (s : Finset α) (hq : Summable q)
    (htail : (∑' x : {x // x ∉ s}, q x) < -(∑ x ∈ s, q x)) :
    (∑' x, q x) < 0 := by
  have hsplit := hq.sum_add_tsum_subtype_compl s
  linarith

/-- An absolute tail estimate implies the sharp scalar condition. -/
theorem tsum_negative_of_abs_tail {α : Type*} (q : α → ℝ)
    (s : Finset α) (hq : Summable q)
    (htail : |∑' x : {x // x ∉ s}, q x| < -(∑ x ∈ s, q x)) :
    (∑' x, q x) < 0 := by
  apply tsum_negative_of_tail_lt_neg_core q s hq
  exact (le_abs_self _).trans_lt htail

/-- A summable pointwise upper envelope suffices; it may be the absolute Gaussian tail. -/
theorem tsum_negative_of_tail_envelope {α : Type*} (q : α → ℝ)
    (s : Finset α) (hq : Summable q) (b : {x // x ∉ s} → ℝ)
    (hb : Summable b) (hqb : ∀ x : {x // x ∉ s}, q x ≤ b x)
    (hbudget : (∑' x, b x) < -(∑ x ∈ s, q x)) :
    (∑' x, q x) < 0 := by
  apply tsum_negative_of_tail_lt_neg_core q s hq
  exact (Summable.tsum_le_tsum hqb (hq.subtype (fun x => x ∉ s)) hb).trans_lt hbudget

/-- A single sufficiently clean finite witness refutes the full polynomial criterion. -/
theorem not_polynomialSquareNonneg_of_tail_budget (w : ℂ → ℂ)
    (s : Finset ℂ) (p : ℝ[X]) (hpsum : Summable (squareTerm w p))
    (htail : (∑' z : {z // z ∉ s}, squareTerm w p z) <
      -(∑ z ∈ s, squareTerm w p z)) : ¬ PolynomialSquareNonneg w := by
  intro h
  exact (not_le_of_gt (tsum_negative_of_tail_lt_neg_core (squareTerm w p) s hpsum htail))
    (h p)

/-- A full absolute-complex tail budget also supplies the needed real summability. -/
theorem not_polynomialSquareNonneg_of_absolute_complex_tail_budget
    (w : ℂ → ℂ) (s : Finset ℂ) (p : ℝ[X])
    (hsum : Summable (absoluteSquareTerm w p))
    (hbudget : (∑' z : {z // z ∉ s}, absoluteSquareTerm w p z) <
      -(∑ z ∈ s, squareTerm w p z)) : ¬ PolynomialSquareNonneg w := by
  intro hpos
  have hneg : (∑' z, squareTerm w p z) < 0 := by
    apply tsum_negative_of_tail_envelope (squareTerm w p) s
      (summable_squareTerm_of_absoluteSquareTerm w p hsum)
      (fun z : {z // z ∉ s} => absoluteSquareTerm w p z)
      (hsum.subtype (fun z => z ∉ s))
    · intro z
      exact squareTerm_le_absoluteSquareTerm w p z
    · exact hbudget
  exact (not_le_of_gt hneg) (hpos p)

/--
The needed provider is convergence of the changing-polynomial tails, not merely
convergence of the tails of one fixed polynomial.  A uniform negative core
margin then gives an eventual full infinite negative witness.
-/
theorem eventually_tsum_negative_of_uniform_core_and_tail_tendsto
    {α : Type*} (q : ℕ → α → ℝ) (s : ℕ → Finset α) (η : ℝ)
    (hη : 0 < η) (hq : ∀ n, Summable (q n))
    (hcore : ∀ n, (∑ x ∈ s n, q n x) ≤ -η)
    (htail : Tendsto (fun n => ∑' x : {x // x ∉ s n}, q n x) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, (∑' x, q n x) < 0 := by
  have he : ∀ᶠ n in atTop, (∑' x : {x // x ∉ s n}, q n x) < η :=
    htail.eventually (isOpen_Iio.mem_nhds hη)
  filter_upwards [he] with n hn
  apply tsum_negative_of_tail_lt_neg_core (q n) (s n) (hq n)
  linarith [hcore n]

/-- Interpolation over the distinct remainder of a finite cutoff. -/
noncomputable def cutoffInterpolant (s : Finset ℂ) (z ξ : ℂ) : ℝ[X] :=
  interpolant ((s.erase z).erase ((starRingEnd ℂ) z)) z ξ

theorem cutoffInterpolant_core (w : ℂ → ℂ) (s : Finset ℂ) {z : ℂ}
    (hz : z.im ≠ 0) (hzin : z ∈ s) (hzcin : (starRingEnd ℂ) z ∈ s)
    (hw : w ((starRingEnd ℂ) z) = (starRingEnd ℂ) (w z)) (ξ : ℂ) :
    (∑ u ∈ s, squareTerm w (cutoffInterpolant s z ξ) u) =
      2 * (w z * ξ ^ 2).re := by
  classical
  have hs : ∀ u ∈ (s.erase z).erase ((starRingEnd ℂ) z),
      u ≠ z ∧ u ≠ (starRingEnd ℂ) z := by
    intro u hu
    simp only [Finset.mem_erase] at hu
    exact ⟨hu.2.1, hu.1⟩
  apply core_square_eq_pair w s (cutoffInterpolant s z ξ) hz hzin hzcin hw
  · exact interpolant_eval hz hs ξ
  · exact interpolant_eval_star hz hs ξ
  · intro u hu huz huc
    apply interpolant_eval_zero (z := z) (ξ := ξ)
    simp only [Finset.mem_erase]
    exact ⟨huc, huz, hu⟩

/--
Abstract infinite converse.  The tail provider is required only for assigned
values with negative pair energy.  The finite interpolant and the exact full
sum transfer are conclusions, while summability and tail decay remain explicit.
-/
theorem not_polynomialSquareNonneg_of_nonreal_pair_and_tail_provider
    (w : ℂ → ℂ) (s : ℕ → Finset ℂ) {z : ℂ}
    (hz : z.im ≠ 0) (hzin : ∀ n, z ∈ s n) (hzcin : ∀ n, (starRingEnd ℂ) z ∈ s n)
    (hw : w ((starRingEnd ℂ) z) = (starRingEnd ℂ) (w z)) (hw0 : w z ≠ 0)
    (hsum : ∀ n ξ, Summable (squareTerm w (cutoffInterpolant (s n) z ξ)))
    (htail : ∀ ξ : ℂ, 2 * (w z * ξ ^ 2).re < 0 →
      Tendsto (fun n => ∑' u : {u // u ∉ s n},
        squareTerm w (cutoffInterpolant (s n) z ξ) u) atTop (𝓝 0)) :
    ¬ PolynomialSquareNonneg w := by
  obtain ⟨ξ, hξ⟩ := exists_negative_pair_value hw0 hz
  have he : ∀ᶠ n in atTop,
      (∑' u, squareTerm w (cutoffInterpolant (s n) z ξ) u) < 0 := by
    apply eventually_tsum_negative_of_uniform_core_and_tail_tendsto
      (fun n => squareTerm w (cutoffInterpolant (s n) z ξ)) s
      (-(2 * (w z * ξ ^ 2).re))
    · exact neg_pos.mpr hξ
    · intro n
      exact hsum n ξ
    · intro n
      rw [cutoffInterpolant_core w (s n) hz (hzin n) (hzcin n) hw ξ]
      simp
    · exact htail ξ hξ
  obtain ⟨n, hn⟩ := he.exists
  intro hpos
  exact (not_le_of_gt hn) (hpos (cutoffInterpolant (s n) z ξ))

end RiemannResearch.Analysis.GaussianHankelInterpolation
