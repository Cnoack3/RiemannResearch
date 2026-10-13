import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Quantitative nonvanishing of positive spectral factors

Source: the user's DPP/Hilbert--Polya discussion, 13 October 2026.
The exact imaginary-part identity precedes the bounds. The compensation
constant depends on the spectral argument, never on the dimension or the
nonnegative eigenvalue. This supplies a limit argument for moving spectra.
-/

noncomputable section

namespace Complex

theorem im_square_factor_mul_star (z : ℂ) (t : ℝ) :
    ((1 - z ^ 2 * (t : ℂ)) * star z).im =
      -z.im * (1 + t * (z.re ^ 2 + z.im ^ 2)) := by
  simp [Complex.mul_re, Complex.mul_im, Complex.star_def, pow_two]
  <;> ring

theorem abs_im_le_norm_square_factor_mul_norm (z : ℂ) (t : ℝ) (ht : 0 ≤ t) :
    |z.im| ≤ ‖1 - z ^ 2 * (t : ℂ)‖ * ‖z‖ := by
  have hq : 0 ≤ t * (z.re ^ 2 + z.im ^ 2) :=
    mul_nonneg ht (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hs : 0 ≤ 1 + t * (z.re ^ 2 + z.im ^ 2) := by linarith
  have hb := Complex.abs_im_le_norm ((1 - z ^ 2 * (t : ℂ)) * star z)
  rw [im_square_factor_mul_star, abs_mul, abs_neg, abs_of_nonneg hs,
    norm_mul, norm_star] at hb
  have hi : |z.im| ≤ |z.im| * (1 + t * (z.re ^ 2 + z.im ^ 2)) := by
    have h := mul_le_mul_of_nonneg_left
      (show (1 : ℝ) ≤ 1 + t * (z.re ^ 2 + z.im ^ 2) by linarith)
      (abs_nonneg z.im)
    simpa only [mul_one] using h
  exact hi.trans hb

theorem one_le_norm_square_factor_compensated (z : ℂ) (hz : z.im ≠ 0)
    (t : ℝ) (ht : 0 ≤ t) :
    1 ≤ ‖1 - z ^ 2 * (t : ℂ)‖ * (1 + (‖z‖ ^ 3 / |z.im|) * t) := by
  have hb : 0 < |z.im| := abs_pos.mpr hz
  have hlow := abs_im_le_norm_square_factor_mul_norm z t ht
  have hcoef : ‖z‖ ^ 2 ≤
      ‖1 - z ^ 2 * (t : ℂ)‖ * (‖z‖ ^ 3 / |z.im|) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hb).2
    have h := mul_le_mul_of_nonneg_right hlow (sq_nonneg ‖z‖)
    nlinarith
  have htri : 1 ≤ ‖1 - z ^ 2 * (t : ℂ)‖ + ‖z‖ ^ 2 * t := by
    have h := norm_add_le (1 - z ^ 2 * (t : ℂ)) (z ^ 2 * (t : ℂ))
    have he : (1 - z ^ 2 * (t : ℂ)) + z ^ 2 * (t : ℂ) = 1 := by ring
    rw [he, norm_one, norm_mul, norm_pow, Complex.norm_of_nonneg ht] at h
    exact h
  have hmul := mul_le_mul_of_nonneg_right hcoef ht
  nlinarith

theorem exists_nonreal_square_factor_compensation (z : ℂ) (hz : z.im ≠ 0) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ t : ℝ, 0 ≤ t →
      1 ≤ ‖1 - z ^ 2 * (t : ℂ)‖ * (1 + c * t) := by
  refine ⟨‖z‖ ^ 3 / |z.im|, by positivity, ?_⟩
  intro t ht
  exact one_le_norm_square_factor_compensated z hz t ht

end Complex


namespace RiemannResearch.Analysis.PositiveSpectralPolynomial

open Filter
open scoped BigOperators Topology

/-- The characteristic product of a finite nonnegative spectrum. -/
def finiteProduct {ι : Type*} [Fintype ι] (τ : ι → ℝ) (z : ℂ) : ℂ :=
  ∏ i, (1 - z ^ 2 * (τ i : ℂ))

theorem imaginaryQuarter_factor_norm (t : ℝ) (ht : 0 ≤ t) :
    ‖1 - (Complex.I / 4) ^ 2 * (t : ℂ)‖ = 1 + t / 16 := by
  have hsq : (Complex.I / 4) ^ 2 = -(1 / 16 : ℂ) := by
    norm_num [div_pow, Complex.I_sq]
  have he : 1 - (Complex.I / 4) ^ 2 * (t : ℂ) = ((1 + t / 16 : ℝ) : ℂ) := by
    rw [hsq]
    push_cast
    ring
  rw [he, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ 1 + t / 16)]

theorem exists_factor_power_compensation (z : ℂ) (hz : z.im ≠ 0) :
    ∃ k : ℕ, ∀ t : ℝ, 0 ≤ t →
      1 ≤ ‖1 - z ^ 2 * (t : ℂ)‖ *
        ‖1 - (Complex.I / 4) ^ 2 * (t : ℂ)‖ ^ k := by
  obtain ⟨c, _hc, hscalar⟩ := Complex.exists_nonreal_square_factor_compensation z hz
  obtain ⟨k, hk⟩ := exists_nat_ge (16 * c)
  refine ⟨k, ?_⟩
  intro t ht
  rw [imaginaryQuarter_factor_norm t ht]
  have hbern : 1 + (k : ℝ) * (t / 16) ≤ (1 + t / 16) ^ k :=
    one_add_mul_le_pow (by linarith) k
  have hlin : 1 + c * t ≤ 1 + (k : ℝ) * (t / 16) := by
    nlinarith [mul_le_mul_of_nonneg_right hk ht]
  exact (hscalar t ht).trans
    (mul_le_mul_of_nonneg_left (hlin.trans hbern) (norm_nonneg _))

theorem finiteProduct_compensation {ι : Type*} [Fintype ι]
    (τ : ι → ℝ) (hτ : ∀ i, 0 ≤ τ i) (z : ℂ) (k : ℕ)
    (hk : ∀ t : ℝ, 0 ≤ t →
      1 ≤ ‖1 - z ^ 2 * (t : ℂ)‖ *
        ‖1 - (Complex.I / 4) ^ 2 * (t : ℂ)‖ ^ k) :
    1 ≤ ‖finiteProduct τ z‖ * ‖finiteProduct τ (Complex.I / 4)‖ ^ k := by
  have hp : 1 ≤ ∏ i, (‖1 - z ^ 2 * (τ i : ℂ)‖ *
      ‖1 - (Complex.I / 4) ^ 2 * (τ i : ℂ)‖ ^ k) :=
    Finset.one_le_prod (fun i _ => hk (τ i) (hτ i))
  simpa only [Finset.prod_mul_distrib, Finset.prod_pow, finiteProduct, norm_prod] using hp

/-- A convergent moving positive spectrum cannot acquire a nonreal zero if its
values at one imaginary test point also converge. -/
theorem moving_limit_ne_zero_of_nonreal
    (rank : ℕ → ℕ) (τ : ∀ N, Fin (rank N) → ℝ)
    (hτ : ∀ N i, 0 ≤ τ N i) (z : ℂ) (hz : z.im ≠ 0) (a b : ℂ)
    (ha : Tendsto (fun N => finiteProduct (τ N) z) atTop (𝓝 a))
    (hb : Tendsto (fun N => finiteProduct (τ N) (Complex.I / 4)) atTop (𝓝 b)) :
    a ≠ 0 := by
  obtain ⟨k, hk⟩ := exists_factor_power_compensation z hz
  have hl := ha.norm.mul (hb.norm.pow k)
  have hbound : 1 ≤ ‖a‖ * ‖b‖ ^ k := ge_of_tendsto hl
    (Filter.Eventually.of_forall (fun N =>
      finiteProduct_compensation (τ N) (hτ N) z k hk))
  intro haz
  rw [haz, norm_zero, zero_mul] at hbound
  norm_num at hbound

theorem moving_scaled_limit_ne_zero_of_nonreal
    (rank : ℕ → ℕ) (τ : ∀ N, Fin (rank N) → ℝ)
    (hτ : ∀ N i, 0 ≤ τ N i) (c : ℂ) (hc : c ≠ 0)
    (z : ℂ) (hz : z.im ≠ 0) (a b : ℂ)
    (ha : Tendsto (fun N => c * finiteProduct (τ N) z) atTop (𝓝 a))
    (hb : Tendsto (fun N => c * finiteProduct (τ N) (Complex.I / 4)) atTop (𝓝 b)) :
    a ≠ 0 := by
  have hcancel (w : ℂ) : c * w / c = w := by
    apply (div_eq_iff hc).2
    ring
  have ha' := ha.div_const c
  have hb' := hb.div_const c
  simp only [hcancel] at ha' hb'
  have hn := moving_limit_ne_zero_of_nonreal rank τ hτ z hz (a / c) (b / c) ha' hb'
  intro haz
  apply hn
  simp [haz]

end RiemannResearch.Analysis.PositiveSpectralPolynomial
