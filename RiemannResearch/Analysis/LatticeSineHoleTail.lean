import RiemannResearch.Analysis.FiniteAbelSummation
import RiemannResearch.Analysis.SummableDiscreteAbel
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # The tail of the discrete sine hole
The oscillatory tail is controlled by finite Abel summation against an exact
sine difference. The unmodulated reciprocal-square tail is bracketed by
two shifted telescopes. The explicit constant degenerates at integer spacing.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.Analysis.LatticeSineHoleTail

private def weight (n j : ℕ) : ℝ := 1 / ((j : ℝ) + n + 1)^2

private theorem weight_summable (n : ℕ) : Summable (weight n) := by
  have h := (summable_nat_add_iff (n+1)).mpr hasSum_zeta_two.summable
  change Summable (fun j : ℕ => 1 / ((j : ℝ) + n + 1)^2)
  simpa [Nat.cast_add, add_assoc] using h

private theorem telescoping (f : ℕ → ℝ) (m : ℕ) :
    (∑ j ∈ Finset.range m, (f j - f (j+1))) = f 0 - f m := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; ring

private theorem reciprocal_tail_bounds {n : ℕ} (hn : 0 < n) :
    1/((n:ℝ)+1) ≤ ∑' j, weight n j ∧ (∑' j, weight n j) ≤ 1/(n:ℝ) := by
  let r (j : ℕ) := 1 / ((j : ℝ) + n)
  have hp : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hcomp (j : ℕ) :
      r (j+1) - r (j+2) ≤ weight n j ∧ weight n j ≤ r j - r (j+1) := by
    dsimp [r,weight]
    push_cast
    have h0 : 0 < (j:ℝ) + n := by positivity
    have h1 : 0 < (j:ℝ) + 1 + n := by positivity
    have h2 : 0 < (j:ℝ) + 2 + n := by positivity
    have h3 : 0 < (j:ℝ) + n + 1 := by positivity
    constructor <;> field_simp <;> nlinarith
  have blo (m : ℕ) : r 1 - r (m+1) ≤ ∑ j ∈ Finset.range m, weight n j := by
    rw [← telescoping (fun j => r (j+1)) m]
    exact Finset.sum_le_sum (fun j _ => (hcomp j).1)
  have bhi (m : ℕ) : (∑ j ∈ Finset.range m, weight n j) ≤ r 0 := by
    calc
      _ ≤ ∑ j ∈ Finset.range m, (r j-r (j+1)) := Finset.sum_le_sum (fun j _ => (hcomp j).2)
      _ ≤ r 0 := by
        rw [telescoping]
        have h : 0 ≤ r m := by dsimp [r]; positivity
        linarith
  have hlim := (weight_summable n).hasSum.tendsto_sum_nat
  have hr : Tendsto (fun j : ℕ => r (j+1)) atTop (𝓝 0) := by
    have hh := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat n)
    simpa [r, Function.comp_def, add_comm, add_left_comm, add_assoc] using hh
  have hrr := le_of_tendsto_of_tendsto' (hr.const_sub (r 1)) hlim blo
  simpa [r, add_comm] using And.intro hrr (le_of_tendsto hlim (Eventually.of_forall bhi))

private theorem cosine_partial_bound {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (n m : ℕ) :
    |∑ j ∈ Finset.range m, Real.cos (2 * (Real.pi*a*((j:ℝ)+n+1)))| ≤
      1 / Real.sin (Real.pi * a) := by
  let h := Real.pi * a
  have hs : 0 < Real.sin h := Real.sin_pos_of_pos_of_lt_pi (by dsimp [h]; positivity)
    (by dsimp [h]; nlinarith [Real.pi_pos, mul_pos Real.pi_pos (sub_pos.mpr ha1)])
  let f (j : ℕ) := Real.sin (2*h*((j:ℝ)+n+1)-h)
  have hd (j : ℕ) : Real.cos (2*(h*((j:ℝ)+n+1))) = (f (j+1) - f j)/(2 * Real.sin h) := by
    let x := 2*(h*((j:ℝ)+n+1))
    have he : f (j+1) = Real.sin (x+h) := by dsimp [f,x]; push_cast; congr 1; ring
    have he' : f j = Real.sin (x-h) := by dsimp [f,x]; congr 1; ring
    change Real.cos x = _
    rw [he,he',Real.sin_add,Real.sin_sub]
    field_simp [hs.ne']
    ring
  change |∑ j ∈ Finset.range m, Real.cos (2*(h*((j:ℝ)+n+1)))| ≤ _
  simp_rw [hd]
  rw [← Finset.sum_div, Finset.sum_range_sub, abs_div,
    abs_of_pos (by positivity : 0 < 2 * Real.sin h)]
  have hb := (abs_sub (f m) (f 0)).trans
    (add_le_add (Real.abs_sin_le_one _) (Real.abs_sin_le_one _))
  change |f m - f 0| / (2 * Real.sin h) ≤ 1 / Real.sin h
  apply (div_le_div_iff₀ (by positivity) hs).2
  nlinarith [mul_le_mul_of_nonneg_right hb hs.le]

private theorem abel_bound {w c : ℕ → ℝ} {B : ℝ} (hw : ∀ j, 0 ≤ w j)
    (hdec : ∀ j, w (j+1) ≤ w j) (hc : ∀ m, |∑ j ∈ Finset.range m, c j| ≤ B) (m : ℕ) :
    |∑ j ∈ Finset.range m, w j * c j| ≤ w 0 * B := by
  cases m with
  | zero =>
    simpa using mul_nonneg (hw 0) (by simpa using hc 0 : 0 ≤ B)
  | succ k =>
    rw [finite_abel]
    calc
      _ ≤ |w k * (∑ j ∈ Finset.range (k+1), c j)| +
          ∑ t ∈ Finset.range k, |(w (t+1)-w t) * (∑ j ∈ Finset.range (t+1), c j)| :=
        (abs_sub _ _).trans (add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _))
      _ ≤ w k * B + ∑ t ∈ Finset.range k, (w t-w (t+1))*B := by
        apply add_le_add
        · rw [abs_mul, abs_of_nonneg (hw k)]
          exact mul_le_mul_of_nonneg_left (hc _) (hw k)
        · apply Finset.sum_le_sum
          intro t _
          rw [abs_mul, abs_of_nonpos (sub_nonpos.mpr (hdec t)), neg_sub]
          exact mul_le_mul_of_nonneg_left (hc _) (sub_nonneg.mpr (hdec t))
      _ = _ := by rw [← Finset.sum_mul, telescoping]; ring

/-- Explicit first-order tail with an error uniform in every positive integer cutoff. -/
theorem sinc_square_tail_asymptotic {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {n : ℕ} (hn : 0 < n) :
    |(∑' j : ℕ, a * Real.sinc (Real.pi * (a * ((j:ℝ)+n+1)))^2) -
      (1/(2*Real.pi^2*a))*(1/(n:ℝ))| ≤
      (1/(2*Real.pi^2*a))*((1 + 1/Real.sin (Real.pi*a))/(n:ℝ)^2) := by
  let c (j : ℕ) := Real.cos (2*(Real.pi*a*((j:ℝ)+n+1)))
  let B := 1 / Real.sin (Real.pi*a)
  let A := 1/(2*Real.pi^2*a)
  have hs : 0 < Real.sin (Real.pi*a) := Real.sin_pos_of_pos_of_lt_pi (by positivity)
    (by nlinarith [Real.pi_pos, mul_pos Real.pi_pos (sub_pos.mpr ha1)])
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hp : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hw := weight_summable n
  have hc : Summable (fun j => weight n j*c j) :=
    summable_bounded_product hw (fun j => Real.abs_cos_le_one _)
  have hd (j : ℕ) : weight n (j+1) ≤ weight n j := by
    dsimp [weight]; push_cast
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [Nat.cast_nonneg (α := ℝ) j]
  have hbound := le_of_tendsto hc.hasSum.tendsto_sum_nat.abs (Eventually.of_forall
    (abel_bound (w := weight n) (c := c) (B := B) (fun j => by dsimp [weight]; positivity) hd
      (cosine_partial_bound ha ha1 n)))
  have hrepr (j : ℕ) : a * Real.sinc (Real.pi*(a*((j:ℝ)+n+1)))^2 =
      A * (weight n j - weight n j*c j) := by
    have hx : 0 < (j:ℝ)+n+1 := by positivity
    have hxx : Real.pi*(a*((j:ℝ)+n+1)) ≠ 0 := by positivity
    dsimp [A,weight,c]
    rw [Real.sinc_of_ne_zero hxx, mul_assoc Real.pi a, Real.cos_two_mul_eq_one_sub]
    field_simp [Real.pi_ne_zero, ha.ne', hx.ne']
    ring
  simp_rw [hrepr]
  rw [tsum_mul_left, hw.tsum_sub hc]
  change |A * (_ - _) - A * (1/(n:ℝ))| ≤ A * _
  rw [← mul_sub, abs_mul, abs_of_nonneg hA]
  apply mul_le_mul_of_nonneg_left _ hA
  obtain ⟨hl,hu⟩ := reciprocal_tail_bounds hn
  have hrec : |(∑' j, weight n j) - 1/(n:ℝ)| ≤ 1/(n:ℝ)^2 := by
    rw [abs_of_nonpos (sub_nonpos.mpr hu)]
    have hdiff : 1/(n:ℝ) - 1/((n:ℝ)+1) ≤ 1/(n:ℝ)^2 := by
      field_simp; nlinarith
    linarith
  have hw0 : weight n 0 ≤ 1/(n:ℝ)^2 := by
    dsimp [weight]; simp only [Nat.cast_zero, zero_add]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have hh := hbound.trans (mul_le_mul_of_nonneg_right hw0 hB)
  rw [show (∑' j, weight n j) - (∑' j, weight n j*c j) - 1/(n:ℝ) =
      ((∑' j, weight n j) - 1/(n:ℝ)) - (∑' j, weight n j*c j) by ring]
  calc
    _ ≤ _ := abs_sub _ _
    _ ≤ 1/(n:ℝ)^2 + (1/(n:ℝ)^2)*B := add_le_add hrec hh
    _ = _ := by dsimp [B]; ring

end RiemannResearch.Analysis.LatticeSineHoleTail
