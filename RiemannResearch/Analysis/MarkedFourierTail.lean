import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Unit-window Fourier-tail estimates

Source: user manuscript `Prime_Phases_Agenda_Proof_Attempts.tex`,
section “The mixed second count: an exact pair bridge and a solved Fourier tail”.
The finite summation argument below is independent of zeta zeros.  Its use for
zeta zeros requires a proved provider of the uniformly bounded unit-window
masses.  No zero-counting or Tsang theorem is assumed implicitly.
-/

open scoped BigOperators

namespace RiemannResearch.Analysis.MarkedFourierTail

/-- The closed-form tent transform, including its value at the origin.
Identification with the actual Fourier transform is a separate analytic theorem. -/
noncomputable def tentTransform (v α : ℝ) : ℝ :=
  if α = 0 then v ^ 2 else (Real.sin (Real.pi * v * α) / (Real.pi * α)) ^ 2

/-- The tent-transform envelope is independent of the tent width `v`. -/
theorem tentTransform_le_inverse_square (v : ℝ) {α : ℝ} (hα : α ≠ 0) :
    tentTransform v α ≤ 1 / (Real.pi ^ 2 * α ^ 2) := by
  have hsin : Real.sin (Real.pi * v * α) ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi * v * α),
      sq_nonneg (Real.cos (Real.pi * v * α))]
  rw [tentTransform, if_neg hα, div_pow, mul_pow]
  exact div_le_div_of_nonneg_right hsin
    (mul_nonneg (sq_nonneg _) (sq_nonneg _))

/-- The elementary estimate which makes unit-window inverse-square tails
summable with a reciprocal-cutoff bound. -/
theorem inv_square_le_telescoping {x : ℝ} (hx : 1 ≤ x) :
    1 / x ^ 2 ≤ 2 * (1 / x - 1 / (x + 1)) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x + 1 := by linarith
  have heq : 2 * (1 / x - 1 / (x + 1)) = 2 / (x * (x + 1)) := by
    field_simp [ne_of_gt hx0, ne_of_gt hx1]
    <;> ring
  rw [heq]
  apply (div_le_div_iff₀ (sq_pos_of_pos hx0) (mul_pos hx0 hx1)).2
  nlinarith [mul_nonneg (sub_nonneg.mpr hx) hx0.le]

/-- The exact remainder of the finite telescoping majorant is retained. -/
theorem window_tail_le_with_remainder (mass : ℕ → ℝ)
    {B C : ℝ} (hB : 1 ≤ B) (hC : 0 ≤ C)
    (hmass : ∀ n, mass n ≤ C) (N : ℕ) :
    (∑ n ∈ Finset.range N, mass n / (B + (n : ℝ)) ^ 2) ≤
      2 * C * (1 / B - 1 / (B + (N : ℝ))) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hBN : 1 ≤ B + (N : ℝ) := by
      linarith [Nat.cast_nonneg (α := ℝ) N]
    have hden : 0 ≤ (B + (N : ℝ)) ^ 2 := sq_nonneg _
    have hterm : mass N / (B + (N : ℝ)) ^ 2 ≤
        2 * C * (1 / (B + (N : ℝ)) - 1 / (B + (N : ℝ) + 1)) := by
      calc
        mass N / (B + (N : ℝ)) ^ 2 ≤ C / (B + (N : ℝ)) ^ 2 :=
          div_le_div_of_nonneg_right (hmass N) hden
        _ = C * (1 / (B + (N : ℝ)) ^ 2) := by ring
        _ ≤ C * (2 * (1 / (B + (N : ℝ)) - 1 / (B + (N : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left (inv_square_le_telescoping hBN) hC
        _ = _ := by ring
    rw [Finset.sum_range_succ]
    calc
      _ ≤ 2 * C * (1 / B - 1 / (B + (N : ℝ))) +
          2 * C * (1 / (B + (N : ℝ)) - 1 / (B + (N : ℝ) + 1)) :=
        add_le_add ih hterm
      _ = _ := by simp only [Nat.cast_add, Nat.cast_one]; ring

/-- A uniform finite bound suitable for passage to a monotone integral limit.
Only upper bounds on masses are needed for this estimate. -/
theorem window_tail_le (mass : ℕ → ℝ)
    {B C : ℝ} (hB : 1 ≤ B) (hC : 0 ≤ C)
    (hmass : ∀ n, mass n ≤ C) (N : ℕ) :
    (∑ n ∈ Finset.range N, mass n / (B + (n : ℝ)) ^ 2) ≤ 2 * C / B := by
  have hBN : 0 < B + (N : ℝ) := by
    linarith [Nat.cast_nonneg (α := ℝ) N]
  have hrem : 0 ≤ 2 * C * (1 / (B + (N : ℝ))) := by positivity
  calc
    _ ≤ 2 * C * (1 / B - 1 / (B + (N : ℝ))) :=
      window_tail_le_with_remainder mass hB hC hmass N
    _ = 2 * C / B - 2 * C / (B + (N : ℝ)) := by ring
    _ ≤ 2 * C / B := sub_le_self _ (by positivity)

/-- Both tails may be bounded with the same unit-window constant. -/
theorem two_sided_window_tail_le (plus minus : ℕ → ℝ)
    {B C : ℝ} (hB : 1 ≤ B) (hC : 0 ≤ C)
    (hplus : ∀ n, plus n ≤ C) (hminus : ∀ n, minus n ≤ C) (N : ℕ) :
    (∑ n ∈ Finset.range N, plus n / (B + (n : ℝ)) ^ 2) +
    (∑ n ∈ Finset.range N, minus n / (B + (n : ℝ)) ^ 2) ≤ 4 * C / B := by
  have hp := window_tail_le plus hB hC hplus N
  have hm := window_tail_le minus hB hC hminus N
  calc
    _ ≤ 2 * C / B + 2 * C / B := add_le_add hp hm
    _ = _ := by ring

/-- Nonnegative window masses have a summable inverse-square tail. -/
theorem summable_window_tail (mass : ℕ → ℝ)
    {B C : ℝ} (hB : 1 ≤ B) (hC : 0 ≤ C)
    (hmass0 : ∀ n, 0 ≤ mass n) (hmass : ∀ n, mass n ≤ C) :
    Summable (fun n => mass n / (B + (n : ℝ)) ^ 2) := by
  exact summable_of_sum_range_le
    (fun n => div_nonneg (hmass0 n) (sq_nonneg _))
    (fun N => window_tail_le mass hB hC hmass N)

/-- The infinite unit-window tail retains the same reciprocal-cutoff bound. -/
theorem window_tsum_tail_le (mass : ℕ → ℝ)
    {B C : ℝ} (hB : 1 ≤ B) (hC : 0 ≤ C)
    (hmass0 : ∀ n, 0 ≤ mass n) (hmass : ∀ n, mass n ≤ C) :
    (∑' n, mass n / (B + (n : ℝ)) ^ 2) ≤ 2 * C / B := by
  exact Real.tsum_le_of_sum_range_le
    (fun n => div_nonneg (hmass0 n) (sq_nonneg _))
    (fun N => window_tail_le mass hB hC hmass N)

/-- Both infinite tails have total bound `4 C / B`.  In the Fourier application
`C` contains the reciprocal-square tent-envelope constant. -/
theorem two_sided_window_tsum_tail_le (plus minus : ℕ → ℝ)
    {B C : ℝ} (hB : 1 ≤ B) (hC : 0 ≤ C)
    (hplus0 : ∀ n, 0 ≤ plus n) (hminus0 : ∀ n, 0 ≤ minus n)
    (hplus : ∀ n, plus n ≤ C) (hminus : ∀ n, minus n ≤ C) :
    (∑' n, plus n / (B + (n : ℝ)) ^ 2) +
    (∑' n, minus n / (B + (n : ℝ)) ^ 2) ≤ 4 * C / B := by
  have hp := window_tsum_tail_le plus hB hC hplus0 hplus
  have hm := window_tsum_tail_le minus hB hC hminus0 hminus
  calc
    _ ≤ 2 * C / B + 2 * C / B := add_le_add hp hm
    _ = _ := by ring

/-- The positive symmetric row-sum estimate used for the Gaussian cell matrix.
No arithmetic fact is needed for this finite quadratic-form estimate. -/
theorem symmetric_kernel_quadratic_le_row_bound {ι : Type*}
    (s : Finset ι) (weight : ι → ℝ) (kernel : ι → ι → ℝ) (D : ℝ)
    (hkernel : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ kernel i j)
    (hsym : ∀ i ∈ s, ∀ j ∈ s, kernel i j = kernel j i)
    (hrow : ∀ i ∈ s, (∑ j ∈ s, kernel i j) ≤ D) :
    (∑ i ∈ s, ∑ j ∈ s, kernel i j * weight i * weight j) ≤
      D * (∑ i ∈ s, weight i ^ 2) := by
  have hpair : ∀ i ∈ s, ∀ j ∈ s,
      kernel i j * weight i * weight j ≤
      (kernel i j * weight i ^ 2 + kernel i j * weight j ^ 2) / 2 := by
    intro i hi j hj
    nlinarith [mul_nonneg (hkernel i hi j hj) (sq_nonneg (weight i - weight j))]
  have hleft : (∑ i ∈ s, ∑ j ∈ s, kernel i j * weight i ^ 2) =
      ∑ i ∈ s, weight i ^ 2 * (∑ j ∈ s, kernel i j) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_mul]
    ring
  have hright : (∑ i ∈ s, ∑ j ∈ s, kernel i j * weight j ^ 2) =
      ∑ j ∈ s, weight j ^ 2 * (∑ i ∈ s, kernel i j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← Finset.sum_mul]
    ring
  have hcol : ∀ j ∈ s, (∑ i ∈ s, kernel i j) ≤ D := by
    intro j hj
    calc
      (∑ i ∈ s, kernel i j) = ∑ i ∈ s, kernel j i := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hsym i hi j hj
      _ ≤ D := hrow j hj
  have hleftBound : (∑ i ∈ s, weight i ^ 2 * (∑ j ∈ s, kernel i j)) ≤
      D * (∑ i ∈ s, weight i ^ 2) := by
    calc
      _ ≤ ∑ i ∈ s, weight i ^ 2 * D := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hrow i hi) (sq_nonneg _)
      _ = _ := by rw [← Finset.sum_mul]; ring
  have hrightBound : (∑ j ∈ s, weight j ^ 2 * (∑ i ∈ s, kernel i j)) ≤
      D * (∑ i ∈ s, weight i ^ 2) := by
    calc
      _ ≤ ∑ j ∈ s, weight j ^ 2 * D := by
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left (hcol j hj) (sq_nonneg _)
      _ = _ := by rw [← Finset.sum_mul]; ring
  calc
    _ ≤ ∑ i ∈ s, ∑ j ∈ s,
        (kernel i j * weight i ^ 2 + kernel i j * weight j ^ 2) / 2 := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact hpair i hi j hj
    _ = ((∑ i ∈ s, weight i ^ 2 * (∑ j ∈ s, kernel i j)) +
        (∑ j ∈ s, weight j ^ 2 * (∑ i ∈ s, kernel i j))) / 2 := by
      simp only [← Finset.sum_div, Finset.sum_add_distrib, hleft, hright]
    _ ≤ D * (∑ i ∈ s, weight i ^ 2) := by linarith

/-- Scalar assembly of a Cauchy--Schwarz window bound.
The square inequality itself must come from the marked kernel/integral provider. -/
theorem marked_window_mass_le {a b m C : ℝ}
    (_ha : 0 ≤ a) (hb : 0 ≤ b) (_hm : 0 ≤ m) (hC : 0 ≤ C)
    (haC : a ≤ C) (hbC : b ≤ C) (hsq : m ^ 2 ≤ a * b) : m ≤ C := by
  have hab : a * b ≤ C ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr haC) hb,
      mul_nonneg (sub_nonneg.mpr hbC) hC]
  nlinarith

end RiemannResearch.Analysis.MarkedFourierTail
