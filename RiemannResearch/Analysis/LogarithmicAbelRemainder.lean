import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity

/-!
# Quantitative tails for a logarithmically decaying reciprocal Abel series

Source: direct telescoping estimates for successive logarithms.
This is elementary real analysis, with no RH hypothesis.
The series is indexed from zero to match `reciprocal_partial_sum_abel` exactly.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.Analysis

/-- A telescoping nonnegative majorant gives an absolutely convergent series
and an explicit remainder. No convergence hypothesis on the majorant is needed.
-/
theorem summable_remainder_of_telescope
    (f u : ℕ → ℝ) (D : ℝ) (hD : 0 ≤ D) (hu : ∀ n, 0 ≤ u n)
    (hf : ∀ n, |f n| ≤ D * (u n - u (n + 1))) :
    Summable f ∧ ∀ N, |(∑ k ∈ Finset.range N, f k) - ∑' k, f k| ≤ D * u N := by
  have hfinite (s n : ℕ) :
      (∑ k ∈ Finset.range n, |f (k + s)|) ≤ D * (u s - u (n + s)) := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ]
        have hn := hf (n + s)
        have he : n + 1 + s = n + s + 1 := by omega
        rw [he]
        linarith
  have habs : Summable (fun n => |f n|) := by
    apply summable_of_sum_range_le (fun _ => abs_nonneg _) (c := D * u 0)
    intro n
    have h := hfinite 0 n
    simp only [Nat.add_zero] at h
    have hnonneg : 0 ≤ D * u n := mul_nonneg hD (hu n)
    linarith
  have hs : Summable f := by
    apply Summable.of_norm
    simpa only [Real.norm_eq_abs] using habs
  refine ⟨hs, fun N => ?_⟩
  have htail : Summable (fun k => f (k + N)) := (summable_nat_add_iff N).2 hs
  have hbound : |∑' k, f (k + N)| ≤ D * u N := by
    apply le_of_tendsto htail.hasSum.tendsto_sum_nat.abs
    apply Eventually.of_forall
    intro n
    calc
      |∑ k ∈ Finset.range n, f (k + N)| ≤
          ∑ k ∈ Finset.range n, |f (k + N)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ D * (u N - u (n + N)) := hfinite N n
      _ ≤ D * u N := by nlinarith [mul_nonneg hD (hu (n + N))]
  have he := hs.sum_add_tsum_nat_add N
  have heq : (∑ k ∈ Finset.range N, f k) - ∑' k, f k =
      -(∑' k, f (k + N)) := by linarith
  rw [heq, abs_neg]
  exact hbound

/-- Consecutive positive logarithms satisfy both the multiplicative comparison
and the explicit increment lower bound needed for the telescoping majorant. -/
theorem logarithmic_successor_comparison (x : ℝ) (hx : 1 ≤ x) :
    1 ≤ 1 + Real.log x ∧
    1 + Real.log x ≤ 1 + Real.log (x + 1) ∧
    1 + Real.log (x + 1) ≤ 2 * (1 + Real.log x) ∧
    1 / (x + 1) ≤ (1 + Real.log (x + 1)) - (1 + Real.log x) := by
  have hxpos : 0 < x := by linarith
  have hx1pos : 0 < x + 1 := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have hmono : Real.log x ≤ Real.log (x + 1) :=
    Real.log_le_log hxpos (by linarith)
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hupper : Real.log (x + 1) ≤ Real.log x + 1 := by
    calc
      Real.log (x + 1) ≤ Real.log (2 * x) :=
        Real.log_le_log hx1pos (by linarith)
      _ = Real.log 2 + Real.log x := Real.log_mul (by norm_num) hxpos.ne'
      _ ≤ Real.log x + 1 := by linarith
  have hquot := Real.log_le_sub_one_of_pos (div_pos hxpos hx1pos)
  rw [Real.log_div hxpos.ne' hx1pos.ne'] at hquot
  have he : x / (x + 1) - 1 = -(1 / (x + 1)) := by
    field_simp [hx1pos.ne']
    <;> ring
  rw [he] at hquot
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Elementary algebra behind the logarithmic telescoping comparison. -/
theorem reciprocal_cube_difference_bound
    (a b δ : ℝ) (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 2 * a)
    (hδ : 0 ≤ δ) (hδb : δ ≤ b - a) :
    δ / a ^ 4 ≤ 8 * (1 / a ^ 3 - 1 / b ^ 3) := by
  have hbpos : 0 < b := ha.trans_le hab
  have hcube : b ^ 3 ≤ 8 * a ^ 3 := by
    calc
      b ^ 3 ≤ (2 * a) ^ 3 := pow_le_pow_left₀ hbpos.le hb 3
      _ = 8 * a ^ 3 := by ring
  have hden : a ^ 3 * b ^ 3 ≤ a ^ 3 * (8 * a ^ 3) :=
    mul_le_mul_of_nonneg_left hcube (by positivity)
  have hnonneg : 0 ≤ 8 * ((b - a) * a ^ 2) :=
    mul_nonneg (by norm_num) (mul_nonneg (sub_nonneg.mpr hab) (sq_nonneg a))
  calc
    δ / a ^ 4 ≤ (b - a) / a ^ 4 :=
      div_le_div_of_nonneg_right hδb (by positivity)
    _ = (8 * ((b - a) * a ^ 2)) / (a ^ 3 * (8 * a ^ 3)) := by
      field_simp [ha.ne']
      <;> ring
    _ ≤ (8 * ((b - a) * a ^ 2)) / (a ^ 3 * b ^ 3) :=
      div_le_div_of_nonneg_left hnonneg (by positivity) hden
    _ ≤ (8 * ((b - a) * (b ^ 2 + b * a + a ^ 2))) /
        (a ^ 3 * b ^ 3) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr hab)
      nlinarith [sq_nonneg b, mul_nonneg hbpos.le ha.le]
    _ = 8 * (1 / a ^ 3 - 1 / b ^ 3) := by
      field_simp [ha.ne', hbpos.ne']
      <;> ring

/-- Explicit summable majorant with no integral comparison. -/
theorem inverse_log_fourth_le_cube_difference (x : ℝ) (hx : 1 ≤ x) :
    1 / ((x + 1) * (1 + Real.log x) ^ 4) ≤
      8 * (1 / (1 + Real.log x) ^ 3 -
        1 / (1 + Real.log (x + 1)) ^ 3) := by
  obtain ⟨ha, hab, hb, hδb⟩ := logarithmic_successor_comparison x hx
  have hxpos : 0 < x := by linarith
  have h := reciprocal_cube_difference_bound (1 + Real.log x)
    (1 + Real.log (x + 1)) (1 / (x + 1))
    (by linarith) hab hb (by positivity) hδb
  simpa only [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc] using h

/-- An inverse fourth logarithmic bound on a primitive gives an explicit
inverse cubic logarithmic remainder in its reciprocal Abel expansion.
The constant 32 is a convenient uniform weakening of the proof's bound 16. -/
theorem reciprocal_abel_inverse_log_remainder
    (A : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ n, 0 < n → |A n| ≤ C * (n : ℝ) / (1 + Real.log n) ^ 4) :
    ∃ β : ℝ, ∀ N, 0 < N →
      |A N / ((N : ℝ) + 1) +
        (∑ k ∈ Finset.range N,
          A (k + 1) / (((k : ℝ) + 1) * ((k : ℝ) + 2))) - β| ≤
        32 * C / (1 + Real.log ((N : ℝ) + 1)) ^ 3 := by
  let f : ℕ → ℝ := fun k =>
    A (k + 1) / (((k : ℝ) + 1) * ((k : ℝ) + 2))
  let u : ℕ → ℝ := fun k => 1 / (1 + Real.log ((k : ℝ) + 1)) ^ 3
  have hu (k : ℕ) : 0 ≤ u k := by
    dsimp [u]
    have hlog : 0 ≤ Real.log ((k : ℝ) + 1) := Real.log_nonneg (le_add_of_nonneg_left (Nat.cast_nonneg k))
    positivity
  have hf (k : ℕ) : |f k| ≤ (8 * C) * (u k - u (k + 1)) := by
    have hx : 1 ≤ (k : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg k)
    have hp : 0 < ((k : ℝ) + 1) * ((k : ℝ) + 2) := by positivity
    have ha := hA (k + 1) (by omega)
    push_cast at ha
    have hlog : 0 ≤ Real.log ((k : ℝ) + 1) := Real.log_nonneg hx
    have ha0 : 1 + Real.log ((k : ℝ) + 1) ≠ 0 := by positivity
    have hb := mul_le_mul_of_nonneg_left
      (inverse_log_fourth_le_cube_difference ((k : ℝ) + 1) hx) hC
    dsimp [f, u]
    rw [abs_div, abs_of_pos hp]
    calc
      |A (k + 1)| / (((k : ℝ) + 1) * ((k : ℝ) + 2)) ≤
          (C * ((k : ℝ) + 1) / (1 + Real.log ((k : ℝ) + 1)) ^ 4) /
            (((k : ℝ) + 1) * ((k : ℝ) + 2)) :=
        div_le_div_of_nonneg_right ha hp.le
      _ = C * (1 / ((((k : ℝ) + 1) + 1) *
            (1 + Real.log ((k : ℝ) + 1)) ^ 4)) := by
        field_simp
        <;> ring
      _ ≤ _ := by simpa only [Nat.cast_add, Nat.cast_one, add_assoc, mul_comm, mul_left_comm, mul_assoc] using hb
  obtain ⟨hs, ht⟩ := summable_remainder_of_telescope f u (8 * C)
    (by positivity) hu hf
  refine ⟨∑' k, f k, fun N hN => ?_⟩
  have hNreal : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  obtain ⟨ha, hab, hb, hδ⟩ := logarithmic_successor_comparison (N : ℝ) hNreal
  have hapos : 0 < 1 + Real.log (N : ℝ) := by linarith
  have hbpos : 0 < 1 + Real.log ((N : ℝ) + 1) := hapos.trans_le hab
  have hcube : (1 + Real.log ((N : ℝ) + 1)) ^ 3 ≤
      8 * (1 + Real.log (N : ℝ)) ^ 3 := by
    calc
      _ ≤ (2 * (1 + Real.log (N : ℝ))) ^ 3 := pow_le_pow_left₀ hbpos.le hb 3
      _ = _ := by ring
  have hend : |A N / ((N : ℝ) + 1)| ≤
      8 * C / (1 + Real.log ((N : ℝ) + 1)) ^ 3 := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (N : ℝ) + 1)]
    calc
      |A N| / ((N : ℝ) + 1) ≤
          (C * (N : ℝ) / (1 + Real.log (N : ℝ)) ^ 4) / ((N : ℝ) + 1) :=
        div_le_div_of_nonneg_right (hA N hN) (by positivity)
      _ = (C / (1 + Real.log (N : ℝ)) ^ 3) *
          ((N : ℝ) / (((N : ℝ) + 1) * (1 + Real.log (N : ℝ)))) := by
        field_simp
        <;> ring
      _ ≤ (C / (1 + Real.log (N : ℝ)) ^ 3) * 1 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply (div_le_one (by positivity :
          (0 : ℝ) < ((N : ℝ) + 1) * (1 + Real.log (N : ℝ)))).2
        nlinarith
      _ = C / (1 + Real.log (N : ℝ)) ^ 3 := mul_one _
      _ ≤ 8 * C / (1 + Real.log ((N : ℝ) + 1)) ^ 3 := by
        apply (div_le_div_iff₀ (pow_pos hapos 3) (pow_pos hbpos 3)).2
        nlinarith [mul_le_mul_of_nonneg_left hcube hC]
  have htail := ht N
  change |(∑ k ∈ Finset.range N, f k) - ∑' k, f k| ≤
    8 * C * (1 / (1 + Real.log ((N : ℝ) + 1)) ^ 3) at htail
  change |A N / ((N : ℝ) + 1) + (∑ k ∈ Finset.range N, f k) - ∑' k, f k| ≤ _
  calc
    _ = |A N / ((N : ℝ) + 1) + ((∑ k ∈ Finset.range N, f k) - ∑' k, f k)| := by
      congr 1 <;> ring
    _ ≤ |A N / ((N : ℝ) + 1)| + |(∑ k ∈ Finset.range N, f k) - ∑' k, f k| :=
      abs_add_le _ _
    _ ≤ 8 * C / (1 + Real.log ((N : ℝ) + 1)) ^ 3 +
        8 * C * (1 / (1 + Real.log ((N : ℝ) + 1)) ^ 3) := add_le_add hend htail
    _ ≤ 32 * C / (1 + Real.log ((N : ℝ) + 1)) ^ 3 := by
      rw [mul_one_div, ← add_div]
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith

end RiemannResearch.Analysis
