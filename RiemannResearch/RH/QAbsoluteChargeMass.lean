/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.MobiusHeadCoercivity
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-! # Absolute inverse-square mass of the actual head charges

Dirichlet inversion transfers the physical inverse-square first moment of
the increments to the absolute mass of the Möbius charges at the same weight.
-/

/- The absolute convergence at exponent two is a special case of Balazard,
Proposition 9, https://doi.org/10.1007/978-3-030-61887-2_3. -/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto
open ZetaTwoHilbert ZetaTwoProbability

private theorem summable_scaled_sequence (u : QHilbert) :
    Summable (fun n : ℕ => |qSequence u n| / (n : ℝ) ^ 2) := by
  have hw : Summable fun n : ℕ => 1 / (n : ℝ) ^ 2 :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hs : Summable fun n : ℕ => qSequence u n ^ 2 / (n : ℝ) ^ 2 := by
    apply ((qSequence_square_summable u).mul_left zetaTwo).congr
    intro n
    simp only [positiveQWeight, div_eq_mul_inv, mul_inv_rev, one_mul]
    field_simp [zetaTwo_pos.ne']
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _ (hs.add hw)
  intro n
  change _ ≤ _ / _ + _ / _
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  nlinarith [sq_nonneg (|qSequence u n| - 1), sq_abs (qSequence u n)]

/-- Finite differences of any physical Q-vector have inverse-square first moment. -/
theorem summable_scaled_difference (u : QHilbert) :
    Summable (fun n : ℕ => |qSequence u n - qSequence u (n - 1)| / (n : ℝ) ^ 2) := by
  have h := summable_scaled_sequence u
  apply (summable_nat_add_iff 1).mp
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _ (((summable_nat_add_iff 1).mpr h).add h)
  intro n
  simp only [Nat.add_sub_cancel, Pi.add_apply]
  by_cases hn : n = 0
  · subst n
    simp
  have hp : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hshift : (n : ℝ) ^ 2 ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by
    push_cast
    nlinarith
  calc
    _ ≤ (|qSequence u (n + 1)| + |qSequence u n|) / ((n + 1 : ℕ) : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (abs_sub _ _) (sq_nonneg _)
    _ ≤ _ := by
      rw [add_div]
      exact add_le_add le_rfl (div_le_div_of_nonneg_left (abs_nonneg _) (sq_pos_of_pos hp) hshift)

/-- Absolute charge mass, applicable to the limiting displacement. -/
theorem summable_scaled_mobiusDifference (f : ℕ → ℝ)
    (hf : Summable (fun k : ℕ => |f k - f (k - 1)| / (k : ℝ) ^ 2)) :
    Summable (fun n : ℕ => |mobiusDifference n f| / (n : ℝ) ^ 2) := by
  let a (k : ℕ) := |f k - f (k - 1)| / (k : ℝ) ^ 2
  let b (k : ℕ) := 1 / (k : ℝ) ^ 2
  let w (v : ℕ × ℕ) := a v.1 * b v.2
  have ha : Summable a := hf
  have hb : Summable b := Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hw : Summable w := ha.mul_of_nonneg hb (fun k => by dsimp [a]; positivity)
    (fun k => by dsimp [b]; positivity)
  let mult (v : ℕ × ℕ) := v.1 * v.2
  have hnn (v : ℕ × ℕ) : 0 ≤ w v := by dsimp [w, a, b]; positivity
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _ (hw.hasSum.tsum_fiberwise mult).summable
  intro n
  by_cases hn : n = 0
  · subst n
    simp only [Nat.cast_zero, zero_pow (by decide : 2 ≠ 0), div_zero]
    exact tsum_nonneg fun i => hnn _
  have hset : mult ⁻¹' {n} = (n.divisorsAntidiagonal : Set (ℕ × ℕ)) := by
    ext x
    simp [mult, hn]
  rw [hset, Finset.tsum_subtype' n.divisorsAntidiagonal w]
  unfold mobiusDifference
  rw [← Nat.sum_divisorsAntidiagonal (fun i j => (ArithmeticFunction.moebius j : ℝ) *
    (f i - f (i - 1)))]
  calc
    _ ≤ (∑ v ∈ n.divisorsAntidiagonal, |(ArithmeticFunction.moebius v.2 : ℝ) *
          (f v.1 - f (v.1 - 1))|) / (n : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (sq_nonneg _)
    _ ≤ _ := by
      rw [Finset.sum_div]
      apply Finset.sum_le_sum
      intro v hv
      have hprod := (Nat.mem_divisorsAntidiagonal.mp hv).1
      have hmu : |(ArithmeticFunction.moebius v.2 : ℝ)| ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := v.2)
      rw [abs_mul, ← hprod, Nat.cast_mul, mul_pow]
      dsimp [w, a, b]
      rw [div_mul_div_comm, mul_one]
      apply div_le_div_of_nonneg_right _ (by positivity)
      simpa using mul_le_mul_of_nonneg_right hmu (abs_nonneg (f v.1 - f (v.1 - 1)))

theorem qSequence_mobiusDifference_absolute_mass (u : QHilbert) :
    Summable (fun n : ℕ => |mobiusDifference n (qSequence u)| / (n : ℝ) ^ 2) :=
  summable_scaled_mobiusDifference _ (summable_scaled_difference u)

end RiemannResearch.RH.Pareto
