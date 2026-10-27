/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.CountableJumpEnergy
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Exact signed identity for a complete reversible countable energy

Source: the user's actual prime-resampling formalization agenda. Absolute
summability of both square terms and the mixed term is established before
rearranging the signed series. The energy itself remains ENNReal-valued.
-/

noncomputable section
open scoped BigOperators ENNReal
namespace RiemannResearch.Analysis.CountableJumpEnergy
variable {α : Type*}

/-- An ordinary square budget and a row-mass envelope give absolute
summability of the complete first square term. -/
theorem kernel_first_square_summable
    (W : α → α → ℝ) (g μ : α → ℝ)
    (hW : ∀ x y, 0 ≤ W x y)
    (hrows : ∀ x, Summable (W x))
    (hrate : ∀ x, (∑' y, W x y) ≤ μ x)
    (hsq : Summable (fun x => μ x * (g x) ^ 2)) :
    Summable (fun e : α × α => W e.1 e.2 * (g e.1) ^ 2) := by
  apply (summable_prod_of_nonneg (fun e => mul_nonneg (hW e.1 e.2) (sq_nonneg _))).mpr
  constructor
  · intro x
    exact (hrows x).mul_right ((g x) ^ 2)
  · have hs : Summable (fun x => (∑' y, W x y) * (g x) ^ 2) := by
      exact Summable.of_nonneg_of_le
        (fun x => mul_nonneg (tsum_nonneg (hW x)) (sq_nonneg _))
        (fun x => mul_le_mul_of_nonneg_right (hrate x) (sq_nonneg _)) hsq
    simpa only [tsum_mul_right] using hs

/-- Exact complete-countable quadratic identity. The displayed signed series
is justified by the supplied first-square budget and reversibility. -/
theorem countableJumpEnergy_eq_signed_rows
    (W : α → α → ℝ) (g : α → ℝ)
    (hW : ∀ x y, 0 ≤ W x y) (hsym : ∀ x y, W x y = W y x)
    (hfirst : Summable (fun e : α × α => W e.1 e.2 * (g e.1) ^ 2)) :
    countableJumpEnergy (fun x y => ENNReal.ofReal (W x y)) g =
      ENNReal.ofReal (∑' x, g x * (∑' y, W x y * (g x - g y))) := by
  let A (e : α × α) : ℝ := W e.1 e.2 * (g e.1) ^ 2
  let B (e : α × α) : ℝ := W e.1 e.2 * (g e.2) ^ 2
  let X (e : α × α) : ℝ := W e.1 e.2 * g e.1 * g e.2
  let J (e : α × α) : ℝ := W e.1 e.2 * ((g e.1 - g e.2) ^ 2 / 2)
  let F (e : α × α) : ℝ := W e.1 e.2 * g e.1 * (g e.1 - g e.2)
  have hA : Summable A := hfirst
  have hB : Summable B := by
    have h := hA.comp_injective (Equiv.prodComm α α).injective
    apply h.congr
    intro e
    change W e.2 e.1 * (g e.2) ^ 2 = W e.1 e.2 * (g e.2) ^ 2
    rw [hsym e.2 e.1]
  have hX : Summable X := by
    apply (hA.add hB).of_norm_bounded
    intro e
    have hxy : |g e.1 * g e.2| ≤ (g e.1) ^ 2 + (g e.2) ^ 2 := by
      rw [abs_mul]
      nlinarith [sq_nonneg (|g e.1| - |g e.2|), sq_abs (g e.1), sq_abs (g e.2)]
    have hm := mul_le_mul_of_nonneg_left hxy (hW e.1 e.2)
    simpa only [X, A, B, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hW e.1 e.2),
      mul_add, mul_assoc] using hm
  have hJ : Summable J := by
    apply (((hA.add hB).div_const 2).sub hX).congr
    intro e
    dsimp [J, A, B, X]
    ring
  have hF : Summable F := by
    apply (hA.sub hX).congr
    intro e
    dsimp [F, A, X]
    ring
  have hBA : (∑' e : α × α, B e) = ∑' e : α × α, A e := by
    have h := (Equiv.prodComm α α).tsum_eq A
    change (∑' e : α × α, W e.2 e.1 * (g e.2) ^ 2) = ∑' e : α × α, A e at h
    calc
      _ = ∑' e : α × α, W e.2 e.1 * (g e.2) ^ 2 := by
        apply tsum_congr
        intro e
        dsimp [B]
        rw [hsym e.1 e.2]
      _ = _ := h
  have hJF : (∑' e : α × α, J e) = ∑' e : α × α, F e := by
    have hj : J = fun e => (A e + B e) / 2 - X e := by
      funext e
      dsimp [J, A, B, X]
      ring
    have hf : F = fun e => A e - X e := by
      funext e
      dsimp [F, A, X]
      ring
    rw [hj, hf, Summable.tsum_sub ((hA.add hB).div_const 2) hX,
      Summable.tsum_sub hA hX, tsum_div_const, hA.tsum_add hB, hBA]
    ring
  have hFrows : (∑' e : α × α, F e) = ∑' x, g x * (∑' y, W x y * (g x - g y)) := by
    rw [hF.tsum_prod]
    apply tsum_congr
    intro x
    rw [← tsum_mul_left]
    apply tsum_congr
    intro y
    dsimp [F]
    ring
  calc
    _ = ∑' e : α × α, ENNReal.ofReal (J e) := by
      rw [countableJumpEnergy_eq_tsum_prod]
      apply tsum_congr
      intro e
      exact (ENNReal.ofReal_mul (hW e.1 e.2)).symm
    _ = ENNReal.ofReal (∑' e : α × α, J e) :=
      (ENNReal.ofReal_tsum_of_nonneg (f := J) (fun e : α × α =>
        mul_nonneg (hW e.1 e.2) (div_nonneg (sq_nonneg _) (by norm_num))) hJ).symm
    _ = _ := by rw [hJF, hFrows]

end RiemannResearch.Analysis.CountableJumpEnergy
