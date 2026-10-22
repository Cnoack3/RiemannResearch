/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.Linarith

/-!
# Bessel--Minkowski bounds for genuinely moving Hilbert vectors

Source: the user's October 1, 2026 Route B continuation, ordinary Bessel's
inequality and Minkowski's inequality, through Mathlib's finite Bessel and
norm-of-sum bounds. The application is the complete signed screening
discrepancy in the Pareto prime contrast program.

The finite masked theorem retains every signed increment. Absolute total
variation is an explicit provider, not a consequence of boundedness or
strong convergence. Orthogonality of the tests is also explicit.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.MovingOrthogonalEnergy
variable {H ι κ : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [Fintype ι] [DecidableEq ι] [Fintype κ]

def pairingVector (v : ι → H) (R : ι → H) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => inner ℝ (v i) (R i))

def maskedPairingVector (v : ι → H) (x : H) (s : Finset ι) :
    EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => if i ∈ s then inner ℝ (v i) x else 0)

theorem maskedPairingVector_norm_le (v : ι → H) (hv : Orthonormal ℝ v)
    (x : H) (s : Finset ι) :
    ‖maskedPairingVector v x s‖ ≤ ‖x‖ := by
  have hb : (∑ i : ι, (inner ℝ (v i) x)^2) ≤ ‖x‖^2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (hv.sum_inner_products_le (s := Finset.univ) x)
  have hm : ‖maskedPairingVector v x s‖^2 ≤ ‖x‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ i : ι, (inner ℝ (v i) x)^2 := by
        apply Finset.sum_le_sum
        intro i hi
        simp only [maskedPairingVector, WithLp.ofLp_toLp]
        split_ifs <;> nlinarith [sq_nonneg (inner ℝ (v i) x)]
      _ ≤ ‖x‖^2 := hb
  nlinarith [norm_nonneg (maskedPairingVector v x s), norm_nonneg x]

/-- Finite moving Bessel--Minkowski estimate with the complete signed increments. -/
theorem finite_masked_moving_bound (v : ι → H) (hv : Orthonormal ℝ v)
    (R : ι → H) (x : H) (d : κ → H) (s : κ → Finset ι)
    (hR : ∀ i, R i = x + ∑ k, if i ∈ s k then d k else 0) :
    ‖pairingVector v R‖ ≤ ‖x‖ + ∑ k, ‖d k‖ := by
  have he : pairingVector v R =
      maskedPairingVector v x Finset.univ + ∑ k, maskedPairingVector v (d k) (s k) := by
    apply WithLp.ofLp_injective 2
    funext i
    simp only [pairingVector, maskedPairingVector, WithLp.ofLp_add,
      WithLp.ofLp_sum, WithLp.ofLp_toLp, Pi.add_apply, Finset.sum_apply,
      Finset.mem_univ, if_true, hR i, inner_add_right, inner_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    split_ifs <;> simp
  rw [he]
  calc
    _ ≤ ‖maskedPairingVector v x Finset.univ‖ +
        ‖∑ k, maskedPairingVector v (d k) (s k)‖ := norm_add_le _ _
    _ ≤ ‖x‖ + ∑ k, ‖maskedPairingVector v (d k) (s k)‖ :=
      add_le_add (maskedPairingVector_norm_le v hv x _) (norm_sum_le _ _)
    _ ≤ ‖x‖ + ∑ k, ‖d k‖ := by
      apply add_le_add_right
      exact Finset.sum_le_sum (fun k _ => maskedPairingVector_norm_le v hv (d k) (s k))


/-- Finite diagonal energy, preserving all increments through the cutoff. -/
theorem moving_pairing_prefix_bound (v R : ℕ → H) (hv : Orthonormal ℝ v) (N : ℕ) :
    (∑ j ∈ Finset.range N, (inner ℝ (v j) (R j))^2) ≤
      (‖R 0‖ + ∑ i ∈ Finset.range N, ‖R (i+1) - R i‖)^2 := by
  classical
  let vf : Fin N → H := fun j => v j.val
  let rf : Fin N → H := fun j => R j.val
  let d : Fin N → H := fun i => R (i.val+1) - R i.val
  let s : Fin N → Finset (Fin N) := fun i => Finset.univ.filter (fun j => i.val < j.val)
  have hvf : Orthonormal ℝ vf := hv.comp Fin.val Fin.val_injective
  have hreal (j : Fin N) :
      rf j = R 0 + ∑ i : Fin N, if j ∈ s i then d i else 0 := by
    simp only [rf, s, Finset.mem_filter, Finset.mem_univ, true_and, d]
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => if i < j.val then R (i+1) - R i else 0), ← Finset.sum_filter]
    have he : (Finset.range N).filter (fun i => i < j.val) = Finset.range j.val := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range]
      have hj := j.isLt
      omega
    rw [he, Finset.sum_range_sub]
    abel
  have hb := finite_masked_moving_bound vf hvf rf (R 0) d s hreal
  have hb0 : 0 ≤ ‖R 0‖ + ∑ i : Fin N, ‖d i‖ :=
    add_nonneg (norm_nonneg _) (Finset.sum_nonneg (fun i _ => norm_nonneg _))
  have hsq : ‖pairingVector vf rf‖^2 ≤ (‖R 0‖ + ∑ i : Fin N, ‖d i‖)^2 :=
    (sq_le_sq₀ (norm_nonneg _) hb0).2 hb
  have hh : (∑ j : Fin N, (inner ℝ (v j.val) (R j.val))^2) ≤
      (‖R 0‖ + ∑ i : Fin N, ‖R (i.val+1)-R i.val‖)^2 := by
    simpa only [EuclideanSpace.real_norm_sq_eq, pairingVector, WithLp.ofLp_toLp,
      vf, rf, d] using hsq
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => (inner ℝ (v j) (R j))^2),
    Fin.sum_univ_eq_sum_range (fun i : ℕ => ‖R (i+1)-R i‖)] at hh
  exact hh

/-- The actual absolute-variation provider remains an explicit hypothesis. -/
theorem moving_pairing_summable (v R : ℕ → H) (hv : Orthonormal ℝ v)
    (hvar : Summable (fun i => ‖R (i+1) - R i‖)) :
    Summable (fun j => (inner ℝ (v j) (R j))^2) := by
  apply summable_of_sum_range_le (fun j => sq_nonneg _)
  intro N
  apply (moving_pairing_prefix_bound v R hv N).trans
  have hl := hvar.sum_le_tsum (Finset.range N) (fun i _ => norm_nonneg (R (i+1)-R i))
  have hp : 0 ≤ ∑ i ∈ Finset.range N, ‖R (i+1)-R i‖ :=
    Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have ht : 0 ≤ ∑' i, ‖R (i+1)-R i‖ := tsum_nonneg (fun i => norm_nonneg _)
  exact (sq_le_sq₀ (add_nonneg (norm_nonneg _) hp)
    (add_nonneg (norm_nonneg _) ht)).2 (add_le_add_right hl _)

end RiemannResearch.Analysis.MovingOrthogonalEnergy
