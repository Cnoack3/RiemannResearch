/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.CotangentBridge

/-!
# Finite cotangent multiplication from the already proved digamma series

This avoids a finite sine-product theorem: an absolutely convergent reciprocal
difference series is grouped by its natural residue classes, with reflected
finite indices handled by `Fin.revPerm` before evaluating the series.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto

def cotangentAt (x : ℝ) : ℝ := Real.cos (Real.pi*x) / Real.sin (Real.pi*x)

theorem hasSum_cotangent_reciprocal_difference {x : ℝ}
    (hx : 0 < x) (hx1 : x < 1) :
    HasSum (fun n : ℕ => 1/((n : ℝ)+x) - 1/((n : ℝ)+1-x))
      (Real.pi*cotangentAt x) := by
  have hs := (hasSum_reciprocal_difference_positive hx).sub
    (hasSum_reciprocal_difference_positive (show 0 < 1-x by linarith))
  have hr := re_digamma_reflection_real hx hx1
  convert! hs using 1
  · funext n
    ring
  · unfold cotangentAt
    linarith

/-- Complete finite cotangent multiplication, with every point strictly inside
the first pole interval. -/
theorem cotangent_finite_multiplication (q : ℕ) (hq : 0 < q) (x : ℝ)
    (hx : 0 < x) (hqx : (q : ℝ)*x < 1) :
    (∑ t : Fin q, cotangentAt (x+(t.val : ℝ)/q)) =
      (q : ℝ)*cotangentAt ((q : ℝ)*x) := by
  haveI : NeZero q := ⟨ne_of_gt hq⟩
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  let y : Fin q → ℝ := fun t => x+(t.val : ℝ)/q
  let z : Fin q → ℝ := fun t => 1-y t.rev
  have hy0 (t : Fin q) : 0 < y t := by dsimp [y]; positivity
  have hy1 (t : Fin q) : y t < 1 := by
    have ht : (t.val : ℝ)+1 ≤ q := by exact_mod_cast (show t.val+1 ≤ q by omega)
    have he : y t * (q : ℝ) = (q : ℝ)*x+t.val := by dsimp [y]; field_simp
    nlinarith
  have hz0 (t : Fin q) : 0 < z t := by dsimp [z]; linarith [hy1 t.rev]
  have hz1 (t : Fin q) : z t < 1 := by dsimp [z]; linarith [hy0 t.rev]
  have hqx0 : 0 < (q : ℝ)*x := mul_pos hqR hx
  let g : ℕ → ℝ := fun n => 1/((n : ℝ)+(q : ℝ)*x) -
    1/((n : ℝ)+1-(q : ℝ)*x)
  have hsg : HasSum g (Real.pi*cotangentAt ((q : ℝ)*x)) :=
    hasSum_cotangent_reciprocal_difference hqx0 hqx
  have hclass (t : Fin q) :
      HasSum (fun n : ℕ => (q : ℝ)*g (t.val+q*n))
        (-(Complex.digamma (y t : ℂ)).re + (Complex.digamma (z t : ℂ)).re) := by
    have hs := (hasSum_reciprocal_difference_positive (hy0 t)).sub
      (hasSum_reciprocal_difference_positive (hz0 t))
    have ht : (t.rev.val : ℝ)+(t.val : ℝ)+1 = q := by
      have hn : t.rev.val+t.val+1 = q := by
        simp only [Fin.val_rev]
        omega
      exact_mod_cast hn
    have hyt : (q : ℝ)*y t = (q : ℝ)*x+t.val := by dsimp [y]; field_simp
    have hzt : (q : ℝ)*z t = 1-(q : ℝ)*x+t.val := by
      calc
        _ = (q : ℝ) - ((q : ℝ)*x+t.rev.val) := by
          dsimp [z, y]
          field_simp [ne_of_gt hqR]
        _ = _ := by linarith
    convert! hs using 1
    · funext n
      dsimp [g]
      push_cast
      have hd1 : (n : ℝ)+y t ≠ 0 := ne_of_gt
        (add_pos_of_nonneg_of_pos (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ)) (hy0 t))
      have hd2 : (n : ℝ)+z t ≠ 0 := ne_of_gt
        (add_pos_of_nonneg_of_pos (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ)) (hz0 t))
      have he3 : (t.val : ℝ)+(q : ℝ)*n+(q : ℝ)*x = (q : ℝ)*((n : ℝ)+y t) := by
        nlinarith
      have he4 : (t.val : ℝ)+(q : ℝ)*n+1-(q : ℝ)*x = (q : ℝ)*((n : ℝ)+z t) := by
        nlinarith
      rw [he3, he4]
      field_simp [hd1, hd2, ne_of_gt hqR]
      <;> ring
    · ring
  have hgroups : (q : ℝ) * Real.pi * cotangentAt ((q : ℝ)*x) =
      ∑ t : Fin q,
        (-(Complex.digamma (y t : ℂ)).re + (Complex.digamma (z t : ℂ)).re) := by
    calc
      _ = (q : ℝ) * ∑' n, g n := by rw [hsg.tsum_eq]; ring
      _ = ∑ t : Fin q, ∑' n, (q : ℝ)*g (t.val+q*n) := by
        rw [Nat.sumByResidueClasses hsg.summable q, Finset.mul_sum]
        -- `sumByResidueClasses` is indexed by ZMod q. At positive q,
        -- both its type and Fintype instance reduce to those of Fin q.
        cases q with
        | zero => omega
        | succ r =>
          apply Finset.sum_congr rfl
          intro t _
          exact (tsum_mul_left :
            (∑' n, ((r+1 : ℕ) : ℝ)*g (t.val+(r+1)*n)) =
              ((r+1 : ℕ) : ℝ)*∑' n, g (t.val+(r+1)*n)).symm
      _ = _ := by simp_rw [(hclass _).tsum_eq]
  have hzsum : (∑ t : Fin q, (Complex.digamma (z t : ℂ)).re) =
      ∑ t : Fin q, (Complex.digamma ((1-y t : ℝ) : ℂ)).re := by
    exact Equiv.sum_comp Fin.revPerm (fun t : Fin q =>
      (Complex.digamma ((1-y t : ℝ) : ℂ)).re)
  rw [Finset.sum_add_distrib, hzsum] at hgroups
  have href (t : Fin q) : -(Complex.digamma (y t : ℂ)).re +
      (Complex.digamma ((1-y t : ℝ) : ℂ)).re = Real.pi*cotangentAt (y t) := by
    have h := re_digamma_reflection_real (hy0 t) (hy1 t)
    unfold cotangentAt
    linarith
  rw [← Finset.sum_add_distrib] at hgroups
  simp_rw [href] at hgroups
  rw [← Finset.mul_sum] at hgroups
  apply mul_left_cancel₀ Real.pi_ne_zero
  change Real.pi * (∑ t : Fin q, cotangentAt (y t)) =
    Real.pi * ((q : ℝ)*cotangentAt ((q : ℝ)*x))
  nlinarith

end RiemannResearch.RH.Pareto
