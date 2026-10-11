import RiemannResearch.Analysis.OrdinateCollisionRemainder
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Collision-mass bound for a rank-separated finite ordinate family

For `N` ordinate locations indexed by `Fin N`, the explicit assumption is
`δ * |i - j| ≤ |τ i - τ j|`. In particular the locations are distinct.
Natural multiplicities are unrestricted. The exact finite sinc-squared
remainder is bounded by `4 π² C / (3 R² δ²)` with `C = ∑ M_i²`.

The proof compares each finite rank row with the full integer Basel series,
then uses symmetry and `2 M_i M_j ≤ M_i² + M_j²`. No zeta-zero sampling input
or RH assumption occurs in this finite theorem.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.OrdinateCollisionCertificate

theorem hasSum_int_inverse_square :
    HasSum (fun z : ℤ => (1 : ℝ) / (z : ℝ) ^ 2) (Real.pi ^ 2 / 3) := by
  have hsucc : HasSum (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2)
      (Real.pi ^ 2 / 6) := by
    have h := (hasSum_nat_add_iff' (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) 1).mpr
      hasSum_zeta_two
    simpa using h
  have hpos : HasSum (fun n : ℕ => (1 : ℝ) / ((n : ℤ) : ℝ) ^ 2)
      (Real.pi ^ 2 / 6) := by simpa using hasSum_zeta_two
  have hneg : HasSum (fun n : ℕ => (1 : ℝ) / ((-((n : ℤ) + 1) : ℤ) : ℝ) ^ 2)
      (Real.pi ^ 2 / 6) := by
    have heq :
        (fun n : ℕ => (1 : ℝ) / ((-((n : ℤ) + 1) : ℤ) : ℝ) ^ 2) =
        (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) := by
      funext n
      push_cast
      congr 1
      ring
    rw [heq]
    exact hsucc
  have h := HasSum.of_nat_of_neg_add_one
    (f := fun z : ℤ => (1 : ℝ) / (z : ℝ) ^ 2) hpos hneg
  convert h using 1 <;> ring

def rankInverseSquare {N : ℕ} (i j : Fin N) : ℝ :=
  1 / ((i.val : ℝ) - (j.val : ℝ)) ^ 2

theorem rankInverseSquare_nonneg {N : ℕ} (i j : Fin N) :
    0 ≤ rankInverseSquare i j := div_nonneg (by norm_num) (sq_nonneg _)

@[simp] theorem rankInverseSquare_self {N : ℕ} (i : Fin N) :
    rankInverseSquare i i = 0 := by simp [rankInverseSquare]

theorem rankInverseSquare_symm {N : ℕ} (i j : Fin N) :
    rankInverseSquare i j = rankInverseSquare j i := by
  unfold rankInverseSquare
  congr 1
  ring

/-- Every finite rank row is bounded by the full integer inverse-square sum. -/
theorem rankInverseSquare_row_le {N : ℕ} (i : Fin N) :
    (∑ j : Fin N, rankInverseSquare i j) ≤ Real.pi ^ 2 / 3 := by
  classical
  let e : Fin N → ℤ := fun j => (j.val : ℤ) - (i.val : ℤ)
  have hinj : Function.Injective e := by
    intro a b hab
    apply Fin.ext
    dsimp only [e] at hab
    omega
  calc
    _ = ∑ z ∈ Finset.univ.image e, (1 : ℝ) / (z : ℝ) ^ 2 := by
      rw [Finset.sum_image (fun a _ b _ h => hinj h)]
      apply Finset.sum_congr rfl
      intro j hj
      dsimp only [e, rankInverseSquare]
      push_cast
      congr 1
      ring
    _ ≤ Real.pi ^ 2 / 3 :=
      sum_le_hasSum _ (fun z _ => div_nonneg (by norm_num) (sq_nonneg _))
        hasSum_int_inverse_square

def rankCollisionMass {N : ℕ} (M : Fin N → ℕ) : ℝ := ∑ i, (M i : ℝ) ^ 2

def rankWeightedSincEnergy {N : ℕ} (ordinate : Fin N → ℝ) (M : Fin N → ℕ)
    (R : ℝ) : ℝ :=
  ∑ i, ∑ j, (M i : ℝ) * (M j : ℝ) * sincSquared R (ordinate i - ordinate j)

theorem weighted_rank_inverse_sum_le {N : ℕ} (M : Fin N → ℕ) :
    (∑ i, ∑ j, (M i : ℝ) * (M j : ℝ) * rankInverseSquare i j) ≤
      (Real.pi ^ 2 / 3) * rankCollisionMass M := by
  let S : ℝ := ∑ i, ∑ j, (M i : ℝ) * (M j : ℝ) * rankInverseSquare i j
  let H : ℝ := ∑ i, ∑ j, (M i : ℝ) ^ 2 * rankInverseSquare i j
  have hswap : (∑ i, ∑ j, (M j : ℝ) ^ 2 * rankInverseSquare i j) = H := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [rankInverseSquare_symm j i]
  have htwo : 2 * S ≤ H + H := by
    calc
      _ = ∑ i, ∑ j,
          2 * ((M i : ℝ) * (M j : ℝ) * rankInverseSquare i j) := by
        simp only [S, Finset.mul_sum]
      _ ≤ ∑ i, ∑ j,
          ((M i : ℝ) ^ 2 + (M j : ℝ) ^ 2) * rankInverseSquare i j := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        have hab : 2 * (M i : ℝ) * (M j : ℝ) ≤ (M i : ℝ) ^ 2 + (M j : ℝ) ^ 2 := by
          nlinarith [sq_nonneg ((M i : ℝ) - (M j : ℝ))]
        calc
          _ = (2 * (M i : ℝ) * (M j : ℝ)) * rankInverseSquare i j := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hab (rankInverseSquare_nonneg i j)
      _ = H + H := by
        simp only [add_mul, Finset.sum_add_distrib]
        rw [hswap]
  have hS : S ≤ H := by linarith
  calc
    _ ≤ H := hS
    _ = ∑ i, (M i : ℝ) ^ 2 * (∑ j, rankInverseSquare i j) := by
      simp only [H, Finset.mul_sum]
    _ ≤ ∑ i, (M i : ℝ) ^ 2 * (Real.pi ^ 2 / 3) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (rankInverseSquare_row_le i) (sq_nonneg _)
    _ = (Real.pi ^ 2 / 3) * rankCollisionMass M := by
      simp only [rankCollisionMass, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

theorem sincSquared_rank_bound {N : ℕ} (ordinate : Fin N → ℝ) {R δ : ℝ}
    (hR : 0 < R) (hδ : 0 < δ)
    (hgap : ∀ i j, δ * |(i.val : ℝ) - (j.val : ℝ)| ≤ |ordinate i - ordinate j|)
    {i j : Fin N} (hne : i ≠ j) :
    sincSquared R (ordinate i - ordinate j) ≤
      (4 / (R ^ 2 * δ ^ 2)) * rankInverseSquare i j := by
  have hdne : (i.val : ℝ) - (j.val : ℝ) ≠ 0 := by
    intro h
    apply hne
    apply Fin.ext
    exact_mod_cast sub_eq_zero.mp h
  have hpos : 0 < δ * |(i.val : ℝ) - (j.val : ℝ)| :=
    mul_pos hδ (abs_pos.mpr hdne)
  calc
    _ ≤ 4 / (R ^ 2 * (δ * |(i.val : ℝ) - (j.val : ℝ)|) ^ 2) :=
      sincSquared_le_gap hR hpos (hgap i j)
    _ = _ := by
      unfold rankInverseSquare
      rw [mul_pow, sq_abs]
      field_simp [hR.ne', hδ.ne', hdne] <;> ring

/-- The paper's sharper remainder, conditional only on explicit finite rank separation. -/
theorem rankWeightedSincEnergy_sharp_remainder {N : ℕ}
    (ordinate : Fin N → ℝ) (M : Fin N → ℕ) {R δ : ℝ}
    (hR : 0 < R) (hδ : 0 < δ)
    (hgap : ∀ i j, δ * |(i.val : ℝ) - (j.val : ℝ)| ≤ |ordinate i - ordinate j|) :
    0 ≤ rankWeightedSincEnergy ordinate M R - rankCollisionMass M ∧
    rankWeightedSincEnergy ordinate M R - rankCollisionMass M ≤
      4 * Real.pi ^ 2 * rankCollisionMass M / (3 * R ^ 2 * δ ^ 2) := by
  classical
  let off : ℝ := ∑ i, ∑ j, if i = j then 0 else
    (M i : ℝ) * (M j : ℝ) * sincSquared R (ordinate i - ordinate j)
  let A : ℝ := 4 / (R ^ 2 * δ ^ 2)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hp : ∀ i j : Fin N,
      (M i : ℝ) * (M j : ℝ) * sincSquared R (ordinate i - ordinate j) =
      (if i = j then (M i : ℝ) ^ 2 else 0) +
      (if i = j then 0 else
        (M i : ℝ) * (M j : ℝ) * sincSquared R (ordinate i - ordinate j)) := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp only [sub_self, sincSquared_zero, mul_one, pow_two, if_true, add_zero]
    · simp [hij]
  have heq : rankWeightedSincEnergy ordinate M R = rankCollisionMass M + off := by
    unfold rankWeightedSincEnergy
    calc
      _ = ∑ i, ∑ j, ((if i = j then (M i : ℝ) ^ 2 else 0) +
          (if i = j then 0 else
            (M i : ℝ) * (M j : ℝ) * sincSquared R (ordinate i - ordinate j))) := by
        exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hp i j))
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
          if_true, rankCollisionMass, off]
  have hoff : 0 ≤ off := by
    apply Finset.sum_nonneg
    intro i hi
    apply Finset.sum_nonneg
    intro j hj
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (sincSquared_nonneg R _)
  have hbound : off ≤ A *
      (∑ i, ∑ j, (M i : ℝ) * (M j : ℝ) * rankInverseSquare i j) := by
    calc
      off ≤ ∑ i, ∑ j, A * ((M i : ℝ) * (M j : ℝ) * rankInverseSquare i j) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        by_cases hij : i = j
        · subst j
          simp
        · simp only [hij, if_false]
          calc
            _ ≤ ((M i : ℝ) * (M j : ℝ)) * (A * rankInverseSquare i j) :=
              mul_le_mul_of_nonneg_left (sincSquared_rank_bound ordinate hR hδ hgap hij)
                (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
            _ = _ := by ring
      _ = _ := by simp only [Finset.mul_sum]
  have hrem : rankWeightedSincEnergy ordinate M R - rankCollisionMass M = off := by
    linarith [heq]
  rw [hrem]
  refine ⟨hoff, ?_⟩
  calc
    off ≤ A * (∑ i, ∑ j, (M i : ℝ) * (M j : ℝ) * rankInverseSquare i j) := hbound
    _ ≤ A * ((Real.pi ^ 2 / 3) * rankCollisionMass M) :=
      mul_le_mul_of_nonneg_left (weighted_rank_inverse_sum_le M) hA
    _ = _ := by dsimp [A]; field_simp [hR.ne', hδ.ne'] <;> ring

end RiemannResearch.Analysis.OrdinateCollisionCertificate
