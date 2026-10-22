import RiemannResearch.RH.DyadicFiniteBoundaryCoordinates

/-!
# Uniform boundary mass on each multiplicative annulus

Source: user-provided `DyadicRegularizedVerificationContinuation20260910 (2).md`,
Appendix §2, September 10, 2026. The following actual-coordinate bound supplies
the uniform one-level contribution estimate directly from physical refinement.
It does not yet identify the geometric support of the dyadic tent kernel.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
noncomputable section

private theorem boundary_indicator_sum (s : Finset ℕ) (l : ℕ) (hl : 0 < l) :
    (∑ i ∈ s, if i+1=l then (1 : ℝ) else 0) =
      if l-1 ∈ s then 1 else 0 := by
  have h (i : ℕ) : (i+1=l) ↔ i=l-1 := by omega
  simp only [h, Finset.sum_ite_eq', one_mul]

/-- The total actual coefficient mass in any boundary annulus `[L,2L)`
is at most one, uniformly in the positive integer step. -/
theorem dyadicBoundaryCoordinate_step_annulus_sum_le_one
    (s : Finset ℕ) (L : ℕ) (hL : 0 < L)
    (hs : ∀ i ∈ s, L ≤ i+1 ∧ i+1 < 2*L)
    (m : ℕ) (hm : 0 < m) :
    (∑ i ∈ s, dyadicBoundaryCoordinate (dyadicProjectedStep m hm) i) ≤ 1 := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases h1 : m = 1
    · subst m
      simp only [dyadicProjectedStep_one, dyadicBoundaryCoordinate_one,
        Finset.sum_const_zero]
      norm_num
    have hm2 : 2 ≤ m := by omega
    have hl : 0 < m/2 := Nat.div_pos_iff.mpr ⟨by norm_num, hm2⟩
    have hmod := Nat.mod_lt m (by norm_num : 0 < 2)
    have hdecomp := Nat.mod_add_div m 2
    by_cases he : m % 2 = 0
    · have hmform : m = 2*(m/2) := by omega
      have hv : dyadicProjectedStep m hm = dyadicProjectedStep (m/2) hl := by
        simpa only [← hmform] using dyadicProjectedStep_double (m/2) hl
      rw [hv]
      exact ih (m/2) (by omega) hl
    · have hmform : m = 2*(m/2)+1 := by omega
      have hv (i : ℕ) : dyadicBoundaryCoordinate (dyadicProjectedStep m hm) i =
          (if i+1 = m/2 then 1 else 0) + (1/2 : ℝ) *
            (dyadicBoundaryCoordinate (dyadicProjectedStep (m/2) hl) i +
              dyadicBoundaryCoordinate
                (dyadicProjectedStep (m/2+1) (by positivity)) i) := by
        simpa only [← hmform] using dyadicBoundaryCoordinate_step_odd (m/2) hl i
      simp_rw [hv]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib,
        boundary_indicator_sum s (m/2) hl]
      by_cases hroot : m/2-1 ∈ s
      · rw [if_pos hroot]
        have hroot_hi := (hs (m/2-1) hroot).2
        have hlow : (∑ i ∈ s,
            dyadicBoundaryCoordinate (dyadicProjectedStep (m/2) hl) i) = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          have h := (hs i hi).1
          exact dyadicBoundaryCoordinate_step_zero (m/2) hl i (by omega)
        have hhigh : (∑ i ∈ s,
            dyadicBoundaryCoordinate
              (dyadicProjectedStep (m/2+1) (by positivity)) i) = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          have h := (hs i hi).1
          exact dyadicBoundaryCoordinate_step_zero (m/2+1) (by positivity) i (by omega)
        rw [hlow, hhigh]
        norm_num
      · rw [if_neg hroot]
        have ha := ih (m/2) (by omega) hl
        have hb := ih (m/2+1) (by omega) (by positivity)
        linarith

/-- Every actual mixed boundary contribution from one annulus lies in `[0,1]`.
This supplies the one-level estimate in the logarithmic kernel argument. -/
theorem dyadicBoundaryCoordinate_step_annulus_product_sum_mem_unit
    (s : Finset ℕ) (L : ℕ) (hL : 0 < L)
    (hs : ∀ i ∈ s, L ≤ i+1 ∧ i+1 < 2*L)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    0 ≤ (∑ i ∈ s,
      dyadicBoundaryCoordinate (dyadicProjectedStep m hm) i *
        dyadicBoundaryCoordinate (dyadicProjectedStep n hn) i) ∧
      (∑ i ∈ s,
        dyadicBoundaryCoordinate (dyadicProjectedStep m hm) i *
          dyadicBoundaryCoordinate (dyadicProjectedStep n hn) i) ≤ 1 := by
  constructor
  · apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (dyadicBoundaryCoordinate_step_mem_unit m hm i).1
      (dyadicBoundaryCoordinate_step_mem_unit n hn i).1
  · calc
      _ ≤ ∑ i ∈ s, dyadicBoundaryCoordinate (dyadicProjectedStep m hm) i := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_of_le_one_right
          (dyadicBoundaryCoordinate_step_mem_unit m hm i).1
          (dyadicBoundaryCoordinate_step_mem_unit n hn i).2
      _ ≤ 1 := dyadicBoundaryCoordinate_step_annulus_sum_le_one s L hL hs m hm

/-- Explicit dyadic levels inherit the uniform mixed-contribution bound. -/
theorem dyadicBoundaryCoordinate_step_level_product_sum_mem_unit
    (r m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    0 ≤ (∑ l ∈ Finset.Ico (2^r-1) (2^(r+1)-1),
      dyadicBoundaryCoordinate (dyadicProjectedStep m hm) l *
        dyadicBoundaryCoordinate (dyadicProjectedStep n hn) l) ∧
      (∑ l ∈ Finset.Ico (2^r-1) (2^(r+1)-1),
        dyadicBoundaryCoordinate (dyadicProjectedStep m hm) l *
          dyadicBoundaryCoordinate (dyadicProjectedStep n hn) l) ≤ 1 := by
  apply dyadicBoundaryCoordinate_step_annulus_product_sum_mem_unit
    (Finset.Ico (2^r-1) (2^(r+1)-1)) (2^r) (by positivity)
  intro i hi
  have hp : 0 < (2 : ℕ)^r := by positivity
  have hi' := Finset.mem_Ico.mp hi
  rw [pow_succ'] at hi'
  constructor <;> omega

/-- Summing the first `R` physical boundary levels costs at most `R`, with
the complete signed Gram products still present in the summand. -/
theorem dyadicBoundaryCoordinate_step_dyadic_prefix_product_sum_le
    (R m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    (∑ i ∈ Finset.range (2^R-1),
      dyadicBoundaryCoordinate (dyadicProjectedStep m hm) i *
        dyadicBoundaryCoordinate (dyadicProjectedStep n hn) i) ≤ (R : ℝ) := by
  induction R with
  | zero => simp
  | succ R ih =>
    have hp : 0 < (2 : ℕ)^R := by positivity
    have hab : 2^R-1 ≤ 2^(R+1)-1 := by
      rw [pow_succ']
      omega
    have hu : Finset.range (2^(R+1)-1) =
        Finset.range (2^R-1) ∪ Finset.Ico (2^R-1) (2^(R+1)-1) := by
      ext i
      simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
      omega
    have hd : Disjoint (Finset.range (2^R-1))
        (Finset.Ico (2^R-1) (2^(R+1)-1)) := by
      apply Finset.disjoint_left.mpr
      intro i hi hj
      have hi' := Finset.mem_range.mp hi
      have hj' := (Finset.mem_Ico.mp hj).1
      omega
    rw [hu, Finset.sum_union hd]
    have hlevel := (dyadicBoundaryCoordinate_step_level_product_sum_mem_unit R m n hm hn).2
    push_cast
    linarith

end
end RiemannResearch.RH.Pareto
