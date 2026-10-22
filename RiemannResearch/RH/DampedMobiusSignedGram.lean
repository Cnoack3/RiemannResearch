import RiemannResearch.RH.DampedMobiusFiniteEnergy

/-!
# Summable damped diagonal and the signed off-diagonal obstruction

For every positive damping the sum of squared residue-atom norms is finite.
No assertion of convergence of the signed vector series follows from this.
The exact finite identity retains all distinct-pair inner products.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto

def dampedMobiusGramDiagonal (ε : ℝ) (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.range N, ‖arithmeticResidueTerm (dampedMobiusWeight ε) m‖ ^ 2

def dampedMobiusGramOffDiagonal (ε : ℝ) (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.range N, ∑ k ∈ (Finset.range N).erase m,
    inner ℝ (arithmeticResidueTerm (dampedMobiusWeight ε) m)
      (arithmeticResidueTerm (dampedMobiusWeight ε) k)

def dampedMobiusDiagonalBudget (ε : ℝ) : ℝ :=
  2 * ∑' m : ℕ, ((m + 1 : ℕ) : ℝ) ^ (-2 * ε - 1)

theorem dampedMobiusResidue_norm_sq_le (ε : ℝ) (m : ℕ) :
    ‖arithmeticResidueTerm (dampedMobiusWeight ε) m‖ ^ 2 ≤
      2 * ((m + 1 : ℕ) : ℝ) ^ (-2 * ε - 1) := by
  have hn : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  have hb := (arithmeticResidueTerm_norm_le (dampedMobiusWeight ε) m).trans
    (mul_le_mul_of_nonneg_left (dampedMobius_half_weight_le ε m) (Real.sqrt_nonneg 2))
  have hp : (((m + 1 : ℕ) : ℝ) ^ (-ε - 1 / 2)) ^ 2 =
      ((m + 1 : ℕ) : ℝ) ^ (-2 * ε - 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]
    congr 1
    norm_num
    ring
  have hs := pow_le_pow_left₀
    (norm_nonneg (arithmeticResidueTerm (dampedMobiusWeight ε) m)) hb 2
  simpa only [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), hp] using hs

theorem dampedMobiusDiagonalMajorant_summable {ε : ℝ} (hε : 0 < ε) :
    Summable (fun m : ℕ => ((m + 1 : ℕ) : ℝ) ^ (-2 * ε - 1)) := by
  exact (summable_nat_add_iff 1).mpr
    (Real.summable_nat_rpow.mpr (by linarith : -2 * ε - 1 < -1))

/-- The diagonal is harmless at EVERY positive damping, including below one half. -/
theorem dampedMobiusResidue_norm_sq_summable {ε : ℝ} (hε : 0 < ε) :
    Summable (fun m : ℕ => ‖arithmeticResidueTerm (dampedMobiusWeight ε) m‖ ^ 2) := by
  exact Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
    (dampedMobiusResidue_norm_sq_le ε)
    ((dampedMobiusDiagonalMajorant_summable hε).mul_left 2)

theorem dampedMobiusGramDiagonal_nonneg (ε : ℝ) (N : ℕ) :
    0 ≤ dampedMobiusGramDiagonal ε N :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem dampedMobiusGramDiagonal_le {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    dampedMobiusGramDiagonal ε N ≤ dampedMobiusDiagonalBudget ε := by
  calc
    _ ≤ ∑ m ∈ Finset.range N, 2 * ((m + 1 : ℕ) : ℝ) ^ (-2 * ε - 1) :=
      Finset.sum_le_sum (fun m _ => dampedMobiusResidue_norm_sq_le ε m)
    _ ≤ ∑' m : ℕ, 2 * ((m + 1 : ℕ) : ℝ) ^ (-2 * ε - 1) :=
      Summable.sum_le_tsum (Finset.range N) (fun _ _ => by positivity)
        ((dampedMobiusDiagonalMajorant_summable hε).mul_left 2)
    _ = _ := by rw [tsum_mul_left]; rfl

/-- All off-diagonal signs survive; there is no termwise absolute-value estimate. -/
theorem dampedMobius_partial_norm_sq_eq_signed (ε : ℝ) (N : ℕ) :
    ‖arithmeticFloorHilbertPartial (dampedMobiusWeight ε) N‖ ^ 2 =
      dampedMobiusGramDiagonal ε N + dampedMobiusGramOffDiagonal ε N := by
  rw [arithmeticFloorHilbertPartial, norm_neg, ← real_inner_self_eq_norm_sq, sum_inner]
  simp_rw [inner_sum]
  unfold dampedMobiusGramDiagonal dampedMobiusGramOffDiagonal
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  rw [← Finset.sum_erase_add _
    (fun k => inner ℝ (arithmeticResidueTerm (dampedMobiusWeight ε) m)
      (arithmeticResidueTerm (dampedMobiusWeight ε) k)) hm,
    real_inner_self_eq_norm_sq]
  ring

theorem dampedMobius_partial_norm_sq_le_offDiagonal {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ‖arithmeticFloorHilbertPartial (dampedMobiusWeight ε) N‖ ^ 2 ≤
      dampedMobiusDiagonalBudget ε + dampedMobiusGramOffDiagonal ε N := by
  rw [dampedMobius_partial_norm_sq_eq_signed]
  exact add_le_add (dampedMobiusGramDiagonal_le hε N) le_rfl

theorem dampedMobius_offDiagonal_le_partial_norm_sq (ε : ℝ) (N : ℕ) :
    dampedMobiusGramOffDiagonal ε N ≤
      ‖arithmeticFloorHilbertPartial (dampedMobiusWeight ε) N‖ ^ 2 := by
  rw [dampedMobius_partial_norm_sq_eq_signed]
  linarith [dampedMobiusGramDiagonal_nonneg ε N]

/-- For fixed positive damping boundedness of signed off-diagonal energies is
exactly boundedness of the complete cutoff norms. This is a reduction only. -/
theorem dampedMobius_frequently_bounded_norm_iff_offDiagonal {ε : ℝ} (hε : 0 < ε) :
    (∃ C : ℝ, ∃ᶠ N in atTop,
      ‖arithmeticFloorHilbertPartial (dampedMobiusWeight ε) N‖ ^ 2 ≤ C) ↔
    (∃ C : ℝ, ∃ᶠ N in atTop, dampedMobiusGramOffDiagonal ε N ≤ C) := by
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C, hC.mono (fun N hN =>
      (dampedMobius_offDiagonal_le_partial_norm_sq ε N).trans hN)⟩
  · rintro ⟨C, hC⟩
    refine ⟨dampedMobiusDiagonalBudget ε + C, hC.mono ?_⟩
    intro N hN
    exact (dampedMobius_partial_norm_sq_le_offDiagonal hε N).trans
      (add_le_add le_rfl hN)

/-- Exact partial coordinates once the residue cutoff contains the physical head. -/
theorem arithmeticFloorHilbertPartial_sequence_of_le
    (w : ℕ → ℝ) (N n : ℕ) (hnN : n ≤ N) :
    hilbertSequence (arithmeticFloorHilbertPartial w N) n =
      arithmeticFloorPrefix w n - (n : ℝ) *
        (∑ m ∈ Finset.range N, w (m + 1) / ((m + 1 : ℕ) : ℝ)) := by
  have hfloor : (∑ m ∈ Finset.range N, w (m + 1) * (n / (m + 1) : ℕ)) =
      arithmeticFloorPrefix w n := by
    rw [arithmeticFloorPrefix_eq_sum hnN, Finset.sum_range_succ']
    simp
  have hterm (m : ℕ) :
      (w (m + 1) / ((m + 1 : ℕ) : ℝ)) * residue (m + 1) n =
        (n : ℝ) * (w (m + 1) / ((m + 1 : ℕ) : ℝ)) -
          w (m + 1) * (n / (m + 1) : ℕ) := by
    have hd : (residue (m + 1) n : ℝ) +
        ((m + 1 : ℕ) : ℝ) * (n / (m + 1) : ℕ) = n := by
      unfold residue
      exact_mod_cast Nat.mod_add_div n (m + 1)
    have hm0 : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp [hm0]
    linear_combination w (m + 1) * hd
  change hilbertSequenceLinear (-(∑ m ∈ Finset.range N, arithmeticResidueTerm w m)) n = _
  simp only [map_neg, map_sum, Pi.neg_apply, Finset.sum_apply]
  change -(∑ m ∈ Finset.range N, hilbertSequence (arithmeticResidueTerm w m) n) = _
  simp_rw [arithmeticResidueTerm_sequence, hterm]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hfloor]
  ring

end RiemannResearch.RH.Pareto
