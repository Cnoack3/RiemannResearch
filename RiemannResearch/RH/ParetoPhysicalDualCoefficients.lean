import RiemannResearch.RH.ParetoPhysicalDualProjection
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Explicit multiples-sum coefficients of the physical-dual projection

Source: user-provided `Prime_Phases_Agenda_Proof_Attempts.tex`, Proposition
"Explicit dual approximation and its coefficient vector". The coefficients
are extracted from the actual biorthogonal legal atoms, then exactly
reindexed over multiples. No inversion or coefficient-provider hypothesis
occurs in the final expansion theorem.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization
open RiemannResearch.RH.Pareto.DualSupportError
open RiemannResearch.RH.ArithmeticCumulative

private theorem coeff_sum_Icc_one_eq_range (K : ℕ) (f : ℕ → ℝ) :
    (∑ k ∈ Finset.Icc 1 K, f k) = ∑ k ∈ Finset.range K, f (k + 1) := by
  classical
  symm
  apply Finset.sum_bij (fun k hk => k + 1)
  · intro k hk
    exact Finset.mem_Icc.mpr ⟨by omega, by have := Finset.mem_range.mp hk; omega⟩
  · intro k hk l hl hkl
    omega
  · intro k hk
    rcases Finset.mem_Icc.mp hk with ⟨hk1, hkK⟩
    exact ⟨k - 1, Finset.mem_range.mpr (by omega), by omega⟩
  · intro k hk
    rfl

def physicalDualProjectionCoeff (n : ℕ) (i : Fin n) : ℝ :=
  inner ℝ (residueAtom i.val) (physicalDualProjection n)

theorem physicalDualProjectionCoeff_spec (n : ℕ) :
    physicalDualProjection n = physicalDualCombination n (physicalDualProjectionCoeff n) := by
  obtain ⟨a, ha⟩ := physicalDualProjection_expansion n
  have hc (i : Fin n) : physicalDualProjectionCoeff n i = a i := by
    unfold physicalDualProjectionCoeff
    rw [ha]
    unfold physicalDualCombination
    simp only [inner_sum, real_inner_smul_right, finiteResidue_dual]
    simp
  have heq : physicalDualProjectionCoeff n = a := funext hc
  rw [heq]
  exact ha

def physicalProjectionHeadWeight (n k : ℕ) : ℝ :=
  positiveWeight k * hilbertSequence (physicalDualProjection n) k

theorem physicalDualProjectionCoeff_finite_inner (n : ℕ) (i : Fin n) :
    physicalDualProjectionCoeff n i =
      ∑ k ∈ Finset.Icc 1 (n + 1),
        residueFraction (i.val + 2) k * physicalProjectionHeadWeight n k := by
  unfold physicalDualProjectionCoeff
  rw [hilbertGibbs_inner_physical]
  rw [tsum_eq_sum (s := Finset.range (n + 1)) (by
    intro k hk
    rw [hilbertGibbsPhysical_eq, hilbertGibbsPhysical_eq,
      physicalDualProjection_support n (k + 1) (by
        have h := Finset.mem_range.not.mp hk
        omega)]
    simp)]
  rw [coeff_sum_Icc_one_eq_range]
  apply Finset.sum_congr rfl
  intro k hk
  rw [hilbertGibbsPhysical_eq, hilbertGibbsPhysical_eq]
  unfold residueAtom physicalProjectionHeadWeight
  rw [normalizedResidueHilbert_sequence, positiveWeight_succ]
  ring

theorem physicalProjectionHeadWeight_first_moment_zero (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 (n + 1), (k : ℝ) * physicalProjectionHeadWeight n k) = 0 := by
  have ho := physicalDualSpace_inner_finiteLinear n (physicalDualProjection n)
    ((physicalDualSpace n).starProjection_apply_mem hilbertOne)
  rw [inner_finiteLinear_eq_sum] at ho
  rw [coeff_sum_Icc_one_eq_range]
  convert ho using 1
  apply Finset.sum_congr rfl
  intro k hk
  unfold physicalProjectionHeadWeight
  rw [positiveWeight_succ]
  unfold paretoWeight
  push_cast
  have h1 : (k : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (k : ℝ) + 2 ≠ 0 := by positivity
  field_simp [h1, h2]

private theorem residueFraction_eq_linear_sub_quotient (d k : ℕ) (hd : 0 < d) :
    residueFraction d k = (k : ℝ) / (d : ℝ) - ((k / d : ℕ) : ℝ) := by
  unfold residueFraction
  have h : ((k % d : ℕ) : ℝ) + (d : ℝ) * ((k / d : ℕ) : ℝ) = (k : ℝ) := by
    exact_mod_cast Nat.mod_add_div k d
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hd
  apply (eq_sub_iff_add_eq).mpr
  apply (eq_div_iff hd0).mpr
  field_simp [hd0]
  nlinarith

theorem physicalDualProjectionCoeff_floor (n : ℕ) (i : Fin n) :
    physicalDualProjectionCoeff n i =
      -(∑ k ∈ Finset.Icc 1 (n + 1),
        ((k / (i.val + 2) : ℕ) : ℝ) * physicalProjectionHeadWeight n k) := by
  rw [physicalDualProjectionCoeff_finite_inner]
  simp_rw [residueFraction_eq_linear_sub_quotient _ _ (by omega : 0 < i.val + 2),
    sub_mul, div_mul_eq_mul_div, Finset.sum_sub_distrib, ← Finset.sum_div]
  rw [physicalProjectionHeadWeight_first_moment_zero]
  simp

private theorem floor_eq_count_multiples (K d k : ℕ) (hd : 0 < d) (hk : k ≤ K) :
    ((k / d : ℕ) : ℝ) =
      ∑ j ∈ Finset.Icc 1 (K / d), if d * j ≤ k then (1 : ℝ) else 0 := by
  classical
  have hfilter :
      (Finset.Icc 1 (K / d)).filter (fun j => d * j ≤ k) = Finset.Icc 1 (k / d) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Icc]
    have he : d * j ≤ k ↔ j ≤ k / d := by
      simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hd).symm
    have hq : k / d ≤ K / d := Nat.div_le_div_right hk
    rw [he]
    omega
  rw [← Finset.sum_filter, hfilter]
  simp

/-- Exact finite floor/tail reindexing, with every multiple retained. -/
private theorem floor_weighted_sum_eq_multiples (K d : ℕ) (hd : 0 < d) (b : ℕ → ℝ) :
    (∑ k ∈ Finset.Icc 1 K, ((k / d : ℕ) : ℝ) * b k) =
      ∑ j ∈ Finset.Icc 1 (K / d), ∑ k ∈ Finset.Icc (d * j) K, b k := by
  classical
  calc
    _ = ∑ k ∈ Finset.Icc 1 K, ∑ j ∈ Finset.Icc 1 (K / d),
        if d * j ≤ k then b k else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [floor_eq_count_multiples K d k hd (Finset.mem_Icc.mp hk).2, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      split_ifs <;> simp
    _ = ∑ j ∈ Finset.Icc 1 (K / d), ∑ k ∈ Finset.Icc 1 K,
        if d * j ≤ k then b k else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjpos : 0 < j := (Finset.mem_Icc.mp hj).1
      have hprod : 0 < d * j := Nat.mul_pos hd hjpos
      have he : (Finset.Icc 1 K).filter (fun k => d * j ≤ k) = Finset.Icc (d * j) K := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_Icc]
        omega
      rw [← Finset.sum_filter, he]

def physicalProjectionTailCharge (n m : ℕ) : ℝ :=
  -(∑ k ∈ Finset.Icc m (n + 1), physicalProjectionHeadWeight n k)

theorem physicalDualProjectionCoeff_multiples (n : ℕ) (i : Fin n) :
    physicalDualProjectionCoeff n i =
      ∑ j ∈ Finset.Icc 1 ((n + 1) / (i.val + 2)),
        physicalProjectionTailCharge n ((i.val + 2) * j) := by
  rw [physicalDualProjectionCoeff_floor,
    floor_weighted_sum_eq_multiples (n + 1) (i.val + 2) (by omega)]
  unfold physicalProjectionTailCharge
  rw [Finset.sum_neg_distrib]

private theorem positiveWeight_eq_difference (k : ℕ) (hk : 0 < k) :
    positiveWeight k = 1 / (k : ℝ) - 1 / ((k : ℝ) + 1) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hk)
  rw [positiveWeight_succ]
  unfold paretoWeight
  push_cast
  have h1 : (j : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (j : ℝ) + 2 ≠ 0 := by positivity
  field_simp [h1, h2] <;> ring

private theorem physical_head_weight_explicit (n k : ℕ)
    (hk : 0 < k) (hkK : k ≤ n + 1) :
    physicalProjectionHeadWeight n k = positiveWeight k -
      (supportA (n + 1) / (((n + 1 : ℕ) : ℝ) - supportA (n + 1))) / ((k : ℝ) + 1) := by
  unfold physicalProjectionHeadWeight
  rw [physicalDualProjection_explicit, if_pos hkK, if_neg (ne_of_gt hk)]
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hk)
  rw [positiveWeight_succ]
  unfold paretoWeight
  push_cast
  have h1 : (j : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (j : ℝ) + 2 ≠ 0 := by positivity
  field_simp [h1, h2]
  ring

private theorem sum_positiveWeight_Icc (m K : ℕ) (hm : 0 < m) (hmK : m ≤ K) :
    (∑ k ∈ Finset.Icc m K, positiveWeight k) =
      1 / (m : ℝ) - 1 / (((K + 1 : ℕ) : ℝ)) := by
  have hI : Finset.Icc m K = Finset.Ico m (K + 1) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hI]
  have hf :
      (∑ k ∈ Finset.Ico m (K + 1), positiveWeight k) =
        -(∑ k ∈ Finset.Ico m (K + 1),
          (1 / ((k + 1 : ℕ) : ℝ) - 1 / (k : ℝ))) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have hkpos : 0 < k := lt_of_lt_of_le hm (Finset.mem_Ico.mp hk).1
    rw [positiveWeight_eq_difference k hkpos]
    push_cast
    ring
  rw [hf, Finset.sum_Ico_sub (fun k => (1 : ℝ) / (k : ℝ)) (by omega)]
  ring

/-- The closed tail charge retains the harmonic tail exactly. -/
theorem physicalProjectionTailCharge_explicit (n m : ℕ)
    (hm : 0 < m) (hmK : m ≤ n + 1) :
    physicalProjectionTailCharge n m =
      -1 / (m : ℝ) + 1 / (((n + 2 : ℕ) : ℝ)) +
        (supportA (n + 1) / (((n + 1 : ℕ) : ℝ) - supportA (n + 1))) *
          ∑ k ∈ Finset.Icc m (n + 1), 1 / ((k : ℝ) + 1) := by
  unfold physicalProjectionTailCharge
  have he :
      (∑ k ∈ Finset.Icc m (n + 1), physicalProjectionHeadWeight n k) =
        (∑ k ∈ Finset.Icc m (n + 1), positiveWeight k) -
          (supportA (n + 1) / (((n + 1 : ℕ) : ℝ) - supportA (n + 1))) *
            ∑ k ∈ Finset.Icc m (n + 1), 1 / ((k : ℝ) + 1) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [physical_head_weight_explicit n k
      (lt_of_lt_of_le hm (Finset.mem_Icc.mp hk).1) (Finset.mem_Icc.mp hk).2]
    ring
  rw [he, sum_positiveWeight_Icc m (n + 1) hm hmK]
  push_cast
  ring

/-- Actual physical-dual coefficients are given by an explicit sum over all
multiples through the head cutoff. -/
theorem physicalDualProjectionCoeff_closed_multiples (n : ℕ) (i : Fin n) :
    physicalDualProjectionCoeff n i =
      ∑ j ∈ Finset.Icc 1 ((n + 1) / (i.val + 2)),
        (-1 / (((i.val + 2) * j : ℕ) : ℝ) + 1 / (((n + 2 : ℕ) : ℝ)) +
          (supportA (n + 1) / (((n + 1 : ℕ) : ℝ) - supportA (n + 1))) *
            ∑ k ∈ Finset.Icc ((i.val + 2) * j) (n + 1), 1 / ((k : ℝ) + 1)) := by
  rw [physicalDualProjectionCoeff_multiples]
  apply Finset.sum_congr rfl
  intro j hj
  have hjpos : 0 < j := (Finset.mem_Icc.mp hj).1
  have hprod : 0 < (i.val + 2) * j := Nat.mul_pos (by omega) hjpos
  have hle : (i.val + 2) * j ≤ n + 1 := by
    have h := (Nat.le_div_iff_mul_le (by omega : 0 < i.val + 2)).mp (Finset.mem_Icc.mp hj).2
    nlinarith
  exact physicalProjectionTailCharge_explicit n _ hprod hle

/-- The ordinary harmonic sum, with its zero-indexed finite representation. -/
def projectionHarmonic (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, 1 / ((k : ℝ) + 1)

theorem supportA_eq_projectionHarmonic_sub_one (K : ℕ) :
    supportA K = projectionHarmonic (K + 1) - 1 := by
  unfold projectionHarmonic
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add, one_div_one]
  have he :
      (∑ k ∈ Finset.range K, 1 / ((k : ℝ) + 1 + 1)) = supportA K := by
    rw [supportA_eq_sum]
    apply Finset.sum_congr rfl
    intro k hk
    congr 1
    ring
  rw [he]
  ring

theorem projectionHarmonic_tail (m K : ℕ) (hmK : m ≤ K + 1) :
    (∑ k ∈ Finset.Icc m K, 1 / ((k : ℝ) + 1)) =
      projectionHarmonic (K + 1) - projectionHarmonic m := by
  have hI : Finset.Icc m K = Finset.Ico m (K + 1) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hI]
  exact Finset.sum_Ico_eq_sub (fun k => (1 : ℝ) / ((k : ℝ) + 1)) hmK

/-- The manuscript's exact harmonic multiples formula for every actual
coefficient; `K=n+1` and `d=i.val+2`. -/
theorem physicalDualProjectionCoeff_harmonic_multiples (n : ℕ) (i : Fin n) :
    physicalDualProjectionCoeff n i =
      ∑ j ∈ Finset.Icc 1 ((n + 1) / (i.val + 2)),
        (-1 / (((i.val + 2) * j : ℕ) : ℝ) + 1 / (((n + 2 : ℕ) : ℝ)) +
          (supportA (n + 1) / (((n + 1 : ℕ) : ℝ) - supportA (n + 1))) *
            (projectionHarmonic (n + 2) - projectionHarmonic ((i.val + 2) * j))) := by
  rw [physicalDualProjectionCoeff_closed_multiples]
  apply Finset.sum_congr rfl
  intro j hj
  have hle : (i.val + 2) * j ≤ n + 1 := by
    have h := (Nat.le_div_iff_mul_le (by omega : 0 < i.val + 2)).mp (Finset.mem_Icc.mp hj).2
    nlinarith
  rw [projectionHarmonic_tail _ _ (by omega)]

end RiemannResearch.RH.Pareto.CoefficientStabilization
