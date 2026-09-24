import RiemannResearch.RH.CanonicalMobiusExactCellEndpoint
import RiemannResearch.RH.NearbyDilationGram
import RiemannResearch.Analysis.MellinNormalizedResidue

/-!
# Full endpoint energy of the boundary residue correction

Source: the endpoint argument developed in HardyEndpointCompactness20260924.md.
The proof splits the exact discrete energy at the conductor and retains the
entire infinite tail. No quantitative Möbius estimate is assumed here.
-/

noncomputable section
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto
open RiemannResearch.RH.ArithmeticCumulative

/-- The exact endpoint energy is a quadratic form under real scalar multiplication. -/
theorem exactEndpointCellEnergy_smul (c : ℝ) (x : ThresholdHilbert) :
    exactEndpointCellEnergy (c • x) = c^2 * exactEndpointCellEnergy x := by
  unfold exactEndpointCellEnergy
  simp only [hilbertSequence_smul, Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  ring

/-- The conductor-scaled residue has exactly the integer remainder as its sequence. -/
theorem conductorScaledResidue_sequence (k : ℕ) (hk : 0 < k) (n : ℕ) :
    hilbertSequence ((k : ℝ) • normalizedResidueHilbert k hk) n = ((n % k : ℕ) : ℝ) := by
  rw [hilbertSequence_smul, normalizedResidueHilbert_sequence]
  simp only [Pi.smul_apply, smul_eq_mul, residueFraction]
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  field_simp

/-- On the exact head, the endpoint energy is bounded by a harmonic summand. -/
theorem exactEndpointCellWeight_mul_sq_le_reciprocal (n : ℕ) :
    exactEndpointCellWeight n * (n : ℝ)^2 ≤ 1 / (n : ℝ) := by
  by_cases hn : n = 0
  · subst n
    simp
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
    calc
      exactEndpointCellWeight n * (n : ℝ)^2 ≤
          (positiveWeight n / (n : ℝ)) * (n : ℝ)^2 :=
        mul_le_mul_of_nonneg_right (exactEndpointCellWeight_le_inverseCoordinateWeight n)
          (sq_nonneg _)
      _ = 1 / ((n : ℝ) + 1) := by
        unfold positiveWeight
        field_simp
        <;> ring
      _ ≤ 1 / (n : ℝ) := one_div_le_one_div_of_le hn0 (by linarith)

/-- Every omitted coordinate is bounded using the full Pareto tail mass. -/
theorem exactEndpointCellWeight_residue_tail_le (k n : ℕ) (hk : 0 < k)
    (hn : k ≤ n) :
    exactEndpointCellWeight n * ((n % k : ℕ) : ℝ)^2 ≤
      (k : ℝ) * positiveWeight n := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hkn : (k : ℝ) ≤ n := by exact_mod_cast hn
  have hnR : (0 : ℝ) < n := lt_of_lt_of_le hkR hkn
  have hm0 : (0 : ℝ) ≤ (n % k : ℕ) := Nat.cast_nonneg _
  have hmk : ((n % k : ℕ) : ℝ) ≤ k := by exact_mod_cast (Nat.mod_lt n hk).le
  have hsq : ((n % k : ℕ) : ℝ)^2 ≤ (k : ℝ) * (n : ℝ) := by
    have hs := mul_self_le_mul_self hm0 hmk
    have ht := mul_le_mul_of_nonneg_left hkn hkR.le
    nlinarith
  calc
    exactEndpointCellWeight n * ((n % k : ℕ) : ℝ)^2 ≤
        (positiveWeight n / (n : ℝ)) * ((n % k : ℕ) : ℝ)^2 :=
      mul_le_mul_of_nonneg_right (exactEndpointCellWeight_le_inverseCoordinateWeight n)
        (sq_nonneg _)
    _ ≤ (positiveWeight n / (n : ℝ)) * ((k : ℝ) * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hsq
        (div_nonneg (positiveWeight_nonneg n) hnR.le)
    _ = (k : ℝ) * positiveWeight n := by field_simp

/-- Complete conductor-scaled residue energy; the infinite tail contributes at most one. -/
theorem conductorScaledResidue_exactEndpointCellEnergy_le (k : ℕ) (hk : 0 < k) :
    exactEndpointCellEnergy ((k : ℝ) • normalizedResidueHilbert k hk) ≤
      (∑ n ∈ Finset.range k, 1 / (n : ℝ)) + 1 := by
  let e : ℕ → ℝ := fun n => exactEndpointCellWeight n * ((n % k : ℕ) : ℝ)^2
  have he : Summable e := by
    simpa only [conductorScaledResidue_sequence] using
      exactEndpointCellEnergy_summable ((k : ℝ) • normalizedResidueHilbert k hk)
  have henergy : exactEndpointCellEnergy ((k : ℝ) • normalizedResidueHilbert k hk) =
      ∑' n, e n := by
    simp only [exactEndpointCellEnergy, conductorScaledResidue_sequence, e]
  have hhead : (∑ n ∈ Finset.range k, e n) ≤ ∑ n ∈ Finset.range k, 1 / (n : ℝ) := by
    apply Finset.sum_le_sum
    intro n hn
    have hnlt : n < k := Finset.mem_range.mp hn
    simpa only [e, Nat.mod_eq_of_lt hnlt] using
      exactEndpointCellWeight_mul_sq_le_reciprocal n
  have htailw : Summable (fun n : ℕ => (k : ℝ) * positiveWeight (n + k)) := by
    exact (positiveWeight_summable.comp_injective
      (fun a b h => Nat.add_right_cancel h)).mul_left _
  have htaile : Summable (fun n : ℕ => e (n + k)) :=
    he.comp_injective (fun a b h => Nat.add_right_cancel h)
  have htail : (∑' n : ℕ, e (n + k)) ≤ 1 := by
    calc
      (∑' n : ℕ, e (n + k)) ≤ ∑' n : ℕ, (k : ℝ) * positiveWeight (n + k) := by
        apply htaile.tsum_le_tsum _ htailw
        intro n
        exact exactEndpointCellWeight_residue_tail_le k (n + k) hk (by omega)
      _ = 1 := by
        rw [tsum_mul_left, positiveWeight_tail_tsum k hk]
        have hk0 : (k : ℝ) ≠ 0 := by positivity
        field_simp
  rw [henergy, ← he.sum_add_tsum_nat_add k]
  exact add_le_add hhead htail

/-- The actual boundary correction costs a harmonic factor times m², with its entire tail retained. -/
theorem boundaryCorrection_exactEndpointCellEnergy_le (k : ℕ) (hk : 0 < k) (m : ℝ) :
    exactEndpointCellEnergy (((k : ℝ) * m) • normalizedResidueHilbert k hk) ≤
      m^2 * ((∑ n ∈ Finset.range k, 1 / (n : ℝ)) + 1) := by
  have heq : ((k : ℝ) * m) • normalizedResidueHilbert k hk =
      m • ((k : ℝ) • normalizedResidueHilbert k hk) := by
    rw [smul_smul, mul_comm]
  rw [heq, exactEndpointCellEnergy_smul]
  exact mul_le_mul_of_nonneg_left (conductorScaledResidue_exactEndpointCellEnergy_le k hk)
    (sq_nonneg m)

end RiemannResearch.RH.Pareto
