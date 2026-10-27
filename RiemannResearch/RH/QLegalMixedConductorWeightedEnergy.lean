/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QLegalMixedConductorPhysical
import RiemannResearch.RH.QLegalMixedConductorReciprocal
import RiemannResearch.RH.QPolylogTailEnergy
import RiemannResearch.Analysis.LogTailWeights

/-!
# Weighted energy obstruction for the actual mixed-conductor correction

Source: LegalSubspaceProjectionObstruction.md, Section 4, supplied by the
user; 27 October 2026. The lower bound uses a finite physical block and the
actual residual-forced projection. No weighted projection-stability
hypothesis is assumed. These varying spaces are not the canonical initial
squarefree stages.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QLegalMixedConductor
open ZetaTwoHilbert ZetaTwoProbability ArithmeticCumulative QPolylogTailEnergy
open RiemannResearch.Analysis.LogTailWeights

def weightedGrowthCoefficient : ℝ := (7 / (36 * 303 ^ 2 : ℝ)) * 10 / 16

theorem weightedGrowthCoefficient_pos : 0 < weightedGrowthCoefficient := by
  norm_num [weightedGrowthCoefficient]

/-- Every point in this finite block is below the conductor and occupies
at least one eighth of its scale. -/
theorem weightedBlock_site_bounds (d i : ℕ) (hd : 16 ≤ d) (hi : i < d / 4) :
    0 < d / 4 + i ∧ d / 4 + i < d ∧
      (d : ℝ) / 8 ≤ (d / 4 + i : ℕ) := by
  refine ⟨by omega, by omega, ?_⟩
  have h : d ≤ 8 * (d / 4 + i) := by omega
  have hR : (d : ℝ) ≤ 8 * (d / 4 + i : ℕ) := by exact_mod_cast h
  linarith

theorem actualCorrection_block_lower_eventually :
    ∀ᶠ d : ℕ in atTop, ∀ i < d / 4,
      weightedGrowthCoefficient * Real.sqrt (d : ℝ) ≤
        qSequence (actualCorrection d) (d / 4 + i) := by
  have hsqrt : Tendsto (fun d : ℕ => Real.sqrt (d : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hscale : ∀ᶠ d : ℕ in atTop,
      64 ≤ (7 / (36 * 303 ^ 2 : ℝ)) * (10 * Real.sqrt (d : ℝ)) := by
    have ht := hsqrt.const_mul_atTop
      (show 0 < (7 / (36 * 303 ^ 2 : ℝ)) * 10 by positivity)
    filter_upwards [ht.eventually (eventually_ge_atTop 64)] with d hd
    nlinarith
  filter_upwards [eventually_ge_atTop (16 : ℕ),
    correctionCoefficient_lower_eventually, physicalRemainder_bounded_eventually,
    hscale] with d hd hβ hw hscale
  intro i hi
  obtain ⟨hn, hnd, hnd8⟩ := weightedBlock_site_bounds d i hd hi
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hg : (1 / 8 : ℝ) ≤ residueFraction d (d / 4 + i) := by
    unfold residueFraction
    rw [Nat.mod_eq_of_lt hnd]
    exact (le_div_iff₀ hdR).mpr (by linarith)
  have hg0 := le_trans (by norm_num : (0 : ℝ) ≤ 1 / 8) hg
  have hmain : (7 / (36 * 303 ^ 2 : ℝ)) * (10 * Real.sqrt (d : ℝ)) / 8 ≤
      correctionCoefficient d * (10 * Real.sqrt (d : ℝ)) *
        residueFraction d (d / 4 + i) := by
    calc
      _ = ((7 / (36 * 303 ^ 2 : ℝ)) * (10 * Real.sqrt (d : ℝ))) * (1 / 8) := by ring
      _ ≤ ((7 / (36 * 303 ^ 2 : ℝ)) * (10 * Real.sqrt (d : ℝ))) *
          residueFraction d (d / 4 + i) :=
        mul_le_mul_of_nonneg_left hg (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hβ (by positivity)) hg0
  have hwlow := (abs_le.mp (hw (d / 4 + i))).1
  rw [actualCorrection_decomposition d _ (by omega)]
  dsimp [weightedGrowthCoefficient]
  nlinarith

/-- Actual weighted Q energy in a finite physical block. -/
def correctionBlockEnergy (d : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (d / 4),
    polylogWeightedEnergyTerm 2 (actualCorrection d) (d / 4 + i)

theorem weightedEnergyTerm_lower_of_block_lower (d n : ℕ) (hd : 0 < d)
    (hn : 0 < n) (hnd : n ≤ d)
    (hb : weightedGrowthCoefficient * Real.sqrt (d : ℝ) ≤
      qSequence (actualCorrection d) n) :
    weightedGrowthCoefficient ^ 2 / (zetaTwo * (8 + Real.log (d : ℝ)) ^ 2) ≤
      polylogWeightedEnergyTerm 2 (actualCorrection d) n := by
  have hzeta := zetaTwo_pos
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hndR : (n : ℝ) ≤ d := by exact_mod_cast hnd
  have hln := Real.log_nonneg hn1
  have hlog := Real.log_le_log hnR hndR
  have hLn : 0 < 8 + Real.log (n : ℝ) := by linarith
  have hLd : 0 < 8 + Real.log (d : ℝ) := by linarith
  have hsq : weightedGrowthCoefficient ^ 2 * (d : ℝ) ≤
      qSequence (actualCorrection d) n ^ 2 := by
    have h := mul_self_le_mul_self
      (mul_nonneg weightedGrowthCoefficient_pos.le (Real.sqrt_nonneg _)) hb
    simpa only [← pow_two, mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)] using h
  have hden : zetaTwo * (n : ℝ) * (8 + Real.log (n : ℝ)) ^ 2 ≤
      zetaTwo * (d : ℝ) * (8 + Real.log (d : ℝ)) ^ 2 := by
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left hndR zetaTwo_pos.le)
      (pow_le_pow_left₀ hLn.le (by linarith) 2)
      (sq_nonneg _) (by positivity)
  rw [polylogWeightedEnergyTerm_eq 2 n (actualCorrection d) hn]
  norm_num only [Nat.cast_ofNat, show (2 : ℝ) + 6 = 8 by norm_num]
  calc
    _ = (weightedGrowthCoefficient ^ 2 * (d : ℝ)) /
        (zetaTwo * (d : ℝ) * (8 + Real.log (d : ℝ)) ^ 2) := by
      field_simp [hdR.ne', hLd.ne', zetaTwo_pos.ne']
    _ ≤ (weightedGrowthCoefficient ^ 2 * (d : ℝ)) /
        (zetaTwo * (n : ℝ) * (8 + Real.log (n : ℝ)) ^ 2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ ≤ _ := div_le_div_of_nonneg_right hsq (by positivity)

theorem correctionBlockEnergy_lower_eventually :
    ∀ᶠ d : ℕ in atTop,
      (weightedGrowthCoefficient ^ 2 / (8 * zetaTwo)) * polylogTailProfile 2 d ≤
        correctionBlockEnergy d := by
  have hzeta := zetaTwo_pos
  filter_upwards [eventually_ge_atTop (16 : ℕ),
    actualCorrection_block_lower_eventually] with d hd hb
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hLd : 0 < 8 + Real.log (d : ℝ) := by linarith [Real.log_nonneg hd1]
  have hcountNat : d ≤ 8 * (d / 4) := by omega
  have hcountR : (d : ℝ) / 8 ≤ (d / 4 : ℕ) := by
    have h : (d : ℝ) ≤ 8 * (d / 4 : ℕ) := by exact_mod_cast hcountNat
    linarith
  have hs : (d / 4 : ℕ) *
      (weightedGrowthCoefficient ^ 2 / (zetaTwo * (8 + Real.log (d : ℝ)) ^ 2)) ≤
      correctionBlockEnergy d := by
    calc
      _ = ∑ i ∈ Finset.range (d / 4),
          weightedGrowthCoefficient ^ 2 /
            (zetaTwo * (8 + Real.log (d : ℝ)) ^ 2) := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' := Finset.mem_range.mp hi
        obtain ⟨hn, hnd, _⟩ := weightedBlock_site_bounds d i hd hi'
        exact weightedEnergyTerm_lower_of_block_lower d _ (by omega) hn hnd.le (hb i hi')
  calc
    _ = ((d : ℝ) / 8) *
        (weightedGrowthCoefficient ^ 2 / (zetaTwo * (8 + Real.log (d : ℝ)) ^ 2)) := by
      rw [polylogTailProfile_eq]
      norm_num only [Nat.cast_ofNat]
      field_simp [hLd.ne', hzeta.ne'] <;> ring
    _ ≤ (d / 4 : ℕ) *
        (weightedGrowthCoefficient ^ 2 / (zetaTwo * (8 + Real.log (d : ℝ)) ^ 2)) :=
      mul_le_mul_of_nonneg_right hcountR (by positivity)
    _ ≤ _ := hs

theorem correctionBlockEnergy_tendsto_atTop :
    Tendsto correctionBlockEnergy atTop atTop := by
  have hzeta := zetaTwo_pos
  have ht := (polylogTailProfile_tendsto_atTop 2).const_mul_atTop
    (show 0 < weightedGrowthCoefficient ^ 2 / (8 * zetaTwo) by
      exact div_pos (sq_pos_of_pos weightedGrowthCoefficient_pos) (by positivity))
  exact tendsto_atTop_mono' atTop correctionBlockEnergy_lower_eventually ht

/-- The complete weighted sum is well-defined at every sufficiently large
conductor; the bounded physical envelope may depend on that conductor. -/
theorem actualCorrection_weightedEnergy_summable_eventually :
    ∀ᶠ d : ℕ in atTop,
      Summable (polylogWeightedEnergyTerm 2 (actualCorrection d)) := by
  filter_upwards [eventually_ge_atTop (3 : ℕ),
    physicalRemainder_bounded_eventually] with d hd hw
  let C : ℝ := |correctionCoefficient d * (10 * Real.sqrt (d : ℝ))| + 4
  have hC : 0 ≤ C := by dsimp [C]; positivity
  apply polylogWeightedEnergyTerm_summable (actualCorrection d) 0 C hC
  intro n
  simp only [pow_zero, mul_one]
  have hg : |residueFraction d n| ≤ 1 := by
    simpa only [qSequence_qResidue] using qResidue_physical_abs_le_one d n
  rw [actualCorrection_decomposition d n (by omega)]
  calc
    _ ≤ |correctionCoefficient d * (10 * Real.sqrt (d : ℝ))| *
          |residueFraction d n| + |physicalRemainder d n| := by
      simpa only [abs_mul] using abs_add_le
        (correctionCoefficient d * (10 * Real.sqrt (d : ℝ)) * residueFraction d n)
        (physicalRemainder d n)
    _ ≤ C := by
      have hm := mul_le_mul_of_nonneg_left hg
        (abs_nonneg (correctionCoefficient d * (10 * Real.sqrt (d : ℝ))))
      dsimp [C]
      linarith [hw n]

def correctionWeightedEnergy (d : ℕ) : ℝ :=
  ∑' n : ℕ, polylogWeightedEnergyTerm 2 (actualCorrection d) n

theorem correctionBlockEnergy_le_weightedEnergy (d : ℕ)
    (hs : Summable (polylogWeightedEnergyTerm 2 (actualCorrection d))) :
    correctionBlockEnergy d ≤ correctionWeightedEnergy d := by
  classical
  let S : Finset ℕ := (Finset.range (d / 4)).image (fun i => d / 4 + i)
  have he : (∑ n ∈ S, polylogWeightedEnergyTerm 2 (actualCorrection d) n) =
      correctionBlockEnergy d := by
    dsimp [S, correctionBlockEnergy]
    rw [Finset.sum_image]
    intro i hi j hj hij
    exact Nat.add_left_cancel hij
  rw [← he]
  exact Summable.sum_le_tsum S
    (fun n hn => polylogWeightedEnergyTerm_nonneg 2 (actualCorrection d) n) hs

/-- The complete weighted Q energy of the actual projected correction
diverges, despite the uniformly bounded unweighted correction norm. -/
theorem correctionWeightedEnergy_tendsto_atTop :
    Tendsto correctionWeightedEnergy atTop atTop := by
  apply tendsto_atTop_mono' atTop _ correctionBlockEnergy_tendsto_atTop
  filter_upwards [actualCorrection_weightedEnergy_summable_eventually] with d hd
  exact correctionBlockEnergy_le_weightedEnergy d hd

/-- Arbitrarily large complete weighted moments occur at arbitrarily large
prime conductors, where the spaces are legal squarefree spans. -/
theorem exists_prime_actualCorrection_large_weightedEnergy (M : ℝ) (N : ℕ) :
    ∃ d : ℕ, d.Prime ∧ N ≤ d ∧ 3 < d ∧ M ≤ correctionWeightedEnergy d := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (correctionWeightedEnergy_tendsto_atTop.eventually (eventually_ge_atTop M))
  obtain ⟨d, hdge, hp⟩ := Nat.exists_infinite_primes (max (max T N) 4)
  have hdT : T ≤ d := (le_trans (le_max_left T N)
    (le_max_left (max T N) 4)).trans hdge
  have hdN : N ≤ d := (le_trans (le_max_right T N)
    (le_max_left (max T N) 4)).trans hdge
  have hd4 : 4 ≤ d := (le_max_right (max T N) 4).trans hdge
  exact ⟨d, hp, hdN, by omega, hT d hdT⟩

/-- Squarefree legality and actual residual forcing do not give a uniform
weighted-moment bound over this family. -/
theorem no_uniform_prime_correctionWeightedEnergy :
    ¬ ∃ C : ℝ, ∀ d : ℕ, d.Prime → 3 < d → correctionWeightedEnergy d ≤ C := by
  rintro ⟨C, hC⟩
  obtain ⟨d, hp, _, hd, hm⟩ :=
    exists_prime_actualCorrection_large_weightedEnergy (C + 1) 0
  have hu := hC d hp hd
  linarith

end RiemannResearch.RH.QLegalMixedConductor
