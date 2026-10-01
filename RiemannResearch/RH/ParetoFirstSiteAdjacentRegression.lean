/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ParetoFirstSitePrimeSourceFloors

/-!
# Adjacent-residue regression certificates for actual screened prime scatter

Source: independently derived assembly of the user's October 1 screened-gap
continuation, exact finite weighted regression, and the repository's
ParetoAdjacentSchurBound and complete split-tree identities. These support
the statements and proof strategy; no mathematical priority is asserted.

The signed numerators are the ACTUAL schurEta values. Replacing inverse
Schur-pivot weights by reciprocal adjacent-trial norms is done only through
an exact identity retaining both regression-comparison squares. The trial
norm formula retains its literal infinite adjacentResidueRemainder.

Both harmonic and full-tail adjacent weights are independent of the actual
pivots; their numerators still contain the complete old-dictionary screening.
Every binary-tree split, capacity channel and zero-source boundary is kept.
Nonsummability hypotheses in RH endpoints remain explicit and Open.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
open RiemannResearch.Analysis.WeightedScalarEnergy
open RiemannResearch.RH.Pareto.IntegerDPP
open RiemannResearch.Analysis

noncomputable def harmonicPrimeRegressionWeight (n : ℕ) : ℝ :=
  if Nat.Prime (n+3) then ((n+3 : ℕ) : ℝ)^2 / (harmonic (n+2) : ℝ) else 0

theorem harmonicPrimeRegressionWeight_nonneg (n : ℕ) :
    0 ≤ harmonicPrimeRegressionWeight n := by
  unfold harmonicPrimeRegressionWeight
  split_ifs
  · exact div_nonneg (sq_nonneg _) (harmonic_nonnegative _)
  · exact le_rfl

theorem harmonicPrimeRegressionWeight_le (n : ℕ) :
    harmonicPrimeRegressionWeight n ≤ primeSchurWeight n := by
  by_cases hp : Nat.Prime (n+3)
  · simp only [harmonicPrimeRegressionWeight, primeSchurWeight, hp, if_true]
    have hs := schurSigma_le_adjacent_harmonic n
    have hH : 0 < (harmonic (n+2) : ℝ) := by
      have hh := (harmonic_interval_bounds 1 (n+2) (by omega)).1
      have h1 : (harmonic 1 : ℝ) = 1 := by norm_num
      rw [h1] at hh
      linarith
    have hq : 0 < ((n+3 : ℕ) : ℝ)^2 := by positivity
    rw [← one_div]
    apply (div_le_div_iff₀ hH (schurSigma_pos (n+1))).mpr
    simpa only [one_mul, mul_comm] using (le_div_iff₀ hq).mp hs
  · simp [harmonicPrimeRegressionWeight, primeSchurWeight, hp]

noncomputable def harmonicPrimeSurvivorSource (N k : ℕ) : ℝ :=
  square (Finset.range k) (fun i => harmonicPrimeRegressionWeight (N+i))
    (fun i => factorialPrimeDelta (N+i))
noncomputable def harmonicPrimeSurvivorCross (N k : ℕ) : ℝ :=
  product (Finset.range k) (fun i => harmonicPrimeRegressionWeight (N+i))
    (fun i => factorialPrimeDelta (N+i)) (fun i => schurEta (N+i+1))
noncomputable def harmonicPrimeSurvivorVariance (N k : ℕ) : ℝ :=
  square (Finset.range k) (fun i => harmonicPrimeRegressionWeight (N+i))
    (fun i => schurEta (N+i+1) -
      (harmonicPrimeSurvivorCross N k / harmonicPrimeSurvivorSource N k) *
        factorialPrimeDelta (N+i))

theorem primeBlockVariance_eq_harmonicSurvivor_remainders (N k : ℕ) :
    primeBlockVariance N k = harmonicPrimeSurvivorVariance N k +
      harmonicPrimeSurvivorSource N k *
        (1 + primeBlockCross N k / primeBlockSource N k -
          harmonicPrimeSurvivorCross N k / harmonicPrimeSurvivorSource N k)^2 +
      square (Finset.range k)
        (fun i => primeSchurWeight (N+i) - harmonicPrimeRegressionWeight (N+i))
        (fun i => schurEta (N+i+1) -
          (1+primeBlockCross N k / primeBlockSource N k) *
            factorialPrimeDelta (N+i)) := by
  rw [primeBlockVariance_eq_survivor_scatter]
  exact regression_weight_remainder _ _ _ _ _ _
    (fun i _ => harmonicPrimeRegressionWeight_nonneg (N+i))

theorem harmonicPrimeSurvivorVariance_nonneg (N k : ℕ) :
    0 ≤ harmonicPrimeSurvivorVariance N k :=
  square_nonneg _ _ _ (fun i _ => harmonicPrimeRegressionWeight_nonneg (N+i))

theorem harmonicPrimeSurvivorVariance_le (N k : ℕ) :
    harmonicPrimeSurvivorVariance N k ≤ primeBlockVariance N k := by
  rw [primeBlockVariance_eq_survivor_scatter]
  exact centered_square_le_larger_weight _ _ _ _ _ _
    (fun i _ => harmonicPrimeRegressionWeight_nonneg (N+i))
    (fun i _ => harmonicPrimeRegressionWeight_le (N+i))

theorem riemannHypothesis_of_harmonicSurvivorVariance_not_summable
    (hdiv : ¬ Summable (fun j => harmonicPrimeSurvivorVariance (2^j) (2^j))) :
    RiemannHypothesis :=
  riemannHypothesis_of_dyadic_prime_block_lower_bound _
    (fun _ => harmonicPrimeSurvivorVariance_nonneg _ _) hdiv
    (fun _ => harmonicPrimeSurvivorVariance_le _ _)

noncomputable def adjacentPrimeRegressionWeight (n : ℕ) : ℝ :=
  if Nat.Prime (n+3) then (‖adjacentSchurTrial n‖^2)⁻¹ else 0

theorem adjacentPrimeRegressionWeight_nonneg (n : ℕ) :
    0 ≤ adjacentPrimeRegressionWeight n := by
  unfold adjacentPrimeRegressionWeight
  split_ifs
  · exact inv_nonneg.mpr (sq_nonneg _)
  · exact le_rfl

theorem adjacentPrimeRegressionWeight_le (n : ℕ) :
    adjacentPrimeRegressionWeight n ≤ primeSchurWeight n := by
  by_cases hp : Nat.Prime (n+3)
  · simp only [adjacentPrimeRegressionWeight, primeSchurWeight, hp, if_true]
    have hs : schurSigma (n+1) ≤ ‖adjacentSchurTrial n‖^2 :=
      schurSigma_le_balancedTrial_norm_sq (n+1)
        (⟨n, Nat.lt_succ_self n⟩ : Fin (n+1))
        (((n+2 : ℕ) : ℝ) / ((n+3 : ℕ) : ℝ))
    simpa only [one_div] using one_div_le_one_div_of_le (schurSigma_pos _) hs
  · simp [adjacentPrimeRegressionWeight, primeSchurWeight, hp]

theorem harmonicPrimeRegressionWeight_le_adjacent (n : ℕ) :
    harmonicPrimeRegressionWeight n ≤ adjacentPrimeRegressionWeight n := by
  by_cases hp : Nat.Prime (n+3)
  · simp only [harmonicPrimeRegressionWeight, adjacentPrimeRegressionWeight, hp, if_true]
    have hs : schurSigma (n+1) ≤ ‖adjacentSchurTrial n‖^2 :=
      schurSigma_le_balancedTrial_norm_sq (n+1)
        (⟨n, Nat.lt_succ_self n⟩ : Fin (n+1))
        (((n+2 : ℕ) : ℝ) / ((n+3 : ℕ) : ℝ))
    have hpos := (schurSigma_pos _).trans_le hs
    have he := adjacentSchurTrial_norm_sq_le_harmonic n
    have hH : 0 < (harmonic (n+2) : ℝ) := by
      have hh := (RiemannResearch.Analysis.harmonic_interval_bounds 1 (n+2) (by omega)).1
      have h1 : (harmonic 1 : ℝ) = 1 := by norm_num
      rw [h1] at hh
      linarith
    rw [← one_div]
    apply (div_le_div_iff₀ hH hpos).mpr
    simpa only [one_mul, mul_comm] using (le_div_iff₀ (by positivity :
      0 < ((n+3 : ℕ) : ℝ)^2)).mp he
  · simp [harmonicPrimeRegressionWeight, adjacentPrimeRegressionWeight, hp]

noncomputable def adjacentPrimeSurvivorSource (N k : ℕ) : ℝ :=
  square (Finset.range k) (fun i => adjacentPrimeRegressionWeight (N+i))
    (fun i => factorialPrimeDelta (N+i))
noncomputable def adjacentPrimeSurvivorCross (N k : ℕ) : ℝ :=
  product (Finset.range k) (fun i => adjacentPrimeRegressionWeight (N+i))
    (fun i => factorialPrimeDelta (N+i)) (fun i => schurEta (N+i+1))
noncomputable def adjacentPrimeSurvivorVariance (N k : ℕ) : ℝ :=
  square (Finset.range k) (fun i => adjacentPrimeRegressionWeight (N+i))
    (fun i => schurEta (N+i+1) -
      (adjacentPrimeSurvivorCross N k / adjacentPrimeSurvivorSource N k) *
        factorialPrimeDelta (N+i))

theorem primeBlockVariance_eq_adjacentSurvivor_remainders (N k : ℕ) :
    primeBlockVariance N k = adjacentPrimeSurvivorVariance N k +
      adjacentPrimeSurvivorSource N k *
        (1 + primeBlockCross N k / primeBlockSource N k -
          adjacentPrimeSurvivorCross N k / adjacentPrimeSurvivorSource N k)^2 +
      square (Finset.range k)
        (fun i => primeSchurWeight (N+i) - adjacentPrimeRegressionWeight (N+i))
        (fun i => schurEta (N+i+1) -
          (1+primeBlockCross N k / primeBlockSource N k) *
            factorialPrimeDelta (N+i)) := by
  rw [primeBlockVariance_eq_survivor_scatter]
  exact regression_weight_remainder _ _ _ _ _ _
    (fun i _ => adjacentPrimeRegressionWeight_nonneg (N+i))

theorem adjacentPrimeSurvivorVariance_nonneg (N k : ℕ) :
    0 ≤ adjacentPrimeSurvivorVariance N k :=
  square_nonneg _ _ _ (fun i _ => adjacentPrimeRegressionWeight_nonneg (N+i))

theorem harmonicPrimeSurvivorVariance_le_adjacent (N k : ℕ) :
    harmonicPrimeSurvivorVariance N k ≤ adjacentPrimeSurvivorVariance N k :=
  centered_square_weight_mono _ _ _ _ _
    (fun i _ => harmonicPrimeRegressionWeight_nonneg (N+i))
    (fun i _ => harmonicPrimeRegressionWeight_le_adjacent (N+i))

theorem adjacentPrimeSurvivorVariance_le (N k : ℕ) :
    adjacentPrimeSurvivorVariance N k ≤ primeBlockVariance N k := by
  rw [primeBlockVariance_eq_survivor_scatter]
  exact centered_square_le_larger_weight _ _ _ _ _ _
    (fun i _ => adjacentPrimeRegressionWeight_nonneg (N+i))
    (fun i _ => adjacentPrimeRegressionWeight_le (N+i))

theorem adjacentPrimeSurvivorVariance_eq_moment_fit (N k : ℕ) :
    adjacentPrimeSurvivorVariance N k =
      square (Finset.range k) (fun i => adjacentPrimeRegressionWeight (N+i))
        (fun i => -inner ℝ (adjacentSchurTrial (N+i)) (tailMinimum (N+i+1)) -
          (adjacentPrimeSurvivorCross N k / adjacentPrimeSurvivorSource N k) *
            factorialPrimeDelta (N+i)) := by
  unfold adjacentPrimeSurvivorVariance
  simp_rw [schurEta_eq_neg_adjacentTrial]

theorem riemannHypothesis_of_adjacentSurvivorVariance_not_summable
    (hdiv : ¬ Summable (fun j => adjacentPrimeSurvivorVariance (2^j) (2^j))) :
    RiemannHypothesis :=
  riemannHypothesis_of_dyadic_prime_block_lower_bound _
    (fun _ => adjacentPrimeSurvivorVariance_nonneg _ _) hdiv
    (fun _ => adjacentPrimeSurvivorVariance_le _ _)

theorem adjacentPrimeRegressionWeight_eq_full_tail (n : ℕ) (hp : Nat.Prime (n+3)) :
    adjacentPrimeRegressionWeight n =
      ((n+3 : ℕ) : ℝ)^2 /
        ((harmonic (n+2) : ℝ) - ((n+2 : ℕ) : ℝ) / (((n+2 : ℕ) : ℝ)+1) +
          RiemannResearch.RH.Pareto.adjacentResidueRemainder (n+2)) := by
  simp only [adjacentPrimeRegressionWeight, if_pos hp, adjacentSchurTrial_norm_sq_exact,
    inv_div]

theorem adjacentPrimeSurvivorVariance_eq_quotient (N k : ℕ) :
    adjacentPrimeSurvivorVariance N k =
      square (Finset.range k) (fun i => adjacentPrimeRegressionWeight (N+i))
        (fun i => schurEta (N+i+1)) -
      (adjacentPrimeSurvivorCross N k)^2 / adjacentPrimeSurvivorSource N k :=
  centered_square_eq_sub_quotient _ _ _ _

theorem adjacentPrimeSurvivorVariance_eq_pairs (N k : ℕ)
    (hU : 0 < adjacentPrimeSurvivorSource N k) :
    adjacentPrimeSurvivorVariance N k =
      (∑ i ∈ Finset.range k, ∑ m ∈ Finset.range k,
        adjacentPrimeRegressionWeight (N+i) * adjacentPrimeRegressionWeight (N+m) *
          (factorialPrimeDelta (N+i)*schurEta (N+m+1) -
            factorialPrimeDelta (N+m)*schurEta (N+i+1))^2) /
        (2*adjacentPrimeSurvivorSource N k) := by
  rw [pair_identity, adjacentPrimeSurvivorVariance_eq_quotient]
  change _ = 2 * (adjacentPrimeSurvivorSource N k *
    square (Finset.range k) (fun i => adjacentPrimeRegressionWeight (N+i))
      (fun i => schurEta (N+i+1)) - (adjacentPrimeSurvivorCross N k)^2) /
      (2*adjacentPrimeSurvivorSource N k)
  field_simp [ne_of_gt hU]

noncomputable def adjacentPrimeSplitDrift (N k l : ℕ) : ℝ :=
  adjacentPrimeSurvivorSource N k * adjacentPrimeSurvivorSource (N+k) l /
    (adjacentPrimeSurvivorSource N k + adjacentPrimeSurvivorSource (N+k) l) *
    (adjacentPrimeSurvivorCross (N+k) l / adjacentPrimeSurvivorSource (N+k) l -
      adjacentPrimeSurvivorCross N k / adjacentPrimeSurvivorSource N k)^2

theorem adjacentPrimeSurvivorSource_nonneg (N k : ℕ) :
    0 ≤ adjacentPrimeSurvivorSource N k :=
  square_nonneg _ _ _ (fun i _ => adjacentPrimeRegressionWeight_nonneg (N+i))

theorem adjacentPrimeSurvivor_gram (N k : ℕ) :
    (adjacentPrimeSurvivorCross N k)^2 ≤ adjacentPrimeSurvivorSource N k *
      square (Finset.range k) (fun i => adjacentPrimeRegressionWeight (N+i))
        (fun i => schurEta (N+i+1)) :=
  gram_nonneg _ _ _ _ (fun i _ => adjacentPrimeRegressionWeight_nonneg (N+i))

theorem adjacentPrimeSurvivorVariance_split (N k l : ℕ) :
    adjacentPrimeSurvivorVariance N (k+l) = adjacentPrimeSurvivorVariance N k +
      adjacentPrimeSurvivorVariance (N+k) l + adjacentPrimeSplitDrift N k l := by
  have hs : adjacentPrimeSurvivorSource N (k+l) =
      adjacentPrimeSurvivorSource N k + adjacentPrimeSurvivorSource (N+k) l := by
    simp only [adjacentPrimeSurvivorSource, square, Finset.sum_range_add, Nat.add_assoc]
  have hx : adjacentPrimeSurvivorCross N (k+l) =
      adjacentPrimeSurvivorCross N k + adjacentPrimeSurvivorCross (N+k) l := by
    simp only [adjacentPrimeSurvivorCross, product, Finset.sum_range_add, Nat.add_assoc]
  rw [adjacentPrimeSurvivorVariance_eq_quotient, adjacentPrimeSurvivorVariance_eq_quotient,
    adjacentPrimeSurvivorVariance_eq_quotient, hs, hx]
  have he : square (Finset.range (k+l)) (fun i => adjacentPrimeRegressionWeight (N+i))
      (fun i => schurEta (N+i+1)) =
      square (Finset.range k) (fun i => adjacentPrimeRegressionWeight (N+i))
        (fun i => schurEta (N+i+1)) +
      square (Finset.range l) (fun i => adjacentPrimeRegressionWeight (N+k+i))
        (fun i => schurEta (N+k+i+1)) := by
    simp only [square, Finset.sum_range_add, Nat.add_assoc]
  rw [he]
  by_cases hk : adjacentPrimeSurvivorSource N k = 0
  · have hxk : adjacentPrimeSurvivorCross N k = 0 := by
      have hg := adjacentPrimeSurvivor_gram N k
      rw [hk, zero_mul] at hg
      nlinarith [sq_nonneg (adjacentPrimeSurvivorCross N k)]
    simp [adjacentPrimeSplitDrift, hk, hxk]
    ring
  by_cases hl : adjacentPrimeSurvivorSource (N+k) l = 0
  · have hxl : adjacentPrimeSurvivorCross (N+k) l = 0 := by
      have hg := adjacentPrimeSurvivor_gram (N+k) l
      rw [hl, zero_mul] at hg
      nlinarith [sq_nonneg (adjacentPrimeSurvivorCross (N+k) l)]
    simp [adjacentPrimeSplitDrift, hl, hxl]
    ring
  exact centered_energy_merge _ _ _ _ _ _ hk hl
    (ne_of_gt (add_pos
      (lt_of_le_of_ne (adjacentPrimeSurvivorSource_nonneg _ _) (Ne.symm hk))
      (lt_of_le_of_ne (adjacentPrimeSurvivorSource_nonneg _ _) (Ne.symm hl))))

theorem adjacentPrimeSurvivorVariance_one (N : ℕ) :
    adjacentPrimeSurvivorVariance N 1 = 0 := by
  rw [adjacentPrimeSurvivorVariance_eq_quotient]
  simp only [adjacentPrimeSurvivorSource, adjacentPrimeSurvivorCross, square, product,
    Finset.sum_range_one, Nat.add_zero]
  by_cases hw : adjacentPrimeRegressionWeight N = 0
  · simp [hw]
  · have hd := ne_of_gt (factorialPrimeDelta_pos N)
    field_simp [hw, hd]
    ring

noncomputable def adjacentPrimeDyadicSplitBudget : ℕ → ℕ → ℝ
  | _, 0 => 0
  | N, h+1 => adjacentPrimeDyadicSplitBudget N h +
      adjacentPrimeDyadicSplitBudget (N+2^h) h + adjacentPrimeSplitDrift N (2^h) (2^h)

theorem adjacentPrimeSurvivorVariance_eq_tree (N h : ℕ) :
    adjacentPrimeSurvivorVariance N (2^h) = adjacentPrimeDyadicSplitBudget N h := by
  induction h generalizing N with
  | zero => simpa [adjacentPrimeDyadicSplitBudget] using adjacentPrimeSurvivorVariance_one N
  | succ h ih =>
    have hp : (2:ℕ)^(h+1)=2^h+2^h := by rw [pow_succ]; omega
    rw [hp, adjacentPrimeSurvivorVariance_split, ih, ih]
    rfl

theorem harmonicPrimeSourceFloor_le_regression_source (n : ℕ) :
    harmonicPrimeSourceFloor n ≤
      harmonicPrimeRegressionWeight n * (factorialPrimeDelta n)^2 := by
  by_cases hp : Nat.Prime (n+3)
  · simp only [harmonicPrimeSourceFloor, harmonicPrimeRegressionWeight, hp, if_true]
    have hd : 1 / (2 * ((n+3 : ℕ) : ℝ)) ≤ factorialPrimeDelta n := by
      simpa only [factorialPrimeDelta, Nat.add_assoc, Nat.reduceAdd] using
        factorialPrimeDefect_lower (n+1) (by omega)
    have hd2 := pow_le_pow_left₀ (by positivity) hd 2
    have hH : (harmonic (n+2) : ℝ) ≠ 0 := by
      have hh := (RiemannResearch.Analysis.harmonic_interval_bounds 1 (n+2) (by omega)).1
      have h1 : (harmonic 1 : ℝ) = 1 := by norm_num
      rw [h1] at hh
      linarith
    calc
      _ = (((n+3 : ℕ) : ℝ)^2 / (harmonic (n+2) : ℝ)) *
          (1/(2*((n+3 : ℕ) : ℝ)))^2 := by
        field_simp
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hd2
        (div_nonneg (sq_nonneg _) (RiemannResearch.Analysis.harmonic_nonnegative _))
  · simp [harmonicPrimeSourceFloor, harmonicPrimeRegressionWeight, hp]

theorem harmonicPrimeBlockSourceFloor_le_adjacent_source (N k : ℕ) :
    harmonicPrimeBlockSourceFloor N k ≤ adjacentPrimeSurvivorSource N k := by
  unfold harmonicPrimeBlockSourceFloor adjacentPrimeSurvivorSource square
  apply Finset.sum_le_sum
  intro i hi
  exact (harmonicPrimeSourceFloor_le_regression_source (N+i)).trans
    (mul_le_mul_of_nonneg_right (harmonicPrimeRegressionWeight_le_adjacent (N+i)) (sq_nonneg _))

theorem adjacentPrimeSurvivorVariance_ge_floor_gap (N k l : ℕ) :
    harmonicPrimeSplitWeight N k l *
      (adjacentPrimeSurvivorCross (N+k) l / adjacentPrimeSurvivorSource (N+k) l -
        adjacentPrimeSurvivorCross N k / adjacentPrimeSurvivorSource N k)^2 ≤
      adjacentPrimeSurvivorVariance N (k+l) := by
  have hw : harmonicPrimeSplitWeight N k l ≤
      adjacentPrimeSurvivorSource N k * adjacentPrimeSurvivorSource (N+k) l /
        (adjacentPrimeSurvivorSource N k + adjacentPrimeSurvivorSource (N+k) l) :=
    reduced_weight_mono _ _ _ _
      (harmonicPrimeBlockSourceFloor_nonneg _ _) (harmonicPrimeBlockSourceFloor_nonneg _ _)
      (harmonicPrimeBlockSourceFloor_le_adjacent_source _ _)
      (harmonicPrimeBlockSourceFloor_le_adjacent_source _ _)
  rw [adjacentPrimeSurvivorVariance_split]
  have hh := mul_le_mul_of_nonneg_right hw (sq_nonneg
    (adjacentPrimeSurvivorCross (N+k) l / adjacentPrimeSurvivorSource (N+k) l -
      adjacentPrimeSurvivorCross N k / adjacentPrimeSurvivorSource N k))
  change _ ≤ adjacentPrimeSplitDrift N k l at hh
  linarith [adjacentPrimeSurvivorVariance_nonneg N k,
    adjacentPrimeSurvivorVariance_nonneg (N+k) l]

/-- Cancellation is performed before any estimate or absolute value. -/
theorem primeBlockCross_eq_adjacent_moment_sub_source (N k : ℕ) :
    primeBlockCross N k =
      product (Finset.range k) (fun i => primeSchurWeight (N+i))
        (fun i => factorialPrimeDelta (N+i))
        (fun i => -inner ℝ (adjacentSchurTrial (N+i)) (tailMinimum (N+i+1))) -
        primeBlockSource N k := by
  simp_rw [← schurEta_eq_neg_adjacentTrial]
  unfold primeBlockCross primeBlockSource product square
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only
  by_cases hp : Nat.Prime (N+i+3)
  · have he : schurEta (N+i+1) = factorialPrimeDelta (N+i)+factorialPrimeError (N+i) := by
      simpa only [factorialPrimeDelta] using factorialPrimeError_decomposition (N+i) hp
    rw [he]
    ring
  · simp [primeSchurWeight, hp]

/-- The boundary quotient is retained at empty prime children. -/
theorem primeBlockSlope_eq_adjacent_moment (N k : ℕ) :
    primeBlockCross N k / primeBlockSource N k =
      product (Finset.range k) (fun i => primeSchurWeight (N+i))
        (fun i => factorialPrimeDelta (N+i))
        (fun i => -inner ℝ (adjacentSchurTrial (N+i)) (tailMinimum (N+i+1))) /
          primeBlockSource N k -
      primeBlockSource N k / primeBlockSource N k := by
  rw [primeBlockCross_eq_adjacent_moment_sub_source, sub_div]

noncomputable def adjacentPrimeRegressionRemainder (N k : ℕ) : ℝ :=
  adjacentPrimeSurvivorSource N k *
    (1+primeBlockCross N k / primeBlockSource N k -
      adjacentPrimeSurvivorCross N k / adjacentPrimeSurvivorSource N k)^2 +
  square (Finset.range k)
    (fun i => primeSchurWeight (N+i)-adjacentPrimeRegressionWeight (N+i))
    (fun i => RiemannResearch.RH.Pareto.IntegerDPP.schurEta (N+i+1) -
      (1+primeBlockCross N k / primeBlockSource N k)*factorialPrimeDelta (N+i))

theorem adjacentPrimeRegressionRemainder_nonneg (N k : ℕ) :
    0 ≤ adjacentPrimeRegressionRemainder N k :=
  add_nonneg (mul_nonneg (adjacentPrimeSurvivorSource_nonneg _ _) (sq_nonneg _))
    (square_nonneg _ _ _ (fun i _ =>
      sub_nonneg.mpr (adjacentPrimeRegressionWeight_le (N+i))))

theorem primeBlockVariance_eq_adjacentSurvivor_add_remainder (N k : ℕ) :
    primeBlockVariance N k =
      adjacentPrimeSurvivorVariance N k + adjacentPrimeRegressionRemainder N k := by
  rw [primeBlockVariance_eq_adjacentSurvivor_remainders]
  unfold adjacentPrimeRegressionRemainder
  ring

/-- The exact capacity retains the original initial, mean, history and nonprime
channels, as well as both new regression-comparison squares. -/
theorem capacity_eq_adjacentPrimeSurvivor_budget (J : ℕ) :
    tailCapacity (2^J+1) = tailCapacity 1 + primeMeanMismatchBudget (2^J) +
      (∑ j ∈ Finset.range J, adjacentPrimeDyadicSplitBudget (2^j) j) +
      (∑ j ∈ Finset.range J, adjacentPrimeRegressionRemainder (2^j) (2^j)) +
      (∑ j ∈ Finset.range J, primeBlockMeanDrift (2^j) (2^j)) +
      compositeGainBudget (2^J) := by
  rw [capacity_eq_dyadic_prime_block_budget]
  have he : (∑ j ∈ Finset.range J, primeBlockVariance (2^j) (2^j)) =
      (∑ j ∈ Finset.range J, adjacentPrimeDyadicSplitBudget (2^j) j) +
      (∑ j ∈ Finset.range J, adjacentPrimeRegressionRemainder (2^j) (2^j)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [primeBlockVariance_eq_adjacentSurvivor_add_remainder,
      adjacentPrimeSurvivorVariance_eq_tree]
  rw [he]
  ring

end RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
