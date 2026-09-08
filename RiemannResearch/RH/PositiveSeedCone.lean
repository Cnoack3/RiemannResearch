import RiemannResearch.RH.ThresholdFiniteCertificate
import RiemannResearch.RH.ParetoDilation
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# An exact positive-coefficient obstruction for the two legal seeds

The generator is the project's actual arithmetic generator
`certificateGenerator a m k = k % (a*m) - k % m`, with real subtraction.
The seeds are 2 and 3 and every positive integer dilation remains available.

The identities at primes 5 and 7 yield a rational completion of squares and
the lower bound 37/1299 for approximation of the constant function by the
nonnegative cone. The unrestricted signed span is not subject to this bound.
The halfspace minimizer below witnesses sharpness of the finite relaxation;
it is not asserted to be a legal generator combination.
-/

namespace RiemannResearch.RH.PositiveSeedCone

open scoped BigOperators
open TwoSeedThreshold

noncomputable section

/-- The exact adjacent-prime defect at prime 5. -/
def defectFive (F : ℕ → ℝ) : ℝ := F 5 - F 4 - F 1

/-- The exact adjacent-prime defect at prime 7. -/
def defectSeven (F : ℕ → ℝ) : ℝ := F 7 - F 6 - F 1

/-- All five error coordinates retained with their actual Pareto weights. -/
def finiteError (F : ℕ → ℝ) : ℝ :=
  (1 - F 1) ^ 2 / 2 + (1 - F 4) ^ 2 / 20 +
  (1 - F 5) ^ 2 / 30 + (1 - F 6) ^ 2 / 42 +
  (1 - F 7) ^ 2 / 56

/-- The remainder in the exact rational dual certificate. -/
def centeredError (F : ℕ → ℝ) : ℝ :=
  (1 - F 1 - 74 / 1299) ^ 2 / 2 +
  (1 - F 4 - 490 / 1299) ^ 2 / 20 +
  (1 - F 5 + 735 / 1299) ^ 2 / 30 +
  (1 - F 6 - 525 / 1299) ^ 2 / 42 +
  (1 - F 7 + 700 / 1299) ^ 2 / 56

/-- Exact identity: no signed term or error coordinate has been discarded. -/
theorem finiteError_completion (F : ℕ → ℝ) :
    finiteError F = 37 / 1299 + centeredError F +
      (49 / 1299) * defectFive F + (25 / 1299) * defectSeven F := by
  unfold finiteError centeredError defectFive defectSeven
  ring

theorem centeredError_nonneg (F : ℕ → ℝ) : 0 ≤ centeredError F := by
  unfold centeredError
  positivity

/-- Sharp lower bound from the two explicitly stated halfspace constraints. -/
theorem finiteError_lower_of_defects (F : ℕ → ℝ)
    (h5 : 0 ≤ defectFive F) (h7 : 0 ≤ defectSeven F) :
    (37 : ℝ) / 1299 ≤ finiteError F := by
  have hc := centeredError_nonneg F
  have h5' : 0 ≤ (49 : ℝ) / 1299 * defectFive F :=
    mul_nonneg (by norm_num) h5
  have h7' : 0 ≤ (25 : ℝ) / 1299 * defectSeven F :=
    mul_nonneg (by norm_num) h7
  rw [finiteError_completion]
  linarith

/-- Exact arithmetic identities, uniform over every positive dilation. -/
theorem generator_defects_exact (a m : ℕ)
    (ha : a = 2 ∨ a = 3) (hm : 0 < m) :
    defectFive (certificateGenerator a m) = (if m = 5 then 5 else 0) ∧
    defectSeven (certificateGenerator a m) = (if m = 7 then 7 else 0) := by
  by_cases hm7 : m ≤ 7
  · rcases ha with rfl | rfl
    all_goals
      interval_cases m <;>
        norm_num [defectFive, defectSeven, certificateGenerator] at *
  · have hmlarge : 7 < m := by omega
    have ha1 : 1 ≤ a := by rcases ha with rfl | rfl <;> omega
    have hg (k : ℕ) (hk : k ≤ 7) : certificateGenerator a m k = 0 := by
      have hkm : k < m := by omega
      have hkam : k < a * m := by nlinarith
      simp only [certificateGenerator, Nat.mod_eq_of_lt hkm,
        Nat.mod_eq_of_lt hkam, sub_self]
    have hm5 : m ≠ 5 := by omega
    have hmseven : m ≠ 7 := by omega
    simp only [defectFive, defectSeven, hg 1 (by omega), hg 4 (by omega),
      hg 5 (by omega), hg 6 (by omega), hg 7 (by omega), hm5, hmseven,
      if_false, sub_self] <;> norm_num

theorem generator_defects_nonneg (a m : ℕ)
    (ha : a = 2 ∨ a = 3) (hm : 0 < m) :
    0 ≤ defectFive (certificateGenerator a m) ∧
    0 ≤ defectSeven (certificateGenerator a m) := by
  obtain ⟨h5, h7⟩ := generator_defects_exact a m ha hm
  rw [h5, h7]
  constructor <;> split_ifs <;> norm_num

/-- A finite combination of the actual seed generators. -/
def seedCombination {ι : Type*} (s : Finset ι)
    (a m : ι → ℕ) (c : ι → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ s, c i * certificateGenerator (a i) (m i) k

theorem defectFive_seedCombination {ι : Type*} (s : Finset ι)
    (a m : ι → ℕ) (c : ι → ℝ) :
    defectFive (seedCombination s a m c) =
      ∑ i ∈ s, c i * defectFive (certificateGenerator (a i) (m i)) := by
  simp only [defectFive, seedCombination, mul_sub, Finset.sum_sub_distrib]

theorem defectSeven_seedCombination {ι : Type*} (s : Finset ι)
    (a m : ι → ℕ) (c : ι → ℝ) :
    defectSeven (seedCombination s a m c) =
      ∑ i ∈ s, c i * defectSeven (certificateGenerator (a i) (m i)) := by
  simp only [defectSeven, seedCombination, mul_sub, Finset.sum_sub_distrib]

/-- The exact surviving defect is coefficient mass at dilations 5 and 7. -/
theorem seedCombination_defects_exact {ι : Type*} (s : Finset ι)
    (a m : ι → ℕ) (c : ι → ℝ)
    (ha : ∀ i ∈ s, a i = 2 ∨ a i = 3) (hm : ∀ i ∈ s, 0 < m i) :
    defectFive (seedCombination s a m c) =
      (∑ i ∈ s, c i * (if m i = 5 then 5 else 0)) ∧
    defectSeven (seedCombination s a m c) =
      (∑ i ∈ s, c i * (if m i = 7 then 7 else 0)) := by
  rw [defectFive_seedCombination, defectSeven_seedCombination]
  constructor
  · apply Finset.sum_congr rfl
    intro i hi
    rw [(generator_defects_exact (a i) (m i) (ha i hi) (hm i hi)).1]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [(generator_defects_exact (a i) (m i) (ha i hi) (hm i hi)).2]

theorem seedCombination_defects_nonneg {ι : Type*} (s : Finset ι)
    (a m : ι → ℕ) (c : ι → ℝ)
    (ha : ∀ i ∈ s, a i = 2 ∨ a i = 3)
    (hm : ∀ i ∈ s, 0 < m i) (hc : ∀ i ∈ s, 0 ≤ c i) :
    0 ≤ defectFive (seedCombination s a m c) ∧
    0 ≤ defectSeven (seedCombination s a m c) := by
  rw [defectFive_seedCombination, defectSeven_seedCombination]
  constructor
  · apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (hc i hi)
      (generator_defects_nonneg (a i) (m i) (ha i hi) (hm i hi)).1
  · apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (hc i hi)
      (generator_defects_nonneg (a i) (m i) (ha i hi) (hm i hi)).2

/-- Concrete obstruction for the finite nonnegative cone with all dilations. -/
theorem positive_seed_cone_finite_lower {ι : Type*} (s : Finset ι)
    (a m : ι → ℕ) (c : ι → ℝ)
    (ha : ∀ i ∈ s, a i = 2 ∨ a i = 3)
    (hm : ∀ i ∈ s, 0 < m i) (hc : ∀ i ∈ s, 0 ≤ c i) :
    (37 : ℝ) / 1299 ≤ finiteError (seedCombination s a m c) := by
  obtain ⟨h5, h7⟩ := seedCombination_defects_nonneg s a m c ha hm hc
  exact finiteError_lower_of_defects _ h5 h7

/-- Actual Pareto error summand, indexed starting at the positive integer 1. -/
def weightedError (F : ℕ → ℝ) (k : ℕ) : ℝ :=
  Pareto.positiveWeight (k + 1) * (1 - F (k + 1)) ^ 2

theorem weightedError_nonneg (F : ℕ → ℝ) (k : ℕ) :
    0 ≤ weightedError F k := by
  exact mul_nonneg (Pareto.positiveWeight_nonneg _) (sq_nonneg _)

theorem finiteError_eq_sum (F : ℕ → ℝ) :
    finiteError F = ∑ k ∈ ({0, 3, 4, 5, 6} : Finset ℕ), weightedError F k := by
  norm_num [finiteError, weightedError, Pareto.positiveWeight] <;> ring

/-- Infinite-norm lower bound, with the analytic summability obligation explicit. -/
theorem fullError_lower_of_defects (F : ℕ → ℝ)
    (h5 : 0 ≤ defectFive F) (h7 : 0 ≤ defectSeven F)
    (hsum : Summable (weightedError F)) :
    (37 : ℝ) / 1299 ≤ ∑' k : ℕ, weightedError F k := by
  calc
    (37 : ℝ) / 1299 ≤ finiteError F := finiteError_lower_of_defects F h5 h7
    _ = ∑ k ∈ ({0, 3, 4, 5, 6} : Finset ℕ), weightedError F k :=
      finiteError_eq_sum F
    _ ≤ ∑' k : ℕ, weightedError F k :=
      hsum.sum_le_tsum _ (fun k _ => weightedError_nonneg F k)

/-- The cone theorem for the full Pareto error, once summability is supplied. -/
theorem positive_seed_cone_full_lower_of_summable {ι : Type*} (s : Finset ι)
    (a m : ι → ℕ) (c : ι → ℝ)
    (ha : ∀ i ∈ s, a i = 2 ∨ a i = 3)
    (hm : ∀ i ∈ s, 0 < m i) (hc : ∀ i ∈ s, 0 ≤ c i)
    (hsum : Summable (weightedError (seedCombination s a m c))) :
    (37 : ℝ) / 1299 ≤ ∑' k : ℕ, weightedError (seedCombination s a m c) k := by
  obtain ⟨h5, h7⟩ := seedCombination_defects_nonneg s a m c ha hm hc
  exact fullError_lower_of_defects _ h5 h7 hsum

/-- A simple uniform bound suffices for absolute convergence of the error. -/
theorem weightedError_summable_of_bounded (F : ℕ → ℝ) (C : ℝ)
    (hF : ∀ k, |F k| ≤ C) : Summable (weightedError F) := by
  have hC : 0 ≤ C := (abs_nonneg (F 0)).trans (hF 0)
  have herr (k : ℕ) : |(1 - F k) ^ 2| ≤ (1 + C) ^ 2 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    have hf := abs_le.mp (hF k)
    have hleft : 0 ≤ (1 + C) - (1 - F k) := by linarith
    have hright : 0 ≤ (1 + C) + (1 - F k) := by linarith
    nlinarith [mul_nonneg hleft hright]
  have hs : Summable (fun k : ℕ => Pareto.positiveWeight k * (1 - F k) ^ 2) :=
    Pareto.weighted_summable_of_bounded herr
  change Summable (fun k : ℕ => Pareto.positiveWeight (k + 1) *
    (1 - F (k + 1)) ^ 2)
  exact (summable_nat_add_iff 1).2 hs

/-- Uniform generator bound obtained directly from the two remainders. -/
theorem generator_abs_le (a m k : ℕ) (ha : 0 < a) (hm : 0 < m) :
    |certificateGenerator a m k| ≤ ((a * m + m : ℕ) : ℝ) := by
  have hx : ((k % (a * m) : ℕ) : ℝ) ≤ ((a * m : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mod_lt k (Nat.mul_pos ha hm)).le
  have hy : ((k % m : ℕ) : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast (Nat.mod_lt k hm).le
  have hx0 : 0 ≤ ((k % (a * m) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hy0 : 0 ≤ ((k % m : ℕ) : ℝ) := Nat.cast_nonneg _
  have ha0 : 0 ≤ ((a * m : ℕ) : ℝ) := Nat.cast_nonneg _
  have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
  simp only [certificateGenerator, Nat.cast_add]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Explicit uniform bound, allowing arbitrary signs on the coefficients. -/
def coefficientBound {ι : Type*} (s : Finset ι)
    (a m : ι → ℕ) (c : ι → ℝ) : ℝ :=
  ∑ i ∈ s, |c i| * ((a i * m i + m i : ℕ) : ℝ)

theorem seedCombination_abs_le {ι : Type*} (s : Finset ι)
    (a m : ι → ℕ) (c : ι → ℝ)
    (ha : ∀ i ∈ s, 0 < a i) (hm : ∀ i ∈ s, 0 < m i) (k : ℕ) :
    |seedCombination s a m c k| ≤ coefficientBound s a m c := by
  have ht (i : ι) (hi : i ∈ s) :
      |c i * certificateGenerator (a i) (m i) k| ≤
        |c i| * ((a i * m i + m i : ℕ) : ℝ) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left
      (generator_abs_le (a i) (m i) k (ha i hi) (hm i hi)) (abs_nonneg _)
  unfold seedCombination coefficientBound
  refine abs_le.mpr ⟨?_, ?_⟩
  · rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum (fun i hi => (abs_le.mp (ht i hi)).1)
  · exact Finset.sum_le_sum (fun i hi => (abs_le.mp (ht i hi)).2)

/-- The actual finite combinations always have summable Pareto error. -/
theorem seedCombination_weightedError_summable {ι : Type*} (s : Finset ι)
    (a m : ι → ℕ) (c : ι → ℝ)
    (ha : ∀ i ∈ s, 0 < a i) (hm : ∀ i ∈ s, 0 < m i) :
    Summable (weightedError (seedCombination s a m c)) := by
  apply weightedError_summable_of_bounded _ (coefficientBound s a m c)
  intro k
  exact seedCombination_abs_le s a m c ha hm k

/-- Full Pareto norm obstruction for the positive cone; no analytic hypothesis. -/
theorem positive_seed_cone_full_lower {ι : Type*} (s : Finset ι)
    (a m : ι → ℕ) (c : ι → ℝ)
    (ha : ∀ i ∈ s, a i = 2 ∨ a i = 3)
    (hm : ∀ i ∈ s, 0 < m i) (hc : ∀ i ∈ s, 0 ≤ c i) :
    (37 : ℝ) / 1299 ≤ ∑' k : ℕ, weightedError (seedCombination s a m c) k := by
  apply positive_seed_cone_full_lower_of_summable s a m c ha hm hc
  apply seedCombination_weightedError_summable s a m c _ hm
  intro i hi
  rcases ha i hi with h | h <;> omega

/-- The exact minimizer of the two-halfspace finite relaxation. -/
def halfspaceMinimizer (k : ℕ) : ℝ :=
  if k = 1 then 1225 / 1299 else
  if k = 4 then 809 / 1299 else
  if k = 5 then 2034 / 1299 else
  if k = 6 then 774 / 1299 else
  if k = 7 then 1999 / 1299 else 0

theorem halfspaceMinimizer_attains :
    defectFive halfspaceMinimizer = 0 ∧
    defectSeven halfspaceMinimizer = 0 ∧
    finiteError halfspaceMinimizer = (37 : ℝ) / 1299 := by
  norm_num [defectFive, defectSeven, finiteError, halfspaceMinimizer]

end

end RiemannResearch.RH.PositiveSeedCone

/- Signed-coefficient extension, retaining the same module and namespace. -/
/-!
# Prime-five coefficient control for signed legal approximants

This module uses the exact arithmetic generators and the actual Pareto weights.
The coefficients may have arbitrary signs. An exact completion of squares
controls the aggregate coefficient mass at dilation 5 by the full error.
-/

namespace RiemannResearch.RH.PositiveSeedCone

open scoped BigOperators

noncomputable section

/-- Remainder after extracting the prime-five defect; all five coordinates remain. -/
def primeFiveCenteredError (F : ℕ → ℝ) : ℝ :=
  (1 - F 1 - (1 + defectFive F) / 26) ^ 2 / 2 +
  (1 - F 4 - 5 * (1 + defectFive F) / 13) ^ 2 / 20 +
  (1 - F 5 + 15 * (1 + defectFive F) / 26) ^ 2 / 30 +
  (1 - F 6) ^ 2 / 42 + (1 - F 7) ^ 2 / 56

/-- Exact prime-five square extraction; this identity imposes no sign condition. -/
theorem finiteError_primeFive_completion (F : ℕ → ℝ) :
    finiteError F = (1 + defectFive F) ^ 2 / 52 + primeFiveCenteredError F := by
  unfold finiteError primeFiveCenteredError defectFive
  ring

theorem primeFiveCenteredError_nonneg (F : ℕ → ℝ) :
    0 ≤ primeFiveCenteredError F := by
  unfold primeFiveCenteredError
  positivity

theorem finiteError_primeFive_forcedMass (F : ℕ → ℝ) :
    (1 + defectFive F) ^ 2 / 52 ≤ finiteError F := by
  have hn := primeFiveCenteredError_nonneg F
  rw [finiteError_primeFive_completion]
  linarith

/-- Quantitative prime-five defect control by the full Pareto error. -/
theorem fullError_primeFive_forcedMass (F : ℕ → ℝ)
    (hsum : Summable (weightedError F)) :
    (1 + defectFive F) ^ 2 / 52 ≤ ∑' k : ℕ, weightedError F k := by
  calc
    (1 + defectFive F) ^ 2 / 52 ≤ finiteError F :=
      finiteError_primeFive_forcedMass F
    _ = ∑ k ∈ ({0, 3, 4, 5, 6} : Finset ℕ), weightedError F k :=
      finiteError_eq_sum F
    _ ≤ ∑' k : ℕ, weightedError F k :=
      hsum.sum_le_tsum _ (fun k _ => weightedError_nonneg F k)

/-- Actual signed coefficients at dilation 5 are constrained by approximation error. -/
theorem signed_seed_primeFive_forcedMass {ι : Type*} (s : Finset ι)
    (a m : ι → ℕ) (c : ι → ℝ)
    (ha : ∀ i ∈ s, a i = 2 ∨ a i = 3)
    (hm : ∀ i ∈ s, 0 < m i) :
    (1 + ∑ i ∈ s, c i * (if m i = 5 then 5 else 0)) ^ 2 / 52 ≤
      ∑' k : ℕ, weightedError (seedCombination s a m c) k := by
  have ha0 : ∀ i ∈ s, 0 < a i := by
    intro i hi
    rcases ha i hi with h | h <;> omega
  have hs := seedCombination_weightedError_summable s a m c ha0 hm
  have hl := fullError_primeFive_forcedMass (seedCombination s a m c) hs
  rw [(seedCombination_defects_exact s a m c ha hm).1] at hl
  exact hl

/-- Passing below 1/52 forces the aggregate prime-five coefficient mass negative. -/
theorem signed_seed_primeFive_mass_negative {ι : Type*} (s : Finset ι)
    (a m : ι → ℕ) (c : ι → ℝ)
    (ha : ∀ i ∈ s, a i = 2 ∨ a i = 3)
    (hm : ∀ i ∈ s, 0 < m i)
    (herr : (∑' k : ℕ, weightedError (seedCombination s a m c) k) < 1 / 52) :
    (∑ i ∈ s, c i * (if m i = 5 then 5 else 0)) < 0 := by
  have hl := signed_seed_primeFive_forcedMass s a m c ha hm
  nlinarith [sq_nonneg (∑ i ∈ s, c i * (if m i = 5 then 5 else 0))]

/-- In particular, an approximant below this threshold has a negative coefficient at m=5. -/
theorem signed_seed_exists_negative_primeFive {ι : Type*} (s : Finset ι)
    (a m : ι → ℕ) (c : ι → ℝ)
    (ha : ∀ i ∈ s, a i = 2 ∨ a i = 3)
    (hm : ∀ i ∈ s, 0 < m i)
    (herr : (∑' k : ℕ, weightedError (seedCombination s a m c) k) < 1 / 52) :
    ∃ i ∈ s, m i = 5 ∧ c i < 0 := by
  classical
  have hneg := signed_seed_primeFive_mass_negative s a m c ha hm herr
  by_contra h
  have hnonneg : 0 ≤ ∑ i ∈ s, c i * (if m i = 5 then 5 else 0) := by
    apply Finset.sum_nonneg
    intro i hi
    by_cases hmi : m i = 5
    · rw [if_pos hmi]
      have hci : 0 ≤ c i := by
        by_contra hn
        exact h ⟨i, hi, hmi, lt_of_not_ge hn⟩
      exact mul_nonneg hci (by norm_num)
    · simp [hmi]
  linarith

end

end RiemannResearch.RH.PositiveSeedCone
