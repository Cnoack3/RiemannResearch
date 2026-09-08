import RiemannResearch.RH.PositiveSeedCone
import RiemannResearch.RH.ParetoResidueDuality
import RiemannResearch.LinearAlgebra.WeightedDualCertificate
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp

/-!
# Exact finite-component obstructions for the actual two-seed generators

Source: ordinary mathematical derivation in the 8 September 2026 RH continuation,
expanding the component-charge argument in `prime7/gain_research.md`, section 3.
The arithmetic charge is the genuine Möbius difference. Its action on every
actual remainder generator is proved, including arbitrary integer dilations.
The finite Riesz identity retains every weighted square before taking a bound.
-/

namespace RiemannResearch.RH.FiniteSeedComponentCharge

open scoped BigOperators
open PositiveSeedCone TwoSeedThreshold Pareto
open RiemannResearch.LinearAlgebra

noncomputable section

/-- The signed charge at one vertex is the actual divisor-inverted jump. -/
theorem mobiusDifference_generator (n a m : ℕ) (hn : 0 < n) :
    mobiusDifference n (certificateGenerator a m) =
      (if n = m then (m : ℝ) else 0) -
        (if n = a * m then ((a * m : ℕ) : ℝ) else 0) := by
  let f : ℕ → ℝ := fun d => (if d = m then (m : ℝ) else 0) -
    (if d = a * m then ((a * m : ℕ) : ℝ) else 0)
  have hs : ∀ k > 0, ∑ d ∈ k.divisors, f d =
      certificateGenerator a m k - certificateGenerator a m (k - 1) := by
    intro k hk
    have h1 := residue_difference m k hk
    have h2 := residue_difference (a * m) k hk
    change (∑ d ∈ k.divisors, f d) =
      (residue (a * m) k - residue m k) -
        (residue (a * m) (k - 1) - residue m (k - 1))
    by_cases hmk : m ∣ k <;> by_cases hamk : a * m ∣ k <;>
      simp [f, Finset.sum_sub_distrib, Nat.mem_divisors, ne_of_gt hk, hmk, hamk] at * <;>
        linarith
  exact (mobius_inversion f (fun k => certificateGenerator a m k -
    certificateGenerator a m (k - 1))).mp hs n hn

/-- Total normalized divergence on a finite arithmetic component. -/
def componentCharge (S : Finset ℕ) (F : ℕ → ℝ) : ℝ :=
  ∑ n ∈ S, mobiusDifference n F / (n : ℝ)

/-- The only possible charge is at the two actual endpoints. -/
theorem componentCharge_generator (S : Finset ℕ) (a m : ℕ)
    (hS : ∀ n ∈ S, 0 < n) (ha : 0 < a) (hm : 0 < m) :
    componentCharge S (certificateGenerator a m) =
      (if m ∈ S then 1 else 0) - (if a * m ∈ S then 1 else 0) := by
  unfold componentCharge
  have ht (n : ℕ) (hn : n ∈ S) :
      mobiusDifference n (certificateGenerator a m) / (n : ℝ) =
        (if n = m then 1 else 0) - (if n = a * m then 1 else 0) := by
    rw [mobiusDifference_generator n a m (hS n hn)]
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (hS n hn))
    split_ifs with h1 h2 <;> simp_all
  rw [Finset.sum_congr rfl ht, Finset.sum_sub_distrib]
  simp

/-- Linearity is proved for arbitrary coefficient signs. -/
theorem componentCharge_seedCombination {ι : Type*} (S : Finset ℕ)
    (s : Finset ι) (a m : ι → ℕ) (c : ι → ℝ) :
    componentCharge S (seedCombination s a m c) =
      ∑ i ∈ s, c i * componentCharge S (certificateGenerator (a i) (m i)) := by
  have hlin (n : ℕ) : mobiusDifference n (seedCombination s a m c) =
      ∑ i ∈ s, c i * mobiusDifference n (certificateGenerator (a i) (m i)) := by
    unfold mobiusDifference seedCombination
    simp_rw [← Finset.sum_sub_distrib, ← mul_sub, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro d hd
    ring
  unfold componentCharge
  simp_rw [hlin, Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  ring

/-- No finite signed legal combination has charge on a closed seed component. -/
theorem seedCombination_componentCharge_eq_zero {ι : Type*} (S : Finset ℕ)
    (s : Finset ι) (a m : ι → ℕ) (c : ι → ℝ)
    (hS : ∀ n ∈ S, 0 < n)
    (ha : ∀ i ∈ s, 0 < a i) (hm : ∀ i ∈ s, 0 < m i)
    (hclosed : ∀ i ∈ s, m i ∈ S ↔ a i * m i ∈ S) :
    componentCharge S (seedCombination s a m c) = 0 := by
  rw [componentCharge_seedCombination]
  apply Finset.sum_eq_zero
  intro i hi
  rw [componentCharge_generator S (a i) (m i) hS (ha i hi) (hm i hi)]
  simp only [hclosed i hi, sub_self, mul_zero]

/-- Exact target signal. It is not imposed as a new positivity assumption. -/
def componentSignal (S : Finset ℕ) : ℝ :=
  ∑ n ∈ S, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ)

theorem componentCharge_target (S : Finset ℕ) (hS : ∀ n ∈ S, 0 < n) :
    componentCharge S (fun k => if k = 0 then 0 else 1) = componentSignal S := by
  unfold componentCharge componentSignal
  apply Finset.sum_congr rfl
  intro n hn
  rw [mobiusDifference_one n (hS n hn)]

/-- A positive-coordinate spike, used to compute the actual dual row. -/
def coordinateSpike (k : ℕ) (n : ℕ) : ℝ := if n = k + 1 then 1 else 0

/-- The coefficients are evaluations of the genuine arithmetic functional. -/
def componentRow (S : Finset ℕ) (k : ℕ) : ℝ :=
  componentCharge S (coordinateSpike k)

private theorem prefix_reconstruct (N d : ℕ) (hd : d ≤ N)
    (F : ℕ → ℝ) (h0 : F 0 = 0) :
    (∑ k ∈ Finset.range N, F (k + 1) * coordinateSpike k d) = F d := by
  by_cases hd0 : d = 0
  · subst d
    simp [coordinateSpike, h0]
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
    have heq (k : ℕ) : d = k + 1 ↔ k = d - 1 := by omega
    simp only [coordinateSpike, heq, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq']
    simp [Finset.mem_range, show d - 1 < N by omega, Nat.sub_add_cancel hdpos]

/-- Exact finite representation; the anchored zero coordinate is retained. -/
theorem componentCharge_eq_row (S : Finset ℕ) (N : ℕ)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N) (F : ℕ → ℝ) (h0 : F 0 = 0) :
    componentCharge S F = ∑ k ∈ Finset.range N, componentRow S k * F (k + 1) := by
  have hlin : componentCharge S
      (fun d => ∑ k ∈ Finset.range N, F (k + 1) * coordinateSpike k d) =
      ∑ k ∈ Finset.range N, F (k + 1) * componentRow S k := by
    unfold componentRow
    unfold componentCharge
    simp_rw [mobiusDifference_sum]
    simp only [Finset.sum_div]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  have hrestrict : componentCharge S F = componentCharge S
      (fun d => ∑ k ∈ Finset.range N, F (k + 1) * coordinateSpike k d) := by
    unfold componentCharge mobiusDifference
    apply Finset.sum_congr rfl
    intro n hn
    congr 1
    apply Finset.sum_congr rfl
    intro d hd
    have hdN : d ≤ N := le_trans (Nat.le_of_dvd (hS n hn).1
      (Nat.dvd_of_mem_divisors hd)) (hS n hn).2
    dsimp only
    rw [prefix_reconstruct N d hdN F h0,
      prefix_reconstruct N (d - 1) (by omega) F h0]
  rw [hrestrict, hlin]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- The row mass equals the exact Möbius target signal. -/
theorem componentRow_sum (S : Finset ℕ) (N : ℕ)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N) :
    (∑ k ∈ Finset.range N, componentRow S k) = componentSignal S := by
  have h := componentCharge_eq_row S N hS
    (fun k => if k = 0 then 0 else 1) (by simp)
  rw [componentCharge_target S (fun n hn => (hS n hn).1)] at h
  simpa using h.symm

/-- The exact squared dual norm, with no mixed-term estimate. -/
def componentDualNorm (S : Finset ℕ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, (componentRow S k) ^ 2 / positiveWeight (k + 1)

private theorem componentWeight_pos (k : ℕ) : 0 < positiveWeight (k + 1) := by
  unfold positiveWeight
  positivity

/-- Exact extraction of the entire finite-component obstruction. -/
theorem componentFiniteError_exact (S : Finset ℕ) (N : ℕ)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N) (F : ℕ → ℝ) (h0 : F 0 = 0)
    (hF : componentCharge S F = 0) (hD : componentDualNorm S N ≠ 0) :
    (∑ k ∈ Finset.range N, weightedError F k) =
      (componentSignal S) ^ 2 / componentDualNorm S N +
        ∑ k ∈ Finset.range N, positiveWeight (k + 1) *
          (1 - F (k + 1) - componentSignal S / componentDualNorm S N *
            componentRow S k / positiveWeight (k + 1)) ^ 2 := by
  let T := componentSignal S
  let D := componentDualNorm S N
  let w : Fin N → ℝ := fun k => positiveWeight (k.val + 1)
  let z : Fin N → ℝ := fun k => T / D * componentRow S k.val
  let f : Fin N → ℝ := fun k => F (k.val + 1)
  have hz : (∑ k : Fin N, z k * f k) = 0 := by
    change (∑ k : Fin N, (T / D * componentRow S k.val) * F (k.val + 1)) = 0
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum,
      Fin.sum_univ_eq_sum_range (fun k => componentRow S k * F (k + 1)) N,
      ← componentCharge_eq_row S N hS F h0, hF, mul_zero]
  have hval : (∑ k : Fin N, (2 * z k - (z k) ^ 2 / w k)) = T ^ 2 / D := by
    change (∑ k : Fin N, (2 * (T / D * componentRow S k.val) -
      (T / D * componentRow S k.val) ^ 2 / positiveWeight (k.val + 1))) = T ^ 2 / D
    have he (k : Fin N) :
        2 * (T / D * componentRow S k.val) -
          (T / D * componentRow S k.val) ^ 2 / positiveWeight (k.val + 1) =
        (2 * T / D) * componentRow S k.val -
          (T / D) ^ 2 * ((componentRow S k.val) ^ 2 / positiveWeight (k.val + 1)) := by
      ring
    simp_rw [he]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      Fin.sum_univ_eq_sum_range (componentRow S) N,
      Fin.sum_univ_eq_sum_range (fun k => (componentRow S k) ^ 2 / positiveWeight (k + 1)) N,
      componentRow_sum S N hS]
    change (2 * T / D) * T - (T / D) ^ 2 * D = T ^ 2 / D
    dsimp [D]
    field_simp [hD]
    ring
  have he := weighted_error_dual_exact w z f
    (fun k => componentWeight_pos k.val) hz
  rw [hval] at he
  dsimp only [w, z, f] at he
  rw [Fin.sum_univ_eq_sum_range
      (fun k => positiveWeight (k + 1) * (1 - F (k + 1)) ^ 2) N,
    Fin.sum_univ_eq_sum_range
      (fun k => positiveWeight (k + 1) *
        (1 - F (k + 1) - T / D * componentRow S k / positiveWeight (k + 1)) ^ 2) N] at he
  simpa only [T, D, weightedError] using he

/-- The exact finite remainder gives the complete infinite error lower bound. -/
theorem componentFullError_lower (S : Finset ℕ) (N : ℕ)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N) (F : ℕ → ℝ) (h0 : F 0 = 0)
    (hF : componentCharge S F = 0) (hD : componentDualNorm S N ≠ 0)
    (hsum : Summable (weightedError F)) :
    (componentSignal S) ^ 2 / componentDualNorm S N ≤ ∑' k : ℕ, weightedError F k := by
  have hr : 0 ≤ ∑ k ∈ Finset.range N, positiveWeight (k + 1) *
      (1 - F (k + 1) - componentSignal S / componentDualNorm S N *
        componentRow S k / positiveWeight (k + 1)) ^ 2 := by
    exact Finset.sum_nonneg fun k _ =>
      mul_nonneg (le_of_lt (componentWeight_pos k)) (sq_nonneg _)
  calc
    _ ≤ ∑ k ∈ Finset.range N, weightedError F k := by
      rw [componentFiniteError_exact S N hS F h0 hF hD]
      exact le_add_of_nonneg_right hr
    _ ≤ ∑' k : ℕ, weightedError F k :=
      hsum.sum_le_tsum _ (fun k _ => weightedError_nonneg F k)

/-- A nonzero target signal makes the explicit dual norm strictly positive. -/
theorem componentDualNorm_pos (S : Finset ℕ) (N : ℕ)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N) (hT : componentSignal S ≠ 0) :
    0 < componentDualNorm S N := by
  have hn : 0 ≤ componentDualNorm S N := by
    unfold componentDualNorm
    exact Finset.sum_nonneg fun k _ =>
      div_nonneg (sq_nonneg _) (le_of_lt (componentWeight_pos k))
  apply lt_of_le_of_ne hn
  intro hz
  have hrows : ∀ k ∈ Finset.range N, componentRow S k = 0 := by
    intro k hk
    have ht : (componentRow S k) ^ 2 / positiveWeight (k + 1) = 0 := by
      have hsum := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j (_ : j ∈ Finset.range N) =>
          div_nonneg (sq_nonneg (componentRow S j))
            (le_of_lt (componentWeight_pos j)))).mp hz.symm
      exact hsum k hk
    have hs : (componentRow S k) ^ 2 = 0 :=
      (div_eq_zero_iff).mp ht |>.resolve_right (ne_of_gt (componentWeight_pos k))
    exact sq_eq_zero_iff.mp hs
  apply hT
  rw [← componentRow_sum S N hS]
  exact Finset.sum_eq_zero hrows

/-- Uniform full-error obstruction for any finite closed component and all signed coefficients. -/
theorem closedComponent_seedCombination_fullError_lower {ι : Type*}
    (S : Finset ℕ) (N : ℕ) (s : Finset ι) (a m : ι → ℕ) (c : ι → ℝ)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N)
    (ha : ∀ i ∈ s, 0 < a i) (hm : ∀ i ∈ s, 0 < m i)
    (hclosed : ∀ i ∈ s, m i ∈ S ↔ a i * m i ∈ S)
    (hT : componentSignal S ≠ 0) :
    0 < (componentSignal S) ^ 2 / componentDualNorm S N ∧
      (componentSignal S) ^ 2 / componentDualNorm S N ≤
        ∑' k : ℕ, weightedError (seedCombination s a m c) k := by
  have hD := componentDualNorm_pos S N hS hT
  constructor
  · exact div_pos (sq_pos_of_ne_zero hT) hD
  · apply componentFullError_lower S N hS _ _ _ (ne_of_gt hD)
      (seedCombination_weightedError_summable s a m c ha hm)
    · simp [seedCombination, certificateGenerator]
    · exact seedCombination_componentCharge_eq_zero S s a m c
        (fun n hn => (hS n hn).1) ha hm hclosed

end

end RiemannResearch.RH.FiniteSeedComponentCharge
