import RiemannResearch.RH.NearbyDilationGram
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Exact energy of sparse arithmetic packets

Source: user's CRT research program; direct termwise Pareto-weight calculation.
The arithmetic profile is arbitrary. For finite divisor-incidence profiles,
all signed coefficients and mixed terms remain inside the full square.
The physical reindexing retains the entire positive-coordinate energy.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.CRTSparseEnergy
open RiemannResearch.RH.Pareto

def referenceEnergy (A : ℕ → ℝ) : ℝ :=
  ∑' k : ℕ, (A (k+1) / ((k : ℝ)+1))^2

/-- The complete Pareto energy supported on positive multiples of M. -/
def sparseEnergy (M : ℕ) (A : ℕ → ℝ) : ℝ :=
  ∑' k : ℕ, positiveWeight (M*(k+1)) * ((M : ℝ)*A (k+1))^2

def positiveRemainder (M : ℕ) (A : ℕ → ℝ) : ℝ :=
  ∑' k : ℕ, (A (k+1)/((k : ℝ)+1))^2 / ((M : ℝ)*((k : ℝ)+1)+1)

theorem sparse_term_exact (M : ℕ) (hM : 0 < M) (A : ℕ → ℝ) (k : ℕ) :
    positiveWeight (M*(k+1))*((M : ℝ)*A (k+1))^2 +
      (A (k+1)/((k : ℝ)+1))^2 / ((M : ℝ)*((k : ℝ)+1)+1) =
      (A (k+1)/((k : ℝ)+1))^2 := by
  have hm : (M : ℝ) ≠ 0 := by positivity
  have hk : (k : ℝ)+1 ≠ 0 := by positivity
  have hmk : (M : ℝ)*((k : ℝ)+1)+1 ≠ 0 := by positivity
  unfold positiveWeight
  push_cast
  field_simp

theorem remainder_term_bounds (M : ℕ) (A : ℕ → ℝ) (k : ℕ) :
    0 ≤ (A (k+1)/((k : ℝ)+1))^2 / ((M : ℝ)*((k : ℝ)+1)+1) ∧
    (A (k+1)/((k : ℝ)+1))^2 / ((M : ℝ)*((k : ℝ)+1)+1) ≤
      (1 / ((M : ℝ)+1)) * (A (k+1)/((k : ℝ)+1))^2 := by
  constructor
  · positivity
  · have hm : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hinv : 1 / ((M : ℝ)*((k : ℝ)+1)+1) ≤ 1/((M : ℝ)+1) :=
      one_div_le_one_div_of_le (by positivity) (by nlinarith)
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using
      mul_le_mul_of_nonneg_left hinv (sq_nonneg (A (k+1)/((k : ℝ)+1)))

theorem remainder_summable (M : ℕ) (A : ℕ → ℝ)
    (hA : Summable (fun k : ℕ => (A (k+1)/((k : ℝ)+1))^2)) :
    Summable (fun k : ℕ =>
      (A (k+1)/((k : ℝ)+1))^2 / ((M : ℝ)*((k : ℝ)+1)+1)) := by
  apply Summable.of_nonneg_of_le (fun k => (remainder_term_bounds M A k).1)
    (fun k => (remainder_term_bounds M A k).2)
  exact hA.mul_left (1/((M : ℝ)+1))

theorem sparse_summable (M : ℕ) (hM : 0 < M) (A : ℕ → ℝ)
    (hA : Summable (fun k : ℕ => (A (k+1)/((k : ℝ)+1))^2)) :
    Summable (fun k : ℕ => positiveWeight (M*(k+1))*((M : ℝ)*A (k+1))^2) := by
  apply Summable.of_nonneg_of_le (fun k =>
    mul_nonneg (positiveWeight_nonneg _) (sq_nonneg _)) _ hA
  intro k
  have he := sparse_term_exact M hM A k
  have hr := (remainder_term_bounds M A k).1
  linarith

/-- Exact full energy decomposition; the remainder is a complete sum of squares. -/
theorem sparseEnergy_add_remainder (M : ℕ) (hM : 0 < M) (A : ℕ → ℝ)
    (hA : Summable (fun k : ℕ => (A (k+1)/((k : ℝ)+1))^2)) :
    sparseEnergy M A + positiveRemainder M A = referenceEnergy A := by
  unfold sparseEnergy positiveRemainder referenceEnergy
  rw [← (sparse_summable M hM A hA).tsum_add (remainder_summable M A hA)]
  apply tsum_congr
  exact sparse_term_exact M hM A

theorem positiveRemainder_bounds (M : ℕ) (A : ℕ → ℝ)
    (hA : Summable (fun k : ℕ => (A (k+1)/((k : ℝ)+1))^2)) :
    0 ≤ positiveRemainder M A ∧
      positiveRemainder M A ≤ referenceEnergy A / ((M : ℝ)+1) := by
  constructor
  · exact tsum_nonneg (fun k => (remainder_term_bounds M A k).1)
  · calc
      positiveRemainder M A ≤
          ∑' k : ℕ, (1/((M : ℝ)+1))*(A (k+1)/((k : ℝ)+1))^2 :=
        Summable.tsum_le_tsum (fun k => (remainder_term_bounds M A k).2)
          (remainder_summable M A hA) (hA.mul_left (1/((M : ℝ)+1)))
      _ = referenceEnergy A / ((M : ℝ)+1) := by
        rw [tsum_mul_left]
        unfold referenceEnergy
        ring

/-- A dimension- and conductor-independent relative quadratic-form comparison. -/
theorem sparseEnergy_relative_bounds (M : ℕ) (hM : 0 < M) (A : ℕ → ℝ)
    (hA : Summable (fun k : ℕ => (A (k+1)/((k : ℝ)+1))^2)) :
    ((M : ℝ)/((M : ℝ)+1))*referenceEnergy A ≤ sparseEnergy M A ∧
      sparseEnergy M A ≤ referenceEnergy A := by
  have he := sparseEnergy_add_remainder M hM A hA
  have hr := positiveRemainder_bounds M A hA
  have hid : ((M : ℝ)/((M : ℝ)+1))*referenceEnergy A =
      referenceEnergy A-referenceEnergy A/((M : ℝ)+1) := by
    have hm : (M : ℝ)+1 ≠ 0 := by positivity
    field_simp
    <;> ring
  rw [hid]
  constructor <;> linarith

/-- Bounded profiles include every finite signed divisor-incidence packet. -/
theorem bounded_profile_summable (A : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ n, |A n| ≤ C) :
    Summable (fun k : ℕ => (A (k+1)/((k : ℝ)+1))^2) := by
  have hw : Summable (fun k : ℕ => positiveWeight (k+1)) :=
    (summable_nat_add_iff 1).mpr positiveWeight_summable
  apply Summable.of_nonneg_of_le (fun k => sq_nonneg _) _ (hw.mul_left (2*C^2))
  intro k
  have hk : (1 : ℝ) ≤ (k : ℝ)+1 := by have := Nat.cast_nonneg (α := ℝ) k; linarith
  have hk0 : (0 : ℝ) < (k : ℝ)+1 := by positivity
  have ha : A (k+1)^2 ≤ C^2 := by
    have h := (sq_le_sq₀ (abs_nonneg (A (k+1))) hC).mpr (hA (k+1))
    simpa only [sq_abs] using h
  have hb : 1/((k : ℝ)+1)^2 ≤ 2*positiveWeight (k+1) := by
    unfold positiveWeight
    push_cast
    rw [mul_one_div]
    apply (div_le_div_iff₀ (sq_pos_of_pos hk0) (by positivity)).mpr
    nlinarith
  calc
    (A (k+1)/((k : ℝ)+1))^2 = A (k+1)^2 * (1/((k : ℝ)+1)^2) := by rw [div_pow]; ring
    _ ≤ C^2*(2*positiveWeight (k+1)) :=
      mul_le_mul ha hb (by positivity) (sq_nonneg C)
    _ = (2*C^2)*positiveWeight (k+1) := by ring

def incidenceProfile (s : Finset ℕ) (c : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ s, if d ∣ n then (d : ℝ)*c d else 0

theorem incidenceProfile_abs_le (s : Finset ℕ) (c : ℕ → ℝ) (n : ℕ) :
    |incidenceProfile s c n| ≤ ∑ d ∈ s, |(d : ℝ)*c d| := by
  unfold incidenceProfile
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro d hd
  split_ifs
  · exact le_rfl
  · simpa only [abs_zero] using abs_nonneg ((d : ℝ) * c d)

theorem incidenceProfile_summable (s : Finset ℕ) (c : ℕ → ℝ) :
    Summable (fun k : ℕ => (incidenceProfile s c (k+1)/((k : ℝ)+1))^2) :=
  bounded_profile_summable _ _ (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
    (incidenceProfile_abs_le s c)

/-- Exact reindexing of the whole physical energy, with no tail discarded. -/
theorem full_physical_energy_eq_sparseEnergy (M : ℕ) (hM : 0 < M)
    (A f : ℕ → ℝ) (hzero : f 0 = 0)
    (hmul : ∀ k : ℕ, f (M*(k+1)) = (M : ℝ)*A (k+1))
    (hsupport : ∀ n : ℕ, ¬ M ∣ n → f n = 0) :
    (∑' n : ℕ, positiveWeight n * (f n)^2) = sparseEnergy M A := by
  unfold sparseEnergy
  apply tsum_eq_tsum_of_ne_zero_bij
    (fun a : Function.support (fun k : ℕ =>
      positiveWeight (M*(k+1))*((M : ℝ)*A (k+1))^2) => M*(a.val+1))
  · intro a b hab
    apply Subtype.ext
    have h := Nat.eq_of_mul_eq_mul_left hM hab
    omega
  · intro n hn
    have hnz : n ≠ 0 := by
      intro hz
      subst n
      simpa only [Function.mem_support, hzero, zero_pow (by omega : 2 ≠ 0),
        mul_zero, ne_eq, not_true_eq_false] using hn
    have hdiv : M ∣ n := by
      by_contra hnot
      simpa only [Function.mem_support, hsupport n hnot,
        zero_pow (by omega : 2 ≠ 0), mul_zero, ne_eq, not_true_eq_false] using hn
    obtain ⟨a, rfl⟩ := hdiv
    have ha : 0 < a := by
      by_contra h
      have hz : a = 0 := Nat.eq_zero_of_not_pos h
      simp [hz] at hnz
    refine ⟨⟨a-1, ?_⟩, ?_⟩
    · have he := hmul (a-1)
      rw [Nat.sub_add_cancel ha] at he
      change positiveWeight (M*((a-1)+1))*((M : ℝ)*A ((a-1)+1))^2 ≠ 0
      rw [Nat.sub_add_cancel ha, ← he]
      exact hn
    · simp [Nat.sub_add_cancel ha]
  · intro a
    rw [hmul]

/-- Core profile comparison applied directly to the actual physical sequence. -/
theorem full_physical_energy_relative_bounds (M : ℕ) (hM : 0 < M)
    (A f : ℕ → ℝ) (hzero : f 0 = 0)
    (hmul : ∀ k : ℕ, f (M*(k+1)) = (M : ℝ)*A (k+1))
    (hsupport : ∀ n : ℕ, ¬ M ∣ n → f n = 0)
    (hA : Summable (fun k : ℕ => (A (k+1)/((k : ℝ)+1))^2)) :
    ((M : ℝ)/((M : ℝ)+1))*referenceEnergy A ≤
      (∑' n : ℕ, positiveWeight n * (f n)^2) ∧
      (∑' n : ℕ, positiveWeight n * (f n)^2) ≤ referenceEnergy A := by
  rw [full_physical_energy_eq_sparseEnergy M hM A f hzero hmul hsupport]
  exact sparseEnergy_relative_bounds M hM A hA

end RiemannResearch.RH.Pareto.CRTSparseEnergy
