import RiemannResearch.NumberTheory.PrimeNumberTheorem.MobiusFloorTailReindex
import RiemannResearch.NumberTheory.MobiusReciprocalSum
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Reciprocal Möbius rate from a summatory logarithmic bound

Source: the exact cutoff argument in HardyEndpointFormalization20260924.md.
The underlying floor approximation is the existing PrimeNumberTheorem.Consequences
identity; this module retains and estimates the complete quotient-level tail.
-/

noncomputable section
open Filter Finset
open scoped BigOperators Topology ArithmeticFunction.Moebius

namespace RiemannResearch.NumberTheory.PrimeNumberTheorem
open RiemannResearch.RH.Pareto

/-- Real and natural quotient floors agree for the nonnegative integer quotient. -/
theorem integer_floor_nat_quotient (X n : ℕ) :
    (⌊(X : ℝ)/(n : ℝ)⌋ : ℝ) = (((X/n : ℕ) : ℝ)) := by
  have hf : ⌊(X : ℝ)/(n : ℝ)⌋₊ = X/n := by
    rw [Nat.floor_div_natCast, Nat.floor_natCast]
  have hlo := Nat.floor_le (show 0 ≤ (X : ℝ)/(n : ℝ) by positivity)
  have hhi := Nat.lt_floor_add_one ((X : ℝ)/(n : ℝ))
  rw [hf] at hlo hhi
  have hi : ⌊(X : ℝ)/(n : ℝ)⌋ = ((X/n : ℕ) : ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor
    · exact_mod_cast hlo
    · exact_mod_cast hhi
  rw [hi]
  norm_cast

/-- The quotient-level harmonic sum is bounded by the inclusive harmonic number. -/
theorem reciprocal_Ico_le_harmonic (K : ℕ) :
    (∑ j ∈ Finset.Ico 1 K, 1 / (j : ℝ)) ≤ (harmonic K : ℝ) := by
  calc
    (∑ j ∈ Finset.Ico 1 K, 1 / (j : ℝ)) ≤
        ∑ j ∈ Finset.Icc 1 K, 1 / (j : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j hj
        simp only [Finset.mem_Ico, Finset.mem_Icc] at hj ⊢
        omega
      · intro j hj hnot
        positivity
    _ = (harmonic K : ℝ) := by
      simp [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]

/-- Finite reciprocal-Möbius cutoff estimate from uniform summatory control above N. -/
theorem mobiusReciprocalSum_cutoff_bound_of_uniform_M_bound (N K : ℕ)
    (hN : 0 < N) (hK : 0 < K) (A : ℝ) (hA : 0 ≤ A)
    (hM : ∀ y : ℝ, (N : ℝ) ≤ y → |M y| ≤ A*y) :
    |mobiusReciprocalSum N| ≤ 1/(K : ℝ) + 1/((N : ℝ)*(K : ℝ)) +
      A*((harmonic K : ℝ)+1) := by
  have hK0 : (K : ℝ) ≠ 0 := by positivity
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  have hx0 : (0 : ℝ) < ((N*K : ℕ) : ℝ) := by positivity
  have hx1 : (1 : ℝ) ≤ ((N*K : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ N*K from Nat.mul_pos hN hK)
  have hdiv : ((N*K : ℕ) : ℝ)/(K : ℝ) = (N : ℝ) := by
    rw [Nat.cast_mul]
    field_simp
  have happ := sum_mobius_div_approx ((N*K : ℕ) : ℝ) K hK hx1
  rw [hdiv, Nat.floor_natCast, Nat.floor_natCast] at happ
  simp_rw [integer_floor_nat_quotient] at happ
  change |((N*K : ℕ) : ℝ)*mobiusReciprocalSum N - 1| ≤
    (N : ℝ) + |∑ n ∈ Finset.Ioc N (N*K), (ArithmeticFunction.moebius n : ℝ) *
      (((N*K)/n : ℕ) : ℝ)| at happ
  have ht0 := mobius_floor_tail_abs_le_of_M_bound N K hN hK A hA hM
  have htail : |∑ n ∈ Finset.Ioc N (N*K), (ArithmeticFunction.moebius n : ℝ) *
      (((N*K)/n : ℕ) : ℝ)| ≤
      A*((N*K : ℕ) : ℝ)*((harmonic K : ℝ)+1) := by
    exact ht0.trans (mul_le_mul_of_nonneg_left
      (add_le_add (reciprocal_Ico_le_harmonic K) le_rfl)
      (mul_nonneg hA hx0.le))
  have hv : ((N*K : ℕ) : ℝ)*|mobiusReciprocalSum N| ≤
      |((N*K : ℕ) : ℝ)*mobiusReciprocalSum N - 1| + 1 := by
    have hh := abs_sub_le (((N*K : ℕ) : ℝ)*mobiusReciprocalSum N) 1 0
    simpa only [sub_zero, abs_one, abs_mul, abs_of_pos hx0] using hh
  calc
    |mobiusReciprocalSum N| ≤
        ((N : ℝ)+A*((N*K : ℕ) : ℝ)*((harmonic K : ℝ)+1)+1)/((N*K : ℕ) : ℝ) := by
      apply (le_div_iff₀ hx0).mpr
      nlinarith
    _ = 1/(K : ℝ)+1/((N : ℝ)*(K : ℝ))+A*((harmonic K : ℝ)+1) := by
      rw [Nat.cast_mul]
      field_simp
      <;> ring

/-- Eventual logarithmic summatory control supplies a cutoff bound simultaneously for every K. -/
theorem mobiusReciprocalSum_eventual_cutoff_bound_of_M_log_bound
    (C : ℝ) (hC : 0 ≤ C)
    (hM : ∀ᶠ y : ℝ in atTop, |M y * Real.log y| ≤ C*y) :
    ∀ᶠ N : ℕ in atTop, ∀ K : ℕ, 0 < K →
      |mobiusReciprocalSum N| ≤ 1/(K : ℝ) + 1/((N : ℝ)*(K : ℝ)) +
        C*((harmonic K : ℝ)+1)/Real.log (N : ℝ) := by
  obtain ⟨Y, hY⟩ := Filter.eventually_atTop.mp hM
  have hNY : ∀ᶠ N : ℕ in atTop, Y ≤ (N : ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop).eventually
      (eventually_ge_atTop Y)
  filter_upwards [hNY, eventually_ge_atTop (2 : ℕ)] with N hNY hN2
  have hN : 0 < N := by omega
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hbound : ∀ y : ℝ, (N : ℝ) ≤ y →
      |M y| ≤ (C/Real.log (N : ℝ))*y := by
    intro y hy
    have hy1 : 1 < y := hN1.trans_le hy
    have hlogy : 0 ≤ Real.log y := (Real.log_pos hy1).le
    have hlog : Real.log (N : ℝ) ≤ Real.log y :=
      Real.log_le_log (by positivity) hy
    have hh := hY y (hNY.trans hy)
    rw [abs_mul, abs_of_nonneg hlogy] at hh
    have hl : |M y| * Real.log (N : ℝ) ≤ C*y :=
      (mul_le_mul_of_nonneg_left hlog (abs_nonneg _)).trans hh
    calc
      |M y| ≤ (C*y)/Real.log (N : ℝ) := (le_div_iff₀ hlogN).mpr hl
      _ = (C/Real.log (N : ℝ))*y := by ring
  intro K hK
  have hb := mobiusReciprocalSum_cutoff_bound_of_uniform_M_bound N K hN hK
    (C/Real.log (N : ℝ)) (div_nonneg hC hlogN.le) hbound
  simpa only [div_mul_eq_mul_div] using hb

end RiemannResearch.NumberTheory.PrimeNumberTheorem
