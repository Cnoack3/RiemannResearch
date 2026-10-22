import RiemannResearch.RH.BalazardReciprocalCharge
import RiemannResearch.NumberTheory.QuotientKernelEnergyLimit
import RiemannResearch.NumberTheory.SquarefreeEulerSeries
import RiemannResearch.Analysis.BoundedSquareEnergy

/-!
# Exact limiting energy of reciprocal-charge Riesz vectors

Source: user-provided `ReciprocalChargeNormLimit20260924.md`, Sections 1--2.
The quotient-window proof strategy extends Balazard, arXiv:1812.04309,
Propositions 5--6. The signed mixed term is retained in the exact identity.
No statement in this module asserts vanishing of the actual RH residual.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto
open RiemannResearch.NumberTheory.QuotientWindow

def mobiusQuotientDifference (N k : ℕ) : ℝ :=
  mobiusReciprocalSum (N / k) - mobiusReciprocalSum (N / (k + 1))

def mobiusQuotientBase (N k : ℕ) : ℝ :=
  mobiusReciprocalSum (N / (k + 1))

theorem reciprocalChargeRiesz_norm_sq_eq_energy (N : ℕ) :
    ‖reciprocalChargeRiesz N‖ ^ 2 =
      ∑ k ∈ Finset.Icc 1 N,
        (k : ℝ) * ((k : ℝ) + 1) * mobiusQuotientKernel N k ^ 2 := by
  rw [hilbert_norm_weighted_sq]
  rw [tsum_eq_sum (s := Finset.Icc 1 N) (by
    intro k hk
    by_cases hk0 : k = 0
    · simp [hk0]
    · have hkN : N < k := by
        have hn : ¬ (1 ≤ k ∧ k ≤ N) := by simpa only [Finset.mem_Icc] using hk
        omega
      rw [reciprocalChargeRiesz_sequence N k (Nat.pos_of_ne_zero hk0)]
      have hkS : N < k + 1 := by omega
      simp [Nat.div_eq_of_lt hkN, Nat.div_eq_of_lt hkS, mobiusReciprocalSum])]
  apply Finset.sum_congr rfl
  intro k hk
  have hk0 : 0 < k := (Finset.mem_Icc.mp hk).1
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hk0
  have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
  rw [reciprocalChargeRiesz_sequence N k hk0]
  unfold positiveWeight
  change 1 / ((k : ℝ) * ((k : ℝ) + 1)) *
    ((k : ℝ) * ((k : ℝ) + 1) * mobiusQuotientKernel N k) ^ 2 = _
  field_simp

theorem reciprocalChargeRiesz_norm_sq_decomposition (N : ℕ) :
    ‖reciprocalChargeRiesz N‖ ^ 2 =
      (∑ k ∈ Finset.Icc 1 N, mobiusQuotientDifference N k ^ 2) +
      (∑ k ∈ Finset.Icc 1 N, mobiusQuotientDifference N k ^ 2 / (k : ℝ)) +
      2 * (∑ k ∈ Finset.Icc 1 N,
        mobiusQuotientDifference N k * mobiusQuotientBase N k / (k : ℝ)) +
      (∑ k ∈ Finset.Icc 1 N,
        mobiusQuotientBase N k ^ 2 / ((k : ℝ) * ((k : ℝ) + 1))) := by
  rw [reciprocalChargeRiesz_norm_sq_eq_energy]
  simp only [Finset.sum_add_distrib, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  exact quotient_kernel_energy_exact mobiusReciprocalSum N k (Finset.mem_Icc.mp hk).1

open RiemannResearch.NumberTheory.QuotientWindow


/-- Exact limit of the full reciprocal-Möbius quotient-difference energy. -/
theorem mobius_quotient_difference_square_sum_tendsto :
    Tendsto (fun N => ∑ d ∈ Finset.Icc 1 N,
      (mobiusReciprocalSum (N / d) - mobiusReciprocalSum (N / (d + 1))) ^ 2)
      atTop (𝓝 (∑' n : ℕ, ((ArithmeticFunction.moebius n : ℝ) / (n : ℝ)) ^ 2)) := by
  have hη (n : ℕ) (hn : 0 < n) :
      |(ArithmeticFunction.moebius n : ℝ) / (n : ℝ)| ≤ 1 / (n : ℝ) := by
    rw [abs_div, abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n)]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
  have hlim (d : ℕ) (hd : 0 < d) :
      Tendsto (fun N => ∑ n ∈ window N d,
        (ArithmeticFunction.moebius n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
    have h1 := mobiusReciprocalSum_tendsto_zero.comp (nat_div_fixed_tendsto hd)
    have h2 := mobiusReciprocalSum_tendsto_zero.comp
      (nat_div_fixed_tendsto (show 0 < d + 1 by omega))
    simpa only [Function.comp_def, sub_zero, mobius_quotient_difference_eq_window _ _ hd] using h1.sub h2
  have ht := window_square_energy_tendsto
    (fun n => (ArithmeticFunction.moebius n : ℝ) / (n : ℝ)) (by simp) hη hlim
  have he (N : ℕ) :
      (∑ d ∈ Finset.Icc 1 N, (∑ n ∈ window N d,
        (ArithmeticFunction.moebius n : ℝ) / (n : ℝ)) ^ 2) =
      ∑ d ∈ Finset.Icc 1 N,
        (mobiusReciprocalSum (N / d) - mobiusReciprocalSum (N / (d + 1))) ^ 2 := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [mobius_quotient_difference_eq_window N d (Finset.mem_Icc.mp hd).1]
  simpa only [he] using ht


private theorem reciprocalSum_abs_le_one (N : ℕ) :
    |mobiusReciprocalSum N| ≤ 1 := by
  by_cases h : N = 0
  · simp [h, mobiusReciprocalSum]
  · exact mobiusReciprocalSum_abs_le_one N (Nat.pos_of_ne_zero h)

/-- The exact positive limiting energy; every arithmetic premise has a provider. -/
theorem reciprocalChargeRiesz_norm_sq_tendsto :
    Tendsto (fun N => ‖reciprocalChargeRiesz N‖ ^ 2)
      atTop (𝓝 (15 / Real.pi ^ 2)) := by
  have hη (n : ℕ) (hn : 0 < n) :
      |(ArithmeticFunction.moebius n : ℝ) / (n : ℝ)| ≤ 1 / (n : ℝ) := by
    rw [abs_div, abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n)]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
  have ht := quotient_kernel_square_energy_tendsto mobiusReciprocalSum
    (fun n => (ArithmeticFunction.moebius n : ℝ) / (n : ℝ)) (by simp) hη
    reciprocalSum_abs_le_one mobiusReciprocalSum_tendsto_zero
    mobius_quotient_difference_eq_window
  have heval : (∑' n : ℕ, ((ArithmeticFunction.moebius n : ℝ) / (n : ℝ)) ^ 2) =
      15 / Real.pi ^ 2 := by
    simpa only [div_pow] using RiemannResearch.NumberTheory.squarefree_reciprocal_square_sum
  rw [heval] at ht
  simpa only [reciprocalChargeRiesz_norm_sq_eq_energy, mobiusQuotientKernel] using ht

/-- Weak cancellation coexists with an exact positive distance from every fixed vector. -/
theorem reciprocalChargeRiesz_distance_sq_tendsto (f : ThresholdHilbert) :
    Tendsto (fun N => ‖f - reciprocalChargeRiesz N‖ ^ 2)
      atTop (𝓝 (‖f‖ ^ 2 + 15 / Real.pi ^ 2)) := by
  have hc : Tendsto (fun _ : ℕ => ‖f‖ ^ 2) atTop (𝓝 (‖f‖ ^ 2)) := tendsto_const_nhds
  have h := (hc.sub
    ((reciprocalChargeRiesz_weak_zero f).const_mul 2)).add reciprocalChargeRiesz_norm_sq_tendsto
  simpa only [norm_sub_sq_real, mul_zero, sub_zero] using h

/-- No cofinal subsequence of the reciprocal-charge vectors converges in norm. -/
theorem reciprocalChargeRiesz_no_norm_convergent_subsequence
    (σ : ℕ → ℕ) (hσ : Tendsto σ atTop atTop) (f : ThresholdHilbert) :
    ¬ Tendsto (fun N => reciprocalChargeRiesz (σ N)) atTop (𝓝 f) := by
  intro ht
  have hz : Tendsto (fun N => ‖f - reciprocalChargeRiesz (σ N)‖ ^ 2)
      atTop (𝓝 (0 : ℝ)) := by
    have hc : Tendsto (fun _ : ℕ => f) atTop (𝓝 f) := tendsto_const_nhds
    simpa using (hc.sub ht).norm.pow 2
  have hd := (reciprocalChargeRiesz_distance_sq_tendsto f).comp hσ
  have he := tendsto_nhds_unique hd hz
  have hp : (0 : ℝ) < 15 / Real.pi ^ 2 := by positivity
  nlinarith [sq_nonneg ‖f‖]

end RiemannResearch.RH.Pareto
