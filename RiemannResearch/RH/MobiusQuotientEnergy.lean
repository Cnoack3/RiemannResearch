import RiemannResearch.NumberTheory.QuotientWindowSquareBound
import RiemannResearch.RH.CanonicalMobiusPNT

/-!
# The actual reciprocal Mobius quotient kernel

Source: Michel Balazard, arXiv:1812.04309, Propositions 5--6.
This module proves a uniform explicit squared energy bound for the kernel
appearing in the reciprocal charge functional and fixed-coordinate decay.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto
open RiemannResearch.NumberTheory.QuotientWindow

theorem mobiusReciprocalSum_sub_eq_Ioc (a b : ℕ) (hab : a ≤ b) :
    mobiusReciprocalSum b - mobiusReciprocalSum a =
      ∑ n ∈ Finset.Ioc a b, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) := by
  have hd : Disjoint (Finset.Icc 1 a) (Finset.Ioc a b) := by
    apply Finset.disjoint_left.mpr
    intro n hn hn'
    simp only [Finset.mem_Icc, Finset.mem_Ioc] at hn hn'
    omega
  have hu : Finset.Icc 1 a ∪ Finset.Ioc a b = Finset.Icc 1 b := by
    ext n
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  unfold mobiusReciprocalSum
  rw [← hu, Finset.sum_union hd]
  ring

theorem mobius_quotient_difference_eq_window (N d : ℕ) (hd : 0 < d) :
    mobiusReciprocalSum (N / d) - mobiusReciprocalSum (N / (d + 1)) =
      ∑ n ∈ window N d, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) := by
  apply mobiusReciprocalSum_sub_eq_Ioc
  have ha : N / (d + 1) * (d + 1) ≤ N := Nat.div_mul_le_self N (d + 1)
  apply (Nat.le_div_iff_mul_le hd).mpr
  nlinarith

theorem mobius_quotient_difference_square_sum_le (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 N,
      (mobiusReciprocalSum (N / d) - mobiusReciprocalSum (N / (d + 1))) ^ 2) ≤ 10 := by
  have hη (n : ℕ) (hn : 0 < n) :
      |(ArithmeticFunction.moebius n : ℝ) / (n : ℝ)| ≤ 1 / (n : ℝ) := by
    rw [abs_div, abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n)]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
  convert sum_window_sq_le_ten _ hη N using 1
  apply Finset.sum_congr rfl
  intro d hd
  rw [mobius_quotient_difference_eq_window N d (Finset.mem_Icc.mp hd).1]

def mobiusQuotientKernel (N k : ℕ) : ℝ :=
  mobiusReciprocalSum (N / k) / (k : ℝ) -
    mobiusReciprocalSum (N / (k + 1)) / ((k : ℝ) + 1)

private theorem mobiusReciprocalSum_abs_le_one_all (N : ℕ) :
    |mobiusReciprocalSum N| ≤ 1 := by
  by_cases h : N = 0
  · simp [h, mobiusReciprocalSum]
  · exact mobiusReciprocalSum_abs_le_one N (Nat.pos_of_ne_zero h)

theorem mobiusQuotientKernel_energy_pointwise (N k : ℕ) (hk : 0 < k) :
    (k : ℝ) * ((k : ℝ) + 1) * mobiusQuotientKernel N k ^ 2 ≤
      4 * (mobiusReciprocalSum (N / k) - mobiusReciprocalSum (N / (k + 1))) ^ 2 +
        2 / ((k : ℝ) * ((k : ℝ) + 1)) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkS : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  let a := mobiusReciprocalSum (N / k) - mobiusReciprocalSum (N / (k + 1))
  let b := mobiusReciprocalSum (N / (k + 1))
  have hb : b ^ 2 ≤ 1 := by
    have hh := mobiusReciprocalSum_abs_le_one_all (N / (k + 1))
    simpa only [b, sq_abs, one_pow] using
      (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mpr hh
  have he : mobiusQuotientKernel N k =
      a / (k : ℝ) + b / ((k : ℝ) * ((k : ℝ) + 1)) := by
    dsimp [mobiusQuotientKernel, a, b]
    field_simp
    ring
  have hsplit : (a * ((k : ℝ) + 1) + b) ^ 2 ≤
      2 * (a * ((k : ℝ) + 1)) ^ 2 + 2 * b ^ 2 := by
    nlinarith [sq_nonneg (a * ((k : ℝ) + 1) - b)]
  have hcoef : 2 * ((k : ℝ) + 1) ^ 2 * a ^ 2 ≤
      (4 * (k : ℝ) * ((k : ℝ) + 1)) * a ^ 2 := by
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg a)
    nlinarith
  have hfinal : (a * ((k : ℝ) + 1) + b) ^ 2 ≤
      4 * (k : ℝ) * ((k : ℝ) + 1) * a ^ 2 + 2 := by
    nlinarith
  have hid : (k : ℝ) * ((k : ℝ) + 1) * mobiusQuotientKernel N k ^ 2 =
      (a * ((k : ℝ) + 1) + b) ^ 2 / ((k : ℝ) * ((k : ℝ) + 1)) := by
    rw [he]
    field_simp
  rw [hid]
  change (a * ((k : ℝ) + 1) + b) ^ 2 / ((k : ℝ) * ((k : ℝ) + 1)) ≤
    4 * a ^ 2 + 2 / ((k : ℝ) * ((k : ℝ) + 1))
  apply (div_le_iff₀ (mul_pos hkR hkS)).mpr
  calc
    _ ≤ 4 * (k : ℝ) * ((k : ℝ) + 1) * a ^ 2 + 2 := hfinal
    _ = _ := by field_simp

theorem mobiusQuotientKernel_square_energy_le (N : ℕ) :
    (∑ k ∈ Finset.Icc 1 N,
      (k : ℝ) * ((k : ℝ) + 1) * mobiusQuotientKernel N k ^ 2) ≤ 42 := by
  have htel (M : ℕ) :
      (∑ k ∈ Finset.Icc 1 M, 1 / ((k : ℝ) * ((k : ℝ) + 1))) =
        1 - 1 / ((M : ℝ) + 1) := by
    induction M with
    | zero => norm_num
    | succ M ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      push_cast
      have h1 : (M : ℝ) + 1 ≠ 0 := by positivity
      have h2 : (M : ℝ) + 2 ≠ 0 := by positivity
      field_simp
      ring
  calc
    _ ≤ ∑ k ∈ Finset.Icc 1 N,
        (4 * (mobiusReciprocalSum (N / k) - mobiusReciprocalSum (N / (k + 1))) ^ 2 +
          2 / ((k : ℝ) * ((k : ℝ) + 1))) := by
      apply Finset.sum_le_sum
      intro k hk
      exact mobiusQuotientKernel_energy_pointwise N k (Finset.mem_Icc.mp hk).1
    _ = 4 * (∑ k ∈ Finset.Icc 1 N,
        (mobiusReciprocalSum (N / k) - mobiusReciprocalSum (N / (k + 1))) ^ 2) +
        2 * (1 - 1 / ((N : ℝ) + 1)) := by
      have he (k : ℕ) : 2 / ((k : ℝ) * ((k : ℝ) + 1)) =
          2 * (1 / ((k : ℝ) * ((k : ℝ) + 1))) := by ring
      simp_rw [he]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, htel]
    _ ≤ 42 := by
      have hi : (0 : ℝ) ≤ 1 / ((N : ℝ) + 1) := by positivity
      linarith [mobius_quotient_difference_square_sum_le N]

theorem nat_div_fixed_tendsto {k : ℕ} (hk : 0 < k) :
    Tendsto (fun N : ℕ => N / k) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (b * k)] with N hN
  exact (Nat.le_div_iff_mul_le hk).mpr hN

theorem mobiusQuotientKernel_tendsto_zero (k : ℕ) (hk : 0 < k) :
    Tendsto (fun N => mobiusQuotientKernel N k) atTop (𝓝 0) := by
  have h1 := mobiusReciprocalSum_tendsto_zero.comp (nat_div_fixed_tendsto hk)
  have h2 := mobiusReciprocalSum_tendsto_zero.comp
    (nat_div_fixed_tendsto (show 0 < k + 1 by omega))
  simpa [mobiusQuotientKernel] using
    (h1.div_const (k : ℝ)).sub (h2.div_const ((k : ℝ) + 1))

end RiemannResearch.RH.Pareto
