import RiemannResearch.RH.MobiusReciprocalChargeBridge
import RiemannResearch.NumberTheory.SquarefreeEulerSeries
import RiemannResearch.NumberTheory.PrimeNumberTheorem.MobiusReciprocal

/-! Arithmetic identities for the sum of reciprocal-charge vectors at
cutoffs `N` and `h*N`. This file retains the signed mixed term exactly. -/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.NumberTheory

/-- Reindex an arbitrary finite sum over positive multiples. -/
theorem positive_dilation_sum (M h : ℕ) (hh : 0 < h) (f : ℕ → ℝ) :
    (∑ n ∈ Finset.Icc 1 M, if h ∣ n then f (n / h) else 0) =
      ∑ d ∈ Finset.Icc 1 (M / h), f d := by
  classical
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun n _ => n / h) ?_ ?_ ?_ ?_
  · intro n hn
    have hnI := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
    have hhn := (Finset.mem_filter.mp hn).2
    apply Finset.mem_Icc.mpr
    constructor
    · apply (Nat.le_div_iff_mul_le hh).mpr
      simpa using Nat.le_of_dvd (show 0 < n by omega) hhn
    · exact Nat.div_le_div_right hnI.2
  · intro n hn m hm he
    have hnq := Nat.div_mul_cancel (Finset.mem_filter.mp hn).2
    have hmq := Nat.div_mul_cancel (Finset.mem_filter.mp hm).2
    calc
      n = (n / h) * h := hnq.symm
      _ = (m / h) * h := by rw [he]
      _ = m := hmq
  · intro d hd
    have hdI := Finset.mem_Icc.mp hd
    have hdM : d * h ≤ M := (Nat.le_div_iff_mul_le hh).mp hdI.2
    have hdvd : h ∣ d * h := ⟨d, by ring⟩
    have hq : (d * h) / h = d := by
      apply Nat.eq_of_mul_eq_mul_left hh
      simpa only [Nat.mul_comm] using Nat.div_mul_cancel hdvd
    refine ⟨d * h, Finset.mem_filter.mpr ⟨?_, hdvd⟩, hq⟩
    exact Finset.mem_Icc.mpr ⟨by nlinarith, hdM⟩
  · intro n hn
    rfl

end RiemannResearch.NumberTheory

namespace RiemannResearch.RH.Pareto
open RiemannResearch.NumberTheory

def mobiusReciprocalCoefficient (n : ℕ) : ℝ :=
  (ArithmeticFunction.moebius n : ℝ) / (n : ℝ)

def dilationMobiusCoefficient (h n : ℕ) : ℝ :=
  mobiusReciprocalCoefficient n +
    if h ∣ n then mobiusReciprocalCoefficient (n / h) else 0

def dilationMobiusKernel (h M : ℕ) : ℝ :=
  mobiusReciprocalSum M + mobiusReciprocalSum (M / h)

@[simp] theorem mobiusReciprocalCoefficient_zero : mobiusReciprocalCoefficient 0 = 0 := by
  simp [mobiusReciprocalCoefficient]

@[simp] theorem dilationMobiusCoefficient_zero (h : ℕ) : dilationMobiusCoefficient h 0 = 0 := by
  simp [dilationMobiusCoefficient]

theorem dilationMobiusCoefficient_sum (h M : ℕ) (hh : 0 < h) :
    (∑ n ∈ Finset.Icc 1 M, dilationMobiusCoefficient h n) = dilationMobiusKernel h M := by
  simp only [dilationMobiusCoefficient, Finset.sum_add_distrib]
  rw [positive_dilation_sum M h hh]
  rfl

theorem mobiusReciprocalCoefficient_abs_le (n : ℕ) :
    |mobiusReciprocalCoefficient n| ≤ 1 / (n : ℝ) := by
  unfold mobiusReciprocalCoefficient
  rw [abs_div, abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n)]
  apply div_le_div_of_nonneg_right _ (show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n)
  exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))

theorem dilationMobiusCoefficient_abs_le (h n : ℕ) (hh : 0 < h) (hn : 0 < n) :
    |dilationMobiusCoefficient h n| ≤ ((h : ℝ) + 1) / (n : ℝ) := by
  have hshift : |if h ∣ n then mobiusReciprocalCoefficient (n / h) else 0| ≤
      (h : ℝ) / (n : ℝ) := by
    by_cases hdvd : h ∣ n
    · rw [if_pos hdvd]
      have hq : 0 < n / h := by
        have hhn : h ≤ n := Nat.le_of_dvd hn hdvd
        have ht : 1 ≤ n / h := (Nat.le_div_iff_mul_le hh).mpr (by simpa using hhn)
        omega
      have hhR : (h : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hh
      have hqR : ((n / h : ℕ) : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hq
      have hnR : (n : ℝ) = ((n / h : ℕ) : ℝ) * (h : ℝ) := by
        exact_mod_cast (Nat.div_mul_cancel hdvd).symm
      calc
        _ ≤ 1 / ((n / h : ℕ) : ℝ) := mobiusReciprocalCoefficient_abs_le _
        _ = (h : ℝ) / (n : ℝ) := by rw [hnR]; field_simp [hhR, hqR]
    · rw [if_neg hdvd, abs_zero]
      positivity
  calc
    |dilationMobiusCoefficient h n| ≤ |mobiusReciprocalCoefficient n| +
        |if h ∣ n then mobiusReciprocalCoefficient (n / h) else 0| := abs_add_le _ _
    _ ≤ 1 / (n : ℝ) + (h : ℝ) / (n : ℝ) :=
      add_le_add (mobiusReciprocalCoefficient_abs_le n) hshift
    _ = ((h : ℝ) + 1) / (n : ℝ) := by ring

theorem dilationMobiusKernel_tendsto_zero (h : ℕ) (hh : 0 < h) :
    Tendsto (dilationMobiusKernel h) atTop (𝓝 0) := by
  have ht : Tendsto (fun M : ℕ => M / h) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop (b * h)] with M hM
    exact (Nat.le_div_iff_mul_le hh).mpr hM
  change Tendsto (fun M => mobiusReciprocalSum M + mobiusReciprocalSum (M / h)) atTop (𝓝 0)
  simpa only [Function.comp_def, zero_add] using
    mobiusReciprocalSum_tendsto_zero.add (mobiusReciprocalSum_tendsto_zero.comp ht)

theorem dilationMobiusKernel_at_dilated_quotient (h N k : ℕ) (hh : 0 < h) :
    dilationMobiusKernel h (h * N / k) =
      mobiusReciprocalSum (h * N / k) + mobiusReciprocalSum (N / k) := by
  have hdiv : h * N / h = N := by
    apply Nat.eq_of_mul_eq_mul_left hh
    have hdvd : h ∣ h * N := ⟨N, rfl⟩
    simpa only [Nat.mul_comm] using Nat.div_mul_cancel hdvd
  have he : (h * N / k) / h = N / k := by
    calc
      (h * N / k) / h = (h * N / h) / k := by
        simp only [Nat.div_div_eq_div_mul, Nat.mul_comm k h]
      _ = N / k := by rw [hdiv]
  simp only [dilationMobiusKernel, he]

/-- The exact finite square expansion; no signed cross term is dropped. -/
theorem dilationMobiusCoefficient_square_sum (h M : ℕ) (hh : 0 < h) :
    (∑ n ∈ Finset.Icc 1 M, (dilationMobiusCoefficient h n) ^ 2) =
      (∑ n ∈ Finset.Icc 1 M, (mobiusReciprocalCoefficient n) ^ 2) +
      (∑ d ∈ Finset.Icc 1 (M / h), (mobiusReciprocalCoefficient d) ^ 2) +
      2 * ∑ d ∈ Finset.Icc 1 (M / h),
        mobiusReciprocalCoefficient (h * d) * mobiusReciprocalCoefficient d := by
  have he (n : ℕ) : (dilationMobiusCoefficient h n) ^ 2 =
      (mobiusReciprocalCoefficient n) ^ 2 +
      (if h ∣ n then (mobiusReciprocalCoefficient (n / h)) ^ 2 else 0) +
      2 * (if h ∣ n then mobiusReciprocalCoefficient (h * (n / h)) *
        mobiusReciprocalCoefficient (n / h) else 0) := by
    by_cases hdvd : h ∣ n
    · have hmul : h * (n / h) = n := by
        simpa only [Nat.mul_comm] using Nat.div_mul_cancel hdvd
      simp only [dilationMobiusCoefficient, if_pos hdvd, hmul]
      ring
    · simp [dilationMobiusCoefficient, hdvd]
  simp_rw [he]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    positive_dilation_sum M h hh (fun d => (mobiusReciprocalCoefficient d) ^ 2),
    positive_dilation_sum M h hh
      (fun d => mobiusReciprocalCoefficient (h * d) * mobiusReciprocalCoefficient d)]

/-- The mixed coefficient term has the precise factor `1/h`. -/
theorem dilationMobiusCoefficient_mixed (h d : ℕ) :
    mobiusReciprocalCoefficient (h * d) * mobiusReciprocalCoefficient d =
      (1 / (h : ℝ)) *
        ((ArithmeticFunction.moebius d : ℝ) * (ArithmeticFunction.moebius (h * d) : ℝ) /
          (d : ℝ) ^ 2) := by
  simp only [mobiusReciprocalCoefficient, Nat.cast_mul, div_eq_mul_inv, mul_inv_rev]
  ring

end RiemannResearch.RH.Pareto
