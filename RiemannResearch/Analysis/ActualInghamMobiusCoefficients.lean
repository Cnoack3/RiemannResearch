/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualInghamRightMoment
import Mathlib.NumberTheory.LSeries.Convolution

/-!
# The actual divisor coefficients of the moving right-line error

Chourasiya and Simonič, Section 4, Lemma 6 of
<https://arxiv.org/html/2507.15184v2>, identify the arithmetic quantity entering
the sharp right-edge moment. The convolution below preserves the signed
truncated Möbius sum. Its terms through the cutoff give only the constant one.
-/

noncomputable section
open scoped BigOperators
open Complex

namespace RiemannResearch.Analysis.InghamMollifier
open DirichletMeanSquare

/-- Coefficient of ζ times the finite Möbius polynomial, before removing its constant. -/
def truncatedMobiusDivisorSum (X n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, if d ≤ X then (ArithmeticFunction.moebius d : ℝ) else 0

theorem truncatedMobiusDivisorSum_of_le {X n : ℕ} (hn : n ≤ X) :
    truncatedMobiusDivisorSum X n = if n = 1 then 1 else 0 := by
  have he : truncatedMobiusDivisorSum X n = ∑ d ∈ n.divisors,
      (ArithmeticFunction.moebius d : ℝ) := by
    apply Finset.sum_congr rfl
    intro d hd
    obtain ⟨hdiv, hn0⟩ := Nat.mem_divisors.mp hd
    exact if_pos ((Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdiv).trans hn)
  rw [he]
  have hm := congrArg (fun f : ArithmeticFunction ℤ => f n)
    ArithmeticFunction.moebius_mul_coe_zeta
  change (ArithmeticFunction.moebius * (ArithmeticFunction.zeta : ArithmeticFunction ℤ)) n =
    (1 : ArithmeticFunction ℤ) n at hm
  rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at hm
  split_ifs at * <;> exact_mod_cast hm

private def truncatedMobius (X n : ℕ) : ℂ :=
  if n ≤ X then (ArithmeticFunction.moebius n : ℂ) else 0

private theorem truncatedMobius_term_zero (X : ℕ) (s : ℂ) (n : ℕ)
    (hn : n ∉ Finset.range (X + 1)) :
    LSeries.term (truncatedMobius X) s n = 0 := by
  have h : ¬ n ≤ X := by simpa [Nat.lt_succ_iff] using hn
  simp [LSeries.term, truncatedMobius, h]

private theorem truncatedMobius_summable (X : ℕ) (s : ℂ) :
    LSeriesSummable (truncatedMobius X) s :=
  summable_of_ne_finset_zero (s := Finset.range (X + 1)) (truncatedMobius_term_zero X s)

private theorem truncatedMobius_LSeries (X : ℕ) (s : ℂ) :
    LSeries (truncatedMobius X) s = mollifier X s := by
  rw [mollifier_eq_sum_range, LSeries, tsum_eq_sum (truncatedMobius_term_zero X s)]
  apply Finset.sum_congr rfl
  intro n hn
  have h : n ≤ X := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
  simp [LSeries.term, truncatedMobius, h]

private theorem truncatedMobius_convolution (X : ℕ) :
    LSeries.convolution (truncatedMobius X) (1 : ℕ → ℂ) =
      fun n => (truncatedMobiusDivisorSum X n : ℂ) := by
  funext n
  rw [LSeries.convolution_def]
  simp only [Pi.one_apply, mul_one]
  rw [Nat.sum_divisorsAntidiagonal (fun d _ => truncatedMobius X d)]
  simp only [truncatedMobiusDivisorSum, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro d _
  by_cases h : d ≤ X <;> simp [truncatedMobius, h]

theorem truncatedMobiusDivisorSum_lseries {s : ℂ} (hs : 1 < s.re) (X : ℕ) :
    LSeries (fun n => (truncatedMobiusDivisorSum X n : ℂ)) s =
      riemannZeta s * mollifier X s := by
  rw [← truncatedMobius_convolution,
    LSeries_convolution' (truncatedMobius_summable X s) (LSeriesSummable_one_iff.mpr hs),
    truncatedMobius_LSeries, LSeries_one_eq_riemannZeta hs, mul_comm]

theorem truncatedMobiusDivisorSum_lseriesSummable {s : ℂ} (hs : 1 < s.re) (X : ℕ) :
    LSeriesSummable (fun n => (truncatedMobiusDivisorSum X n : ℂ)) s := by
  rw [← truncatedMobius_convolution]
  exact (truncatedMobius_summable X s).convolution (LSeriesSummable_one_iff.mpr hs)

/-- The actual error is the full signed divisor-coefficient tail beyond the cutoff. -/
theorem mollifier_error_eq_divisor_dirichletTail {σ : ℝ} (hσ : 1 < σ)
    {X : ℕ} (hX : 1 ≤ X) (t : ℝ) :
    riemannZeta ((σ : ℂ) + I * t) * mollifier X ((σ : ℂ) + I * t) - 1 =
      dirichletTail (fun n => (truncatedMobiusDivisorSum X n : ℂ)) σ X t := by
  let s : ℂ := (σ : ℂ) + I * t
  let a : ℕ → ℂ := fun n => (truncatedMobiusDivisorSum X n : ℂ)
  have hs : 1 < s.re := by simpa [s] using hσ
  have hsum : Summable (LSeries.term a s) := truncatedMobiusDivisorSum_lseriesSummable hs X
  have hsplit := hsum.sum_add_tsum_nat_add (X + 1)
  have hhead : ∑ n ∈ Finset.range (X + 1), LSeries.term a s n = 1 := by
    rw [Finset.sum_eq_single 1]
    · simp [a, truncatedMobiusDivisorSum_of_le hX]
    · intro n hn hne
      have hnX := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
      simp [LSeries.term, a, truncatedMobiusDivisorSum_of_le hnX, hne]
    · intro hne
      exact (hne (Finset.mem_range.mpr (by omega))).elim
  change _ + _ = LSeries a s at hsplit
  rw [hhead, truncatedMobiusDivisorSum_lseries hs] at hsplit
  have htail : (∑' k : ℕ, LSeries.term a s (k + (X + 1))) = dirichletTail a σ X t := by
    unfold dirichletTail
    apply tsum_congr
    intro k
    rw [← Nat.add_assoc]
    have hn : k + X + 1 ≠ 0 := by omega
    rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg,
      Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn), ← Complex.natCast_log]
    unfold tailTerm tailCoefficient ZeroOrdinate.phase
    rw [mul_assoc, ← Complex.exp_add]
    dsimp [s]
    congr 2
    push_cast
    ring
  rw [htail] at hsplit
  change riemannZeta s * mollifier X s - 1 = dirichletTail a σ X t
  rw [← hsplit]
  ring

/-- The signed double sum over the least common multiple of the two divisors. -/
def truncatedMobiusLCMForm (X : ℕ) (τ : ℝ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 X, ∑ e ∈ Finset.Icc 1 X,
    (ArithmeticFunction.moebius d : ℝ) * (ArithmeticFunction.moebius e : ℝ) *
      (Nat.lcm d e : ℝ) ^ (-τ)

theorem truncatedMobiusDivisorSum_eq_dvd_sum (X : ℕ) {n : ℕ} (hn : n ≠ 0) :
    truncatedMobiusDivisorSum X n = ∑ d ∈ Finset.Icc 1 X,
      if d ∣ n then (ArithmeticFunction.moebius d : ℝ) else 0 := by
  unfold truncatedMobiusDivisorSum
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  congr 1
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hdn, _⟩, hdX⟩
    refine ⟨⟨?_, hdX⟩, hdn⟩
    exact Nat.pos_of_dvd_of_pos hdn (Nat.pos_of_ne_zero hn)
  · exact fun ⟨h, hdn⟩ => ⟨⟨hdn, hn⟩, h.2⟩

/-- A per-cutoff majorant for use in absolute convergence on every line to the right of one. -/
theorem norm_truncatedMobiusDivisorSum_le (X n : ℕ) :
    ‖(truncatedMobiusDivisorSum X n : ℂ)‖ ≤ (X : ℝ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [truncatedMobiusDivisorSum]
  rw [Complex.norm_real, truncatedMobiusDivisorSum_eq_dvd_sum X hn]
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 X,
        ‖if d ∣ n then (ArithmeticFunction.moebius d : ℝ) else 0‖ := norm_sum_le _ _
    _ ≤ ∑ _d ∈ Finset.Icc 1 X, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d _
      by_cases hd : d ∣ n
      · rw [if_pos hd, Real.norm_eq_abs]
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
      · simp [hd]
    _ = _ := by simp

private theorem sum_real_zeta_weight {τ : ℝ} (hτ : 1 < τ) :
    (∑' n : ℕ, (n : ℝ) ^ (-τ)) = ‖riemannZeta (τ : ℂ)‖ := by
  rw [norm_riemannZeta_real_eq_tsum_norm hτ]
  apply tsum_congr
  intro n
  rw [LSeries.norm_term_eq]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Real.zero_rpow (by linarith : -τ ≠ 0)]
  · simp [hn, Real.rpow_neg (Nat.cast_nonneg n), one_div]

private theorem sum_dvd_real_zeta_weight {τ : ℝ} (hτ : 1 < τ) {d : ℕ} (hd : 0 < d) :
    (∑' n : ℕ, if d ∣ n then (n : ℝ) ^ (-τ) else 0) =
      (d : ℝ) ^ (-τ) * ‖riemannZeta (τ : ℂ)‖ := by
  let f : ℕ → ℝ := fun n => if d ∣ n then (n : ℝ) ^ (-τ) else 0
  have hg : Function.Injective (fun k : ℕ => d * k) := fun _ _ h => Nat.mul_left_cancel hd h
  have hsup : Function.support f ⊆ Set.range (fun k : ℕ => d * k) := by
    intro n h
    change (if d ∣ n then (n : ℝ) ^ (-τ) else 0) ≠ 0 at h
    by_cases hn : d ∣ n
    · obtain ⟨k, hk⟩ := hn
      exact ⟨k, hk.symm⟩
    · simp [hn] at h
  change (∑' n, f n) = _
  rw [← hg.tsum_eq hsup]
  calc
    _ = ∑' k : ℕ, (d : ℝ) ^ (-τ) * (k : ℝ) ^ (-τ) := by
      apply tsum_congr
      intro k
      simp [f, Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg d) (Nat.cast_nonneg k)]
    _ = _ := by
      rw [(Real.summable_nat_rpow.mpr (by linarith : -τ < -1)).tsum_mul_left,
        sum_real_zeta_weight hτ]

private def divisorPairWeight (τ : ℝ) (d e n : ℕ) : ℝ :=
  (ArithmeticFunction.moebius d : ℝ) * (ArithmeticFunction.moebius e : ℝ) *
    (if Nat.lcm d e ∣ n then (n : ℝ) ^ (-τ) else 0)

private theorem summable_dvd_real_zeta_weight {τ : ℝ} (hτ : 1 < τ) (d : ℕ) :
    Summable (fun n : ℕ => if d ∣ n then (n : ℝ) ^ (-τ) else 0) := by
  have h := (Real.summable_nat_rpow.mpr (by linarith : -τ < -1)).indicator
    {n : ℕ | d ∣ n}
  apply h.congr
  intro n
  by_cases hd : d ∣ n <;> simp [Set.indicator, hd]

private theorem divisorPairWeight_summable {τ : ℝ} (hτ : 1 < τ) (d e : ℕ) :
    Summable (divisorPairWeight τ d e) :=
  (summable_dvd_real_zeta_weight hτ (Nat.lcm d e)).mul_left _

private theorem divisorPairWeight_energy (X n : ℕ) {τ : ℝ} (hτ : 1 < τ) :
    (truncatedMobiusDivisorSum X n) ^ 2 * (n : ℝ) ^ (-τ) =
    ∑ d ∈ Finset.Icc 1 X, ∑ e ∈ Finset.Icc 1 X, divisorPairWeight τ d e n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [divisorPairWeight, Real.zero_rpow (by linarith : -τ ≠ 0)]
  rw [truncatedMobiusDivisorSum_eq_dvd_sum X hn, pow_two]
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro e _
  by_cases hd : d ∣ n <;> by_cases he : e ∣ n <;>
    simp [divisorPairWeight, Nat.lcm_dvd_iff, hd, he, mul_comm]

/-- The complete squared Dirichlet coefficients have an exact signed LCM evaluation. -/
theorem truncatedMobiusDivisorSum_energy_eq_lcm (X : ℕ) {τ : ℝ} (hτ : 1 < τ) :
    (∑' n : ℕ, (truncatedMobiusDivisorSum X n) ^ 2 * (n : ℝ) ^ (-τ)) =
      ‖riemannZeta (τ : ℂ)‖ * truncatedMobiusLCMForm X τ := by
  let D := Finset.Icc 1 X
  have hrow (d : ℕ) : Summable (fun n => ∑ e ∈ D, divisorPairWeight τ d e n) :=
    summable_sum (fun e _ => divisorPairWeight_summable hτ d e)
  calc
    _ = ∑' n : ℕ, ∑ d ∈ D, ∑ e ∈ D, divisorPairWeight τ d e n :=
      tsum_congr (fun n => divisorPairWeight_energy X n hτ)
    _ = ∑ d ∈ D, ∑ e ∈ D, ∑' n : ℕ, divisorPairWeight τ d e n := by
      rw [Summable.tsum_finsetSum (fun d (_ : d ∈ D) => hrow d)]
      apply Finset.sum_congr rfl
      intro d _
      exact Summable.tsum_finsetSum (fun e _ => divisorPairWeight_summable hτ d e)
    _ = _ := by
      unfold truncatedMobiusLCMForm
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      have hd0 : 0 < d := (Finset.mem_Icc.mp hd).1
      have he0 : 0 < e := (Finset.mem_Icc.mp he).1
      have ht := summable_dvd_real_zeta_weight hτ (Nat.lcm d e)
      unfold divisorPairWeight
      rw [ht.tsum_mul_left, sum_dvd_real_zeta_weight hτ (Nat.lcm_pos hd0 he0)]
      ring

theorem summable_truncatedMobiusDivisorSum_energy (X : ℕ) {τ : ℝ} (hτ : 1 < τ) :
    Summable (fun n : ℕ => (truncatedMobiusDivisorSum X n) ^ 2 * (n : ℝ) ^ (-τ)) := by
  refine (summable_sum (s := Finset.Icc 1 X) (fun d _ =>
    summable_sum (s := Finset.Icc 1 X) (fun e _ => divisorPairWeight_summable hτ d e))).congr ?_
  intro n
  exact (divisorPairWeight_energy X n hτ).symm

theorem summable_truncatedMobiusDivisorSum_tail_energy (X : ℕ) {τ : ℝ} (hτ : 1 < τ) :
    Summable (fun k : ℕ => (truncatedMobiusDivisorSum X (k + X + 1)) ^ 2 *
      ((k + X + 1 : ℕ) : ℝ) ^ (-τ)) := by
  simpa only [Nat.add_assoc] using
    (summable_nat_add_iff (X + 1)).mpr (summable_truncatedMobiusDivisorSum_energy X hτ)

/-- Subtracting the constant removes precisely one from the full squared-coefficient sum. -/
theorem truncatedMobiusDivisorSum_tail_energy_eq_lcm {X : ℕ} (hX : 1 ≤ X)
    {τ : ℝ} (hτ : 1 < τ) :
    (∑' k : ℕ, (truncatedMobiusDivisorSum X (k + X + 1)) ^ 2 *
      ((k + X + 1 : ℕ) : ℝ) ^ (-τ)) =
      ‖riemannZeta (τ : ℂ)‖ * truncatedMobiusLCMForm X τ - 1 := by
  let a : ℕ → ℝ := fun n => (truncatedMobiusDivisorSum X n) ^ 2 * (n : ℝ) ^ (-τ)
  have hsum : Summable a := summable_truncatedMobiusDivisorSum_energy X hτ
  have hsplit := hsum.sum_add_tsum_nat_add (X + 1)
  have hhead : ∑ n ∈ Finset.range (X + 1), a n = 1 := by
    rw [Finset.sum_eq_single 1]
    · simp [a, truncatedMobiusDivisorSum_of_le hX]
    · intro n hn hne
      simp [a, truncatedMobiusDivisorSum_of_le (Nat.le_of_lt_succ (Finset.mem_range.mp hn)), hne]
    · intro hne
      exact (hne (Finset.mem_range.mpr (by omega))).elim
  rw [hhead] at hsplit
  change 1 + _ = ∑' n : ℕ, (truncatedMobiusDivisorSum X n)^2 * (n : ℝ)^(-τ) at hsplit
  rw [truncatedMobiusDivisorSum_energy_eq_lcm X hτ] at hsplit
  rw [← hsplit]
  simp [a, Nat.add_assoc]

end RiemannResearch.Analysis.InghamMollifier
