import RiemannResearch.RH.NymanReturnKernel
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Exact cumulative conductor coefficients and their positive kernel

Source: the user-provided Nyman–Weil continuation, coefficient beta_n(k).
The finite sum is evaluated by counting the positive multiples of n. This
provides the actual positive integrable kernel used by the broad return family.
-/

open scoped BigOperators
namespace RiemannResearch.RH

theorem sum_nymanConductorBeta_Icc (n M : ℕ) :
    (∑ k ∈ Finset.Icc 0 M, nymanConductorBeta n k) =
      (M : ℝ) / n - (M / n : ℕ) := by
  have hremove :
      (∑ k ∈ Finset.Icc 0 M, nymanConductorBeta n k) =
        ∑ k ∈ Finset.Ioc 0 M, nymanConductorBeta n k := by
    symm
    apply Finset.sum_subset
    · exact Finset.Ioc_subset_Icc_self
    · intro k hk hnot
      have hk0 : k = 0 := by
        simp only [Finset.mem_Icc, Finset.mem_Ioc, not_and] at hk hnot
        omega
      simp [hk0]
  rw [hremove]
  have hterms : (∑ k ∈ Finset.Ioc 0 M, nymanConductorBeta n k) =
      ∑ k ∈ Finset.Ioc 0 M, (1 / (n : ℝ) - if n ∣ k then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact nymanConductorBeta_apply (Nat.ne_of_gt (Finset.mem_Ioc.mp hk).1)
  rw [hterms]
  rw [Finset.sum_sub_distrib]
  have hc : (∑ k ∈ Finset.Ioc 0 M, if n ∣ k then (1 : ℝ) else 0) =
      (M / n : ℕ) := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one,
      Nat.Ioc_filter_dvd_card_eq_div]
  rw [hc]
  simp [Nat.card_Ioc, div_eq_mul_inv]

theorem nymanCumulativeBeta_eq (n : ℕ) (x : ℝ) :
    nymanCumulativeBeta n x =
      (⌊x⌋₊ : ℝ) / n - (⌊x⌋₊ / n : ℕ) :=
  sum_nymanConductorBeta_Icc n ⌊x⌋₊

theorem nymanCumulativeBeta_eq_mod {n : ℕ} (hn : 0 < n) (x : ℝ) :
    nymanCumulativeBeta n x = (⌊x⌋₊ % n : ℕ) / (n : ℝ) := by
  rw [nymanCumulativeBeta_eq]
  have he : ((⌊x⌋₊ % n : ℕ) : ℝ) + (n : ℝ) * ((⌊x⌋₊ / n : ℕ) : ℝ) =
      (⌊x⌋₊ : ℝ) := by exact_mod_cast Nat.mod_add_div ⌊x⌋₊ n
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  field_simp
  nlinarith

theorem nymanCumulativeBeta_nonneg {n : ℕ} (hn : 0 < n) (x : ℝ) :
    0 ≤ nymanCumulativeBeta n x := by
  rw [nymanCumulativeBeta_eq_mod hn]
  positivity

theorem nymanCumulativeBeta_lt_one {n : ℕ} (hn : 0 < n) (x : ℝ) :
    nymanCumulativeBeta n x < 1 := by
  rw [nymanCumulativeBeta_eq_mod hn]
  have hp : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  exact (div_lt_one hp).mpr (by exact_mod_cast Nat.mod_lt ⌊x⌋₊ hn)

theorem nymanReturnKernel_nonneg {n : ℕ} (hn : 0 < n) (t : ℝ) :
    0 ≤ nymanReturnKernel n t :=
  mul_nonneg (Real.exp_nonneg _) (nymanCumulativeBeta_nonneg hn _)

theorem nymanReturnKernel_le_exp {n : ℕ} (hn : 0 < n) (t : ℝ) :
    nymanReturnKernel n t ≤ Real.exp (-t / 2) := by
  exact mul_le_of_le_one_right (Real.exp_nonneg _)
    (le_of_lt (nymanCumulativeBeta_lt_one hn _))

theorem nymanReturnKernel_eq_zero_of_neg (n : ℕ) {t : ℝ} (ht : t < 0) :
    nymanReturnKernel n t = 0 := by
  have hexp : Real.exp t < 1 := Real.exp_lt_one_iff.mpr ht
  have hfloor : ⌊Real.exp t⌋₊ = 0 := Nat.floor_eq_zero.mpr hexp
  simp [nymanReturnKernel, nymanCumulativeBeta_eq, hfloor]

theorem nymanReturnKernel_pos {n : ℕ} (hn : 2 ≤ n) {t : ℝ}
    (ht : 0 ≤ t) (ht2 : t < Real.log 2) :
    0 < nymanReturnKernel n t := by
  have hexp0 : 1 ≤ Real.exp t := Real.one_le_exp_iff.mpr ht
  have hexp2 : Real.exp t < 2 := (Real.lt_log_iff_exp_lt (by norm_num)).mp ht2
  have hfloor : ⌊Real.exp t⌋₊ = 1 := by
    apply (Nat.floor_eq_iff (by positivity : 0 ≤ Real.exp t)).mpr
    refine ⟨?_, ?_⟩
    · simpa only [Nat.cast_one] using hexp0
    · convert hexp2 using 1 <;> first | rfl | norm_num
  have hdiv : 1 / n = (0 : ℕ) := Nat.div_eq_of_lt (by omega)
  rw [nymanReturnKernel, nymanCumulativeBeta_eq, hfloor, hdiv]
  simp only [Nat.cast_one, Nat.cast_zero, sub_zero]
  exact mul_pos (Real.exp_pos _) (one_div_pos.mpr (by exact_mod_cast (show 0 < n by omega)))

end RiemannResearch.RH
