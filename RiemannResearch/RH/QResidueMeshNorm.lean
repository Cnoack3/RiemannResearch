import RiemannResearch.RH.StepCorrectionConstant
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# The sharp leading constant in the complete Q residue norm

The unit cells are those in C. Noack's 13 October 2026 CRT note. They give
a stronger upper bound after retaining the missing first mesh point.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QResidueMeshNorm
open StepCorrectionNorm ZetaTwoProbability ZetaTwoHilbert ArithmeticCumulative

private def kernel (d m : ℕ) (x : ℝ) : ℝ := (x / ((m : ℝ) * d + x)) ^ 2

private def cell (d m : ℕ) : ℝ := ∑ j ∈ Finset.range d, kernel d m j

private theorem cell_zero (d : ℕ) (hd : 0 < d) : cell d 0 = (d : ℝ) - 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hd)
  have h (j : ℕ) : (j : ℝ) + 1 ≠ 0 := by positivity
  simp [cell, kernel, Finset.sum_range_succ', Nat.cast_succ, h]

private theorem cell_sum (d : ℕ) (hd : 0 < d) :
    zetaTwo * (d : ℝ) ^ 2 * ‖qResidue d‖ ^ 2 =
      (d : ℝ) - 1 + ∑' m : ℕ, cell d (m + 1) := by
  have : NeZero d := ⟨hd.ne'⟩
  let f (n : ℕ) : ℝ := ((n % d : ℕ) / (n : ℝ)) ^ 2
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hZ := zetaTwo_pos
  have hstart : zetaTwo * (d : ℝ) ^ 2 * ‖qResidue d‖ ^ 2 = ∑' n, f n := by
    rw [qNorm_weighted_sq, ← tsum_mul_left]
    apply tsum_congr
    intro n
    simp only [qSequence_qResidue, positiveQWeight, residueFraction, f]
    by_cases hn : (n : ℝ) = 0
    · simp [hn]
    · field_simp [hdR, hn, hZ.ne']

  let e := (Nat.divModEquiv d).symm
  have hs : Summable f := by
    have h := (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))).mul_left ((d : ℝ)^2)
    apply Summable.of_nonneg_of_le (fun n => sq_nonneg _) _ h
    intro n
    have hk : ((n % d : ℕ) : ℝ) ≤ d := by exact_mod_cast (Nat.mod_lt n hd).le
    simp only [div_pow, mul_one_div]
    exact div_le_div_of_nonneg_right ((sq_le_sq₀ (by positivity) (by positivity)).mpr hk) (sq_nonneg _)
  have hprod : Summable (fun p : ℕ × Fin d => f (e p)) := e.summable_iff.mpr hs
  have hblock (m : ℕ) : (∑' i : Fin d, f (e (m,i))) = cell d m := by
    rw [tsum_fintype, cell, ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j _
    simp [f, e, kernel, Nat.mod_eq_of_lt j.isLt, Nat.cast_add, Nat.cast_mul]
  have hc : Summable (cell d) := hprod.prod.congr hblock
  rw [hstart, ← e.tsum_eq f, hprod.tsum_prod, tsum_congr hblock, hc.tsum_eq_zero_add, cell_zero d hd]

private theorem cell_inequalities (d m : ℕ) (hd : 0 < d) :
    cell d (m + 1) ≤ (d : ℝ) * rawResidueCellEnergy m ∧
      (d : ℝ) * rawResidueCellEnergy m ≤ cell d (m + 1) + 1 / ((m : ℝ) + 2)^2 := by
  let a : ℝ := (m : ℝ) + 1
  have ha : 0 < a := by dsimp [a]; positivity
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hmono : MonotoneOn (kernel d (m + 1)) (Set.Icc 0 (0 + (d : ℝ))) := by
    intro x hx y hy hxy
    have hx0 := hx.1
    have hy0 := hy.1
    simp only [kernel, Nat.cast_add, Nat.cast_one]
    change (x / (a * d + x))^2 ≤ (y / (a * d + y))^2
    apply (sq_le_sq₀ (by positivity) (by positivity)).mpr
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hxy (mul_pos ha hdR).le]
  have hI : (∫ x in (0 : ℝ)..(d : ℝ), kernel d (m + 1) x) = (d : ℝ) * rawResidueCellEnergy m := by
    let F (x : ℝ) := (x - a)^2 / x^2
    have he (x : ℝ) : kernel d (m + 1) x = F (x / d + a) := by
      simp only [kernel, F, Nat.cast_add, Nat.cast_one, add_sub_cancel_right, a, div_pow]
      rw [show x / d + ((m : ℝ) + 1) = (((m : ℝ) + 1) * d + x) / d by field_simp; ring]
      simp [div_pow, div_div_div_cancel_right₀, hdR.ne']
    simp_rw [he]
    rw [intervalIntegral.integral_comp_div_add F hdR.ne' a]
    simp only [zero_div, zero_add, div_self hdR.ne', smul_eq_mul]
    congr 1
    simpa only [F, a, show (1 : ℝ) + ((m : ℝ) + 1) = (m : ℝ) + 2 by ring] using rawResidueCellEnergy_integral m
  have hl := hmono.sum_le_integral
  have hu := hmono.integral_le_sum
  simp only [zero_add] at hl hu
  rw [hI] at hl hu
  refine ⟨hl, hu.trans_eq ?_⟩
  have hshift := Finset.sum_range_succ' (fun j : ℕ => kernel d (m + 1) (j : ℝ)) d
  rw [Finset.sum_range_succ] at hshift
  have hzero : kernel d (m + 1) 0 = 0 := by simp [kernel]
  have hend : kernel d (m + 1) d = 1 / ((m : ℝ) + 2)^2 := by
    simp only [kernel, Nat.cast_add, Nat.cast_one, div_pow]
    field_simp
    ring
  simpa only [Nat.cast_zero, hzero, add_zero, hend, cell] using hshift.symm

/-- Exact quadrature defect, in the scale where the omitted first mesh point contributes one. -/
def defect (d : ℕ) : ℝ :=
  (d : ℝ) * (Real.log (2 * Real.pi) - Real.eulerMascheroniConstant) -
    zetaTwo * (d : ℝ)^2 * ‖qResidue d‖^2

theorem defect_bounds (d : ℕ) (hd : 0 < d) : 1 ≤ defect d ∧ defect d ≤ zetaTwo := by
  have hR := rawResidueCellEnergy_summable.mul_left (d : ℝ)
  have hC : Summable (fun m => cell d (m + 1)) := by
    apply Summable.of_nonneg_of_le (fun m => Finset.sum_nonneg (fun j _ => sq_nonneg _))
      (fun m => (cell_inequalities d m hd).1) hR
  have hT : Summable (fun m : ℕ => 1 / ((m : ℝ) + 2)^2) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using ((summable_nat_add_iff 2).mpr
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))))
  have htail : (∑' m : ℕ, 1 / ((m : ℝ) + 2)^2) = zetaTwo - 1 := by
    have h := (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))).sum_add_tsum_nat_add 2
    rw [← zetaTwo_eq_nat_sum] at h
    norm_num [Finset.sum_range_succ, Nat.cast_add] at h
    simp only [one_div]
    linarith
  have h₁ := hC.tsum_le_tsum (fun m => (cell_inequalities d m hd).1) hR
  have h₂ := hR.tsum_le_tsum (fun m => (cell_inequalities d m hd).2) (hC.add hT)
  rw [hC.tsum_add hT, htail, tsum_mul_left] at h₂
  rw [tsum_mul_left] at h₁
  rw [defect, cell_sum d hd, ← residueEnergy_eq_log_two_pi_sub_gamma, residueEnergy]
  constructor <;> nlinarith

/-- Both sides have a second-order correction, including -1/(zeta(2) d²) on the upper side. -/
theorem norm_bounds (d : ℕ) (hd : 0 < d) :
    let c := Real.log (2 * Real.pi) - Real.eulerMascheroniConstant
    c / (zetaTwo * d) - 1 / (d : ℝ)^2 ≤ ‖qResidue d‖^2 ∧
      ‖qResidue d‖^2 ≤ c / (zetaTwo * d) - 1 / (zetaTwo * (d : ℝ)^2) := by
  dsimp only
  have ⟨hl, hu⟩ := defect_bounds d hd
  unfold defect at hl hu
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hZ := zetaTwo_pos
  constructor
  · field_simp
    nlinarith only [hu]
  · field_simp
    nlinarith only [hl]

/-- All finite coordinate traces retain the sum of their exact mesh defects. -/
theorem residue_trace_exact (s : Finset ℕ) (hp : ∀ d ∈ s, 0 < d) :
    (∑ d ∈ s, ‖qResidue d‖^2) + (∑ d ∈ s, defect d / (zetaTwo * (d : ℝ)^2)) =
      (Real.log (2 * Real.pi) - Real.eulerMascheroniConstant) / zetaTwo *
      ∑ d ∈ s, 1 / (d : ℝ) := by
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have h : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hp d hd).ne'
  unfold defect
  field_simp [h, zetaTwo_pos.ne']
  ring

theorem total_defect_bounds (s : Finset ℕ) (hp : ∀ d ∈ s, 0 < d) :
    (∑ d ∈ s, 1 / (zetaTwo * (d : ℝ)^2)) ≤
      (∑ d ∈ s, defect d / (zetaTwo * (d : ℝ)^2)) ∧
    (∑ d ∈ s, defect d / (zetaTwo * (d : ℝ)^2)) ≤ ∑ d ∈ s, 1 / (d : ℝ)^2 := by
  constructor <;> apply Finset.sum_le_sum <;> intro d hd
  · exact div_le_div_of_nonneg_right (defect_bounds d (hp d hd)).1
      (mul_nonneg zetaTwo_pos.le (sq_nonneg _))
  · have h : (0 : ℝ) < d := by exact_mod_cast hp d hd
    rw [div_le_div_iff₀ (mul_pos zetaTwo_pos (sq_pos_of_pos h)) (sq_pos_of_pos h), one_mul]
    exact mul_le_mul_of_nonneg_right (defect_bounds d (hp d hd)).2 (sq_nonneg _)

/-- Uniform bounded remainder, independent of the chosen finite conductor dictionary. -/
theorem total_defect_le_zetaTwo (s : Finset ℕ) (hp : ∀ d ∈ s, 0 < d) :
    (∑ d ∈ s, defect d / (zetaTwo * (d : ℝ)^2)) ≤ zetaTwo := by
  apply (total_defect_bounds s hp).2.trans
  rw [zetaTwo_eq_nat_sum]
  exact Summable.sum_le_tsum s (fun d _ => by positivity)
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ)))

/-- Any asymptotic for the reciprocal divisor mass transfers to the actual residue Gram trace. -/
theorem residue_trace_asymptotic_of_mass (s : ℕ → Finset ℕ)
    (hp : ∀ n, ∀ d ∈ s n, 0 < d) (y : ℕ → ℝ) (hy : Filter.Tendsto y Filter.atTop Filter.atTop)
    {a : ℝ} (h : Filter.Tendsto (fun n => (∑ d ∈ s n, 1 / (d : ℝ)) / y n)
      Filter.atTop (nhds a)) :
    Filter.Tendsto (fun n => (∑ d ∈ s n, ‖qResidue d‖^2) / y n)
      Filter.atTop (nhds (((Real.log (2*Real.pi) - Real.eulerMascheroniConstant) / zetaTwo)*a)) := by
  let E (n : ℕ) := ∑ d ∈ s n, defect d / (zetaTwo * (d : ℝ)^2)
  have h0 (n : ℕ) : 0 ≤ E n := by
    apply Finset.sum_nonneg
    intro d hd
    exact div_nonneg (zero_le_one.trans (defect_bounds _ (hp n d hd)).1)
      (mul_nonneg zetaTwo_pos.le (sq_nonneg _))
  have he : Filter.Tendsto (fun n => E n / y n) Filter.atTop (nhds 0) := by
    apply squeeze_zero' _ _ (tendsto_const_nhds.div_atTop hy : Filter.Tendsto
      (fun n => zetaTwo / y n) Filter.atTop (nhds 0))
    · filter_upwards [hy.eventually_ge_atTop (0 : ℝ)] with n hn
      exact div_nonneg (h0 n) hn
    · filter_upwards [hy.eventually_ge_atTop (0 : ℝ)] with n hn
      exact div_le_div_of_nonneg_right (total_defect_le_zetaTwo _ (hp n)) hn
  have ht := (h.const_mul ((Real.log (2*Real.pi) - Real.eulerMascheroniConstant)/zetaTwo)).sub he
  rw [sub_zero] at ht
  apply ht.congr
  intro n
  have htrace := residue_trace_exact (s n) (hp n)
  change (∑ d ∈ s n, ‖qResidue d‖^2) + E n = _ at htrace
  change _ - E n / y n = _
  rw [← mul_div_assoc, ← sub_div, ← htrace, add_sub_cancel_right]

end RiemannResearch.RH.QResidueMeshNorm
