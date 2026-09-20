import RiemannResearch.RH.IntegerDPPClosure
import RiemannResearch.RH.ParetoMellinDilation

/-!
# Exact Mellin obstruction for the first-site vacancy

Source: RH_DPP_Proof_Attempt_and_Explicit_Zero_Hole_Obstruction_2026-09-20.md,
Sections 4 and 8. These are consequences of a hypothetical right-half-plane
zero of the actual Riemann zeta function. They do not assert that such a zero
exists, nor do they exclude the resulting positive vacancy.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto.IntegerDPP
open CoefficientStabilization
open CoefficientStabilization.TailCapacity
open RiemannResearch.Analysis.ExhaustiveWalk

/-- The actual Mellin transform of the point target, derived from dilation. -/
theorem firstPoint_mellin (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    paretoMellin (paretoPointHilbert 0) s = (1 - (2 : ℂ) ^ (-s)) / s := by
  rw [firstPoint_eq_dilation_difference]
  change paretoMellinContinuous s hs
    (hilbertOne - (1 / 2 : ℝ) • hilbertDilation 2 (by omega) hilbertOne) = _
  rw [map_sub, map_smul]
  change paretoMellin hilbertOne s - (1 / 2 : ℝ) •
    paretoMellin (hilbertDilation 2 (by omega) hilbertOne) s = _
  rw [paretoMellin_dilation, paretoMellin_one s hs]
  norm_num only [Complex.real_smul, Complex.ofReal_div]
  change (1 / s : ℂ) - (1 / 2 : ℂ) * ((2 : ℂ) ^ (1 - s) * (1 / s)) = _
  rw [show (1 : ℂ) - s = 1 + (-s) by ring,
    Complex.cpow_add 1 (-s) (by norm_num : (2 : ℂ) ≠ 0), Complex.cpow_one]
  ring

theorem firstPoint_mellin_ne_zero (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    paretoMellin (paretoPointHilbert 0) s ≠ 0 := by
  have hs0 : s ≠ 0 := by intro he; norm_num [he] at hs
  have hn : ‖(2 : ℂ) ^ (-s)‖ < 1 := by
    change ‖((2 : ℝ) : ℂ) ^ (-s)‖ < 1
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2)]
    simp only [Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  rw [firstPoint_mellin s hs]
  apply div_ne_zero _ hs0
  intro hz
  have he : (2 : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp hz).symm
  rw [he, norm_one] at hn
  exact (lt_irrefl (1 : ℝ)) hn

/-- The exact deterministic lower bound forced by one Mellin zero. -/
def mellinVacancyFloor (s : ℂ) : ℝ :=
  2 * (2 * s.re - 1) * ‖paretoMellin (paretoPointHilbert 0) s‖ ^ 2

theorem mellinVacancyFloor_pos (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    0 < mellinVacancyFloor s := by
  have hp := sq_pos_of_pos (norm_pos_iff.mpr (firstPoint_mellin_ne_zero s hs))
  unfold mellinVacancyFloor
  exact mul_pos (mul_pos (by norm_num) (by linarith)) hp

theorem mellinVacancyFloor_eq (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    mellinVacancyFloor s =
      2 * (2 * s.re - 1) * ‖1 - (2 : ℂ) ^ (-s)‖ ^ 2 / ‖s‖ ^ 2 := by
  rw [mellinVacancyFloor, firstPoint_mellin s hs, norm_div, div_pow]
  ring

theorem mellinVacancyFloor_le_limitingVacancy
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) : mellinVacancyFloor s ≤ limitingVacancy := by
  have h := closedSpace_mellin_distance_sq_lower_bound s hs hs1 hz
    (paretoPointHilbert 0) (closedSpace.starProjection (paretoPointHilbert 0))
    (closedSpace.starProjection_apply_mem _)
  unfold mellinVacancyFloor limitingVacancy limitingError
  nlinarith

theorem mellinVacancyFloor_le_vacancy
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) (n : ℕ) : mellinVacancyFloor s ≤ vacancy n :=
  (mellinVacancyFloor_le_limitingVacancy s hs hs1 hz).trans
    (limitingVacancy_le_vacancy n)

/-- A positive vacancy floor bounds the actual full-tail Gram capacity. -/
theorem capacity_bound_of_vacancy_floor {δ : ℝ} (hδ : 0 < δ)
    (hfloor : ∀ n, δ ≤ vacancy n) (n : ℕ) :
    tailCapacity n + 2 ≤ 2 / δ := by
  have hc : 0 < tailCapacity n + 2 := by linarith [tailCapacity_nonneg n]
  have h := hfloor n
  rw [vacancy_eq_capacity] at h
  have hm := (le_div_iff₀ hc).mp h
  apply (le_div_iff₀ hδ).mpr
  nlinarith

/-- Persistent positive vacancy makes the actual hazard series summable. -/
theorem hazard_summable_of_vacancy_floor {δ : ℝ} (hδ : 0 < δ)
    (hfloor : ∀ n, δ ≤ vacancy n) : Summable hazard := by
  by_contra hn
  have ht := vacancy_tendsto_zero_iff_hazard_not_summable.mpr hn
  have hlim : δ ≤ 0 := ge_of_tendsto ht (Eventually.of_forall hfloor)
  linarith

theorem hazard_tsum_bound_of_vacancy_floor {δ : ℝ} (hδ : 0 < δ)
    (hfloor : ∀ n, δ ≤ vacancy n) :
    (∑' n, hazard n) ≤ -Real.log δ := by
  have hs := hazard_summable_of_vacancy_floor hδ hfloor
  apply le_of_tendsto hs.hasSum.tendsto_sum_nat
  apply Eventually.of_forall
  intro n
  exact (hazard_sum_le_log_vacancy n).trans
    (neg_le_neg (Real.log_le_log hδ (hfloor n)))

theorem capacity_bound_of_zeta_zero
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) (n : ℕ) :
    tailCapacity n + 2 ≤ 2 / mellinVacancyFloor s :=
  capacity_bound_of_vacancy_floor (mellinVacancyFloor_pos s hs)
    (mellinVacancyFloor_le_vacancy s hs hs1 hz) n

theorem hazard_summable_of_zeta_zero
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) : Summable hazard :=
  hazard_summable_of_vacancy_floor (mellinVacancyFloor_pos s hs)
    (mellinVacancyFloor_le_vacancy s hs hs1 hz)

theorem hazard_tsum_bound_of_zeta_zero
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) :
    (∑' n, hazard n) ≤ -Real.log (mellinVacancyFloor s) :=
  hazard_tsum_bound_of_vacancy_floor (mellinVacancyFloor_pos s hs)
    (mellinVacancyFloor_le_vacancy s hs hs1 hz)

theorem hazard_summable_of_not_RH (h : ¬ RiemannHypothesis) : Summable hazard :=
  hazard_summable_of_vacancy_floor (limitingVacancy_pos_of_not_RH h)
    limitingVacancy_le_vacancy

end RiemannResearch.RH.Pareto.IntegerDPP
