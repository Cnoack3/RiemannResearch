import RiemannResearch.RH.IntegerDPPVacancyCertificates
import RiemannResearch.RH.IntegerDPPVacancyDuality
import RiemannResearch.RH.IntegerDPPWeightedDeterminant

/-!
# Exact comparison of finite trials, dual certificates, and vacancy cutoffs

Source: user-requested comparison at commit 0330eb1553c2c843446b2434fedbe1b741277dee
(2026-09-30). These are deductions from the existing exact Gram, projection,
and certificate identities. No provider of the equivalent RH-strength
conditions is constructed. Every physical tail and square remainder is retained.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto.IntegerDPP
open CoefficientStabilization CoefficientStabilization.TailCapacity HistoricalTargets
open RiemannResearch.Analysis.FiniteGramCapacity

/-- The physical prefix beyond the first site; M further sites are observed. -/
def offsiteWeightedVacancyPrefix (N M : ℕ) : ℝ :=
  ∑ i ∈ Finset.range M, weightedVacancyTerm N (i + 1)

theorem offsiteWeightedVacancyPrefix_nonneg (N M : ℕ) :
    0 ≤ offsiteWeightedVacancyPrefix N M :=
  Finset.sum_nonneg (fun i _ => (weightedVacancyTerm_bounds N (i + 1)).1)

/-- Complete finite physical split, with first-site vacancy and tail separated. -/
theorem weightedVacancyPrefix_first_site_split (N M : ℕ) :
    weightedVacancyPrefix N (M + 1) =
      vacancy N / 2 + offsiteWeightedVacancyPrefix N M := by
  have h0 : weightedVacancyTerm N 0 = vacancy N / 2 := by
    simp [weightedVacancyTerm, vacancy_eq_kernel_complement, paretoWeight]
    ring
  unfold weightedVacancyPrefix offsiteWeightedVacancyPrefix
  rw [Finset.sum_range_succ', h0]
  ring

/-- Exact Cauchy--Schwarz slack, retaining the full Hilbert square. -/
theorem finiteTrial_capacity_gap_eq_square (n : ℕ) (c : Fin n → ℝ)
    (hE : 0 < finiteTrialEnergy n c) :
    tailCapacity n * finiteTrialEnergy n c - finiteTrialSource n c ^ 2 =
      finiteTrialEnergy n c *
        ‖tailMinimum n - (finiteTrialSource n c / finiteTrialEnergy n c) •
          Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) c‖ ^ 2 := by
  have hi := inner_synthesis_minimumVector
    (finiteTailAtom_independent n) (reciprocalSource n) c
  change inner ℝ (Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) c)
    (tailMinimum n) = finiteTrialSource n c at hi
  have hi' : inner ℝ (tailMinimum n)
      (Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) c) =
      finiteTrialSource n c := by
    rw [real_inner_comm]
    exact hi
  rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    inner_smul_right, hi', tailMinimum_norm_sq]
  change tailCapacity n * finiteTrialEnergy n c - finiteTrialSource n c ^ 2 =
    finiteTrialEnergy n c * (tailCapacity n -
      2 * (finiteTrialSource n c / finiteTrialEnergy n c * finiteTrialSource n c) +
      (finiteTrialSource n c / finiteTrialEnergy n c) ^ 2 * finiteTrialEnergy n c)
  field_simp [ne_of_gt hE]
  ring

/-- The exact excess of the trial's upper bound over half the actual vacancy. -/
def finiteTrialVacancySlack (n : ℕ) (c : Fin n → ℝ) : ℝ :=
  (tailCapacity n * finiteTrialEnergy n c - finiteTrialSource n c ^ 2) /
    ((tailCapacity n + 2) *
      (finiteTrialSource n c ^ 2 + 2 * finiteTrialEnergy n c))

theorem finiteTrialVacancySlack_nonneg (n : ℕ) (c : Fin n → ℝ)
    (hE : 0 < finiteTrialEnergy n c) : 0 ≤ finiteTrialVacancySlack n c := by
  unfold finiteTrialVacancySlack
  rw [finiteTrial_capacity_gap_eq_square n c hE]
  exact div_nonneg (mul_nonneg hE.le (sq_nonneg _))
    (mul_nonneg (by linarith [tailCapacity_nonneg n])
      (by nlinarith [sq_nonneg (finiteTrialSource n c)]))

/-- Complete identity before replacing a trial's first-site bound by an estimate. -/
theorem weightedVacancyCutoff_eq_trial_split (n M : ℕ) (c : Fin n → ℝ)
    (hE : 0 < finiteTrialEnergy n c) :
    weightedVacancyPrefix n (M + 1) + 1 / (((M + 1 : ℕ) : ℝ) + 1) =
      finiteTrialEnergy n c /
          (finiteTrialSource n c ^ 2 + 2 * finiteTrialEnergy n c) -
        finiteTrialVacancySlack n c + offsiteWeightedVacancyPrefix n M +
        1 / (((M + 1 : ℕ) : ℝ) + 1) := by
  have hd : finiteTrialSource n c ^ 2 + 2 * finiteTrialEnergy n c ≠ 0 := by
    nlinarith [sq_nonneg (finiteTrialSource n c)]
  have hc : tailCapacity n + 2 ≠ 0 := by linarith [tailCapacity_nonneg n]
  rw [weightedVacancyPrefix_first_site_split, vacancy_eq_capacity,
    finiteTrialVacancySlack]
  field_simp [hd, hc]
  ring

/-- A trial controls the first site at every later rank. Other sites remain explicit. -/
theorem weightedVacancyCutoff_le_trial_offsite (n N M : ℕ) (hnN : n ≤ N)
    (c : Fin n → ℝ) (hE : 0 < finiteTrialEnergy n c) :
    weightedVacancyPrefix N (M + 1) + 1 / (((M + 1 : ℕ) : ℝ) + 1) ≤
      finiteTrialEnergy n c /
          (finiteTrialSource n c ^ 2 + 2 * finiteTrialEnergy n c) +
        offsiteWeightedVacancyPrefix N M + 1 / (((M + 1 : ℕ) : ℝ) + 1) := by
  rw [weightedVacancyPrefix_first_site_split]
  have hv := (vacancy_antitone hnN).trans (vacancy_le_finiteTrial_bound n c hE)
  rw [mul_div_assoc] at hv
  linarith

/-- Necessary and sufficient finite-stage budget; the square slack is retained. -/
theorem weightedVacancyCutoff_lt_iff_trial_budget (n M : ℕ) (c : Fin n → ℝ)
    (hE : 0 < finiteTrialEnergy n c) (ε : ℝ) :
    weightedVacancyPrefix n (M + 1) + 1 / (((M + 1 : ℕ) : ℝ) + 1) < ε ↔
      offsiteWeightedVacancyPrefix n M + 1 / (((M + 1 : ℕ) : ℝ) + 1) <
        ε - finiteTrialEnergy n c /
          (finiteTrialSource n c ^ 2 + 2 * finiteTrialEnergy n c) +
            finiteTrialVacancySlack n c := by
  rw [weightedVacancyCutoff_eq_trial_split n M c hE]
  constructor <;> intro h <;> linarith

/-- This is an equivalence of provider propositions, not a construction of either. -/
theorem weightedVacancyCutoffCertificates_iff_finiteTrial_certificates :
    WeightedVacancyCutoffCertificates ↔
      ∀ B : ℝ, ∃ (n : ℕ) (c : Fin n → ℝ),
        0 < finiteTrialEnergy n c ∧
          B * finiteTrialEnergy n c < finiteTrialSource n c ^ 2 :=
  weightedVacancyCutoffCertificates_iff_top.trans
    (limitingVacancy_zero_iff_top.symm.trans
      limitingVacancy_zero_iff_finiteTrial_certificates)

theorem weightedVacancyCutoffCertificates_iff_no_tailCertificate :
    WeightedVacancyCutoffCertificates ↔
      ¬ ∃ z : ThresholdHilbert, IsResidueTailCertificate z :=
  weightedVacancyCutoffCertificates_iff_top.trans
    (limitingVacancy_zero_iff_top.symm.trans limitingVacancy_zero_iff_no_certificate)

/-- A genuine dual certificate obstructs every finite physical cutoff.
The exact physical tail allowance is included even in this lower bound. -/
theorem tailCertificate_weightedVacancyCutoff_lower (z : ThresholdHilbert)
    (hz : IsResidueTailCertificate z) (N M : ℕ) :
    1 / (‖z‖ ^ 2 + 2) + 1 / (((M + 1 : ℕ) : ℝ) + 1) ≤
      weightedVacancyPrefix N (M + 1) + 1 / (((M + 1 : ℕ) : ℝ) + 1) := by
  rw [weightedVacancyPrefix_first_site_split]
  have hv := (certificate_vacancy_lower_bound z hz).trans
    (limitingVacancy_le_vacancy N)
  have ho := offsiteWeightedVacancyPrefix_nonneg N M
  simp only [div_eq_mul_inv] at hv ⊢
  linarith

/-- The minimum-energy dual certificate obstructs the limiting weighted mass. -/
theorem tailCertificate_weightedVacancyMass_lower (z : ThresholdHilbert)
    (hz : IsResidueTailCertificate z) :
    1 / (‖z‖ ^ 2 + 2) ≤ weightedVacancyMass := by
  have hv := certificate_vacancy_lower_bound z hz
  have hm := limitingWeightedVacancyMass_first_site_lower
  simp only [div_eq_mul_inv] at hv hm ⊢
  linarith

/-- Damping detects the same missing provider for every window containing site zero. -/
theorem weightedVacancyCutoffCertificates_iff_dampedWindow_minimum
    (m : ℕ) (e : Fin m ↪ ℕ) (a : Fin m → ℝ)
    (ha : ∀ i, 0 < a i ∧ a i < 1) (i₀ : Fin m) (hi₀ : e i₀ = 0) :
    WeightedVacancyCutoffCertificates ↔
      dampedWindowDeterminant m e a =
        RiemannResearch.Probability.Occupancy.benchmark a :=
  weightedVacancyCutoffCertificates_iff_top.trans
    (limitingVacancy_zero_iff_top.symm.trans
      (dampedWindowDeterminant_minimum_iff_zero_vacancy m e a ha i₀ hi₀).symm)

/-- The damped infinite-prefix limit also has the same certificate criterion. -/
theorem weightedVacancyCutoffCertificates_iff_dampedPrefixLimit :
    WeightedVacancyCutoffCertificates ↔
      dampedPrefixLimit = paretoProductBenchmark :=
  weightedVacancyCutoffCertificates_iff_top.trans
    (weightedVacancyMass_zero_iff_top.symm.trans
      weightedVacancyMass_zero_iff_dampedPrefixLimit_eq_benchmark)

/-- The quantitative damped estimate transfers dual obstruction, not smallness. -/
theorem tailCertificate_dampedPrefixLimit_lower (z : ThresholdHilbert)
    (hz : IsResidueTailCertificate z) :
    paretoProductBenchmark / (‖z‖ ^ 2 + 2) ≤
      dampedPrefixLimit - paretoProductBenchmark := by
  have h := mul_le_mul_of_nonneg_left
    (tailCertificate_weightedVacancyMass_lower z hz) paretoProductBenchmark_pos.le
  have h' : paretoProductBenchmark / (‖z‖ ^ 2 + 2) ≤
      paretoProductBenchmark * weightedVacancyMass := by
    simpa only [mul_one_div] using h
  exact h'.trans dampedPrefixLimit_defect_bounds.1


/-- In the obstruction case, every finite cutoff has a complete canonical split.
The finite-to-closed projection square is retained as well as every offsite term. -/
theorem weightedVacancyCutoff_eq_canonical_split (h : 0 < limitingVacancy)
    (N M : ℕ) :
    weightedVacancyPrefix N (M + 1) + 1 / (((M + 1 : ℕ) : ℝ) + 1) =
      1 / (‖canonicalTailCertificate‖ ^ 2 + 2) +
        ‖projectedPoint - (finiteSpace N).starProjection (paretoPointHilbert 0)‖ ^ 2 +
        offsiteWeightedVacancyPrefix N M + 1 / (((M + 1 : ℕ) : ℝ) + 1) := by
  have hw := RiemannResearch.Analysis.ExhaustiveWalk.walkError_eq_limitingError_add
    residueAtom id (paretoPointHilbert 0) N
  have hs : vacancy N = limitingVacancy +
      2 * ‖projectedPoint - (finiteSpace N).starProjection (paretoPointHilbert 0)‖ ^ 2 := by
    change 2 * RiemannResearch.Analysis.ExhaustiveWalk.walkError
        residueAtom id (paretoPointHilbert 0) N =
      2 * RiemannResearch.Analysis.ExhaustiveWalk.limitingError
        residueAtom (paretoPointHilbert 0) +
      2 * ‖closedSpace.starProjection (paretoPointHilbert 0) -
        (finiteSpace N).starProjection (paretoPointHilbert 0)‖ ^ 2
    rw [hw]
    ring
  have hc := canonicalTailCertificate_attains_vacancy_bound h
  rw [weightedVacancyPrefix_first_site_split]
  simp only [div_eq_mul_inv] at hc ⊢
  linarith


/-- A finite observation certificate has an energy remainder that cannot be
discarded when converting its energy into a cutoff value. -/
theorem finiteTailCertificate_weightedVacancyCutoff_exact (n M : ℕ)
    (z : ThresholdHilbert)
    (hz : ∀ i : Fin n, inner ℝ (tailAtom i.val) z = reciprocalSource n i) :
    weightedVacancyPrefix n (M + 1) + 1 / (((M + 1 : ℕ) : ℝ) + 1) =
      1 / (‖z‖ ^ 2 - ‖z - tailMinimum n‖ ^ 2 + 2) +
        offsiteWeightedVacancyPrefix n M + 1 / (((M + 1 : ℕ) : ℝ) + 1) := by
  have he := finiteTailCertificate_energy_completion n z hz
  have hc : ‖z‖ ^ 2 - ‖z - tailMinimum n‖ ^ 2 + 2 = tailCapacity n + 2 := by
    linarith
  rw [hc, weightedVacancyPrefix_first_site_split, vacancy_eq_capacity]
  ring

end RiemannResearch.RH.Pareto.IntegerDPP
