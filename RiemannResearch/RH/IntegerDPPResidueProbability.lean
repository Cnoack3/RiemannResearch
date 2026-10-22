import RiemannResearch.RH.IntegerDPPHistoricalTargets
import RiemannResearch.RH.IntegerDPPArithmeticExclusion
import RiemannResearch.RH.ResidueGramModeIdentities
import RiemannResearch.RH.ParetoPeriodicRegrouping
/-!
# Exact occupation probability of the shrinking first residue class

Source: user-provided DPP / q_N calculation, 21 September 2026.
The probabilistic bridge uses the already checked arithmetic pair exclusion
and countable additivity: the class contains at most one occupied site.
All Gram entries and progression weights retain their complete infinite tails.
The statements are unconditional exact finite-rank identities; no limiting
saturation or Riemann Hypothesis assertion is assumed or proved.
-/

open MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace RiemannResearch.RH.Pareto.IntegerDPP
open CoefficientStabilization CoefficientStabilization.TailCapacity
open HistoricalTargets

theorem first_progression_occupation_exact (N L : ℕ) (hL0 : 0 < L)
    (hL : ∀ d : Fin N, d.val + 2 ∣ L) :
    residueClassOccupationProbability N L =
      progressionWeight L 1 * fullCapacity N := by
  let E : ℕ → Set (ℕ → Bool) := fun k => {x | x (L * k) = true}
  have hres (k : ℕ) (d : Fin N) :
      (L * k + 1) % (d.val + 2) = (0 + 1) % (d.val + 2) := by
    have hd : d.val + 2 ∣ L * k := dvd_mul_of_dvd_left (hL d) k
    simp [Nat.add_mod, Nat.mod_eq_zero_of_dvd hd]
  have hm (k : ℕ) : MeasurableSet (E k) := by
    exact (measurable_pi_apply (L * k) :
      Measurable (fun x : ℕ → Bool => x (L * k))) (measurableSet_singleton true)
  have hd : Pairwise (fun i j => AEDisjoint (integerLaw N) (E i) (E j)) := by
    intro i j hij
    change (integerLaw N) (E i ∩ E j) = 0
    apply (measureReal_eq_zero_iff).mp
    exact integerLaw_pair_exclusion N (L * i) (L * j)
      (fun hh => hij (Nat.mul_left_cancel hL0 hh))
      (fun d => (hres i d).trans (hres j d).symm)
  have hu : {x : ℕ → Bool | ∃ k : ℕ, x (L * k) = true} = ⋃ k, E k := by
    ext x
    simp [E]
  have hk0 : integerKernel N 0 0 = fullCapacity N / 2 := by
    have hv := vacancy_eq_fullCapacity N
    rw [vacancy_eq_kernel_complement] at hv
    linarith
  have hk (k : ℕ) :
      (integerLaw N).real (E k) = paretoWeight (L * k) * fullCapacity N := by
    have h := integerKernel_weighted_diagonal_residue_congr N (L * k) 0 (hres k)
    rw [hk0] at h
    rw [show paretoWeight 0 = (1 / 2 : ℝ) by norm_num [paretoWeight]] at h
    have he : (integerLaw N).real (E k) = integerKernel N (L * k) (L * k) :=
      (integerLaw_isDPP N).occupation (L * k)
    rw [he]
    linarith
  unfold residueClassOccupationProbability
  rw [hu]
  change ((integerLaw N) (⋃ k, E k)).toReal = _
  rw [measure_iUnion₀ hd (fun k => (hm k).nullMeasurableSet),
    ENNReal.tsum_toReal_eq (fun k => measure_ne_top (integerLaw N) (E k))]
  change (∑' k, (integerLaw N).real (E k)) = _
  simp_rw [hk]
  rw [tsum_mul_right]
  congr 1
  unfold progressionWeight
  apply tsum_congr
  intro k
  simp only [paretoWeight, positiveWeight, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  ring

/-- The lcm of conductors 2,...,N+1, with the empty lcm equal to 1. -/
def residueModulus : ℕ → ℕ
  | 0 => 1
  | N + 1 => Nat.lcm (residueModulus N) (N + 2)

theorem residueModulus_pos (N : ℕ) : 0 < residueModulus N := by
  induction N with
  | zero => norm_num [residueModulus]
  | succ N ih => exact Nat.lcm_pos ih (by omega)

theorem conductor_dvd_residueModulus (N k : ℕ) (hk : k < N) :
    k + 2 ∣ residueModulus N := by
  induction N with
  | zero => omega
  | succ N ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | rfl
    · exact (ih h).trans (Nat.dvd_lcm_left _ _)
    · exact Nat.dvd_lcm_right _ _

/-- The actual first residue-class occupation probability at rank N. -/
def qN (N : ℕ) : ℝ := residueClassOccupationProbability N (residueModulus N)

theorem qN_eq_fullCapacity (N : ℕ) :
    qN N = progressionWeight (residueModulus N) 1 * fullCapacity N :=
  first_progression_occupation_exact N (residueModulus N) (residueModulus_pos N)
    (fun d => conductor_dvd_residueModulus N d.val d.isLt)

theorem qN_eq_inverseGram (N : ℕ) :
    qN N = progressionWeight (residueModulus N) 1 *
      dotProduct (reciprocalSource N) ((fullGram N)⁻¹.mulVec (reciprocalSource N)) := by
  rw [qN_eq_fullCapacity, fullCapacity_eq_inverseGram]

theorem qN_eq_mode_sum (N : ℕ) :
    qN N = progressionWeight (residueModulus N) 1 *
      ∑ j ∈ Finset.range N, (anchoredEvaluationCLM 1 (residueMode j))^2 := by
  rw [qN_eq_fullCapacity, fullCapacity_eq_mode_evaluation_sum]
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun j => (anchoredEvaluationCLM 1 (residueMode j))^2) N

theorem qN_eq_determinant_ratio (N : ℕ) :
    qN N = 1 -
      (fullGram N - progressionWeight (residueModulus N) 1 •
        Matrix.vecMulVec (reciprocalSource N) (reciprocalSource N)).det /
          (fullGram N).det := by
  have h := headDeterminant_eq N (2 * progressionWeight (residueModulus N) 1)
  unfold headDeterminant at h
  rw [show 2 * progressionWeight (residueModulus N) 1 / 2 =
    progressionWeight (residueModulus N) 1 by ring] at h
  rw [qN_eq_fullCapacity]
  linarith

theorem qN_succ (N : ℕ) :
    qN (N + 1) =
      progressionWeight (residueModulus (N + 1)) 1 /
        progressionWeight (residueModulus N) 1 * qN N +
      progressionWeight (residueModulus (N + 1)) 1 *
        (anchoredEvaluationCLM 1 (residueMode N))^2 := by
  have hw : progressionWeight (residueModulus N) 1 ≠ 0 :=
    ne_of_gt (progressionWeight_pos _ _ (residueModulus_pos N) (by omega))
  rw [qN_eq_mode_sum (N + 1), qN_eq_mode_sum N, Finset.sum_range_succ]
  field_simp


end RiemannResearch.RH.Pareto.IntegerDPP
