import RiemannResearch.RH.QResidueMeshNorm
import RiemannResearch.RH.QCarryScreenedBlock
import RiemannResearch.RH.QCRTPrimorialCarry
import RiemannResearch.RH.QSquarefreePrimePacket
import RiemannResearch.Analysis.ScreenedBlockGain
import RiemannResearch.Analysis.ResidualPrimeGain
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Arithmetic lower budgets for complete prime-first carry blocks

Source: Christian Noack, *Q CRT Carry Gram and Schur Matrices with Zeta Trace
Identities*, 13 October 2026. The squarefree closure implication is Bagchi,
Remark 8 (2006), DOI 10.1007/BF02829783. At cutoff n the incoming prime is n + 4.
Any finite selection of old divisors can be used at each prime. All scores,
traces and intermediate errors below refer to the actual Q projections.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QCRTCarrySourceBudget

open ZetaTwoHilbert QSquarefreePrimorialCofinality QSquarefreePrimePacket
open QCRTPrimorialCarry Pareto.SquarefreeStageExhaustion
open RiemannResearch.Analysis.ScreenedCarry

/-- The residual after adjoining the new prime, before its composite block. -/
def middleError (n : ℕ) : ℝ := ‖screen (primeBase n (n + 4)) qOne‖ ^ 2

/-- All multi-prime CRT representatives have this same screened direction. -/
def innovation (n : ℕ) (d : DivisorIndex n) : QHilbert :=
  -screen (primeBase n (n + 4)) (qResidue ((n + 4) * d.val))

def score (n : ℕ) (d : DivisorIndex n) : ℝ :=
  inner ℝ (innovation n d) (screen (primeBase n (n + 4)) qOne)

/-- Pair the middle residual directly with the unscreened incoming atom. -/
def rawPairing (n : ℕ) (d : DivisorIndex n) : ℝ :=
  inner ℝ (screen (primeBase n (n + 4)) qOne) (qResidue ((n + 4) * d.val))

theorem score_eq_neg_rawPairing (n : ℕ) (d : DivisorIndex n) :
    score n d = -rawPairing n d := by
  let V := primeBase n (n + 4)
  let x := qResidue ((n + 4) * d.val)
  have ho := Submodule.starProjection_inner_eq_zero qOne (V.starProjection x)
    (V.starProjection_apply_mem x)
  change inner ℝ (screen V qOne) (V.starProjection x) = 0 at ho
  change inner ℝ (-screen V x) (screen V qOne) = -inner ℝ (screen V qOne) x
  calc
    _ = -inner ℝ (screen V qOne) (screen V x) := by rw [inner_neg_left, real_inner_comm]
    _ = _ := by rw [screen_apply V x, inner_sub_right, ho, sub_zero]

def blockTrace (n : ℕ) (s : Finset (DivisorIndex n)) : ℝ :=
  ∑ d ∈ s, ‖innovation n d‖ ^ 2

def sourceMass (n : ℕ) (s : Finset (DivisorIndex n)) : ℝ :=
  ∑ d ∈ s, score n d ^ 2

private theorem primeBase_le_next (n : ℕ) (hp : (n + 4).Prime) :
    primeBase n (n + 4) ≤ primorialStage (n + 1) := by
  apply sup_le (primorialStage_mono (Nat.le_succ n)) (Submodule.span_le.mpr ?_)
  intro x hx
  rcases Set.mem_singleton_iff.mp hx with rfl
  apply residue_mem_primorialStage _ _ (by omega)
  rw [primorialPeriod_prime_step n hp]
  exact dvd_mul_right _ _

private theorem incoming_mem_next (n : ℕ) (hp : (n + 4).Prime) (d : DivisorIndex n) :
    qResidue ((n + 4) * d.val) ∈ primorialStage (n + 1) := by
  apply residue_mem_primorialStage _ _ (by have := d.property.2; nlinarith)
  rw [primorialPeriod_prime_step n hp]
  exact Nat.mul_dvd_mul_left _ (Nat.mem_divisors.mp d.property.1).1

theorem middle_error_bounds (n : ℕ) (hp : (n + 4).Prime) :
    primorialError (n + 1) ≤ middleError n ∧ middleError n ≤ primorialError n := by
  have h₁ := RiemannResearch.Analysis.ExhaustiveWalk.nested_projection_energy
    (primorialStage n) (primeBase n (n + 4)) (show primorialStage n ≤ _ from le_sup_left) qOne
  have h₂ := RiemannResearch.Analysis.ExhaustiveWalk.nested_projection_energy
    (primeBase n (n + 4)) (primorialStage (n + 1)) (primeBase_le_next n hp) qOne
  change primorialError n = middleError n + _ at h₁
  change middleError n = primorialError (n + 1) + _ at h₂
  exact ⟨by linarith [sq_nonneg ((‖(primorialStage (n + 1)).starProjection qOne -
    (primeBase n (n + 4)).starProjection qOne‖))],
    by linarith [sq_nonneg (‖(primeBase n (n + 4)).starProjection qOne -
    (primorialStage n).starProjection qOne‖)]⟩

theorem selected_scores_le_trace_mul_gain (n : ℕ) (hp : (n + 4).Prime)
    (s : Finset (DivisorIndex n)) :
    sourceMass n s ≤ blockTrace n s * (middleError n - primorialError (n + 1)) := by
  unfold sourceMass blockTrace
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro d _
  have h := screened_score_sq_le_nested_gain (primeBase n (n + 4))
    (primorialStage (n + 1)) (primeBase_le_next n hp) qOne
    (qResidue ((n + 4) * d.val)) (incoming_mem_next n hp d)
  simpa only [score, innovation, inner_neg_left, neg_sq, norm_neg, middleError,
    primorialError, primorialOptimizer, screen_apply] using h

/-- Capacity in the note is 1/error - 4. Its increments agree with the
repository's 1/error - 1 convention. The two terms retain the prime-only gain. -/
theorem capacity_split (n : ℕ) (hp : (n + 4).Prime) :
    primorialCapacity (n + 1) - primorialCapacity n =
      (1 / middleError n - 1 / primorialError n) +
      (middleError n - primorialError (n + 1)) /
        (middleError n * primorialError (n + 1)) := by
  have h := (primorialError_pos (n + 1)).trans_le (middle_error_bounds n hp).1
  unfold primorialCapacity
  field_simp [ne_of_gt h, ne_of_gt (primorialError_pos n), ne_of_gt (primorialError_pos (n + 1))]
  ring

/-- Actual trace-normalized carry score. Empty selections contribute zero. -/
def selectedBudget (n : ℕ) (s : Finset (DivisorIndex n)) : ℝ :=
  if (n + 4).Prime then sourceMass n s / (blockTrace n s * middleError n ^ 2) else 0

theorem selectedBudget_nonneg (n : ℕ) (s : Finset (DivisorIndex n)) :
    0 ≤ selectedBudget n s := by
  unfold selectedBudget sourceMass blockTrace
  split <;> positivity

theorem prime_gain_add_selectedBudget_le (n : ℕ) (hp : (n + 4).Prime)
    (s : Finset (DivisorIndex n)) :
    (1 / middleError n - 1 / primorialError n) + selectedBudget n s ≤
      primorialCapacity (n + 1) - primorialCapacity n := by
  have h := middle_error_bounds n hp
  have hf := primorialError_pos (n + 1)
  have he := hf.trans_le h.1
  have ht : 0 ≤ blockTrace n s := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hg : 0 ≤ middleError n - primorialError (n + 1) := sub_nonneg.mpr h.1
  rw [capacity_split n hp, selectedBudget, if_pos hp]
  apply add_le_add_right
  by_cases hz : blockTrace n s = 0
  · simp only [hz, zero_mul, div_zero]
    exact div_nonneg hg (mul_nonneg he.le hf.le)
  have ht' := lt_of_le_of_ne ht (Ne.symm hz)
  calc
    _ ≤ (middleError n - primorialError (n + 1)) / middleError n ^ 2 := by
      apply (div_le_div_iff₀ (mul_pos ht' (sq_pos_of_pos he)) (sq_pos_of_pos he)).mpr
      have hs := mul_le_mul_of_nonneg_right
        (selected_scores_le_trace_mul_gain n hp s) (sq_nonneg (middleError n))
      nlinarith only [hs]
    _ ≤ _ := div_le_div_of_nonneg_left hg (mul_pos he hf)
      (by simpa only [pow_two] using mul_le_mul_of_nonneg_left h.1 he.le)

theorem selectedBudget_le_cutoffGain (n : ℕ) (s : Finset (DivisorIndex n)) :
    selectedBudget n s ≤ cutoffGain n := by
  by_cases hp : (n + 4).Prime
  · have h := prime_gain_add_selectedBudget_le n hp s
    have he := (primorialError_pos (n + 1)).trans_le (middle_error_bounds n hp).1
    have hprime := one_div_le_one_div_of_le he (middle_error_bounds n hp).2
    rw [primorialCapacity_prime_step n hp] at h
    simp only [cutoffGain, if_pos hp]
    linarith
  · simp [selectedBudget, cutoffGain, hp]

theorem selectedBudget_sum_le_capacity (s : ∀ n, Finset (DivisorIndex n)) (N : ℕ) :
    primorialCapacity 0 + ∑ n ∈ Finset.range N, selectedBudget n (s n) ≤
      primorialCapacity N := by
  rw [primorialCapacity_eq_initial_add_sum N]
  exact add_le_add_right (Finset.sum_le_sum (fun n _ => selectedBudget_le_cutoffGain n (s n))) _

/-- Conditional research reduction. Only the selected arithmetic scores enter the premise. -/
theorem riemannHypothesis_of_selectedBudget_diverges (s : ∀ n, Finset (DivisorIndex n))
    (h : Tendsto (fun N => ∑ n ∈ Finset.range N, selectedBudget n (s n)) atTop atTop) :
    RiemannHypothesis :=
  riemannHypothesis_of_packetGain_sum_tendsto (tendsto_atTop_mono
    (fun _ => Finset.sum_le_sum (fun n _ => selectedBudget_le_cutoffGain n (s n))) h)

/-- Even infinitely many poor prime stages are allowed if their total deficit is summable. -/
theorem riemannHypothesis_of_prime_scores_with_defect
    (s : ∀ n, Finset (DivisorIndex n)) {c : ℝ} (hc : 0 < c) {loss : ℕ → ℝ}
    (hloss : Summable loss) (hpos : ∀ n, 0 ≤ loss n)
    (hlower : ∀ n, (n + 4).Prime →
      c / ((n + 4 : ℕ) : ℝ) ≤ selectedBudget n (s n) + loss n) : RiemannHypothesis := by
  apply riemannHypothesis_of_selectedBudget_diverges s
  by_contra h
  have hs := (summable_iff_not_tendsto_nat_atTop_of_nonneg
    (fun n => selectedBudget_nonneg n (s n))).mpr h
  exact RiemannResearch.Analysis.ResidualGain.not_summable_of_shifted_prime_lower 4 hc
    (fun n => add_nonneg (selectedBudget_nonneg n (s n)) (hpos n)) hlower (hs.add hloss)

/-- Under failure of RH the total selected budget is finite for every selection. -/
theorem summable_selectedBudget_of_not_RH (hn : ¬ RiemannHypothesis)
    (s : ∀ n, Finset (DivisorIndex n)) : Summable (fun n => selectedBudget n (s n)) :=
  (summable_iff_not_tendsto_nat_atTop_of_nonneg (fun n => selectedBudget_nonneg n (s n))).mpr
    (fun h => hn (riemannHypothesis_of_selectedBudget_diverges s h))

private def candidateBudgets (n : ℕ) : Finset ℝ :=
  insert 0 ((Finset.univ : Finset (DivisorIndex n)).image (fun d => selectedBudget n {d}))

/-- Maximum over the empty choice and every physical single-divisor score. -/
def bestBudget (n : ℕ) : ℝ :=
  (candidateBudgets n).max' (by exact ⟨0, Finset.mem_insert_self _ _⟩)

theorem bestBudget_nonneg (n : ℕ) : 0 ≤ bestBudget n :=
  Finset.le_max' _ _ (Finset.mem_insert_self _ _)

theorem singleton_le_best (n : ℕ) (d : DivisorIndex n) :
    selectedBudget n {d} ≤ bestBudget n := by
  apply Finset.le_max' (candidateBudgets n) (selectedBudget n {d})
  exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem
    (fun j : DivisorIndex n => selectedBudget n {j}) (Finset.mem_univ d))

theorem bestBudget_attained (n : ℕ) :
    ∃ s : Finset (DivisorIndex n), s.card ≤ 1 ∧ selectedBudget n s = bestBudget n := by
  classical
  have hx : bestBudget n ∈ candidateBudgets n := Finset.max'_mem _ _
  rcases Finset.mem_insert.mp hx with hz | hr
  · refine ⟨∅, by simp, ?_⟩
    simp [hz, selectedBudget, sourceMass, blockTrace]
  · obtain ⟨d, _, he⟩ := Finset.mem_image.mp hr
    exact ⟨{d}, by simp, he⟩

/-- Exact variance-weighted singleton formula, including empty and zero-variance subblocks. -/
theorem selectedBudget_weighted_singletons (n : ℕ) (hp : (n + 4).Prime)
    (s : Finset (DivisorIndex n)) :
    selectedBudget n s =
      (∑ d ∈ s, ‖innovation n d‖^2 * selectedBudget n {d}) / blockTrace n s := by
  have he := (primorialError_pos (n + 1)).trans_le (middle_error_bounds n hp).1
  have ht : (∑ d ∈ s, ‖innovation n d‖^2 * selectedBudget n {d}) =
      sourceMass n s / middleError n^2 := by
    rw [sourceMass, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro d _
    rw [selectedBudget, if_pos hp]
    simp only [sourceMass, blockTrace, Finset.sum_singleton]
    by_cases hv : innovation n d = 0
    · simp [score, hv]
    · have hn := (norm_pos_iff.mpr hv).ne'
      field_simp [hn, he.ne']
  rw [ht, selectedBudget, if_pos hp, div_div, mul_comm (middleError n ^ 2)]

/-- The trace ratio of a subblock is a variance-weighted average of singleton ratios. -/
theorem selectedBudget_le_best (n : ℕ) (s : Finset (DivisorIndex n)) :
    selectedBudget n s ≤ bestBudget n := by
  by_cases hp : (n + 4).Prime
  · rw [selectedBudget, if_pos hp]
    by_cases hz : blockTrace n s = 0
    · simpa only [hz, zero_mul, div_zero] using bestBudget_nonneg n
    have ht : 0 < blockTrace n s := lt_of_le_of_ne
      (show 0 ≤ blockTrace n s from Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Ne.symm hz)
    have he := (primorialError_pos (n + 1)).trans_le (middle_error_bounds n hp).1
    rw [div_le_iff₀ (mul_pos ht (sq_pos_of_pos he))]
    calc
      sourceMass n s ≤ ∑ d ∈ s, (bestBudget n * middleError n^2) * ‖innovation n d‖^2 := by
        apply Finset.sum_le_sum
        intro d _
        by_cases hv : innovation n d = 0
        · simp [score, hv]
        · have hd := singleton_le_best n d
          rw [selectedBudget, if_pos hp] at hd
          simp only [sourceMass, blockTrace, Finset.sum_singleton] at hd
          have hh := (div_le_iff₀ (mul_pos (sq_pos_of_pos (norm_pos_iff.mpr hv)) (sq_pos_of_pos he))).mp hd
          exact hh.trans_eq (by ring)
      _ = _ := by rw [← Finset.mul_sum]; unfold blockTrace; ring
  · simpa only [selectedBudget, if_neg hp] using bestBudget_nonneg n

theorem riemannHypothesis_of_best_singletons
    (h : Tendsto (fun N => ∑ n ∈ Finset.range N, bestBudget n) atTop atTop) : RiemannHypothesis := by
  choose s hs he using bestBudget_attained
  apply riemannHypothesis_of_selectedBudget_diverges s
  simpa only [he] using h

theorem divergent_selection_iff_best_singletons :
    (∃ s : ∀ n, Finset (DivisorIndex n),
      Tendsto (fun N => ∑ n ∈ Finset.range N, selectedBudget n (s n)) atTop atTop) ↔
      Tendsto (fun N => ∑ n ∈ Finset.range N, bestBudget n) atTop atTop := by
  constructor
  · rintro ⟨s, hs⟩
    exact tendsto_atTop_mono (fun N => Finset.sum_le_sum (fun n _ => selectedBudget_le_best n (s n))) hs
  · intro h
    choose s hs he using bestBudget_attained
    exact ⟨s, by simpa only [he] using h⟩

/-- The source test can be restricted to any set of stages with divergent reciprocal sum.
It needs no lower bound on the complementary primes. -/
theorem riemannHypothesis_of_singletons_on_good_stages (good : Set ℕ) [DecidablePred (· ∈ good)]
    {c : ℝ} (hc : 0 < c)
    (hrecip : ¬ Summable (fun n : ℕ => if n ∈ good then 1 / ((n + 4 : ℕ) : ℝ) else 0))
    (hgood : ∀ n ∈ good, c / ((n + 4 : ℕ) : ℝ) ≤ bestBudget n) : RiemannHypothesis := by
  apply riemannHypothesis_of_best_singletons
  by_contra hn
  have hb := (summable_iff_not_tendsto_nat_atTop_of_nonneg bestBudget_nonneg).mpr hn
  apply hrecip (Summable.of_nonneg_of_le _ _ (hb.mul_right (1/c)))
  · intro n
    split <;> positivity
  · intro n
    by_cases h : n ∈ good
    · rw [if_pos h, mul_one_div, le_div_iff₀ hc]
      exact (le_of_eq (by ring : (1 / ((n + 4 : ℕ) : ℝ)) * c = c / ((n + 4 : ℕ) : ℝ))).trans (hgood n h)
    · rw [if_neg h]
      exact mul_nonneg (bestBudget_nonneg n) (by positivity)

/-- Reciprocal mass of the selected old divisors. -/
def divisorMass (n : ℕ) (s : Finset (DivisorIndex n)) : ℝ :=
  ∑ d ∈ s, 1 / (d.val : ℝ)

/-- Each omitted term in the trace estimate has an explicit value. -/
theorem blockTrace_exact (n : ℕ) (s : Finset (DivisorIndex n)) :
    blockTrace n s + (∑ d ∈ s, ‖(primeBase n (n + 4)).starProjection
      (qResidue ((n + 4) * d.val))‖ ^ 2) +
      (∑ d ∈ s, QResidueMeshNorm.defect ((n + 4) * d.val) /
        (ZetaTwoProbability.zetaTwo * (((n + 4) * d.val : ℕ) : ℝ) ^ 2)) =
    (Real.log (2 * Real.pi) - Real.eulerMascheroniConstant) /
      (ZetaTwoProbability.zetaTwo * ((n + 4 : ℕ) : ℝ)) * divisorMass n s := by
  unfold blockTrace divisorMass
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  have he := QCarryScreenedBlock.screen_energy (primeBase n (n + 4))
    (qResidue ((n + 4) * d.val))
  change ‖screen _ _‖ ^ 2 = _ at he
  rw [innovation, norm_neg, he]
  have hd : (d.val : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := d.property.2; omega)
  have hp : (((n + 4 : ℕ) : ℝ)) ≠ 0 := by positivity
  unfold QResidueMeshNorm.defect
  simp only [Nat.cast_mul]
  field_simp [ZetaTwoProbability.zetaTwo_pos.ne', hd, hp]
  ring

theorem blockTrace_upper (n : ℕ) (s : Finset (DivisorIndex n)) :
    blockTrace n s ≤ (Real.log (2 * Real.pi) - Real.eulerMascheroniConstant) /
      (ZetaTwoProbability.zetaTwo * ((n + 4 : ℕ) : ℝ)) * divisorMass n s := by
  rw [← blockTrace_exact]
  have h₁ : 0 ≤ ∑ d ∈ s, ‖(primeBase n (n + 4)).starProjection
      (qResidue ((n + 4) * d.val))‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have h₂ : 0 ≤ ∑ d ∈ s, QResidueMeshNorm.defect ((n + 4) * d.val) /
      (ZetaTwoProbability.zetaTwo * (((n + 4) * d.val : ℕ) : ℝ) ^ 2) := by
    apply Finset.sum_nonneg
    intro d _
    have hd : 0 < (n + 4) * d.val := Nat.mul_pos (by omega) (by have := d.property.2; omega)
    exact div_nonneg (zero_le_one.trans (QResidueMeshNorm.defect_bounds _ hd).1)
      (mul_nonneg ZetaTwoProbability.zetaTwo_pos.le (sq_nonneg _))
  linarith

/-- Positivity of the constant in the upper estimate for the residue atom norms. -/
theorem cZero_pos : 0 < Real.log (2 * Real.pi) - Real.eulerMascheroniConstant := by
  rw [← StepCorrectionNorm.residueEnergy_eq_log_two_pi_sub_gamma, StepCorrectionNorm.residueEnergy]
  have ht : 0 ≤ ∑' m, StepCorrectionNorm.rawResidueCellEnergy m :=
    tsum_nonneg StepCorrectionNorm.rawResidueCellEnergy_nonneg
  linarith

/-- The paper's arithmetic budget, with the trace replaced by its Euler-product upper bound. -/
def arithmeticBudget (n : ℕ) (s : Finset (DivisorIndex n)) : ℝ :=
  if (n + 4).Prime then sourceMass n s /
    (((Real.log (2 * Real.pi) - Real.eulerMascheroniConstant) /
      (ZetaTwoProbability.zetaTwo * ((n + 4 : ℕ) : ℝ)) * divisorMass n s) * middleError n ^ 2)
  else 0

theorem arithmeticBudget_le_selected (n : ℕ) (s : Finset (DivisorIndex n)) :
    arithmeticBudget n s ≤ selectedBudget n s := by
  by_cases hp : (n + 4).Prime
  · rw [arithmeticBudget, selectedBudget, if_pos hp, if_pos hp]
    by_cases hz : sourceMass n s = 0
    · simp [hz]
    have ha : 0 < sourceMass n s := lt_of_le_of_ne (show 0 ≤ sourceMass n s from Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Ne.symm hz)
    have ht : 0 < blockTrace n s := by
      apply lt_of_le_of_ne (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      intro heq
      change 0 = blockTrace n s at heq
      have h := selected_scores_le_trace_mul_gain n hp s
      rw [← heq, zero_mul] at h
      exact ha.not_ge h
    have he := (primorialError_pos (n + 1)).trans_le (middle_error_bounds n hp).1
    exact div_le_div_of_nonneg_left ha.le (mul_pos ht (sq_pos_of_pos he))
      (mul_le_mul_of_nonneg_right (blockTrace_upper n s) (sq_nonneg _))
  · simp [arithmeticBudget, selectedBudget, hp]

theorem arithmeticBudget_sum_le_capacity (s : ∀ n, Finset (DivisorIndex n)) (N : ℕ) :
    primorialCapacity 0 + ∑ n ∈ Finset.range N, arithmeticBudget n (s n) ≤ primorialCapacity N :=
  (add_le_add_right (Finset.sum_le_sum (fun n _ => arithmeticBudget_le_selected n (s n))) _).trans
    (selectedBudget_sum_le_capacity s N)

theorem riemannHypothesis_of_arithmeticBudget_diverges (s : ∀ n, Finset (DivisorIndex n))
    (h : Tendsto (fun N => ∑ n ∈ Finset.range N, arithmeticBudget n (s n)) atTop atTop) :
    RiemannHypothesis :=
  riemannHypothesis_of_selectedBudget_diverges s (tendsto_atTop_mono
    (fun _ => Finset.sum_le_sum (fun n _ => arithmeticBudget_le_selected n (s n))) h)

private theorem source_floor_algebra {c z C p e b t a : ℝ} (hc : 0 < c) (hz : 0 < z)
    (hC : 0 < C) (hp : 0 < p) (he : 0 < e) (ht : 0 < t)
    (hu : t ≤ C / (z * p) * b) (hl : c * e ^ 2 * b / p ^ 2 ≤ a) :
    (c * z / C) / p ≤ a / (t * e ^ 2) := by
  rw [le_div_iff₀ (mul_pos ht (sq_pos_of_pos he))]
  calc
    _ ≤ ((c * z / C) / p) * ((C / (z * p) * b) * e ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hu (sq_nonneg e)) (by positivity)
    _ = c * e ^ 2 * b / p ^ 2 := by field_simp
    _ ≤ a := hl

/-- One arithmetic source lower bound implies a prime-harmonic budget for the actual block. -/
theorem prime_budget_of_source_floor (n : ℕ) (hp : (n + 4).Prime)
    (s : Finset (DivisorIndex n)) {c : ℝ} (hc : 0 < c) (hb : 0 < divisorMass n s)
    (hl : c * middleError n ^ 2 * divisorMass n s / ((n + 4 : ℕ) : ℝ) ^ 2 ≤ sourceMass n s) :
    (c * ZetaTwoProbability.zetaTwo / (Real.log (2 * Real.pi) - Real.eulerMascheroniConstant)) /
      ((n + 4 : ℕ) : ℝ) ≤ selectedBudget n s := by
  have he := (primorialError_pos (n + 1)).trans_le (middle_error_bounds n hp).1
  have hpR : (0 : ℝ) < ((n + 4 : ℕ) : ℝ) := by positivity
  have hS : 0 < sourceMass n s :=
    (div_pos (mul_pos (mul_pos hc (sq_pos_of_pos he)) hb) (sq_pos_of_pos hpR)).trans_le hl
  have hT : 0 < blockTrace n s := by
    have ht : 0 ≤ blockTrace n s := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    apply lt_of_le_of_ne ht
    intro hz
    have hu := selected_scores_le_trace_mul_gain n hp s
    rw [← hz, zero_mul] at hu
    exact (not_lt_of_ge hu) hS
  rw [selectedBudget, if_pos hp]
  exact source_floor_algebra hc ZetaTwoProbability.zetaTwo_pos cZero_pos hpR he hT
    (blockTrace_upper n s) hl

/-- The arithmetic floor in the note with a finite initial exception and arbitrary nonempty
divisor selections. The source is evaluated after adjoining the next prime. -/
theorem riemannHypothesis_of_eventual_source_floor (s : ∀ n, Finset (DivisorIndex n))
    {c : ℝ} (hc : 0 < c) (N : ℕ)
    (hpos : ∀ n, N ≤ n → (n + 4).Prime → 0 < divisorMass n (s n))
    (hlower : ∀ n, N ≤ n → (n + 4).Prime →
      c * middleError n ^ 2 * divisorMass n (s n) / ((n + 4 : ℕ) : ℝ) ^ 2 ≤
        sourceMass n (s n)) : RiemannHypothesis := by
  let k := c * ZetaTwoProbability.zetaTwo / (Real.log (2 * Real.pi) - Real.eulerMascheroniConstant)
  have hk : 0 < k := div_pos (mul_pos hc ZetaTwoProbability.zetaTwo_pos) cZero_pos
  let b : ℕ → ℝ := fun n => selectedBudget n (s n)
  have hh (m : ℕ) (hp : (m + (N + 4)).Prime) : k / ((m + (N + 4) : ℕ) : ℝ) ≤ b (m + N) := by
    have hp' : (m + N + 4).Prime := by simpa only [Nat.add_assoc] using hp
    have hN : N ≤ m + N := by omega
    exact (Nat.add_assoc m N 4) ▸ prime_budget_of_source_floor (m + N) hp' (s (m + N))
      hc (hpos _ hN hp') (hlower _ hN hp')
  by_contra h
  have hb : Summable b := summable_selectedBudget_of_not_RH h s
  exact RiemannResearch.Analysis.ResidualGain.not_summable_of_shifted_prime_lower
    (r := fun m => b (m + N)) (N + 4) hk
    (fun m => selectedBudget_nonneg _ _) hh ((summable_nat_add_iff N).mpr hb)

end RiemannResearch.RH.QCRTCarrySourceBudget
