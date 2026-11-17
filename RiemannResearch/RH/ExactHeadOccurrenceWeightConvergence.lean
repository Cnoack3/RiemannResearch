import RiemannResearch.RH.ExactHeadOccurrenceRational
import RiemannResearch.Analysis.FiniteWeightedVariancePerturbation
import RiemannResearch.RH.ParetoRationalWeightConvergence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Effective refinement of complete occurrence-energy certificates

Source: exact finite weighted-variance perturbation and complete progression
enclosures. A finite arithmetic sensitivity controls the optimized-energy
interval width. The period and cutoff are fixed in the refinement limit;
this is not a uniform cofinal RH estimate.
-/
noncomputable section
open scoped BigOperators
open Filter
namespace RiemannResearch.RH.Pareto.ExactHeadOccurrenceProjection
open RiemannResearch.Analysis
open RiemannResearch.Analysis.FiniteProfileEnergy
open RiemannResearch.Analysis.FiniteWeightedVariance
open ExactHeadAtomOptimizer

/-- An explicit finite arithmetic sensitivity, independent of the weight-approximation depth. -/
def occurrenceWeightSensitivity (P x : ℕ) : ℝ :=
  (∑ r ∈ Finset.Ico 1 (occurrenceBoundary P x 0), target P r ^ 2) +
  ∑ i ∈ Finset.range (freePositions P x).card,
    ((Finset.Ico (occurrenceBoundary P x i) (occurrenceBoundary P x (i+1))).card : ℝ) *
      (target P (occurrenceBoundary P x (i+1)-1) - target P (occurrenceBoundary P x i))^2

theorem occurrenceWeightSensitivity_nonneg (P x : ℕ) :
    0 ≤ occurrenceWeightSensitivity P x := by
  apply add_nonneg
  · exact Finset.sum_nonneg (fun r hr => sq_nonneg _)
  · exact Finset.sum_nonneg (fun i hi => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))

/-- The complete optimized energy has an effective error bound under finite weight perturbation. -/
theorem occurrenceWeightEnergy_error_bounds (P x : ℕ) (hP : 0 < P)
    (w v : ℕ → ℝ) (hw : ∀ r ∈ Finset.Icc 1 (P-1), 0 < w r)
    (hwv : ∀ r ∈ Finset.Icc 1 (P-1), w r ≤ v r)
    (eps : ℝ) (herr : ∀ r ∈ Finset.Icc 1 (P-1), v r - w r ≤ eps) :
    0 ≤ occurrenceWeightEnergy P x v - occurrenceWeightEnergy P x w ∧
      occurrenceWeightEnergy P x v - occurrenceWeightEnergy P x w ≤
        eps * occurrenceWeightSensitivity P x := by
  constructor
  · exact sub_nonneg.mpr (occurrenceWeightEnergy_mono P x hP w v hw hwv)
  · have hinit :
        energy (Finset.Ico 1 (occurrenceBoundary P x 0)) v (target P) -
          energy (Finset.Ico 1 (occurrenceBoundary P x 0)) w (target P) ≤
        eps * (∑ r ∈ Finset.Ico 1 (occurrenceBoundary P x 0), target P r^2) := by
      unfold energy
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro r hr
      have hrI : r ∈ Finset.Icc 1 (P-1) := by
        have := Finset.mem_Ico.mp hr
        have := occurrenceBoundary_le_period P x 0
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      simpa only [sub_mul] using
        mul_le_mul_of_nonneg_right (herr r hrI) (sq_nonneg (target P r))
    have hblock (i : ℕ) (hi : i ∈ Finset.range (freePositions P x).card) :
        variance (Finset.Ico (occurrenceBoundary P x i) (occurrenceBoundary P x (i+1)))
            v (target P) -
          variance (Finset.Ico (occurrenceBoundary P x i) (occurrenceBoundary P x (i+1)))
            w (target P) ≤
        eps * (((Finset.Ico (occurrenceBoundary P x i)
          (occurrenceBoundary P x (i+1))).card : ℝ) *
          (target P (occurrenceBoundary P x (i+1)-1) -
            target P (occurrenceBoundary P x i))^2) := by
      let s := Finset.Ico (occurrenceBoundary P x i) (occurrenceBoundary P x (i+1))
      have hs : ∀ r ∈ s, r ∈ Finset.Icc 1 (P-1) := by
        intro r hr
        have := Finset.mem_Ico.mp hr
        have := occurrenceBoundary_pos P x i hP
        have := occurrenceBoundary_le_period P x (i+1)
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      have hm : 0 < FiniteWeightedVariance.mass s w := by
        apply Finset.sum_pos
        · exact fun r hr => hw r (hs r hr)
        · exact ⟨occurrenceBoundary P x i, Finset.mem_Ico.mpr
            ⟨le_rfl, occurrenceBoundary_strict P x i (Finset.mem_range.mp hi)⟩⟩
      have hb := (variance_weight_error_bounds s w v (target P)
        (fun r hr => (hw r (hs r hr)).le) hm (fun r hr => hwv r (hs r hr))
        (target P (occurrenceBoundary P x i)) (target P (occurrenceBoundary P x (i+1)-1))
        (fun r hr => occurrence_target_mono P (Finset.mem_Ico.mp hr).1)
        (fun r hr => occurrence_target_mono P (by have := Finset.mem_Ico.mp hr; omega))).2
      have hmass : FiniteWeightedVariance.mass s (fun r => v r - w r) ≤
          (s.card : ℝ) * eps := by
        calc
          _ ≤ ∑ r ∈ s, eps := Finset.sum_le_sum (fun r hr => herr r (hs r hr))
          _ = _ := by simp
      exact hb.trans ((mul_le_mul_of_nonneg_left hmass (sq_nonneg _)).trans_eq (by ring))
    have hsum := Finset.sum_le_sum hblock
    unfold occurrenceWeightEnergy occurrenceWeightSensitivity
    rw [← Finset.mul_sum, Finset.sum_sub_distrib] at hsum
    nlinarith [hinit]

/-- A certified inverse-square enclosure width for every fixed period and cutoff. -/
theorem rationalOccurrenceEnergy_width_le (P x K : ℕ) (hP : 0 < P) (hK : 0 < K) :
    0 ≤ (rationalOccurrenceEnergy P x
        (fun r => (elementaryProgressionInterval P r K).hi) : ℝ) -
      (rationalOccurrenceEnergy P x
        (fun r => (elementaryProgressionInterval P r K).lo) : ℝ) ∧
    (rationalOccurrenceEnergy P x
        (fun r => (elementaryProgressionInterval P r K).hi) : ℝ) -
      (rationalOccurrenceEnergy P x
        (fun r => (elementaryProgressionInterval P r K).lo) : ℝ) ≤
      (1 / (((P : ℝ)*K)^2)) * occurrenceWeightSensitivity P x := by
  simp only [rationalOccurrenceEnergy_cast]
  apply occurrenceWeightEnergy_error_bounds P x hP
  · intro r hr
    exact_mod_cast elementaryProgressionInterval_lower_pos P r K hP (Finset.mem_Icc.mp hr).1
  · intro r hr
    have h := elementaryProgressionInterval_contains P r K hP (Finset.mem_Icc.mp hr).1
    exact h.1.trans h.2
  · intro r hr
    have h := (Rat.cast_le (K := ℝ)).2
      (elementaryProgressionInterval_width_le P r K hP (Finset.mem_Icc.mp hr).1 hK)
    simpa only [Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_pow,
      Rat.cast_mul, Rat.cast_natCast] using h

theorem rationalOccurrenceEnergy_lower_mono (P x : ℕ) (hP : 0 < P) :
    Monotone (fun K => (rationalOccurrenceEnergy P x
      (fun r => (elementaryProgressionInterval P r K).lo) : ℝ)) := by
  intro K L hKL
  simp only [rationalOccurrenceEnergy_cast]
  apply occurrenceWeightEnergy_mono P x hP
  · intro r hr
    exact_mod_cast elementaryProgressionInterval_lower_pos P r K hP (Finset.mem_Icc.mp hr).1
  · intro r hr
    exact_mod_cast elementaryProgressionInterval_lower_mono P r hP (Finset.mem_Icc.mp hr).1 hKL

theorem rationalOccurrenceEnergy_upper_antitone (P x : ℕ) (hP : 0 < P) :
    Antitone (fun K => (rationalOccurrenceEnergy P x
      (fun r => (elementaryProgressionInterval P r K).hi) : ℝ)) := by
  intro K L hKL
  simp only [rationalOccurrenceEnergy_cast]
  apply occurrenceWeightEnergy_mono P x hP
  · intro r hr
    exact (progressionWeight_pos P r hP (Finset.mem_Icc.mp hr).1).trans_le
      (elementaryProgressionInterval_contains P r L hP (Finset.mem_Icc.mp hr).1).2
  · intro r hr
    exact_mod_cast elementaryProgressionInterval_upper_antitone P r hP
      (Finset.mem_Icc.mp hr).1 hKL

theorem rationalOccurrenceEnergy_width_tendsto_zero (P x : ℕ) (hP : 0 < P) :
    Tendsto (fun K => (rationalOccurrenceEnergy P x
        (fun r => (elementaryProgressionInterval P r K).hi) : ℝ) -
      (rationalOccurrenceEnergy P x
        (fun r => (elementaryProgressionInterval P r K).lo) : ℝ)) atTop (nhds 0) := by
  have hinv : Tendsto (fun K : ℕ => (K : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hh := (hinv.pow 2).const_mul (occurrenceWeightSensitivity P x / (P : ℝ)^2)
  have hb : Tendsto (fun K : ℕ =>
      (1 / (((P : ℝ)*K)^2)) * occurrenceWeightSensitivity P x) atTop (nhds 0) := by
    convert hh using 1 <;>
      simp [div_eq_mul_inv, mul_pow, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc]
  apply squeeze_zero' _ _ hb
  · filter_upwards [eventually_ge_atTop 1] with K hK
    exact (rationalOccurrenceEnergy_width_le P x K hP hK).1
  · filter_upwards [eventually_ge_atTop 1] with K hK
    exact (rationalOccurrenceEnergy_width_le P x K hP hK).2

theorem rationalOccurrenceEnergy_lower_tendsto (P x : ℕ) (hP : 0 < P) :
    Tendsto (fun K => (rationalOccurrenceEnergy P x
      (fun r => (elementaryProgressionInterval P r K).lo) : ℝ))
      atTop (nhds (occurrenceEnergy P x)) := by
  have hd : Tendsto (fun K => occurrenceEnergy P x -
      (rationalOccurrenceEnergy P x
        (fun r => (elementaryProgressionInterval P r K).lo) : ℝ)) atTop (nhds 0) := by
    apply squeeze_zero _ _ (rationalOccurrenceEnergy_width_tendsto_zero P x hP)
    · intro K
      exact sub_nonneg.mpr (rationalOccurrenceEnergy_enclosure P x K hP).1
    · intro K
      exact sub_le_sub_right (rationalOccurrenceEnergy_enclosure P x K hP).2 _
  simpa only [sub_sub_cancel, sub_zero] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => occurrenceEnergy P x)
      atTop (nhds (occurrenceEnergy P x))).sub hd

theorem rationalOccurrenceEnergy_upper_tendsto (P x : ℕ) (hP : 0 < P) :
    Tendsto (fun K => (rationalOccurrenceEnergy P x
      (fun r => (elementaryProgressionInterval P r K).hi) : ℝ))
      atTop (nhds (occurrenceEnergy P x)) := by
  have hd : Tendsto (fun K =>
      (rationalOccurrenceEnergy P x
        (fun r => (elementaryProgressionInterval P r K).hi) : ℝ) -
      occurrenceEnergy P x) atTop (nhds 0) := by
    apply squeeze_zero _ _ (rationalOccurrenceEnergy_width_tendsto_zero P x hP)
    · intro K
      exact sub_nonneg.mpr (rationalOccurrenceEnergy_enclosure P x K hP).2
    · intro K
      exact sub_le_sub_left (rationalOccurrenceEnergy_enclosure P x K hP).1 _
  simpa only [sub_add_cancel, zero_add] using
    hd.add (tendsto_const_nhds : Tendsto (fun _ : ℕ => occurrenceEnergy P x)
      atTop (nhds (occurrenceEnergy P x)))

/-- Every positive finite period admits rational energy certificates of arbitrary accuracy. -/
theorem rationalOccurrenceEnergy_arbitrarily_tight (P x : ℕ) (hP : 0 < P)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ K : ℕ, 1 ≤ K ∧
      (rationalOccurrenceEnergy P x
        (fun r => (elementaryProgressionInterval P r K).lo) : ℝ) ≤ occurrenceEnergy P x ∧
      occurrenceEnergy P x ≤ (rationalOccurrenceEnergy P x
        (fun r => (elementaryProgressionInterval P r K).hi) : ℝ) ∧
      (rationalOccurrenceEnergy P x
        (fun r => (elementaryProgressionInterval P r K).hi) : ℝ) -
      (rationalOccurrenceEnergy P x
        (fun r => (elementaryProgressionInterval P r K).lo) : ℝ) < eps := by
  have he := (tendsto_order.mp (rationalOccurrenceEnergy_width_tendsto_zero P x hP)).2 eps heps
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  refine ⟨max N 1, le_max_right _ _, ?_, ?_, hN _ (le_max_left _ _)⟩
  · exact (rationalOccurrenceEnergy_enclosure P x _ hP).1
  · exact (rationalOccurrenceEnergy_enclosure P x _ hP).2

end RiemannResearch.RH.Pareto.ExactHeadOccurrenceProjection
