import RiemannResearch.RH.BalancedSquarefreeCrossing
import RiemannResearch.RH.ParetoFiniteWindowEnergy
import RiemannResearch.RH.LegalExactHeadSubpolynomial

/-!
# The actual crossing-balanced finite-window RH reduction

Source: user-provided Green--Pareto--Schur continuation, 6 October 2026,
Sections 21--24. The source supplies the construction and proof strategy.
The arithmetic growth hypothesis and cofinal choice of crossings are explicit.
No estimate discharging them is asserted.
-/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto.BalancedSquarefree
open RiemannResearch.RH.Pareto
open RiemannResearch.RH.Pareto.FiniteWindow

theorem trialHilbert_mem_legalClosure (Y : ℕ) :
    trialHilbert Y ∈ hilbertLegalClosure (Set.Ici 1) := by
  apply Submodule.le_topologicalClosure (hilbertLegalSubspace (Set.Ici 1))
  change hilbertSequence (trialHilbert Y) ∈ legalSeedSpan (Set.Ici 1)
  rw [canonicalMobiusHilbert_sequence]
  exact trial_mem_legal Y

theorem residual_sequence_pos (Y j : ℕ) (hj : 0 < j) :
    hilbertSequence (hilbertOne - trialHilbert Y) j = 1 - trial Y j := by
  change hilbertSequenceLinear (hilbertOne - trialHilbert Y) j = _
  rw [map_sub]
  change hilbertSequence hilbertOne j - hilbertSequence (trialHilbert Y) j = _
  rw [hilbertOne_sequence, trialHilbert_sequence]
  simp [zeroAnchor, ne_of_gt hj]

theorem residual_head (Y j : ℕ) (hjY : j < Y+1) :
    hilbertSequence (hilbertOne - trialHilbert Y) j = 0 := by
  by_cases hj0 : j = 0
  · subst j
    exact hilbertSequence_zero _
  · rw [residual_sequence_pos Y j (Nat.pos_of_ne_zero hj0),
      trial_head Y j (Nat.pos_of_ne_zero hj0) hjY]
    ring

theorem residual_abs_le (Y j : ℕ) (hY : 0 < Y) (h : Crossing Y) :
    |hilbertSequence (hilbertOne - trialHilbert Y) j| ≤ ((Y+1 : ℕ) : ℝ) := by
  by_cases hj0 : j = 0
  · subst j
    rw [hilbertSequence_zero, abs_zero]
    positivity
  · rw [residual_sequence_pos Y j (Nat.pos_of_ne_zero hj0)]
    exact trial_error_abs_le Y j hY h

/-- The physical finite certificate of the actual residual. -/
def certificate (Y : ℕ) : ℝ :=
  windowEnergy (Y+1) (hilbertSequence (hilbertOne - trialHilbert Y))

theorem certificate_eq (Y : ℕ) :
    certificate Y = windowEnergy (Y+1) (fun j => 1 - trial Y j) := by
  unfold certificate windowEnergy
  apply Finset.sum_congr rfl
  intro j hj
  rw [residual_sequence_pos Y j (by have := (Finset.mem_Ico.mp hj).1; omega)]

theorem certificate_nonneg (Y : ℕ) : 0 ≤ certificate Y :=
  windowEnergy_nonneg _ _

/-- Exact complete-energy equality, retaining the entire farther tail. -/
theorem residual_norm_sq_eq (Y : ℕ) :
    ‖hilbertOne - trialHilbert Y‖^2 = certificate Y +
      farEnergy (Y+1) (hilbertSequence (hilbertOne - trialHilbert Y)) :=
  norm_sq_eq_window_add_far _ _ (residual_head Y)

theorem residual_norm_sq_bounds (Y : ℕ) (hY : 0 < Y) (h : Crossing Y) :
    certificate Y ≤ ‖hilbertOne - trialHilbert Y‖^2 ∧
      ‖hilbertOne - trialHilbert Y‖^2 ≤ certificate Y + 1 :=
  norm_sq_window_bounds _ _ (by omega) (residual_head Y)
    (fun j => residual_abs_le Y j hY h)

/-- Conditional research reduction. Subpolynomial window growth is OPEN;
cofinal crossings are supplied explicitly rather than postulated as an axiom. -/
theorem riemannHypothesis_of_subpolynomial_crossing_window
    (Y : ℕ → ℕ)
    (hcofinal : Tendsto (fun i => ((Y i + 1 : ℕ) : ℝ)) atTop atTop)
    (hY : ∀ i, 0 < Y i) (hcross : ∀ i, Crossing (Y i))
    (hsub : Tendsto (fun i => Real.log (1 + certificate (Y i)) /
      Real.log ((Y i + 1 : ℕ) : ℝ)) atTop (𝓝 0)) : RiemannHypothesis := by
  exact riemannHypothesis_of_cofinal_legal_exact_head_subpolynomial
    (Set.Ici 1) (fun a ha => lt_of_lt_of_le Nat.zero_lt_one ha)
    (fun i => trialHilbert (Y i)) (fun i => Y i + 1)
    (fun i => certificate (Y i)) hcofinal
    (fun i => trialHilbert_mem_legalClosure (Y i))
    (fun i j hj hjY => trialHilbert_head (Y i) j hj hjY)
    (fun i => certificate_nonneg (Y i))
    (fun i => (residual_norm_sq_bounds (Y i) (hY i) (hcross i)).2) hsub

end RiemannResearch.RH.Pareto.BalancedSquarefree



namespace RiemannResearch.RH.Pareto.BalancedSquarefree
open RiemannResearch.RH.ArithmeticCumulative
open RiemannResearch.RH.Pareto.FiniteWindow

theorem trial_eq_legal_source_sum (Y j : ℕ) :
    trial Y j = ∑ d ∈ Finset.Ico 2 (Y+2), (-source Y d) * modularAtom d j := by
  have hm : 1 ∈ Finset.Icc 1 (Y+1) := by simp
  have hs : (Finset.Icc 1 (Y+1)).erase 1 = Finset.Ico 2 (Y+2) := by
    ext d
    simp only [Finset.mem_erase, Finset.mem_Icc, Finset.mem_Ico]
    omega
  have hsplit : (∑ d ∈ Finset.Icc 1 (Y+1), source Y d * residueFraction d j) =
      ∑ d ∈ Finset.Ico 2 (Y+2), source Y d * residueFraction d j := by
    rw [← Finset.sum_erase_add (Finset.Icc 1 (Y+1))
      (fun d => source Y d * residueFraction d j) hm, hs]
    simp [residueFraction, Nat.mod_one]
  rw [trial_eq_source, hsplit]
  simp only [neg_mul, Finset.sum_neg_distrib, modularAtom]

/-- Trial energy is the actual complete signed modular quadratic form. -/
theorem trial_window_eq_quadratic (Y : ℕ) :
    windowEnergy (Y+1) (trial Y) =
      modularQuadratic (Y+1) (fun d => -source Y d) := by
  rw [modularQuadratic_eq_weighted_square]
  unfold windowEnergy
  apply Finset.sum_congr rfl
  intro j hj
  rw [trial_eq_legal_source_sum]

theorem trial_window_eq_diagonal_add_pair (Y : ℕ) :
    windowEnergy (Y+1) (trial Y) =
      modularDiagonal (Y+1) (fun d => -source Y d) +
      2 * modularSignedPair (Y+1) (fun d => -source Y d) := by
  rw [trial_window_eq_quadratic, modularQuadratic_eq_diagonal_add_pair]

theorem trial_diagonal_lt_one (Y : ℕ) (hY : 0 < Y) (h : Crossing Y) :
    modularDiagonal (Y+1) (fun d => -source Y d) < 1 := by
  apply modularDiagonal_lt_one (Y+1) (by omega)
  intro d hd
  simpa only [abs_neg] using source_abs_le_one Y d h

theorem trial_pair_ge_neg_half (Y : ℕ) (hY : 0 < Y) (h : Crossing Y) :
    -(1/2 : ℝ) ≤ modularSignedPair (Y+1) (fun d => -source Y d) := by
  apply modularSignedPair_ge_neg_half (Y+1) (by omega)
  intro d hd
  simpa only [abs_neg] using source_abs_le_one Y d h

theorem certificate_one_add_le_three_trial (Y : ℕ) (hY : 0 < Y) :
    1 + certificate Y ≤ 3 * (1 + windowEnergy (Y+1) (trial Y)) := by
  rw [certificate_eq]
  exact residual_one_add_le_three_trial _ _ (windowMass_le_one _ (by omega))

theorem certificate_one_add_le_five_positivePair
    (Y : ℕ) (hY : 0 < Y) (h : Crossing Y) :
    1 + certificate Y ≤
      5 * (1 + max (modularSignedPair (Y+1) (fun d => -source Y d)) 0) := by
  apply residual_one_add_le_five_positivePair
    (certificate Y) (windowEnergy (Y+1) (trial Y))
    (modularDiagonal (Y+1) (fun d => -source Y d))
    (modularSignedPair (Y+1) (fun d => -source Y d)) (windowMass (Y+1))
  · rw [certificate_eq]
    exact residual_square_le_twice_trial _ _
  · exact trial_window_eq_diagonal_add_pair Y
  · exact (trial_diagonal_lt_one Y hY h).le
  · exact windowMass_le_one _ (by omega)

/-- The literal positive part of all signed unequal-pair interactions
is a sufficient arithmetic provider; its growth estimate is OPEN. -/
theorem riemannHypothesis_of_subpolynomial_positive_crossing_pairs
    (Y : ℕ → ℕ)
    (hcofinal : Tendsto (fun i => ((Y i+1 : ℕ) : ℝ)) atTop atTop)
    (hY : ∀ i, 0 < Y i) (hcross : ∀ i, Crossing (Y i))
    (hsub : Tendsto (fun i => Real.log (1 +
      max (modularSignedPair (Y i+1) (fun d => -source (Y i) d)) 0) /
      Real.log ((Y i+1 : ℕ) : ℝ)) atTop (𝓝 0)) : RiemannHypothesis := by
  apply riemannHypothesis_of_subpolynomial_crossing_window Y hcofinal hY hcross
  exact RiemannResearch.Analysis.SubpolynomialWindow.relativeLog_tendsto_zero_of_scaled_budget
    (fun i => certificate (Y i))
    (fun i => max (modularSignedPair (Y i+1) (fun d => -source (Y i) d)) 0)
    (fun i => ((Y i+1 : ℕ) : ℝ)) 5 (by norm_num)
    (fun i => certificate_nonneg _) (fun i => le_max_right _ _)
    hcofinal (Filter.Eventually.of_forall (fun i =>
      certificate_one_add_le_five_positivePair (Y i) (hY i) (hcross i))) hsub

end RiemannResearch.RH.Pareto.BalancedSquarefree
