/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.FiniteResidueDilation
import RiemannResearch.Analysis.SingleObservationProjection
import RiemannResearch.RH.MobiusResidualFirstCoordinate
import RiemannResearch.RH.ResidueGramDigamma
import RiemannResearch.RH.ThresholdHilbertL1

/-!
# Full-Pareto parity-normalized least-squares optimizers

Source: the user's parity-normalized scalar L1 target and indicator reduction.
The law is P(N=k)=1/(k(k+1)) on positive integers, with zero coordinate anchored.
The target is the indicator of divisibility by 2; its mass is 1-log(2).
Stage n is manuscript cutoff M=n+3 and uses every atom g₂,...,g_M.

The optimizer is constructed by scaling the orthogonal projection of the
even indicator. Its two exact parity observations, legal finite expansion,
unique constrained minimality and unconditional Hilbert convergence are proved.
All norms and expectations use the entire infinite Pareto distribution.

Conditional research reduction: convergence of the concrete optimizers' L1
norms to 1-log(2) implies the existing formalized RiemannHypothesis statement.
This scalar limit remains Open. Equivalent formulations are L1 convergence
to the even indicator and disappearance of the pointwise negative mass.
The reverse implication from RH is not asserted in this module.
No distribution change or finite truncation of the norm occurs.

The two-sided limiting L1 excess bound, exact finite dyadic completion, and
one-coordinate/cofinal-stage sufficient criteria are also formalized below.
For the classical discrete closed-span background, see Bagchi, Theorem 1,
https://arxiv.org/abs/math/0607733; this supports the background criterion.
The finite dyadic identities are derived here from the user's Pareto setup.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.RH.Pareto.CoefficientStabilization.ParityOptimizer

open RiemannResearch.RH.ArithmeticCumulative

def oddIndicator : ThresholdHilbert := (2 : ℝ) • residueAtom 0
def evenIndicator : ThresholdHilbert := hilbertOne - oddIndicator
def evenMass : ℝ := 1 - Real.log 2

theorem odd_inner_one : inner ℝ oddIndicator hilbertOne = Real.log 2 := by
  have h := residueAtom_inner_one 0
  norm_num at h
  rw [oddIndicator, real_inner_smul_left, h]
  ring

theorem odd_norm_sq : ‖oddIndicator‖ ^ 2 = Real.log 2 := by
  rw [oddIndicator, norm_smul, Real.norm_eq_abs, mul_pow,
    residueAtom_zero_norm_sq]
  norm_num
  ring

theorem even_inner_one : inner ℝ evenIndicator hilbertOne = evenMass := by
  rw [evenIndicator, inner_sub_left, real_inner_self_eq_norm_sq,
    hilbertOne_norm_sq, odd_inner_one]
  rfl

theorem even_inner_odd : inner ℝ evenIndicator oddIndicator = 0 := by
  rw [evenIndicator, inner_sub_left, real_inner_comm,
    odd_inner_one, real_inner_self_eq_norm_sq, odd_norm_sq, sub_self]

theorem even_norm_sq : ‖evenIndicator‖ ^ 2 = evenMass := by
  rw [evenIndicator, norm_sub_sq_real, hilbertOne_norm_sq,
    real_inner_comm, odd_inner_one, odd_norm_sq]
  unfold evenMass
  ring

theorem even_sequence_one : hilbertSequence evenIndicator 1 = 0 := by
  change hilbertSequenceLinear (hilbertOne - (2 : ℝ) • residueAtom 0) 1 = 0
  rw [map_sub, map_smul]
  change hilbertSequence hilbertOne 1 -
    2 * hilbertSequence (residueAtom 0) 1 = 0
  rw [hilbertOne_sequence, residueAtom, normalizedResidueHilbert_sequence]
  norm_num [zeroAnchor, residueFraction]

theorem even_sequence_two : hilbertSequence evenIndicator 2 = 1 := by
  change hilbertSequenceLinear (hilbertOne - (2 : ℝ) • residueAtom 0) 2 = 1
  rw [map_sub, map_smul]
  change hilbertSequence hilbertOne 2 -
    2 * hilbertSequence (residueAtom 0) 2 = 1
  rw [hilbertOne_sequence, residueAtom, normalizedResidueHilbert_sequence]
  norm_num [zeroAnchor, residueFraction]

theorem evenMass_pos : 0 < evenMass := by
  rw [← even_norm_sq]
  apply sq_pos_of_pos
  apply norm_pos_iff.mpr
  intro h
  have hh := even_sequence_two
  rw [h] at hh
  norm_num [hilbertSequence] at hh

open RiemannResearch.RH.ArithmeticCumulative
open RiemannResearch.Analysis.ExhaustiveWalk
open RiemannResearch.Analysis.SingleObservationProjection

theorem even_sequence (k : ℕ) :
    hilbertSequence evenIndicator k =
      zeroAnchor (fun _ => (1 : ℝ)) k - ((k % 2 : ℕ) : ℝ) := by
  change hilbertSequenceLinear (hilbertOne - (2 : ℝ) • residueAtom 0) k = _
  rw [map_sub, map_smul]
  change hilbertSequence hilbertOne k - 2 * hilbertSequence (residueAtom 0) k = _
  rw [hilbertOne_sequence, residueAtom, normalizedResidueHilbert_sequence]
  dsimp [residueFraction]
  ring


/-- Positive coordinates are exactly the indicator that 2 divides the integer. -/
theorem even_sequence_indicator (k : ℕ) (hk : 0 < k) :
    hilbertSequence evenIndicator k = if 2 ∣ k then 1 else 0 := by
  rw [even_sequence]
  simp only [zeroAnchor, if_neg (Nat.ne_of_gt hk)]
  by_cases hd : 2 ∣ k
  · rw [if_pos hd, Nat.mod_eq_zero_of_dvd hd]
    norm_num
  · have hm : k % 2 = 1 := by
      have hn : k % 2 ≠ 0 := fun h => hd (Nat.dvd_of_mod_eq_zero h)
      omega
    rw [if_neg hd, hm]
    norm_num

theorem even_sequence_nonneg (k : ℕ) : 0 ≤ hilbertSequence evenIndicator k := by
  rw [even_sequence]
  by_cases hk : k = 0
  · subst k
    norm_num [zeroAnchor]
  · have hm : ((k % 2 : ℕ) : ℝ) ≤ 1 := by
      exact_mod_cast (show k % 2 ≤ 1 by omega)
    simp only [zeroAnchor, if_neg hk]
    linarith

theorem even_inner_three_pos : 0 < inner ℝ evenIndicator (residueAtom 1) := by
  have hs := weighted_product_summable_of_square
    (hilbertSequence_square_summable evenIndicator)
    (hilbertSequence_square_summable (residueAtom 1))
  have ht := hs.le_tsum 2 (fun k _ =>
    mul_nonneg (positiveWeight_nonneg k)
      (mul_nonneg (even_sequence_nonneg k) (by
        rw [residueAtom, normalizedResidueHilbert_sequence]
        unfold residueFraction
        positivity)))
  change positiveWeight 2 * (hilbertSequence evenIndicator 2 *
      hilbertSequence (residueAtom 1) 2) ≤
    paretoInner (hilbertSequence evenIndicator) (hilbertSequence (residueAtom 1)) at ht
  rw [← hilbert_inner_weighted] at ht
  have hthree : hilbertSequence (residueAtom 1) 2 = 2 / 3 := by
    rw [residueAtom, normalizedResidueHilbert_sequence]
    norm_num [residueFraction]
  rw [even_sequence_two, hthree] at ht
  norm_num [positiveWeight] at ht
  linarith

def projected (n : ℕ) : ThresholdHilbert :=
  (finiteSpace (n + 2)).starProjection evenIndicator
def limitProjected : ThresholdHilbert := closedSpace.starProjection evenIndicator
/-- Index n is manuscript cutoff M=n+3, using g₂,...,g_M. -/
def optimizer (n : ℕ) : ThresholdHilbert :=
  observationOptimizer (finiteSpace (n + 2)) evenIndicator evenMass
def limitOptimizer : ThresholdHilbert :=
  observationOptimizer closedSpace evenIndicator evenMass

theorem atom_mem_finite (n i : ℕ) (hi : i < n + 2) :
    residueAtom i ∈ finiteSpace (n + 2) :=
  Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩

theorem atom_mem_closed (i : ℕ) : residueAtom i ∈ closedSpace :=
  (Submodule.span ℝ (Set.range residueAtom)).le_topologicalClosure
    (Submodule.subset_span ⟨i, rfl⟩)

theorem projected_energy_pos (n : ℕ) : 0 < ‖projected n‖ ^ 2 :=
  projection_energy_pos_of_observation (finiteSpace (n + 2)) evenIndicator
    (residueAtom 1) (atom_mem_finite n 1 (by omega)) (ne_of_gt even_inner_three_pos)

theorem limitProjected_energy_pos : 0 < ‖limitProjected‖ ^ 2 :=
  projection_energy_pos_of_observation closedSpace evenIndicator
    (residueAtom 1) (atom_mem_closed 1) (ne_of_gt even_inner_three_pos)

theorem projected_eq (n : ℕ) :
    projected n = projection (n + 2) - oddIndicator := by
  unfold projected evenIndicator oddIndicator
  rw [map_sub, map_smul,
    Submodule.starProjection_eq_self_iff.mpr (atom_mem_finite n 0 (by omega))]
  rfl

theorem limitProjected_eq : limitProjected = limitProjection - oddIndicator := by
  unfold limitProjected evenIndicator oddIndicator
  rw [map_sub, map_smul,
    Submodule.starProjection_eq_self_iff.mpr (atom_mem_closed 0)]
  rfl

theorem optimizer_mem (n : ℕ) : optimizer n ∈ finiteSpace (n + 2) :=
  observationOptimizer_mem _ _ _

theorem optimizer_even_mean (n : ℕ) : inner ℝ (optimizer n) evenIndicator = evenMass := by
  rw [real_inner_comm]
  exact observationOptimizer_observation _ _ _ (ne_of_gt (projected_energy_pos n))

theorem optimizer_odd_mean (n : ℕ) : inner ℝ (optimizer n) oddIndicator = 0 :=
  observationOptimizer_orthogonal _ _ _ _
    ((finiteSpace (n + 2)).smul_mem 2 (atom_mem_finite n 0 (by omega)))
    even_inner_odd

theorem optimizer_mean (n : ℕ) : inner ℝ (optimizer n) hilbertOne = evenMass := by
  have he : hilbertOne = evenIndicator + oddIndicator := by
    unfold evenIndicator
    abel
  rw [he, inner_add_right, optimizer_even_mean, optimizer_odd_mean, add_zero]

/-- Exact completion in the full infinite Pareto norm, hence global minimality. -/
theorem optimizer_completion (n : ℕ) (f : ThresholdHilbert)
    (hf : f ∈ finiteSpace (n + 2))
    (hfe : inner ℝ f evenIndicator = evenMass) :
    ‖f - evenIndicator‖ ^ 2 = ‖optimizer n - evenIndicator‖ ^ 2 +
      ‖f - optimizer n‖ ^ 2 :=
  observation_distance_completion _ _ _ _ (ne_of_gt (projected_energy_pos n)) hf hfe

theorem optimizer_minimizes (n : ℕ) (f : ThresholdHilbert)
    (hf : f ∈ finiteSpace (n + 2))
    (hfe : inner ℝ f evenIndicator = evenMass) :
    ‖optimizer n - evenIndicator‖ ^ 2 ≤ ‖f - evenIndicator‖ ^ 2 := by
  rw [optimizer_completion n f hf hfe]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem optimizer_unique (n : ℕ) (f : ThresholdHilbert)
    (hf : f ∈ finiteSpace (n + 2))
    (hfe : inner ℝ f evenIndicator = evenMass)
    (he : ‖f - evenIndicator‖ ^ 2 = ‖optimizer n - evenIndicator‖ ^ 2) :
    f = optimizer n := by
  have hc := optimizer_completion n f hf hfe
  have hz : ‖f - optimizer n‖ ^ 2 = 0 := by linarith
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))


/-- Exact unconditional parity observations, equivalent to the stated conditional means. -/
def Feasible (n : ℕ) (f : ThresholdHilbert) : Prop :=
  f ∈ finiteSpace (n + 2) ∧
    inner ℝ f evenIndicator = evenMass ∧ inner ℝ f oddIndicator = 0

theorem optimizer_feasible (n : ℕ) : Feasible n (optimizer n) :=
  ⟨optimizer_mem n, optimizer_even_mean n, optimizer_odd_mean n⟩

theorem optimizer_even_conditional_mean (n : ℕ) :
    inner ℝ (optimizer n) evenIndicator / evenMass = 1 := by
  rw [optimizer_even_mean, div_self (ne_of_gt evenMass_pos)]

theorem optimizer_odd_conditional_mean (n : ℕ) :
    inner ℝ (optimizer n) oddIndicator / (1 - evenMass) = 0 := by
  rw [optimizer_odd_mean, zero_div]

theorem optimizer_expansion (n : ℕ) :
    ∃ c : Fin (n + 2) → ℝ,
      optimizer n = ∑ j : Fin (n + 2), c j • residueAtom j.val :=
  finiteSpace_expansion _ _ (optimizer_mem n)

/-- This definition is precisely the user's unique parity-constrained minimizer. -/
theorem optimizer_characterization (n : ℕ) (f : ThresholdHilbert) :
    (Feasible n f ∧ ∀ g : ThresholdHilbert, Feasible n g →
      ‖f - evenIndicator‖ ^ 2 ≤ ‖g - evenIndicator‖ ^ 2) ↔ f = optimizer n := by
  constructor
  · rintro ⟨⟨hf, hfe, _⟩, hmin⟩
    exact optimizer_unique n f hf hfe
      (le_antisymm (hmin _ (optimizer_feasible n)) (optimizer_minimizes n f hf hfe))
  · rintro rfl
    refine ⟨optimizer_feasible n, ?_⟩
    rintro g ⟨hg, hge, _⟩
    exact optimizer_minimizes n g hg hge

theorem projected_tendsto : Tendsto projected atTop (𝓝 limitProjected) := by
  have h := walkProjection_tendsto residueAtom id Function.surjective_id evenIndicator
  exact h.comp (tendsto_add_atTop_nat 2)

theorem optimizer_tendsto : Tendsto optimizer atTop (𝓝 limitOptimizer) := by
  change Tendsto (fun n => (evenMass / ‖projected n‖ ^ 2) • projected n) atTop
    (𝓝 ((evenMass / ‖limitProjected‖ ^ 2) • limitProjected))
  exact (tendsto_const_nhds.div (projected_tendsto.norm.pow 2)
    (ne_of_gt limitProjected_energy_pos)).smul projected_tendsto

theorem optimizer_first_tendsto :
    Tendsto (fun n => hilbertSequence (optimizer n) 1) atTop
      (𝓝 (hilbertSequence limitOptimizer 1)) := by
  simpa only [Function.comp_def, anchoredEvaluationCLM_apply] using
    ((anchoredEvaluationCLM 1).continuous.tendsto limitOptimizer).comp optimizer_tendsto

theorem limitOptimizer_first :
    hilbertSequence limitOptimizer 1 =
      -(evenMass / ‖limitProjected‖ ^ 2) * hilbertSequence limitResidual 1 := by
  have hs : hilbertSequence limitProjected 1 = -hilbertSequence limitResidual 1 := by
    have he : limitProjected = evenIndicator - limitResidual := by
      rw [limitProjected_eq]
      unfold evenIndicator limitResidual
      abel
    rw [he, hilbertSequence_sub, Pi.sub_apply, even_sequence_one, zero_sub]
  change hilbertSequenceLinear
    ((evenMass / ‖limitProjected‖ ^ 2) • limitProjected) 1 = _
  rw [map_smul]
  change (evenMass / ‖limitProjected‖ ^ 2) * hilbertSequence limitProjected 1 = _
  rw [hs]
  ring

/-- The user's scalar target is the sole open analytic hypothesis. -/
theorem limitResidual_zero_of_l1Norm_tendsto
    (h : Tendsto (fun n => hilbertL1Norm (optimizer n)) atTop (𝓝 evenMass)) :
    limitResidual = 0 := by
  have hb : evenMass - hilbertSequence limitOptimizer 1 ≤ evenMass :=
    le_of_tendsto_of_tendsto
      (tendsto_const_nhds.sub optimizer_first_tendsto) h
      (Eventually.of_forall (fun n => by
        simpa only [optimizer_mean] using inner_one_sub_first_le_hilbertL1Norm (optimizer n)))
  have hu : 0 ≤ hilbertSequence limitOptimizer 1 := by linarith
  rw [limitOptimizer_first] at hu
  have hp : 0 < evenMass / ‖limitProjected‖ ^ 2 :=
    div_pos evenMass_pos limitProjected_energy_pos
  have hr : hilbertSequence limitResidual 1 = 0 := by
    nlinarith [firstCoordinate_nonneg]
  exact firstCoordinate_zero_iff_residual_zero.mp hr

theorem riemannHypothesis_of_l1Norm_tendsto
    (h : Tendsto (fun n => hilbertL1Norm (optimizer n)) atTop
      (𝓝 (1 - Real.log 2))) : RiemannHypothesis :=
  riemannHypothesis_of_limitCoefficients
    (limitCoefficients_eq_mobius_iff_residual_zero.mpr
      (limitResidual_zero_of_l1Norm_tendsto h))

theorem even_l1Norm : hilbertL1Norm evenIndicator = evenMass := by
  calc
    _ = inner ℝ evenIndicator hilbertOne := by
      rw [hilbert_inner_one]
      unfold hilbertL1Norm paretoMean
      apply tsum_congr
      intro k
      rw [abs_of_nonneg (even_sequence_nonneg k)]
    _ = _ := even_inner_one

theorem limitProjected_eq_even_sub_residual :
    limitProjected = evenIndicator - limitResidual := by
  rw [limitProjected_eq]
  unfold evenIndicator limitResidual
  abel

theorem limitOptimizer_eq_even_of_residual_zero (h : limitResidual = 0) :
    limitOptimizer = evenIndicator := by
  have he : limitProjected = evenIndicator := by
    rw [limitProjected_eq_even_sub_residual, h, sub_zero]
  change (evenMass / ‖limitProjected‖ ^ 2) • limitProjected = evenIndicator
  rw [he, even_norm_sq, div_self (ne_of_gt evenMass_pos), one_smul]

theorem optimizer_tendsto_even_of_l1Norm_tendsto
    (h : Tendsto (fun n => hilbertL1Norm (optimizer n)) atTop (𝓝 evenMass)) :
    Tendsto optimizer atTop (𝓝 evenIndicator) := by
  have he := limitOptimizer_eq_even_of_residual_zero
    (limitResidual_zero_of_l1Norm_tendsto h)
  simpa only [he] using optimizer_tendsto

theorem l1Norm_tendsto_iff_l1_convergence :
    Tendsto (fun n => hilbertL1Norm (optimizer n)) atTop (𝓝 evenMass) ↔
      Tendsto (fun n => hilbertL1Norm (optimizer n - evenIndicator)) atTop (𝓝 0) := by
  constructor
  · intro h
    exact hilbertL1Norm_tendsto_zero_of_norm
      (tendsto_iff_norm_sub_tendsto_zero.mp (optimizer_tendsto_even_of_l1Norm_tendsto h))
  · exact hilbertL1Norm_tendsto_of_sub even_l1Norm

theorem negativeMass_tendsto_zero_iff_l1Norm :
    Tendsto (fun n => hilbertNegativeMass (optimizer n)) atTop (𝓝 0) ↔
      Tendsto (fun n => hilbertL1Norm (optimizer n)) atTop (𝓝 evenMass) :=
  hilbertNegativeMass_tendsto_zero_iff optimizer_mean

theorem riemannHypothesis_of_negativeMass_tendsto_zero
    (h : Tendsto (fun n => hilbertNegativeMass (optimizer n)) atTop (𝓝 0)) :
    RiemannHypothesis :=
  riemannHypothesis_of_l1Norm_tendsto (negativeMass_tendsto_zero_iff_l1Norm.mp h)

theorem riemannHypothesis_of_l1_convergence
    (h : Tendsto (fun n => hilbertL1Norm (optimizer n - evenIndicator)) atTop (𝓝 0)) :
    RiemannHypothesis :=
  riemannHypothesis_of_l1Norm_tendsto (l1Norm_tendsto_iff_l1_convergence.mpr h)


theorem optimizer_norm_sq (n : ℕ) :
    ‖optimizer n‖ ^ 2 = evenMass ^ 2 / ‖projected n‖ ^ 2 :=
  observationOptimizer_energy _ _ _ (ne_of_gt (projected_energy_pos n))

theorem projected_eq_even_sub_residual (n : ℕ) :
    projected n = evenIndicator - (hilbertOne - projection (n + 2)) := by
  rw [projected_eq]
  unfold evenIndicator
  abel

theorem projected_energy_eq (n : ℕ) :
    ‖projected n‖ ^ 2 = evenMass - energy (n + 2) := by
  have hr : evenIndicator - projected n = hilbertOne - projection (n + 2) := by
    rw [projected_eq_even_sub_residual]
    abel
  have h := projection_defect_energy (finiteSpace (n + 2)) evenIndicator
  change ‖evenIndicator - projected n‖ ^ 2 =
    ‖evenIndicator‖ ^ 2 - ‖projected n‖ ^ 2 at h
  rw [hr, even_norm_sq] at h
  change energy (n + 2) = evenMass - ‖projected n‖ ^ 2 at h
  linarith

theorem optimizer_error_sq (n : ℕ) :
    ‖optimizer n - evenIndicator‖ ^ 2 =
      evenMass * energy (n + 2) / ‖projected n‖ ^ 2 := by
  have hr : evenIndicator - projected n = hilbertOne - projection (n + 2) := by
    rw [projected_eq_even_sub_residual]
    abel
  have h := observationOptimizer_error (finiteSpace (n + 2)) evenIndicator
    (ne_of_gt (projected_energy_pos n))
  rw [even_norm_sq] at h
  change ‖optimizer n - evenIndicator‖ ^ 2 =
    evenMass * ‖evenIndicator - projected n‖ ^ 2 / ‖projected n‖ ^ 2 at h
  rw [hr] at h
  exact h

theorem limitOptimizer_mem : limitOptimizer ∈ closedSpace :=
  observationOptimizer_mem _ _ _

theorem limitOptimizer_even_mean :
    inner ℝ limitOptimizer evenIndicator = evenMass := by
  rw [real_inner_comm]
  exact observationOptimizer_observation _ _ _
    (ne_of_gt limitProjected_energy_pos)

theorem limitOptimizer_odd_mean :
    inner ℝ limitOptimizer oddIndicator = 0 :=
  observationOptimizer_orthogonal _ _ _ _
    (closedSpace.smul_mem 2 (atom_mem_closed 0)) even_inner_odd

theorem limitOptimizer_mean :
    inner ℝ limitOptimizer hilbertOne = evenMass := by
  have he : hilbertOne = evenIndicator + oddIndicator := by
    unfold evenIndicator
    abel
  rw [he, inner_add_right, limitOptimizer_even_mean,
    limitOptimizer_odd_mean, add_zero]

theorem limitOptimizer_norm_sq :
    ‖limitOptimizer‖ ^ 2 = evenMass ^ 2 / ‖limitProjected‖ ^ 2 :=
  observationOptimizer_energy _ _ _ (ne_of_gt limitProjected_energy_pos)

theorem limitProjected_energy_eq :
    ‖limitProjected‖ ^ 2 = evenMass - limitEnergy := by
  have hr : evenIndicator - limitProjected = limitResidual := by
    rw [limitProjected_eq_even_sub_residual]
    abel
  have h := projection_defect_energy closedSpace evenIndicator
  change ‖evenIndicator - limitProjected‖ ^ 2 =
    ‖evenIndicator‖ ^ 2 - ‖limitProjected‖ ^ 2 at h
  rw [hr, even_norm_sq] at h
  change limitEnergy = evenMass - ‖limitProjected‖ ^ 2 at h
  linarith

theorem limitOptimizer_error_sq :
    ‖limitOptimizer - evenIndicator‖ ^ 2 =
      evenMass * limitEnergy / ‖limitProjected‖ ^ 2 := by
  have hr : evenIndicator - limitProjected = limitResidual := by
    rw [limitProjected_eq_even_sub_residual]
    abel
  have h := observationOptimizer_error closedSpace evenIndicator
    (ne_of_gt limitProjected_energy_pos)
  rw [even_norm_sq] at h
  change ‖limitOptimizer - evenIndicator‖ ^ 2 =
    evenMass * ‖evenIndicator - limitProjected‖ ^ 2 /
      ‖limitProjected‖ ^ 2 at h
  rw [hr] at h
  exact h

theorem limitOptimizer_first_exact :
    -hilbertSequence limitOptimizer 1 =
      ‖limitOptimizer - evenIndicator‖ ^ 2 / 2 +
        (evenMass / ‖limitProjected‖ ^ 2) *
          ‖limitResidual - (1 / 2 : ℝ) •
            hilbertDilation 2 (by omega) limitResidual‖ ^ 2 := by
  rw [limitOptimizer_first, firstCoordinate_exact_positive_identity,
    limitOptimizer_error_sq]
  ring

theorem limitOptimizer_l1Excess_lower :
    ‖limitOptimizer - evenIndicator‖ ^ 2 / 2 ≤
      hilbertL1Norm limitOptimizer - evenMass := by
  have hp : 0 ≤ evenMass / ‖limitProjected‖ ^ 2 :=
    le_of_lt (div_pos evenMass_pos limitProjected_energy_pos)
  have hb := inner_one_sub_first_le_hilbertL1Norm limitOptimizer
  rw [limitOptimizer_mean] at hb
  calc
    ‖limitOptimizer - evenIndicator‖ ^ 2 / 2 =
        (evenMass / ‖limitProjected‖ ^ 2) * (limitEnergy / 2) := by
      rw [limitOptimizer_error_sq]
      ring
    _ ≤ (evenMass / ‖limitProjected‖ ^ 2) *
        hilbertSequence limitResidual 1 :=
      mul_le_mul_of_nonneg_left firstCoordinate_energy_half_le hp
    _ = -hilbertSequence limitOptimizer 1 := by
      rw [limitOptimizer_first]
      ring
    _ ≤ hilbertL1Norm limitOptimizer - evenMass := by linarith

theorem limitOptimizer_l1Excess_upper :
    hilbertL1Norm limitOptimizer - evenMass ≤
      ‖limitOptimizer - evenIndicator‖ := by
  calc
    hilbertL1Norm limitOptimizer - evenMass =
        hilbertL1Norm limitOptimizer - hilbertL1Norm evenIndicator := by
      rw [even_l1Norm]
    _ ≤ hilbertL1Norm (limitOptimizer - evenIndicator) :=
      hilbertL1Norm_sub_le _ _
    _ ≤ ‖limitOptimizer - evenIndicator‖ := hilbertL1Norm_le_norm _

/-- The stronger coefficient follows from the normalized dilation norm bound.
This theorem makes no claim that the coefficient is optimal for actual residuals. -/
theorem limitOptimizer_l1Excess_lower_sqrt_two :
    (2 - Real.sqrt 2) * ‖limitOptimizer - evenIndicator‖ ^ 2 ≤
      hilbertL1Norm limitOptimizer - evenMass := by
  have hp : 0 ≤ evenMass / ‖limitProjected‖ ^ 2 :=
    le_of_lt (div_pos evenMass_pos limitProjected_energy_pos)
  have hr : (2 - Real.sqrt 2) * limitEnergy ≤
      hilbertSequence limitResidual 1 := by
    have h := firstCoordinate_energy_bounds.1
    nlinarith
  have hb := inner_one_sub_first_le_hilbertL1Norm limitOptimizer
  rw [limitOptimizer_mean] at hb
  calc
    (2 - Real.sqrt 2) * ‖limitOptimizer - evenIndicator‖ ^ 2 =
        (evenMass / ‖limitProjected‖ ^ 2) *
          ((2 - Real.sqrt 2) * limitEnergy) := by
      rw [limitOptimizer_error_sq]
      ring
    _ ≤ (evenMass / ‖limitProjected‖ ^ 2) *
        hilbertSequence limitResidual 1 :=
      mul_le_mul_of_nonneg_left hr hp
    _ = -hilbertSequence limitOptimizer 1 := by
      rw [limitOptimizer_first]
      ring
    _ ≤ hilbertL1Norm limitOptimizer - evenMass := by linarith

theorem limitOptimizer_first_nonpos :
    hilbertSequence limitOptimizer 1 ≤ 0 := by
  rw [limitOptimizer_first]
  have hp : 0 < evenMass / ‖limitProjected‖ ^ 2 :=
    div_pos evenMass_pos limitProjected_energy_pos
  nlinarith [firstCoordinate_nonneg]
theorem optimizer_first_tendsto_zero_iff_residual_zero :
    Tendsto (fun n => hilbertSequence (optimizer n) 1) atTop (𝓝 0) ↔
      limitResidual = 0 := by
  constructor
  · intro h
    have hu := tendsto_nhds_unique optimizer_first_tendsto h
    rw [limitOptimizer_first] at hu
    have hp : 0 < evenMass / ‖limitProjected‖ ^ 2 :=
      div_pos evenMass_pos limitProjected_energy_pos
    apply firstCoordinate_zero_iff_residual_zero.mp
    nlinarith
  · intro h
    have hu : hilbertSequence limitOptimizer 1 = 0 := by
      rw [limitOptimizer_eq_even_of_residual_zero h, even_sequence_one]
    simpa only [hu] using optimizer_first_tendsto
theorem optimizer_first_tendsto_zero_iff_l1Norm :
    Tendsto (fun n => hilbertSequence (optimizer n) 1) atTop (𝓝 0) ↔
      Tendsto (fun n => hilbertL1Norm (optimizer n)) atTop (𝓝 evenMass) := by
  constructor
  · intro h
    have hr := optimizer_first_tendsto_zero_iff_residual_zero.mp h
    have he := limitOptimizer_eq_even_of_residual_zero hr
    have ht : Tendsto optimizer atTop (𝓝 evenIndicator) := by
      simpa only [he] using optimizer_tendsto
    simpa only [Function.comp_def, even_l1Norm] using
      (hilbertL1Norm_continuous.tendsto evenIndicator).comp ht
  · intro h
    exact optimizer_first_tendsto_zero_iff_residual_zero.mpr
      (limitResidual_zero_of_l1Norm_tendsto h)
theorem riemannHypothesis_of_optimizer_first_tendsto_zero
    (h : Tendsto (fun n => hilbertSequence (optimizer n) 1) atTop (𝓝 0)) :
    RiemannHypothesis :=
  riemannHypothesis_of_l1Norm_tendsto
    (optimizer_first_tendsto_zero_iff_l1Norm.mp h)

theorem optimizer_first (n : ℕ) :
    hilbertSequence (optimizer n) 1 =
      -(evenMass / ‖projected n‖ ^ 2) *
        hilbertSequence (hilbertOne - projection (n + 2)) 1 := by
  have hs : hilbertSequence (projected n) 1 =
      -hilbertSequence (hilbertOne - projection (n + 2)) 1 := by
    rw [projected_eq_even_sub_residual, hilbertSequence_sub,
      Pi.sub_apply, even_sequence_one, zero_sub]
  change hilbertSequenceLinear
    ((evenMass / ‖projected n‖ ^ 2) • projected n) 1 = _
  rw [map_smul]
  change (evenMass / ‖projected n‖ ^ 2) *
      hilbertSequence (projected n) 1 = _
  rw [hs]
  ring

/-- Exact finite two-scale accounting, with both nonnegative corrections retained. -/
theorem optimizer_dyadic_completion (n : ℕ) :
    ‖optimizer (2 * n + 3) - evenIndicator‖ ^ 2 +
      (evenMass / ‖projected (2 * n + 3)‖ ^ 2) *
        ‖(hilbertOne - projection ((2 * n + 3) + 2)) -
          (1 / 2 : ℝ) • hilbertDilation 2 (by omega)
            (hilbertOne - projection (n + 2))‖ ^ 2 +
      evenMass * energy (n + 2) *
        (energy (n + 2) - energy ((2 * n + 3) + 2)) /
          (2 * ‖projected n‖ ^ 2 * ‖projected (2 * n + 3)‖ ^ 2) =
      ‖optimizer n - evenIndicator‖ ^ 2 / 2 -
        hilbertSequence (optimizer (2 * n + 3)) 1 := by
  have hd : hilbertSequence
      (hilbertOne - projection ((2 * n + 3) + 2)) 1 =
      energy ((2 * n + 3) + 2) - energy (n + 2) / 2 +
        ‖(hilbertOne - projection ((2 * n + 3) + 2)) -
          (1 / 2 : ℝ) • hilbertDilation 2 (by omega)
            (hilbertOne - projection (n + 2))‖ ^ 2 := by
    simpa only [show 2 * (n + 2) + 1 = (2 * n + 3) + 2 by omega] using
      projectionResidual_first_exact_dyadic (n + 2)
  have ha : evenMass - energy (n + 2) ≠ 0 := by
    rw [← projected_energy_eq]
    exact ne_of_gt (projected_energy_pos n)
  have hb : evenMass - energy ((2 * n + 3) + 2) ≠ 0 := by
    rw [← projected_energy_eq]
    exact ne_of_gt (projected_energy_pos (2 * n + 3))
  rw [optimizer_error_sq, optimizer_error_sq, optimizer_first, hd]
  simp only [projected_energy_eq]
  field_simp [ha, hb]
  ring

/-- The exact finite completion gives a sharper bound than replacing the
first coordinate by the entire L1 excess. -/
theorem optimizer_error_dyadic_first_bound (n : ℕ) :
    ‖optimizer (2 * n + 3) - evenIndicator‖ ^ 2 ≤
      ‖optimizer n - evenIndicator‖ ^ 2 / 2 -
        hilbertSequence (optimizer (2 * n + 3)) 1 := by
  have hs : 0 ≤ (evenMass / ‖projected (2 * n + 3)‖ ^ 2) *
      ‖(hilbertOne - projection ((2 * n + 3) + 2)) -
        (1 / 2 : ℝ) • hilbertDilation 2 (by omega)
          (hilbertOne - projection (n + 2))‖ ^ 2 :=
    mul_nonneg (le_of_lt (div_pos evenMass_pos
      (projected_energy_pos (2 * n + 3)))) (sq_nonneg _)
  have henergy : energy ((2 * n + 3) + 2) ≤ energy (n + 2) :=
    energy_antitone (by omega)
  have he : 0 ≤ energy (n + 2) := by
    change 0 ≤ ‖hilbertOne - projection (n + 2)‖ ^ 2
    exact sq_nonneg _
  have hc : 0 ≤ evenMass * energy (n + 2) *
      (energy (n + 2) - energy ((2 * n + 3) + 2)) /
        (2 * ‖projected n‖ ^ 2 * ‖projected (2 * n + 3)‖ ^ 2) :=
    div_nonneg
      (mul_nonneg (mul_nonneg (le_of_lt evenMass_pos) he)
        (sub_nonneg.mpr henergy))
      (le_of_lt (mul_pos
        (mul_pos (by norm_num : (0 : ℝ) < 2) (projected_energy_pos n))
        (projected_energy_pos (2 * n + 3))))
  have hi := optimizer_dyadic_completion n
  linarith

theorem optimizer_error_dyadic_bound (n : ℕ) :
    ‖optimizer (2 * n + 3) - evenIndicator‖ ^ 2 ≤
      ‖optimizer n - evenIndicator‖ ^ 2 / 2 +
        (hilbertL1Norm (optimizer (2 * n + 3)) - evenMass) := by
  have hi := optimizer_error_dyadic_first_bound n
  have hl := inner_one_sub_first_le_hilbertL1Norm (optimizer (2 * n + 3))
  rw [optimizer_mean] at hl
  linarith


theorem optimizer_l1Norm_tendsto :
    Tendsto (fun n => hilbertL1Norm (optimizer n)) atTop
      (𝓝 (hilbertL1Norm limitOptimizer)) := by
  simpa only [Function.comp_def] using
    (hilbertL1Norm_continuous.tendsto limitOptimizer).comp optimizer_tendsto

/-- A cofinal selection of stages suffices; no full-sequence hypothesis is needed. -/
theorem riemannHypothesis_of_cofinal_l1Norm_tendsto
    (j : ℕ → ℕ) (hj : Tendsto j atTop atTop)
    (h : Tendsto (fun n => hilbertL1Norm (optimizer (j n))) atTop
      (𝓝 evenMass)) : RiemannHypothesis := by
  have he := tendsto_nhds_unique (optimizer_l1Norm_tendsto.comp hj) h
  apply riemannHypothesis_of_l1Norm_tendsto
  simpa only [he, evenMass] using optimizer_l1Norm_tendsto

theorem optimizer_first_negative_tendsto_zero_iff :
    Tendsto (fun n => max (-hilbertSequence (optimizer n) 1) 0) atTop (𝓝 0) ↔
      Tendsto (fun n => hilbertSequence (optimizer n) 1) atTop (𝓝 0) := by
  constructor
  · intro h
    have ht := optimizer_first_tendsto.neg.max (tendsto_const_nhds (x := (0 : ℝ)))
    have hz := tendsto_nhds_unique ht h
    have hp : 0 ≤ -hilbertSequence limitOptimizer 1 :=
      neg_nonneg.mpr limitOptimizer_first_nonpos
    rw [max_eq_left hp] at hz
    have hu : hilbertSequence limitOptimizer 1 = 0 := neg_eq_zero.mp hz
    simpa only [hu] using optimizer_first_tendsto
  · intro h
    simpa using h.neg.max (tendsto_const_nhds (x := (0 : ℝ)))

theorem riemannHypothesis_of_optimizer_first_negative_tendsto_zero
    (h : Tendsto (fun n => max (-hilbertSequence (optimizer n) 1) 0)
      atTop (𝓝 0)) : RiemannHypothesis :=
  riemannHypothesis_of_optimizer_first_tendsto_zero
    (optimizer_first_negative_tendsto_zero_iff.mp h)

/-- A one-sided lower bound at arbitrarily large stages forces the limiting
first coordinate to be nonnegative, hence zero by the unconditional sign. -/
theorem limitResidual_zero_of_cofinal_optimizer_first_lower
    (h : ∀ ε : ℝ, 0 < ε → ∀ n₀ : ℕ,
      ∃ n ≥ n₀, -ε ≤ hilbertSequence (optimizer n) 1) :
    limitResidual = 0 := by
  have hnonneg : 0 ≤ hilbertSequence limitOptimizer 1 := by
    by_contra hn
    have hneg : hilbertSequence limitOptimizer 1 < 0 := lt_of_not_ge hn
    let ε : ℝ := -hilbertSequence limitOptimizer 1 / 2
    have hε : 0 < ε := by
      dsimp only [ε]
      linarith only [hneg]
    have hlimit : hilbertSequence limitOptimizer 1 < -ε := by
      dsimp only [ε]
      linarith only [hneg]
    have hevent : ∀ᶠ n in atTop,
        hilbertSequence (optimizer n) 1 < -ε :=
      optimizer_first_tendsto.eventually (isOpen_Iio.mem_nhds hlimit)
    obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 hevent
    obtain ⟨n, hn, hbound⟩ := h ε hε n₀
    have hsmall := hn₀ n hn
    linarith
  have hzero : hilbertSequence limitOptimizer 1 = 0 :=
    le_antisymm limitOptimizer_first_nonpos hnonneg
  apply optimizer_first_tendsto_zero_iff_residual_zero.mp
  simpa only [hzero] using optimizer_first_tendsto

/-- The approximate cofinal one-point lower bound suffices for RH. -/
theorem riemannHypothesis_of_cofinal_optimizer_first_lower
    (h : ∀ ε : ℝ, 0 < ε → ∀ n₀ : ℕ,
      ∃ n ≥ n₀, -ε ≤ hilbertSequence (optimizer n) 1) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_optimizer_first_tendsto_zero
  exact optimizer_first_tendsto_zero_iff_residual_zero.mpr
    (limitResidual_zero_of_cofinal_optimizer_first_lower h)

/-- In particular, nonnegative first coordinates at arbitrarily large
stages would suffice. This stronger assumption is not asserted to follow
from RH, since convergence to zero need not produce nonnegative terms. -/
theorem riemannHypothesis_of_cofinal_optimizer_first_nonneg
    (h : ∀ n₀ : ℕ, ∃ n ≥ n₀,
      0 ≤ hilbertSequence (optimizer n) 1) : RiemannHypothesis := by
  apply riemannHypothesis_of_cofinal_optimizer_first_lower
  intro ε hε n₀
  obtain ⟨n, hn, hnonneg⟩ := h n₀
  exact ⟨n, hn, le_trans (by linarith) hnonneg⟩

end RiemannResearch.RH.Pareto.CoefficientStabilization.ParityOptimizer
