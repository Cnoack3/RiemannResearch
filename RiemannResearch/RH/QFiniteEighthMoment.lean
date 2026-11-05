/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QFiniteEighthForcing
import RiemannResearch.RH.QSubcriticalDisplacementMoment
import RiemannResearch.RH.QSquarefreeFiniteDisplacement
import RiemannResearch.RH.QSquarefreeCapacity
import RiemannResearch.RH.QSquarefreeDisplacementRigidity
import RiemannResearch.RH.QHilbertConvergence
import RiemannResearch.RH.QShiftedReciprocal
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! # An eighth-moment criterion on aligned finite projection heads

Source: the user's finite-head argument. The arithmetic input is subcritical
approximation in physical L^(8 / 7)(Q). J. Lee's natural approximation is
described by L. Báez-Duarte, https://arxiv.org/abs/math/0011254, §1,
(1.12), (1.17). The strict zero-free margin used to specialize the literature
is reported in B. Liu, https://arxiv.org/abs/2610.12234v2. We keep this input
explicit. The cofinal bound for the actual finite projections is open.
-/

noncomputable section
open Filter
open scoped Topology BigOperators ENNReal
namespace RiemannResearch.RH.QSquarefreeFiniteDisplacement
open ZetaTwoHilbert ZetaTwoProbability QSquarefreeDisplacementRigidity
open ZetaTwoOptimizerStage QShiftedReciprocal

/-- Unnormalized physical eighth moment through coordinate N. The zero term vanishes. -/
def eighthHead (v : QHilbert) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), |qSequence v n| ^ 8 / (n : ℝ) ^ 2

/-- Convert the handoff's unnormalized moment to the physical probability weights. -/
theorem eighthHead_eq_weighted (v : QHilbert) (H : ℕ) :
    eighthHead v H = zetaTwo * ∑ n ∈ Finset.Icc 1 H, positiveQWeight n * (qSequence v n)^8 := by
  classical
  have hi : Finset.range (H + 1) = insert 0 (Finset.Icc 1 H) := by
    ext n
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [eighthHead, hi, Finset.sum_insert (by simp), Finset.mul_sum]
  simp only [qSequence_zero, abs_zero, zero_pow (by decide : 8 ≠ 0), zero_div, zero_add]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Even.pow_abs (by decide : Even 8), positiveQWeight]
  field_simp [zetaTwo_pos.ne', (show (n : ℝ) ≠ 0 by
    exact_mod_cast (show n ≠ 0 from Nat.ne_of_gt (Finset.mem_Icc.mp hn).1))]

private def eighthScaledCoord (v : QHilbert) (n : ℕ) : ℝ :=
  qSequence v n / Real.sqrt (Real.sqrt (n : ℝ))

private theorem eighthScaledCoord_add (v w : QHilbert) (n : ℕ) :
    eighthScaledCoord (v + w) n = eighthScaledCoord v n + eighthScaledCoord w n := by
  have hvw : qSequence (v + w) n = qSequence v n + qSequence w n :=
    congrFun (qSequenceLinear.map_add v w) n
  simp only [eighthScaledCoord, hvw, add_div]

private theorem scaled_eighth_sum_eq (v : QHilbert) (H : ℕ) :
    (∑ n ∈ Finset.range (H + 1), |eighthScaledCoord v n| ^ (8 : ℝ)) = eighthHead v H := by
  unfold eighthHead
  apply Finset.sum_congr rfl
  intro n _
  have hw : (Real.sqrt (Real.sqrt (n : ℝ))) ^ 8 = (n : ℝ) ^ 2 := by
    calc
      _ = (((Real.sqrt (Real.sqrt (n : ℝ))) ^ 2) ^ 2) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt (Nat.cast_nonneg n)]
  rw [eighthScaledCoord, abs_div, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.rpow_ofNat, div_pow, hw]

/-- Weighted finite Minkowski for the unnormalized eighth head. -/
theorem eighthHead_root_add_le (v w : QHilbert) (H : ℕ) :
    (eighthHead (v + w) H) ^ (1 / 8 : ℝ) ≤
      (eighthHead v H) ^ (1 / 8 : ℝ) + (eighthHead w H) ^ (1 / 8 : ℝ) := by
  simpa only [← eighthScaledCoord_add, scaled_eighth_sum_eq] using
    (Real.Lp_add_le (Finset.range (H + 1)) (eighthScaledCoord v) (eighthScaledCoord w)
      (p := (8 : ℝ)) (by norm_num))

/-- Replacing a fitted vector changes the eighth-root statistic by at most
    the eighth root of the aligned physical error. -/
theorem abs_eighthHead_root_sub_le (v w : QHilbert) (H : ℕ) :
    |(eighthHead v H) ^ (1 / 8 : ℝ) - (eighthHead w H) ^ (1 / 8 : ℝ)| ≤
      (eighthHead (v - w) H) ^ (1 / 8 : ℝ) := by
  have hswap : eighthHead (w - v) H = eighthHead (v - w) H := by
    unfold eighthHead
    apply Finset.sum_congr rfl
    intro n _
    have h₁ : qSequence (w - v) n = qSequence w n - qSequence v n :=
      congrFun (qSequenceLinear.map_sub w v) n
    have h₂ : qSequence (v - w) n = qSequence v n - qSequence w n :=
      congrFun (qSequenceLinear.map_sub v w) n
    rw [h₁, h₂, abs_sub_comm]
  have hv := eighthHead_root_add_le (v - w) w H
  have hw := eighthHead_root_add_le (w - v) v H
  rw [sub_add_cancel] at hv
  rw [sub_add_cancel, hswap] at hw
  exact abs_le.mpr ⟨by linarith only [hw], by linarith only [hv]⟩

/-- Vanishing physical head error gives a vanishing difference of the
    eighth roots at aligned stages. -/
theorem eighthHead_root_sub_tendsto {v w : ℕ → QHilbert}
    (h : Tendsto (fun n => eighthHead (v n - w n) n) atTop (𝓝 0)) :
    Tendsto (fun n => (eighthHead (v n) n) ^ (1 / 8 : ℝ) -
      (eighthHead (w n) n) ^ (1 / 8 : ℝ)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun n => by simpa only [Real.norm_eq_abs] using abs_eighthHead_root_sub_le (v n) (w n) n)
    (h.rpow_const_nhds_zero (by norm_num : (0 : ℝ) < 1 / 8))

/-- Cofinal boundedness of the *original*, unrooted statistics is equivalent
    across an aligned replacement with vanishing head error. -/
theorem frequently_eighthHead_bounded_iff_of_error {v w : ℕ → QHilbert}
    (h : Tendsto (fun n => eighthHead (v n - w n) n) atTop (𝓝 0)) :
    (∃ C : ℝ, ∃ᶠ n : ℕ in atTop, eighthHead (v n) n ≤ C) ↔
      ∃ C : ℝ, ∃ᶠ n : ℕ in atTop, eighthHead (w n) n ≤ C := by
  let R (u : ℕ → QHilbert) (n : ℕ) := (eighthHead (u n) n) ^ (1 / 8 : ℝ)
  have hnon (u : ℕ → QHilbert) (n : ℕ) : 0 ≤ eighthHead (u n) n := by
    unfold eighthHead
    exact Finset.sum_nonneg (fun _ _ => by positivity)
  have hclose : ∀ᶠ n : ℕ in atTop, |R v n - R w n| < 1 := by
    have hc := (eighthHead_root_sub_tendsto h).abs
    have hzero : Tendsto (fun n => |R v n - R w n|) atTop (𝓝 0) := by simpa [R] using hc
    exact hzero.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have transfer (x y : ℕ → QHilbert) (hxy : ∀ᶠ n : ℕ in atTop, R y n ≤ R x n + 1)
      (hx : ∃ C : ℝ, ∃ᶠ n : ℕ in atTop, eighthHead (x n) n ≤ C) :
      ∃ D : ℝ, ∃ᶠ n : ℕ in atTop, eighthHead (y n) n ≤ D := by
    obtain ⟨C, hC⟩ := hx
    refine ⟨(C ^ (1 / 8 : ℝ) + 1) ^ 8, (hC.and_eventually hxy).mono ?_⟩
    intro n hn
    have hr : R y n ≤ C ^ (1 / 8 : ℝ) + 1 := hn.2.trans
      (add_le_add (Real.rpow_le_rpow (hnon x n) hn.1 (by norm_num : (0 : ℝ) ≤ 1 / 8)) le_rfl)
    have hp : 0 ≤ R y n := Real.rpow_nonneg (hnon y n) _
    calc
      eighthHead (y n) n = (R y n) ^ 8 := by
        simpa only [R, one_div, Nat.cast_ofNat] using
          (Real.rpow_inv_natCast_pow (hnon y n) (by decide : (8 : ℕ) ≠ 0)).symm
      _ ≤ _ := pow_le_pow_left₀ hp hr _
  constructor
  · exact transfer v w (hclose.mono fun n hn => by linarith only [(abs_lt.mp hn).1])
  · exact transfer w v (hclose.mono fun n hn => by linarith only [(abs_lt.mp hn).2])

/-- A cofinal bound on aligned heads controls every fixed limiting partial sum. -/
theorem summable_eighth_of_frequent_diagonal {v : ℕ → QHilbert} {u : QHilbert}
    (hv : Tendsto v atTop (𝓝 u)) (C : ℝ)
    (h : ∃ᶠ N : ℕ in atTop, eighthHead (v N) N ≤ C) :
    Summable (fun n : ℕ => positiveQWeight n * |qSequence u n| ^ 8) := by
  have hs : Summable (fun n : ℕ => |qSequence u n| ^ 8 / (n : ℝ) ^ 2) := by
    apply summable_of_sum_range_le (c := C) (fun n => by positivity)
    intro K
    by_contra! hbad
    have ht : Tendsto (fun N => ∑ n ∈ Finset.range K,
        |qSequence (v N) n| ^ 8 / (n : ℝ) ^ 2) atTop
        (𝓝 (∑ n ∈ Finset.range K, |qSequence u n| ^ 8 / (n : ℝ) ^ 2)) := by
      apply tendsto_finsetSum
      intro n _
      exact ((qSequence_tendsto_of_tendsto hv n).abs.pow 8).div_const _
    have he := ht.eventually (Ioi_mem_nhds hbad)
    obtain ⟨N, ⟨hN, hKN⟩, hgt⟩ :=
      ((h.and_eventually (eventually_ge_atTop K)).and_eventually he).exists
    have hle : (∑ n ∈ Finset.range K, |qSequence (v N) n| ^ 8 / (n : ℝ) ^ 2)
        ≤ eighthHead (v N) N := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      intros
      positivity
    exact (not_lt_of_ge (hle.trans hN)) hgt
  apply (hs.mul_left (1 / zetaTwo)).congr
  intro n
  simp [positiveQWeight, div_eq_mul_inv, mul_comm, mul_assoc]

/-- The arithmetic approximation input, stated just for the squarefree closure.
Any legal sequence converging to one in physical L^(8 / 7)(Q) supplies it. -/
def HasSubcriticalApproximation : Prop :=
  ∃ G : ℕ → QHilbert, (∀ j, G j ∈ closure) ∧
    (∀ j, Summable (fun n => positiveQWeight n *
      |qSequence (qOne - G j) n| ^ (8 / 7 : ℝ))) ∧
    Tendsto (fun j => (∑' n, positiveQWeight n *
      |qSequence (qOne - G j) n| ^ (8 / 7 : ℝ)) ^ (7 / 8 : ℝ)) atTop (𝓝 0)

/-- Physical L^(8/7) approximation kills the mean of each L^8 annihilator. -/
theorem annihilator_mean_zero_of_eighth (happrox : HasSubcriticalApproximation)
    (w : QHilbert) (hw : w ∈ closureᗮ)
    (hsw : Summable fun n => positiveQWeight n * |qSequence w n| ^ 8) :
    inner ℝ qOne w = 0 := by
  apply annihilator_mean_zero_of_conjugate_moment
    (Real.holderConjugate_iff.mpr (by norm_num) : (8 / 7 : ℝ).HolderConjugate 8)
    _ w hw
  · simpa using hsw
  · simpa only [HasPhysicalApproximationAt, HasSubcriticalApproximation,
      show (1 / (8 / 7) : ℝ) = 7 / 8 by norm_num] using happrox

/-- The dual eighth moment suffices under the physical subcritical approximation. -/
theorem riemannHypothesis_of_displacement_eighth (happrox : HasSubcriticalApproximation)
    (hd : Summable fun n => positiveQWeight n * |qSequence displacement n| ^ 8) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_displacement_conjugate_moment
    (Real.holderConjugate_iff.mpr (by norm_num) : (8 / 7 : ℝ).HolderConjugate 8)
  · simpa only [HasPhysicalApproximationAt, HasSubcriticalApproximation,
      show (1 / (8 / 7) : ℝ) = 7 / 8 by norm_num] using happrox
  · simpa using hd

/-- The aligned finite-head liminf, taken in the extended nonnegative reals. -/
theorem riemannHypothesis_of_finite_eighth_liminf (happrox : HasSubcriticalApproximation)
    (h : liminf (fun N : ℕ =>
      (Real.nnabs (eighthHead (finiteDisplacement N) N) : ℝ≥0∞)) atTop < ⊤) :
    RiemannHypothesis := by
  obtain ⟨C, hC⟩ := ENNReal.exists_frequently_lt_of_liminf_ne_top h.ne
  exact riemannHypothesis_of_displacement_eighth happrox
    (summable_eighth_of_frequent_diagonal finiteDisplacement_tendsto C (hC.mono fun _ hN => hN.le))

/-- For sufficiency alone the input head may grow arbitrarily slowly.
The physical output is still tested through its aligned projection stage. -/
theorem riemannHypothesis_of_truncated_forcing_eighth_liminf
    (happrox : HasSubcriticalApproximation) (T : ℕ → ℕ) (hT : Tendsto T atTop atTop)
    (h : liminf (fun N : ℕ =>
      (Real.nnabs (eighthHead (projectedFiniteForcing N (T N)) N) : ℝ≥0∞)) atTop < ⊤) :
    RiemannHypothesis := by
  obtain ⟨C, hC⟩ := ENNReal.exists_frequently_lt_of_liminf_ne_top h.ne
  apply riemannHypothesis_of_displacement_eighth happrox
  exact summable_eighth_of_frequent_diagonal (projectedFiniteForcing_tendsto T hT) C
    (hC.mono fun _ hN => hN.le)

end RiemannResearch.RH.QSquarefreeFiniteDisplacement
