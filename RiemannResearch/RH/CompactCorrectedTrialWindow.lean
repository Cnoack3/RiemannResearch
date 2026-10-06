import RiemannResearch.RH.ParetoCompactHead
import RiemannResearch.RH.CompactShiftedMobiusSource
import RiemannResearch.RH.CanonicalMobiusConditionalHead
import RiemannResearch.RH.ReciprocalChargeDilationArithmetic
import RiemannResearch.RH.CompensatedTwoCoefficientCriterion
import RiemannResearch.RH.CanonicalMobiusFullEnergy
import RiemannResearch.RH.ParetoFiniteWindowEnergy
import RiemannResearch.RH.CompactTargetMellinObstruction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Explicit compact-target corrected lifts and complete finite certificates

Source: user-provided Green--Pareto--Schur continuation, 6 October 2026,
Section 25 (source inversion, trial and proof strategy). The RH consumer
keeps cofinal selected cutoffs and subpolynomial window growth explicit.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.Pareto.CoefficientStabilization
open RiemannResearch.RH.ArithmeticCumulative
open RiemannResearch.NumberTheory

def compactStepTarget (j : ℕ) : ℝ :=
  14 * (if j = 0 then 0 else 1)
    - 26 * (if j / 2 = 0 then 0 else 1)
    + 12 * (if j / 4 = 0 then 0 else 1)

theorem twoThreeDual_sequence (j : ℕ) :
    hilbertSequence twoThreeDual j = compactStepTarget j := by
  rw [twoThreeDual, twoThreeRiesz_eq_dilation, doubleDilation_twice]
  simp only [hilbertSequence_add, hilbertSequence_sub, hilbertSequence_smul,
    doubleDilation, hilbertDilationContinuous_apply, hilbertDilation_sequence,
    hilbertOne_sequence, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  simp [compactStepTarget, dilation, zeroAnchor]
  ring_nf

theorem compactStepTarget_eq_zero (j : ℕ) (hj : 4 ≤ j) :
    compactStepTarget j = 0 := by
  have h0 : j ≠ 0 := by omega
  have h2 : j / 2 ≠ 0 := by omega
  have h4 : j / 4 ≠ 0 := by omega
  norm_num [compactStepTarget, h0, h2, h4]

theorem finite_shifted_moebius_floor_sum
    (Y j h : ℕ) (hh : 0 < h) (hjY : j ≤ Y) :
    (∑ d ∈ Finset.Icc 1 Y,
      (if h ∣ d then (ArithmeticFunction.moebius (d / h) : ℝ) else 0)
        * ((j / d : ℕ) : ℝ)) =
      if j / h = 0 then 0 else 1 := by
  have he (d : ℕ) :
      (if h ∣ d then (ArithmeticFunction.moebius (d / h) : ℝ) else 0)
          * ((j / d : ℕ) : ℝ) =
        if h ∣ d then
          (ArithmeticFunction.moebius (d / h) : ℝ)
            * (((j / h) / (d / h) : ℕ) : ℝ)
        else 0 := by
    by_cases hd : h ∣ d
    · have hq : (j / h) / (d / h) = j / d := by
        rw [Nat.div_div_eq_div_mul, Nat.mul_div_cancel' hd]
      simp [hd, hq]
    · simp [hd]
  simp_rw [he]
  rw [positive_dilation_sum Y h hh
    (fun r => (ArithmeticFunction.moebius r : ℝ) * (((j / h) / r : ℕ) : ℝ))]
  by_cases hz : j / h = 0
  · simp [hz]
  · rw [if_neg hz]
    exact finite_mobius_floor_sum (Y / h) (j / h)
      (Nat.pos_of_ne_zero hz) (Nat.div_le_div_right hjY)

theorem finite_compactShiftedMobius_floor_sum
    (Y j : ℕ) (hjY : j ≤ Y) :
    (∑ d ∈ Finset.Icc 1 Y,
      compactShiftedMobius d * ((j / d : ℕ) : ℝ)) = compactStepTarget j := by
  have h1 : (∑ d ∈ Finset.Icc 1 Y,
      (ArithmeticFunction.moebius d : ℝ) * ((j / d : ℕ) : ℝ)) =
        if j = 0 then 0 else 1 := by
    simpa using finite_shifted_moebius_floor_sum Y j 1 (by decide) hjY
  simp only [compactShiftedMobius_formula, add_mul, sub_mul, mul_assoc,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [h1, finite_shifted_moebius_floor_sum Y j 2 (by decide) hjY,
    finite_shifted_moebius_floor_sum Y j 4 (by decide) hjY]
  rfl

def compactReciprocalSum (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N, compactShiftedMobius d / (d : ℝ)

def compactCorrectedTrial (N j : ℕ) : ℝ :=
  -(∑ d ∈ Finset.Icc 1 N, compactShiftedMobius d * residueFraction d j)
    + (N : ℝ) * compactReciprocalSum N * residueFraction N j

theorem compact_residue_prefix_identity (N j : ℕ) (hjN : j ≤ N) :
    (∑ d ∈ Finset.Icc 1 N, compactShiftedMobius d * residueFraction d j) =
      (j : ℝ) * compactReciprocalSum N - compactStepTarget j := by
  calc
    _ = ∑ d ∈ Finset.Icc 1 N,
        ((j : ℝ) * (compactShiftedMobius d / (d : ℝ)) -
          compactShiftedMobius d * ((j / d : ℕ) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [residueFraction_eq_div_sub_floor d j (Finset.mem_Icc.mp hd).1]
      ring
    _ = _ := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum,
        finite_compactShiftedMobius_floor_sum N j hjN]
      rfl

theorem compactCorrectedTrial_exact_head (N j : ℕ)
    (hjN : j < N) : compactCorrectedTrial N j = compactStepTarget j := by
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  unfold compactCorrectedTrial
  rw [compact_residue_prefix_identity N j hjN.le]
  unfold residueFraction
  rw [Nat.mod_eq_of_lt hjN]
  field_simp [hNR]
  ring

theorem compactCorrectedTrial_endpoint (N : ℕ) :
    compactStepTarget N - compactCorrectedTrial N N =
      (N : ℝ) * compactReciprocalSum N := by
  unfold compactCorrectedTrial
  rw [compact_residue_prefix_identity N N (le_refl _)]
  simp [residueFraction, Nat.mod_self]

theorem compactCorrectedTrial_actual_head (N j : ℕ) (hjN : j < N) :
    compactCorrectedTrial N j = hilbertSequence twoThreeDual j := by
  rw [compactCorrectedTrial_exact_head N j hjN,
    twoThreeDual_sequence]

theorem compactCorrectedTrial_abs_le (N j : ℕ)
    (hN : 0 < N) (hsmall : |compactReciprocalSum N| ≤ 20 / (N : ℝ)) :
    |compactCorrectedTrial N j| ≤ 40 * (N : ℝ) := by
  classical
  have h1 : 1 ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨le_refl _, hN⟩
  have hsplit := Finset.sum_erase_add (s := Finset.Icc 1 N)
    (f := fun d => compactShiftedMobius d * residueFraction d j) h1
  have hg1 : residueFraction 1 j = 0 := by simp [residueFraction, Nat.mod_one]
  rw [hg1, mul_zero, add_zero] at hsplit
  have hcard : ((Finset.Icc 1 N).erase 1).card = N - 1 := by
    rw [Finset.card_erase_of_mem h1]
    simp [Nat.card_Icc]
  have hraw : |∑ d ∈ Finset.Icc 1 N,
      compactShiftedMobius d * residueFraction d j| ≤ 40 * ((N : ℝ) - 1) := by
    rw [← hsplit]
    calc
      _ ≤ ∑ d ∈ (Finset.Icc 1 N).erase 1,
          |compactShiftedMobius d * residueFraction d j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _d ∈ (Finset.Icc 1 N).erase 1, (40 : ℝ) := by
        apply Finset.sum_le_sum
        intro d hd
        rw [abs_mul]
        calc
          _ ≤ 40 * 1 := mul_le_mul (compactShiftedMobius_abs_le_forty d)
            (residueFraction_abs_le_one d j
              (Finset.mem_Icc.mp (Finset.mem_of_mem_erase hd)).1)
            (abs_nonneg _) (by norm_num)
          _ = 40 := by norm_num
      _ = _ := by
        simp only [Finset.sum_const, nsmul_eq_mul, hcard]
        rw [Nat.cast_sub (by omega : 1 ≤ N)]
        ring
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hcharge : |(N : ℝ) * compactReciprocalSum N| ≤ 20 := by
    rw [abs_mul, abs_of_pos hNR]
    calc
      _ ≤ (N : ℝ) * (20 / (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hsmall hNR.le
      _ = 20 := by field_simp [ne_of_gt hNR]
  have hcorrection :
      |(N : ℝ) * compactReciprocalSum N * residueFraction N j| ≤ 20 := by
    rw [abs_mul]
    calc
      _ ≤ 20 * 1 := mul_le_mul hcharge
        (residueFraction_abs_le_one N j hN) (abs_nonneg _) (by norm_num)
      _ = 20 := by norm_num
  unfold compactCorrectedTrial
  calc
    _ ≤ |-(∑ d ∈ Finset.Icc 1 N,
        compactShiftedMobius d * residueFraction d j)| +
        |(N : ℝ) * compactReciprocalSum N * residueFraction N j| := abs_add_le _ _
    _ ≤ 40 * ((N : ℝ) - 1) + 20 := by
      rw [abs_neg]
      exact add_le_add hraw hcorrection
    _ ≤ 40 * (N : ℝ) := by linarith

def compactCorrectedHilbert (N : ℕ) (hN : 0 < N) : ThresholdHilbert :=
  -(∑ d ∈ (Finset.Icc 1 N).attach,
      compactShiftedMobius d •
        normalizedResidueHilbert d (Finset.mem_Icc.mp d.property).1) +
    ((N : ℝ) * compactReciprocalSum N) • normalizedResidueHilbert N hN

theorem compactCorrectedHilbert_sequence (N : ℕ) (hN : 0 < N) :
    hilbertSequence (compactCorrectedHilbert N hN) = compactCorrectedTrial N := by
  change hilbertSequenceLinear (compactCorrectedHilbert N hN) = _
  unfold compactCorrectedHilbert
  simp only [map_add, map_neg, map_sum, map_smul]
  change -(∑ d ∈ (Finset.Icc 1 N).attach,
      compactShiftedMobius d •
        hilbertSequence (normalizedResidueHilbert d (Finset.mem_Icc.mp d.property).1)) +
    ((N : ℝ) * compactReciprocalSum N) •
      hilbertSequence (normalizedResidueHilbert N hN) = _
  simp_rw [normalizedResidueHilbert_sequence]
  funext j
  simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_apply, compactCorrectedTrial]
  rw [Finset.sum_attach (Finset.Icc 1 N)
    (fun d : ℕ => compactShiftedMobius d * residueFraction d j)]

theorem compactCorrectedHilbert_mem_finiteSpace
    (N : ℕ) (hN : 0 < N) : compactCorrectedHilbert N hN ∈ finiteSpace N := by
  unfold compactCorrectedHilbert
  apply (finiteSpace N).add_mem
  · apply (finiteSpace N).neg_mem
    apply (finiteSpace N).sum_mem
    intro d hd
    apply (finiteSpace N).smul_mem
    apply normalizedResidueHilbert_mem_finiteSpace
    have hh := (Finset.mem_Icc.mp d.property).2
    omega
  · apply (finiteSpace N).smul_mem
    exact normalizedResidueHilbert_mem_finiteSpace N N hN (by omega)

theorem compactCorrectedHilbert_mem_closedSpace
    (N : ℕ) (hN : 0 < N) : compactCorrectedHilbert N hN ∈ closedSpace := by
  apply (Submodule.le_topologicalClosure _)
  exact RiemannResearch.Analysis.ExhaustiveWalk.walkSpan_le residueAtom id N
    (compactCorrectedHilbert_mem_finiteSpace N hN)

theorem compactCorrectedHilbert_mem_legalClosure
    (N : ℕ) (hN : 0 < N) :
    compactCorrectedHilbert N hN ∈ hilbertLegalClosure {d : ℕ | 0 < d} :=
  closedSpace_le_legalClosure (compactCorrectedHilbert_mem_closedSpace N hN)

theorem compactCorrectedHilbert_exact_head
    (N : ℕ) (hN : 0 < N) (j : ℕ) (hjN : j < N) :
    hilbertSequence (compactCorrectedHilbert N hN) j =
      hilbertSequence twoThreeDual j := by
  rw [compactCorrectedHilbert_sequence]
  exact compactCorrectedTrial_actual_head N j hjN

def compactWindowCertificate (N : ℕ) : ℝ :=
  FiniteWindow.windowEnergy N (fun j => compactStepTarget j - compactCorrectedTrial N j)

theorem compactWindowCertificate_nonneg (N : ℕ) :
    0 ≤ compactWindowCertificate N := FiniteWindow.windowEnergy_nonneg N _

theorem compactWindowCertificate_eq_actual (N : ℕ) (hN : 0 < N) :
    compactWindowCertificate N = FiniteWindow.windowEnergy N
      (hilbertSequence (twoThreeDual - compactCorrectedHilbert N hN)) := by
  unfold compactWindowCertificate
  congr 1
  funext j
  rw [hilbertSequence_sub, compactCorrectedHilbert_sequence]
  simp only [Pi.sub_apply]
  rw [twoThreeDual_sequence]

theorem compactCorrectedHilbert_norm_window_bounds
    (N : ℕ) (hN4 : 4 ≤ N)
    (hsmall : |compactReciprocalSum N| ≤ 20 / (N : ℝ)) :
    compactWindowCertificate N ≤
        ‖twoThreeDual - compactCorrectedHilbert N (by omega)‖^2 ∧
      ‖twoThreeDual - compactCorrectedHilbert N (by omega)‖^2 ≤
        compactWindowCertificate N + 1600 := by
  let hN : 0 < N := by omega
  let e := twoThreeDual - compactCorrectedHilbert N hN
  have hhead : ∀ j < N, hilbertSequence e j = 0 := by
    intro j hj
    dsimp [e]
    rw [hilbertSequence_sub]
    simp only [Pi.sub_apply]
    rw [compactCorrectedHilbert_exact_head N hN j hj]
    ring
  have ht : ∀ j, N * N ≤ j → |hilbertSequence e j| ≤ 40 * (N : ℝ) := by
    intro j hj
    have hj4 : 4 ≤ j := hN4.trans ((Nat.le_mul_self N).trans hj)
    dsimp [e]
    rw [hilbertSequence_sub, compactCorrectedHilbert_sequence]
    simp only [Pi.sub_apply]
    rw [twoThreeDual_sequence, compactStepTarget_eq_zero j hj4,
      zero_sub, abs_neg]
    exact compactCorrectedTrial_abs_le N j hN hsmall
  have hfar := FiniteWindow.farEnergy_le_sq_of_tail_bound e N hN 40 ht
  norm_num at hfar
  have heq := FiniteWindow.norm_sq_eq_window_add_far e N hhead
  have hcert : compactWindowCertificate N =
      FiniteWindow.windowEnergy N (hilbertSequence e) :=
    compactWindowCertificate_eq_actual N hN
  rw [← hcert] at heq
  have hfar0 := FiniteWindow.farEnergy_nonneg N (hilbertSequence e)
  change compactWindowCertificate N ≤ ‖e‖^2 ∧
    ‖e‖^2 ≤ compactWindowCertificate N + 1600
  constructor <;> linarith

open Filter
open scoped Topology

theorem riemannHypothesis_of_cofinal_compactCorrectedTrial_subpolynomial
    (n : ℕ → ℕ) (hn4 : ∀ i, 4 ≤ n i)
    (hn : Tendsto (fun i => (n i : ℝ)) atTop atTop)
    (hsmall : ∀ i, |compactReciprocalSum (n i)| ≤ 20 / (n i : ℝ))
    (hsub : Tendsto (fun i =>
      Real.log (1 + compactWindowCertificate (n i)) / Real.log (n i : ℝ))
      atTop (𝓝 0)) : RiemannHypothesis := by
  apply riemannHypothesis_of_cofinal_compact_exact_head_subpolynomial
    {d : ℕ | 0 < d} (fun _ hd => hd)
    (fun i => compactCorrectedHilbert (n i) (by have := hn4 i; omega))
    n (fun i => compactWindowCertificate (n i)) 1600 hn
  · intro i
    exact compactCorrectedHilbert_mem_legalClosure (n i) _
  · intro i j hj hjn
    exact compactCorrectedHilbert_exact_head (n i) _ j hjn
  · exact fun i => compactWindowCertificate_nonneg (n i)
  · norm_num
  · exact fun i => (compactCorrectedHilbert_norm_window_bounds
      (n i) (hn4 i) (hsmall i)).2
  · exact hsub

end RiemannResearch.RH.Pareto.CoefficientStabilization

namespace RiemannResearch.RH.Pareto.CoefficientStabilization

theorem compact_boundaryCharge_abs_le (N : ℕ) (hN : 0 < N)
    (hsmall : |compactReciprocalSum N| ≤ 20 / (N : ℝ)) :
    |(N : ℝ) * compactReciprocalSum N| ≤ 20 := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  rw [abs_mul, abs_of_pos hNR]
  calc
    _ ≤ (N : ℝ) * (20 / (N : ℝ)) :=
      mul_le_mul_of_nonneg_left hsmall hNR.le
    _ = 20 := by field_simp [ne_of_gt hNR]

theorem compact_endpointEnergy_le_small (N : ℕ) (hN : 0 < N)
    (hsmall : |compactReciprocalSum N| ≤ 20 / (N : ℝ)) :
    positiveWeight N * (compactStepTarget N - compactCorrectedTrial N N)^2 ≤
      400 / ((N : ℝ) * ((N : ℝ) + 1)) := by
  rw [compactCorrectedTrial_endpoint]
  have hh := abs_le.mp (compact_boundaryCharge_abs_le N hN hsmall)
  have hp :
      0 ≤ (20 - (N : ℝ) * compactReciprocalSum N) *
        (20 + (N : ℝ) * compactReciprocalSum N) :=
    mul_nonneg (by linarith [hh.2]) (by linarith [hh.1])
  have hsq : ((N : ℝ) * compactReciprocalSum N)^2 ≤ 400 := by
    nlinarith [hp]
  calc
    _ ≤ positiveWeight N * 400 :=
      mul_le_mul_of_nonneg_left hsq (positiveWeight_nonneg N)
    _ = _ := by unfold positiveWeight; ring

/-- The actual orthogonal head Q_N has exactly the reciprocal boundary charge. -/
theorem compactCorrectedHilbert_head_norm_sq_eq_boundary
    (N : ℕ) (hN : 0 < N) :
    ‖compactHead N (twoThreeDual - compactCorrectedHilbert N hN)‖^2 =
      positiveWeight N * ((N : ℝ) * compactReciprocalSum N)^2 := by
  let f := twoThreeDual - compactCorrectedHilbert N hN
  have hhead : ∀ j < N, hilbertSequence f j = 0 := by
    intro j hj
    dsimp [f]
    rw [hilbertSequence_sub]
    simp only [Pi.sub_apply]
    rw [compactCorrectedHilbert_exact_head N hN j hj]
    ring
  have heN : hilbertSequence f N =
      compactStepTarget N - compactCorrectedTrial N N := by
    dsimp [f]
    rw [hilbertSequence_sub, compactCorrectedHilbert_sequence]
    simp only [Pi.sub_apply]
    rw [twoThreeDual_sequence]
  change ‖compactHead N f‖^2 = _
  rw [compactHead_norm_sq_eq_endpoint N f hhead, heN,
    compactCorrectedTrial_endpoint]

/-- Formula 69 applies to the actual orthogonal head Q_N. -/
theorem compactCorrectedHilbert_head_norm_sq_le_small
    (N : ℕ) (hN : 0 < N)
    (hsmall : |compactReciprocalSum N| ≤ 20 / (N : ℝ)) :
    ‖compactHead N (twoThreeDual - compactCorrectedHilbert N hN)‖^2 ≤
      400 / ((N : ℝ) * ((N : ℝ) + 1)) := by
  rw [compactCorrectedHilbert_head_norm_sq_eq_boundary]
  have he := compact_endpointEnergy_le_small N hN hsmall
  rw [compactCorrectedTrial_endpoint] at he
  exact he

end RiemannResearch.RH.Pareto.CoefficientStabilization
