/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.MeanOneRepair
import RiemannResearch.RH.SquarefreeParetoTransfer
import RiemannResearch.RH.ArithmeticCoreRHCriterion
import RiemannResearch.RH.PhysicalCoreMonotonicity
import RiemannResearch.RH.SquarefreeStageExhaustion
import RiemannResearch.RH.SquarefreePacketBasis
import RiemannResearch.RH.MeanOneThirtyTrial

/-!
# Squarefree physical approximation and arithmetic saturation geometry

The complete centered continuum error, actual Hilbert error, unrestricted
squarefree packet closure, and ordinary mean-one squarefree packet closure
are identified here. Actual stage charge convergence is equivalent to
vanishing actual constrained error. These are geometric and scalar bridges.

The analytic RH-to-squarefree-approximation direction remains a separate
explicit hypothesis wherever used. Neither the unconditional half-damped
Möbius convergence nor coefficient support supplies this missing theorem.
Source: Bagchi, `On Nyman, Beurling and Baez-Duarte's Hilbert space
reformulation of the Riemann hypothesis`, Remarks 4 and 8,
https://arxiv.org/abs/math/0607733; user-directed continuation of
`CriticalZeroMeanOneAdvance20261008.md`, Sections 4 and 5.
-/

namespace RiemannResearch.RH.Pareto.SquarefreeArithmeticSaturation
noncomputable section
open Filter
open scoped BigOperators Topology
open MeanOneRepair BaezDuarte SquarefreeTransfer ArithmeticCoreInertia
open SquarefreePacketBasis

theorem one_mem_closure_iff_squared_error (S : Set ThresholdHilbert) :
    hilbertOne ∈ closure S ↔
      ∀ ε : ℝ, 0 < ε → ∃ f : ThresholdHilbert, f ∈ S ∧ ‖hilbertOne - f‖ ^ 2 < ε := by
  constructor
  · intro h ε hε
    obtain ⟨f, hf, he⟩ := Metric.mem_closure_iff.mp h
      (Real.sqrt ε) (Real.sqrt_pos.mpr hε)
    refine ⟨f, hf, ?_⟩
    have hn : ‖hilbertOne - f‖ < Real.sqrt ε := by
      simpa only [dist_eq_norm] using he
    nlinarith [norm_nonneg (hilbertOne - f), Real.sqrt_nonneg ε,
      Real.sq_sqrt hε.le]
  · intro h
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨f, hf, he⟩ := h (ε ^ 2) (sq_pos_of_pos hε)
    refine ⟨f, hf, ?_⟩
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (hilbertOne - f)]

def SquarefreePacketApproximation : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (s : Finset ℕ) (a : ℕ → ℝ),
    (∀ d ∈ s, 0 < d) ∧ (∀ d ∈ s, Squarefree d) ∧
      ‖hilbertOne - finiteResidueSum s a‖ ^ 2 < ε

def MeanOneSquarefreePacketApproximation : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (s : Finset ℕ) (a : ℕ → ℝ),
    (∀ d ∈ s, 0 < d) ∧ (∀ d ∈ s, Squarefree d) ∧
      packetOrdinaryMean s a = 1 ∧ ‖hilbertOne - finiteResidueSum s a‖ ^ 2 < ε

theorem one_mem_squarefree_closure_iff_packetApproximation :
    hilbertOne ∈ closure squarefreePackets ↔ SquarefreePacketApproximation := by
  rw [one_mem_closure_iff_squared_error]
  constructor
  · intro h ε hε
    obtain ⟨f, ⟨s, a, hs, hsf, rfl⟩, he⟩ := h ε hε
    exact ⟨s, a, hs, hsf, he⟩
  · intro h ε hε
    obtain ⟨s, a, hs, hsf, he⟩ := h ε hε
    exact ⟨finiteResidueSum s a, ⟨s, a, hs, hsf, rfl⟩, he⟩

theorem one_mem_meanOne_squarefree_closure_iff_packetApproximation :
    hilbertOne ∈ closure meanOneSquarefreePackets ↔ MeanOneSquarefreePacketApproximation := by
  rw [one_mem_closure_iff_squared_error]
  constructor
  · intro h ε hε
    obtain ⟨f, ⟨s, a, hs, hsf, hm, rfl⟩, he⟩ := h ε hε
    exact ⟨s, a, hs, hsf, hm, he⟩
  · intro h ε hε
    obtain ⟨s, a, hs, hsf, hm, he⟩ := h ε hε
    exact ⟨finiteResidueSum s a, ⟨s, a, hs, hsf, hm, rfl⟩, he⟩

/-- The mean constraint is exactly free at the level of global squarefree
approximation, without a coefficient growth bound or an RH hypothesis. -/
theorem squarefreePacketApproximation_iff_meanOne :
    SquarefreePacketApproximation ↔ MeanOneSquarefreePacketApproximation := by
  rw [← one_mem_squarefree_closure_iff_packetApproximation,
    ← one_mem_meanOne_squarefree_closure_iff_packetApproximation,
    closure_meanOneSquarefreePackets_eq]

theorem squarefreeCenteredApproximation_iff_packetApproximation :
    SquarefreeCenteredApproximation ↔ SquarefreePacketApproximation := by
  constructor
  · intro h ε hε
    obtain ⟨s, a, hs, hsf, he⟩ := h ε hε
    rw [centeredError_eq_hilbert_norm_sq s a hs] at he
    exact ⟨s, a, hs, hsf, (ENNReal.ofReal_lt_ofReal_iff hε).mp he⟩
  · intro h ε hε
    obtain ⟨s, a, hs, hsf, he⟩ := h ε hε
    refine ⟨s, a, hs, hsf, ?_⟩
    rw [centeredError_eq_hilbert_norm_sq s a hs]
    exact (ENNReal.ofReal_lt_ofReal_iff hε).mpr he

theorem squarefreeCenteredApproximation_iff_meanOne :
    SquarefreeCenteredApproximation ↔ MeanOneSquarefreePacketApproximation :=
  squarefreeCenteredApproximation_iff_packetApproximation.trans
    squarefreePacketApproximation_iff_meanOne

theorem riemannHypothesis_of_meanOneSquarefreePacketApproximation
    (h : MeanOneSquarefreePacketApproximation) : RiemannHypothesis :=
  riemannHypothesis_of_squarefreeCenteredApproximation
    (squarefreeCenteredApproximation_iff_meanOne.mpr h)

/-- This explicitly conditional equivalence isolates the genuine analytic
reverse theorem; the displayed provider is not proved in this module. -/
theorem riemannHypothesis_iff_meanOne_of_analytic_reverse
    (hReverse : RiemannHypothesis → SquarefreeCenteredApproximation) :
    RiemannHypothesis ↔ MeanOneSquarefreePacketApproximation := by
  exact ⟨fun hRH => squarefreeCenteredApproximation_iff_meanOne.mp (hReverse hRH),
    riemannHypothesis_of_meanOneSquarefreePacketApproximation⟩

def squarefreeStageError (L : ℕ) : ℝ :=
  1 + 4 * Real.pi / arithmeticInverseCharge L (PhysicalPacketCore.divisorPackets L)

def SquarefreeArithmeticMinima : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ L : ℕ, 2 < L ∧ Squarefree L ∧ squarefreeStageError L < ε

/-- Arbitrarily small errors of actual ordinary mean-one arithmetic stage
packets, retained as a property rather than asserted here. -/
def SquarefreeStageMeanOneApproximation : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (L : ℕ) (c : PhysicalPacketCore.divisorPackets L → ℝ),
    2 < L ∧ Squarefree L ∧
      (∑ r : Fin L, PhysicalPacketCore.synthesis (PhysicalPacketCore.divisorPackets L) c r.val) /
        (L : ℝ) = 1 ∧
      paretoError (PhysicalPacketCore.synthesis (PhysicalPacketCore.divisorPackets L) c) < ε

/-- Taking the actual uniquely attained constrained minimum is equivalent
to the original stage approximation problem, without an analytic input. -/
theorem squarefreeStageMeanOneApproximation_iff_arithmeticMinima :
    SquarefreeStageMeanOneApproximation ↔ SquarefreeArithmeticMinima := by
  constructor
  · intro h ε hε
    obtain ⟨L, c, hL, hsq, hm, he⟩ := h ε hε
    refine ⟨L, hL, hsq, ?_⟩
    exact ((squarefree_stage_optimizer L hL hsq).2.2 c hm).1.trans_lt he
  · intro h ε hε
    obtain ⟨L, hL, hsq, he⟩ := h ε hε
    refine ⟨L, arithmeticConstrainedOptimizer L (PhysicalPacketCore.divisorPackets L),
      hL, hsq, (squarefree_stage_optimizer L hL hsq).1, ?_⟩
    rw [(squarefree_stage_optimizer L hL hsq).2.1]
    exact he

/-- Both finite basis transforms, together with an actual squarefree common
period, identify global ordinary mean-one packets with arithmetic stages.
Neither implication assumes an approximating sequence exists. -/
theorem meanOneSquarefreePacketApproximation_iff_stageMeanOne :
    MeanOneSquarefreePacketApproximation ↔ SquarefreeStageMeanOneApproximation := by
  constructor
  · intro h ε hε
    obtain ⟨s, a, hs, hsq, hm, he⟩ := h ε hε
    obtain ⟨L, hL, hsqL, _, hdiv⟩ :=
      SquarefreeStageExhaustion.finite_squarefree_common_period s hsq
    have hL0 : 0 < L := by omega
    refine ⟨L, packetCoefficients L s a, hL, hsqL, ?_, ?_⟩
    · rw [synthesis_period_mean L (PhysicalPacketCore.divisorPackets L)
        (packetCoefficients L s a) hL0 (PhysicalPacketCore.divisorPackets_legal L)
        (PhysicalPacketCore.divisorPackets_period L),
        packetCoefficients_totient L s a hL0 hs hdiv, hm]
      norm_num
    · rw [residueSum_error_eq_synthesis L s a hL0 hs hdiv]
      exact he
  · intro h ε hε
    obtain ⟨L, c, hL, hsq, hm, he⟩ := h ε hε
    have hL0 : 0 < L := by omega
    refine ⟨L.divisors, residueCoefficients L c,
      (fun _ hd => Nat.pos_of_mem_divisors hd), period_divisors_squarefree L hsq, ?_, ?_⟩
    · rw [residueCoefficients_mean L c hL0]
      rw [synthesis_period_mean L (PhysicalPacketCore.divisorPackets L) c hL0
        (PhysicalPacketCore.divisorPackets_legal L)
        (PhysicalPacketCore.divisorPackets_period L)] at hm
      exact hm
    · rw [← synthesis_error_eq_residueSum L c hL0]
      exact he

/-- The centered squarefree approximation problem is exactly the arithmetic
finite-minimum problem. This proves equivalence of two open assertions. -/
theorem squarefreeCenteredApproximation_iff_arithmeticMinima :
    SquarefreeCenteredApproximation ↔ SquarefreeArithmeticMinima :=
  squarefreeCenteredApproximation_iff_meanOne.trans
    (meanOneSquarefreePacketApproximation_iff_stageMeanOne.trans
      squarefreeStageMeanOneApproximation_iff_arithmeticMinima)

theorem riemannHypothesis_iff_arithmeticMinima_of_analytic_reverse
    (hReverse : RiemannHypothesis → SquarefreeCenteredApproximation) :
    RiemannHypothesis ↔ SquarefreeArithmeticMinima :=
  ⟨fun hRH => squarefreeCenteredApproximation_iff_arithmeticMinima.mp (hReverse hRH),
    fun h => riemannHypothesis_of_meanOneSquarefreePacketApproximation
      (squarefreeCenteredApproximation_iff_meanOne.mp
        (squarefreeCenteredApproximation_iff_arithmeticMinima.mpr h))⟩

theorem riemannHypothesis_of_squarefreeArithmeticMinima
    (h : SquarefreeArithmeticMinima) : RiemannHypothesis :=
  ArithmeticCoreRHCriterion.riemannHypothesis_of_squarefree_arithmeticMinima h

theorem squarefreeStageError_nonneg (L : ℕ) (hL : 2 < L) (hsq : Squarefree L) :
    0 ≤ squarefreeStageError L := by
  rw [squarefreeStageError, ← (squarefree_stage_optimizer L hL hsq).2.1]
  exact paretoInner_self_nonneg _

theorem squarefreeStageError_lt_one (L : ℕ) (hL : 2 < L) (hsq : Squarefree L) :
    squarefreeStageError L < 1 := by
  have hC : arithmeticInverseCharge L (PhysicalPacketCore.divisorPackets L) < 0 :=
    arithmeticInverseCharge_neg L _ (by omega)
      (PhysicalPacketCore.divisorPackets_legal L) (PhysicalPacketCore.divisorPackets_period L)
      (PhysicalPacketCore.divisorPackets_odd L hL hsq)
  have hneg : 4 * Real.pi /
      arithmeticInverseCharge L (PhysicalPacketCore.divisorPackets L) < 0 :=
    div_neg_of_pos_of_neg (by positivity) hC
  unfold squarefreeStageError
  linarith

/-- Exact inversion of the complete constrained error. -/
theorem squarefreeCharge_eq_error_fraction (L : ℕ) (hL : 2 < L) (hsq : Squarefree L) :
    arithmeticInverseCharge L (PhysicalPacketCore.divisorPackets L) =
      4 * Real.pi / (squarefreeStageError L - 1) := by
  have hC : arithmeticInverseCharge L (PhysicalPacketCore.divisorPackets L) ≠ 0 :=
    ne_of_lt (arithmeticInverseCharge_neg L _ (by omega)
      (PhysicalPacketCore.divisorPackets_legal L) (PhysicalPacketCore.divisorPackets_period L)
      (PhysicalPacketCore.divisorPackets_odd L hL hsq))
  have he : squarefreeStageError L - 1 =
      4 * Real.pi / arithmeticInverseCharge L (PhysicalPacketCore.divisorPackets L) := by
    unfold squarefreeStageError
    ring
  rw [he]
  field_simp [hC, ne_of_gt Real.pi_pos]

/-- Vanishing physical stage error and arithmetic charge saturation are
equivalent scalar limits. This theorem provides neither limit. -/
theorem squarefreeCharge_tendsto_iff_error_tendsto
    (L : ℕ → ℕ) (hL : ∀ j, 2 < L j) (hsq : ∀ j, Squarefree (L j)) :
    Tendsto (fun j => arithmeticInverseCharge (L j) (PhysicalPacketCore.divisorPackets (L j)))
      atTop (𝓝 (-4 * Real.pi)) ↔
    Tendsto (fun j => squarefreeStageError (L j)) atTop (𝓝 0) := by
  constructor
  · intro h
    have hn : (-4 * Real.pi : ℝ) ≠ 0 := by positivity
    have hfrac : Tendsto
        (fun j => 4 * Real.pi /
          arithmeticInverseCharge (L j) (PhysicalPacketCore.divisorPackets (L j)))
        atTop (𝓝 (4 * Real.pi / (-4 * Real.pi))) :=
      tendsto_const_nhds.div h hn
    have ht := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add
      hfrac
    have he : (1 : ℝ) + 4 * Real.pi / (-4 * Real.pi) = 0 := by
      field_simp [ne_of_gt Real.pi_pos]
      ring
    simpa only [squarefreeStageError, Pi.add_apply, he] using ht
  · intro h
    have ht : Tendsto (fun j => 4 * Real.pi / (squarefreeStageError (L j) - 1))
        atTop (𝓝 (4 * Real.pi / ((0 : ℝ) - 1))) :=
      tendsto_const_nhds.div (h.sub_const 1) (by norm_num : (0 : ℝ) - 1 ≠ 0)
    have he : 4 * Real.pi / ((0 : ℝ) - 1) = -4 * Real.pi := by ring
    have heq : (fun j => 4 * Real.pi / (squarefreeStageError (L j) - 1)) =
        (fun j => arithmeticInverseCharge (L j) (PhysicalPacketCore.divisorPackets (L j))) := by
      funext j
      exact (squarefreeCharge_eq_error_fraction (L j) (hL j) (hsq j)).symm
    rw [heq] at ht
    simpa only [he] using ht

theorem squarefreeStageError_antitone_of_dvd (L M : ℕ) (hdiv : L ∣ M)
    (hL : 2 < L) (hM : 2 < M) (hsqL : Squarefree L) :
    squarefreeStageError M ≤ squarefreeStageError L := by
  unfold squarefreeStageError
  rw [arithmeticInverseCharge_eq_physical M _ (by omega)
      (PhysicalPacketCore.divisorPackets_legal M) (PhysicalPacketCore.divisorPackets_period M),
    arithmeticInverseCharge_eq_physical L _ (by omega)
      (PhysicalPacketCore.divisorPackets_legal L) (PhysicalPacketCore.divisorPackets_period L)]
  exact PhysicalCoreMonotonicity.constrained_error_antitone
    (PhysicalPacketCore.divisorPackets L) (PhysicalPacketCore.divisorPackets M)
    (PhysicalCoreMonotonicity.divisorPackets_subset_of_dvd L M hdiv (by omega))
    (PhysicalPacketCore.divisorPackets_legal L) (PhysicalPacketCore.divisorPackets_legal M)
    (PhysicalPacketCore.divisorPackets_odd L hL hsqL)

/-- Every exhaustive nested squarefree divisor chain has vanishing optimizer
error exactly when arbitrarily small finite arithmetic minima exist. No
approximation or saturation provider is assumed other than the displayed
property on the corresponding side of the equivalence. -/
theorem arithmeticMinima_iff_exhaustive_chain_error
    (L : ℕ → ℕ) (hL : ∀ n, 2 < L n) (hsq : ∀ n, Squarefree (L n))
    (hdiv : ∀ n m, n ≤ m → L n ∣ L m)
    (hexhaust : ∀ d : ℕ, Squarefree d → ∃ n, d ∣ L n) :
    SquarefreeArithmeticMinima ↔ Tendsto (fun n => squarefreeStageError (L n)) atTop (𝓝 0) := by
  constructor
  · intro h
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨D, hD, hsqD, heD⟩ := h ε hε
    obtain ⟨N, hDN⟩ := hexhaust D hsqD
    refine ⟨N, ?_⟩
    intro n hn
    have hDn : D ∣ L n := dvd_trans hDN (hdiv N n hn)
    have herror := (squarefreeStageError_antitone_of_dvd D (L n) hDn hD (hL n) hsqD).trans_lt heD
    simpa only [Real.dist_eq, sub_zero,
      abs_of_nonneg (squarefreeStageError_nonneg (L n) (hL n) (hsq n))] using herror
  · intro h ε hε
    obtain ⟨n, hn⟩ := (h.eventually (gt_mem_nhds hε)).exists
    exact ⟨L n, hL n, hsq n, hn⟩

/-- Actual charge saturation on every exhaustive squarefree divisor chain is
the same remaining finite arithmetic approximation property. -/
theorem arithmeticMinima_iff_exhaustive_chain_charge
    (L : ℕ → ℕ) (hL : ∀ n, 2 < L n) (hsq : ∀ n, Squarefree (L n))
    (hdiv : ∀ n m, n ≤ m → L n ∣ L m)
    (hexhaust : ∀ d : ℕ, Squarefree d → ∃ n, d ∣ L n) :
    SquarefreeArithmeticMinima ↔
      Tendsto (fun n => arithmeticInverseCharge (L n) (PhysicalPacketCore.divisorPackets (L n)))
        atTop (𝓝 (-4 * Real.pi)) :=
  (arithmeticMinima_iff_exhaustive_chain_error L hL hsq hdiv hexhaust).trans
    (squarefreeCharge_tendsto_iff_error_tendsto L hL hsq).symm

/-- The explicit primorial chain discharges all common-period, nesting,
and exhaustion premises of the preceding geometric criterion. -/
theorem arithmeticMinima_iff_primorial_error :
    SquarefreeArithmeticMinima ↔
      Tendsto (fun n => squarefreeStageError (SquarefreeStageExhaustion.primorialPeriod n))
        atTop (𝓝 0) := by
  apply arithmeticMinima_iff_exhaustive_chain_error
    SquarefreeStageExhaustion.primorialPeriod
    SquarefreeStageExhaustion.primorialPeriod_gt_two
    SquarefreeStageExhaustion.primorialPeriod_squarefree
    (fun _ _ h => SquarefreeStageExhaustion.primorialPeriod_nested h)
  intro d hd
  exact ⟨d, SquarefreeStageExhaustion.squarefree_dvd_primorialPeriod d d hd le_rfl⟩

/-- Saturation at the arithmetic endpoint on this concrete chain is exactly
the finite squarefree approximation problem, not an unconditional limit. -/
theorem arithmeticMinima_iff_primorial_charge :
    SquarefreeArithmeticMinima ↔
      Tendsto (fun n => arithmeticInverseCharge
        (SquarefreeStageExhaustion.primorialPeriod n)
        (PhysicalPacketCore.divisorPackets (SquarefreeStageExhaustion.primorialPeriod n)))
        atTop (𝓝 (-4 * Real.pi)) :=
  arithmeticMinima_iff_primorial_error.trans
    (squarefreeCharge_tendsto_iff_error_tendsto
      SquarefreeStageExhaustion.primorialPeriod
      SquarefreeStageExhaustion.primorialPeriod_gt_two
      SquarefreeStageExhaustion.primorialPeriod_squarefree).symm

theorem riemannHypothesis_of_primorial_charge_saturation
    (h : Tendsto (fun n => arithmeticInverseCharge
      (SquarefreeStageExhaustion.primorialPeriod n)
      (PhysicalPacketCore.divisorPackets (SquarefreeStageExhaustion.primorialPeriod n)))
      atTop (𝓝 (-4 * Real.pi))) : RiemannHypothesis :=
  riemannHypothesis_of_squarefreeArithmeticMinima
    (arithmeticMinima_iff_primorial_charge.mpr h)

/-- The concrete primorial arithmetic charge saturation problem has the
same content as complete centered squarefree approximation. -/
theorem squarefreeCenteredApproximation_iff_primorial_charge :
    SquarefreeCenteredApproximation ↔
      Tendsto (fun n => arithmeticInverseCharge
        (SquarefreeStageExhaustion.primorialPeriod n)
        (PhysicalPacketCore.divisorPackets (SquarefreeStageExhaustion.primorialPeriod n)))
        atTop (𝓝 (-4 * Real.pi)) :=
  squarefreeCenteredApproximation_iff_arithmeticMinima.trans
    arithmeticMinima_iff_primorial_charge

/-- The genuine analytic RH reverse is still an explicit premise. All
finite arithmetic, physical mean, closure-repair, and cofinality premises
are discharged by the proved declarations used in this equivalence. -/
theorem riemannHypothesis_iff_primorial_charge_of_analytic_reverse
    (hReverse : RiemannHypothesis → SquarefreeCenteredApproximation) :
    RiemannHypothesis ↔
      Tendsto (fun n => arithmeticInverseCharge
        (SquarefreeStageExhaustion.primorialPeriod n)
        (PhysicalPacketCore.divisorPackets (SquarefreeStageExhaustion.primorialPeriod n)))
        atTop (𝓝 (-4 * Real.pi)) :=
  (riemannHypothesis_iff_arithmeticMinima_of_analytic_reverse hReverse).trans
    arithmeticMinima_iff_primorial_charge

/-- The actual arithmetic charges do converge unconditionally, to an
unidentified member of the certified interval. This does not establish
that the limit is the saturation endpoint. -/
theorem exists_primorial_arithmetic_charge_limit :
    ∃ C : ℝ, C ∈ Set.Icc (-8 * Real.sqrt 3) (-4 * Real.pi) ∧
      Tendsto (fun n => arithmeticInverseCharge
        (SquarefreeStageExhaustion.primorialPeriod n)
        (PhysicalPacketCore.divisorPackets (SquarefreeStageExhaustion.primorialPeriod n)))
        atTop (𝓝 C) := by
  obtain ⟨C, hC, ht⟩ := SquarefreeStageExhaustion.exists_primorial_charge_limit
  refine ⟨C, hC, ?_⟩
  have heq : (fun n => arithmeticInverseCharge
      (SquarefreeStageExhaustion.primorialPeriod n)
      (PhysicalPacketCore.divisorPackets (SquarefreeStageExhaustion.primorialPeriod n))) =
      (fun n => PhysicalPacketCore.inverseCharge
        (PhysicalPacketCore.divisorPackets (SquarefreeStageExhaustion.primorialPeriod n))) := by
    funext n
    exact arithmeticInverseCharge_eq_physical _ _
      (SquarefreeStageExhaustion.primorialPeriod_pos n)
      (PhysicalPacketCore.divisorPackets_legal _)
      (PhysicalPacketCore.divisorPackets_period _)
  rw [heq]
  exact ht

/-- The exact thirty-period trial narrows the unconditional interval for the
actual arithmetic limit. It still does not identify the upper endpoint. -/
theorem exists_primorial_arithmetic_charge_limit_improved :
    ∃ C : ℝ, C ∈ Set.Icc
      (-43200 / (797 * Real.sqrt 3 + 1224 * MeanOneThirtyTrial.cotFiveOne +
        648 * MeanOneThirtyTrial.cotFiveTwo)) (-4 * Real.pi) ∧
      Tendsto (fun n => arithmeticInverseCharge
        (SquarefreeStageExhaustion.primorialPeriod n)
        (PhysicalPacketCore.divisorPackets (SquarefreeStageExhaustion.primorialPeriod n)))
        atTop (𝓝 C) := by
  obtain ⟨C, hC, ht⟩ := exists_primorial_arithmetic_charge_limit
  refine ⟨C, ⟨?_, hC.2⟩, ht⟩
  apply ge_of_tendsto ht
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  have h30 : 30 ∣ SquarefreeStageExhaustion.primorialPeriod n := by
    have h : SquarefreeStageExhaustion.primorialPeriod 2 = 30 := by decide
    rw [← h]
    exact SquarefreeStageExhaustion.primorialPeriod_nested hn
  rw [arithmeticInverseCharge_eq_physical _ _
    (SquarefreeStageExhaustion.primorialPeriod_pos n)
    (PhysicalPacketCore.divisorPackets_legal _)
    (PhysicalPacketCore.divisorPackets_period _)]
  exact MeanOneThirtyTrial.inverseCharge_ge_improved_trial_of_thirty_dvd _
    (SquarefreeStageExhaustion.primorialPeriod_gt_two n) h30

end
end RiemannResearch.RH.Pareto.SquarefreeArithmeticSaturation
noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto.SquarefreeArithmeticSaturation
open MeanOneRepair BaezDuarte SquarefreeTransfer ArithmeticCoreInertia
open SquarefreePacketBasis

/-- Bagchi's finite damped Möbius trial in the repository's discrete Pareto
residue model. The sign matches the Fourier--Mellin transfer
Φ(g_d) = -G_d; the term at d = 1 is the zero residue vector. -/
def bagchiMobiusCutoff (N : ℕ) (ε : ℝ) : ThresholdHilbert :=
  finiteResidueSum (Finset.Icc 1 N) (fun d =>
    -(ArithmeticFunction.moebius d : ℝ) * (d : ℝ) ^ (-ε))

/-- The same cutoff with its squarefree support displayed explicitly. -/
def bagchiSquarefreeMobiusCutoff (N : ℕ) (ε : ℝ) : ThresholdHilbert :=
  finiteResidueSum ((Finset.Icc 1 N).filter Squarefree) (fun d =>
    -(ArithmeticFunction.moebius d : ℝ) * (d : ℝ) ^ (-ε))

/-- Möbius vanishing gives exact squarefree support before any limit or norm
estimate. -/
theorem bagchiMobiusCutoff_eq_squarefree (N : ℕ) (ε : ℝ) :
    bagchiMobiusCutoff N ε = bagchiSquarefreeMobiusCutoff N ε := by
  classical
  unfold bagchiMobiusCutoff bagchiSquarefreeMobiusCutoff finiteResidueSum
  symm
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hsq : Squarefree d
  · simp [hsq]
  · simp [hsq, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]

/-- Every finite Bagchi cutoff is an admissible squarefree packet in the
actual Pareto Hilbert space. -/
theorem bagchiSquarefreeMobiusCutoff_mem (N : ℕ) (ε : ℝ) :
    bagchiSquarefreeMobiusCutoff N ε ∈ squarefreePackets := by
  classical
  unfold bagchiSquarefreeMobiusCutoff
  refine ⟨(Finset.Icc 1 N).filter Squarefree,
    (fun d => -(ArithmeticFunction.moebius d : ℝ) * (d : ℝ) ^ (-ε)),
    ?_, ?_, rfl⟩
  · intro d hd
    have hd' : d ∈ Finset.Icc 1 N := (Finset.mem_filter.mp hd).1
    simp only [Finset.mem_Icc] at hd'
    omega
  · intro d hd
    exact (Finset.mem_filter.mp hd).2

/-- Bagchi's two strong-limit steps imply the squarefree target closure.
The inner limit is the cutoff-length limit at each positive damping; the
outer limit is the damping-to-zero endpoint. The theorem supplies only the
Hilbert-space and closure transfer: both displayed analytic limits remain
separate hypotheses. -/
theorem squarefreeCenteredApproximation_of_bagchi_two_stage_limit
    (ε : ℕ → ℝ) (F : ℕ → ThresholdHilbert)
    (_hε : ∀ j, 0 < ε j)
    (_hεzero : Tendsto ε atTop (𝓝 0))
    (hinner : ∀ j, Tendsto (fun N => bagchiMobiusCutoff N (ε j))
      atTop (𝓝 (F j)))
    (houter : Tendsto F atTop (𝓝 hilbertOne)) :
    SquarefreeCenteredApproximation := by
  have hF : ∀ j, F j ∈ closure squarefreePackets := by
    intro j
    apply isClosed_closure.mem_of_tendsto (hinner j)
    exact Filter.Eventually.of_forall fun N => by
      rw [bagchiMobiusCutoff_eq_squarefree]
      exact subset_closure (bagchiSquarefreeMobiusCutoff_mem N (ε j))
  have hone : hilbertOne ∈ closure squarefreePackets :=
    isClosed_closure.mem_of_tendsto houter (Filter.Eventually.of_forall hF)
  exact squarefreeCenteredApproximation_iff_packetApproximation.mpr
    (one_mem_squarefree_closure_iff_packetApproximation.mp hone)

/-- The same two-stage limit transfer includes the repository's exact
fresh-prime repair to ordinary mean one. Thus Bagchi's uncentered Hilbert
closure is not silently identified with a mean-one finite trial. -/
theorem meanOneSquarefreePacketApproximation_of_bagchi_two_stage_limit
    (ε : ℕ → ℝ) (F : ℕ → ThresholdHilbert)
    (hε : ∀ j, 0 < ε j)
    (hεzero : Tendsto ε atTop (𝓝 0))
    (hinner : ∀ j, Tendsto (fun N => bagchiMobiusCutoff N (ε j))
      atTop (𝓝 (F j)))
    (houter : Tendsto F atTop (𝓝 hilbertOne)) :
    MeanOneSquarefreePacketApproximation :=
  squarefreeCenteredApproximation_iff_meanOne.mp
    (squarefreeCenteredApproximation_of_bagchi_two_stage_limit
      ε F hε hεzero hinner houter)

end RiemannResearch.RH.Pareto.SquarefreeArithmeticSaturation
