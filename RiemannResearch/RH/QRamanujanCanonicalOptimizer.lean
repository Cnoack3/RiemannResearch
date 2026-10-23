import RiemannResearch.RH.RamanujanFiniteSpanBridge
import RiemannResearch.RH.RamanujanPrimeCoordinates
import RiemannResearch.RH.RamanujanSaturationCriteria
import RiemannResearch.RH.RamanujanHilbertTransfer
import RiemannResearch.RH.QFullResidueProjection
import RiemannResearch.RH.SquarefreeMobiusProjection
import RiemannResearch.RH.QTriangularDualDensity
import RiemannResearch.RH.QParetoEquivalence
import RiemannResearch.Analysis.FiniteHilbertGramProjection
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Canonical complete-Q inverse-Gram approximants in Ramanujan coordinates

Source: user-requested Pareto/Q to dual Ramanujan transfer, 23 October 2026.
The finite dictionary contains all conductors 2 through n+1. Its actual
Q inverse-Gram minimizer equals the existing complete-Q residue minimizer.
The signed multiple transforms of its packet coefficients stabilize; no
convergence of individual packet synthesis coefficients is presumed.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.QRamanujanCanonicalOptimizer
open Pareto ZetaTwoHilbert ZetaTwoParetoTransfer QParetoEquivalence
open QRamanujanPackets SquarefreeMobiusProjection
open RiemannResearch.Analysis.FiniteHilbertGram

def packetFamily (n : ℕ) (i : Fin n) : QHilbert :=
  qRamanujanPacket (i.val + 2)

theorem packet_independent (n : ℕ) :
    LinearIndependent ℝ (packetFamily n) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro a ha
  have hp := congrArg toParetoLinear ha
  simp only [map_sum, map_smul, map_zero] at hp
  change (∑ i : Fin n, a i • toPareto (qRamanujanPacket (i.val + 2))) = 0 at hp
  simp only [RamanujanPrimeCoordinates.toPareto_packet] at hp
  exact Fintype.linearIndependent_iff.mp (finitePacket_independent n) a hp

theorem packet_span_eq (n : ℕ) :
    Submodule.span ℝ (Set.range (packetFamily n)) =
      Submodule.span ℝ (Set.range (fun i : Fin n => qResidue (i.val + 2))) := by
  have hmap :
      (Submodule.span ℝ (Set.range (packetFamily n))).map paretoEquiv.toLinearMap =
        (Submodule.span ℝ
          (Set.range (fun i : Fin n => qResidue (i.val + 2)))).map
            paretoEquiv.toLinearMap := by
    rw [map_span_range, map_span_range]
    simpa only [packetFamily, RamanujanPrimeCoordinates.toPareto_packet,
      toPareto_residueAtom] using finitePacket_span_eq n
  apply le_antisymm
  · intro x hx
    have hx' : paretoEquiv x ∈
        (Submodule.span ℝ
          (Set.range (fun i : Fin n => qResidue (i.val + 2)))).map
            paretoEquiv.toLinearMap := by
      rw [← hmap]
      exact ⟨x, hx, rfl⟩
    rcases hx' with ⟨y, hy, he⟩
    exact paretoEquiv.injective he ▸ hy
  · intro x hx
    have hx' : paretoEquiv x ∈
        (Submodule.span ℝ (Set.range (packetFamily n))).map
          paretoEquiv.toLinearMap := by
      rw [hmap]
      exact ⟨x, hx, rfl⟩
    rcases hx' with ⟨y, hy, he⟩
    exact paretoEquiv.injective he ▸ hy

theorem packet_span_eq_stage (n : ℕ) :
    synthesisSpan (packetFamily n) = QFullResidueProjection.stage n := by
  simpa only [synthesisSpan, QFullResidueProjection.stage,
    RiemannResearch.Analysis.ExhaustiveWalk.walkSpan, id_eq] using packet_span_eq n

def packetCoefficients (n : ℕ) : Fin n → ℝ :=
  inverseCoeff (packet_independent n) qOne

def packetCandidate (n : ℕ) : QHilbert :=
  Fintype.linearCombination ℝ (packetFamily n) (packetCoefficients n)

/-- Two genuine inverse-Gram constructions give the same actual Q vector. -/
theorem packetCandidate_eq_residueCandidate (n : ℕ) :
    packetCandidate n = QFullResidueProjection.candidate n := by
  have hmem : packetCandidate n ∈ QFullResidueProjection.stage n := by
    have h := synthesis_mem (packetFamily n) (packetCoefficients n)
    change packetCandidate n ∈ synthesisSpan (packetFamily n) at h
    rw [packet_span_eq_stage] at h
    exact h
  rw [QFullResidueProjection.candidate_eq_projection]
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero hmem
  intro w hw
  have hp : w ∈ synthesisSpan (packetFamily n) := by
    rw [packet_span_eq_stage]
    exact hw
  rw [synthesisSpan, ← Fintype.range_linearCombination] at hp
  obtain ⟨a, rfl⟩ := hp
  exact residual_orthogonal (packet_independent n) qOne a

theorem packetCandidate_tendsto_projection :
    Tendsto packetCandidate atTop
      (𝓝 (QFullResidueProjection.closure.starProjection qOne)) := by
  have he : packetCandidate = QFullResidueProjection.candidate := by
    funext n
    exact packetCandidate_eq_residueCandidate n
  rw [he]
  exact QFullResidueProjection.candidate_tendsto_projection

/-- Continuous residue coordinates applied to an actual Ramanujan packet. -/
theorem qCoefficient_packet (m q : ℕ) (hm : 1 < m) (hq : 0 < q) :
    qCoefficientCLM m (qRamanujanPacket q) =
      if m ∣ q then (m : ℝ) * (ArithmeticFunction.moebius (q / m) : ℝ) else 0 := by
  change -mobiusDifferenceCLM m (toPareto (qRamanujanPacket q)) = _
  rw [RamanujanPrimeCoordinates.toPareto_packet,
    mobiusDifferenceCLM_ramanujanPacketHilbert m q hm hq]
  split_ifs <;> ring

/-- The actual finite signed multiple transform of the packet inverse solve. -/
def packetCoordinate (n m : ℕ) : ℝ :=
  (m : ℝ) * ∑ i : Fin n,
    if m ∣ i.val + 2 then
      (ArithmeticFunction.moebius ((i.val + 2) / m) : ℝ) * packetCoefficients n i
    else 0

theorem packetCoordinate_eq (n m : ℕ) (hm : 1 < m) :
    packetCoordinate n m = qCoefficientCLM m (packetCandidate n) := by
  symm
  change qCoefficientCLM m
      (∑ i : Fin n, packetCoefficients n i • qRamanujanPacket (i.val + 2)) = _
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  unfold packetCoordinate
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [qCoefficient_packet m (i.val + 2) hm (by omega)]
  split_ifs <;> ring

/-- Literal residue inverse coefficients are exactly the transformed packet coefficients. -/
theorem residueCoefficients_eq_packetCoordinate (n : ℕ) (i : Fin n) :
    QFullResidueProjection.coefficients n i = packetCoordinate n (i.val + 2) := by
  rw [packetCoordinate_eq n (i.val + 2) (by omega),
    packetCandidate_eq_residueCandidate]
  symm
  unfold QFullResidueProjection.candidate QCovarianceInverse.qSynthesis
  simp only [map_sum, map_smul, smul_eq_mul]
  have hpair (j : Fin n) :
      qCoefficientCLM (i.val + 2)
        (qResidue (QFullResidueProjection.conductor n j)) =
          if i = j then 1 else 0 := by
    simpa only [QFullResidueProjection.conductor, Fin.ext_iff] using
      q_coordinate_biorthogonal i.val j.val
  simp only [hpair]
  simp [mul_ite]

def limitCoordinate (m : ℕ) : ℝ :=
  qCoefficientCLM m (QFullResidueProjection.closure.starProjection qOne)

/-- Every fixed signed multiple transform stabilizes unconditionally. -/
theorem packetCoordinate_tendsto (m : ℕ) (hm : 1 < m) :
    Tendsto (fun n => packetCoordinate n m) atTop (𝓝 (limitCoordinate m)) := by
  have ht := (qCoefficientCLM m).continuous.continuousAt.tendsto.comp
    packetCandidate_tendsto_projection
  have he : (fun n => packetCoordinate n m) =
      (fun n => qCoefficientCLM m (packetCandidate n)) := by
    funext n
    exact packetCoordinate_eq n m hm
  rw [he]
  exact ht

theorem limitCoordinates_eq_moebius_iff_closure :
    (∀ m : ℕ, 1 < m →
      limitCoordinate m = -(ArithmeticFunction.moebius m : ℝ)) ↔
      qOne ∈ QFullResidueProjection.closure := by
  constructor
  · intro h
    have hr : qOne - QFullResidueProjection.closure.starProjection qOne = 0 := by
      apply QTriangularCharge.q_eq_zero_of_all_coefficients_zero
      intro i
      rw [map_sub, q_target_coordinate (i + 2) (by omega)]
      change -(ArithmeticFunction.moebius (i + 2) : ℝ) - limitCoordinate (i + 2) = 0
      rw [h (i + 2) (by omega)]
      ring
    have he : qOne = QFullResidueProjection.closure.starProjection qOne :=
      sub_eq_zero.mp hr
    exact he.symm ▸ QFullResidueProjection.closure.starProjection_apply_mem qOne
  · intro h m hm
    have he : QFullResidueProjection.closure.starProjection qOne = qOne :=
      Submodule.starProjection_eq_self_iff.mpr h
    rw [limitCoordinate, he, q_target_coordinate m (by omega)]

/-- The missing target identification is exposed as an exact iff condition. -/
theorem packetCoordinate_limits_moebius_iff_closure :
    (∀ m : ℕ, 1 < m →
      Tendsto (fun n => packetCoordinate n m) atTop
        (𝓝 (-(ArithmeticFunction.moebius m : ℝ)))) ↔
      qOne ∈ QFullResidueProjection.closure := by
  constructor
  · intro h
    apply limitCoordinates_eq_moebius_iff_closure.mp
    intro m hm
    exact tendsto_nhds_unique (packetCoordinate_tendsto m hm) (h m hm)
  · intro h m hm
    have he := limitCoordinates_eq_moebius_iff_closure.mpr h m hm
    simpa only [he] using packetCoordinate_tendsto m hm


/-- The actual Q packet source is determined by Q means, not Pareto means. -/
def packetSource (n : ℕ) (i : Fin n) : ℝ :=
  inner ℝ (packetFamily n i) qOne

def packetGram (n : ℕ) : Matrix (Fin n) (Fin n) ℝ := gramMatrix (packetFamily n)

def packetMass (n : ℕ) : ℝ :=
  ∑ i : Fin n, packetCoefficients n i * packetSource n i

theorem packetSource_divisor_formula (n : ℕ) (i : Fin n) :
    packetSource n i =
      ∑ d ∈ (i.val + 2).divisors,
        ((ArithmeticFunction.moebius ((i.val + 2) / d) : ℝ) * d) *
          inner ℝ qOne (qResidue d) := by
  rw [packetSource, real_inner_comm]
  exact RamanujanTransfer.packet_moment qOne (i.val + 2)

theorem packetCoefficients_eq_inverseGram (n : ℕ) :
    packetCoefficients n = (packetGram n)⁻¹.mulVec (packetSource n) := by
  rw [packetGram, gramMatrix_inverseSource (packet_independent n)]
  rfl

theorem packetMass_eq_inverseGram (n : ℕ) :
    packetMass n = dotProduct (packetSource n)
      ((packetGram n)⁻¹.mulVec (packetSource n)) := by
  unfold packetMass dotProduct
  rw [packetCoefficients_eq_inverseGram]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem packet_error (n : ℕ) :
    ‖qOne - packetCandidate n‖ ^ 2 = 1 - packetMass n := by
  simpa only [qOne_norm_sq, packetCandidate, packetCoefficients,
    packetMass, packetSource, cross] using
    residual_schur_value (packet_independent n) qOne

theorem packet_completion (n : ℕ) (a : Fin n → ℝ) :
    ‖qOne - Fintype.linearCombination ℝ (packetFamily n) a‖ ^ 2 =
      1 - packetMass n +
        ‖Fintype.linearCombination ℝ (packetFamily n) (a - packetCoefficients n)‖ ^ 2 := by
  have h := residual_completion (packet_independent n) qOne a
  change _ = ‖qOne - packetCandidate n‖ ^ 2 + _ at h
  rw [packet_error] at h
  exact h

theorem closure_iff_pareto :
    qOne ∈ QFullResidueProjection.closure ↔
      hilbertOne ∈ CoefficientStabilization.closedSpace := by
  have h := mem_closure_span_iff (fun i : ℕ => qResidue (i+2)) qOne
  simpa only [toPareto_qOne, toPareto_residueAtom,
    QFullResidueProjection.closure, QFullResidueProjection.legalSpan,
    CoefficientStabilization.closedSpace,
    RiemannResearch.Analysis.ExhaustiveWalk.dictionaryClosure] using h

theorem packetCoordinate_limits_iff_pareto :
    (∀ m : ℕ, 1 < m → Tendsto (fun n => packetCoordinate n m) atTop
      (𝓝 (-(ArithmeticFunction.moebius m : ℝ)))) ↔
    (∀ m : ℕ, 1 < m →
      Tendsto (fun n => RamanujanCanonicalOptimizer.packetMultipleCoefficient n m)
        atTop (𝓝 (-(ArithmeticFunction.moebius m : ℝ)))) := by
  have hp := RamanujanCanonicalOptimizer.packetMultipleCoefficient_targets_iff_residual_zero
  rw [CoefficientStabilization.limitResidual_zero_iff_energy_zero,
    CoefficientStabilization.limitEnergy_zero_iff_mem] at hp
  exact packetCoordinate_limits_moebius_iff_closure.trans (closure_iff_pareto.trans hp.symm)

theorem packetCoordinate_limits_iff_rh
    (hBaezDuarte : RiemannHypothesis → BaezDuarte.NaturalApproximation) :
    (∀ m : ℕ, 1 < m → Tendsto (fun n => packetCoordinate n m) atTop
      (𝓝 (-(ArithmeticFunction.moebius m : ℝ)))) ↔ RiemannHypothesis := by
  exact packetCoordinate_limits_iff_pareto.trans
    (RamanujanCanonicalOptimizer.packet_cofinal_rh_equivalences
      hBaezDuarte id tendsto_id).2.2.1


theorem packet_mass_tendsto :
    Tendsto packetMass atTop (𝓝
      (1 - ‖qOne - QFullResidueProjection.closure.starProjection qOne‖ ^ 2)) := by
  have he (n : ℕ) : packetMass n = 1 - ‖qOne - packetCandidate n‖ ^ 2 := by
    linarith [packet_error n]
  change Tendsto (fun n => packetMass n) _ _
  simp_rw [he]
  exact tendsto_const_nhds.sub
    ((tendsto_const_nhds.sub packetCandidate_tendsto_projection).norm.pow 2)

theorem packet_mass_iff_closure :
    Tendsto packetMass atTop (𝓝 1) ↔ qOne ∈ QFullResidueProjection.closure := by
  constructor
  · intro h
    have he := tendsto_nhds_unique packet_mass_tendsto h
    have hn : ‖qOne - QFullResidueProjection.closure.starProjection qOne‖ ^ 2 = 0 := by
      linarith
    have hz := norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
    have hp : QFullResidueProjection.closure.starProjection qOne = qOne :=
      (sub_eq_zero.mp hz).symm
    exact Submodule.starProjection_eq_self_iff.mp hp
  · intro h
    have hp : QFullResidueProjection.closure.starProjection qOne = qOne :=
      Submodule.starProjection_eq_self_iff.mpr h
    simpa only [hp, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0),
      sub_zero] using packet_mass_tendsto

theorem packet_norm_iff_closure :
    Tendsto (fun n => ‖qOne - packetCandidate n‖) atTop (𝓝 0) ↔
      qOne ∈ QFullResidueProjection.closure := by
  have ht : Tendsto (fun n => ‖qOne - packetCandidate n‖) atTop
      (𝓝 ‖qOne - QFullResidueProjection.closure.starProjection qOne‖) :=
    (tendsto_const_nhds.sub packetCandidate_tendsto_projection).norm
  constructor
  · intro h
    have hz := norm_eq_zero.mp (tendsto_nhds_unique ht h)
    exact Submodule.starProjection_eq_self_iff.mp (sub_eq_zero.mp hz).symm
  · intro h
    have hp : QFullResidueProjection.closure.starProjection qOne = qOne :=
      Submodule.starProjection_eq_self_iff.mpr h
    simpa only [hp, sub_self, norm_zero] using ht

theorem packet_rh_equivalences
    (hBaezDuarte : RiemannHypothesis → BaezDuarte.NaturalApproximation) :
    (Tendsto packetMass atTop (𝓝 1) ↔ RiemannHypothesis) ∧
    (Tendsto (fun n => ‖qOne - packetCandidate n‖) atTop (𝓝 0) ↔ RiemannHypothesis) ∧
    ((∀ m : ℕ, 1 < m → Tendsto (fun n => packetCoordinate n m) atTop
      (𝓝 (-(ArithmeticFunction.moebius m : ℝ)))) ↔ RiemannHypothesis) := by
  have hc := packetCoordinate_limits_moebius_iff_closure.symm.trans
    (packetCoordinate_limits_iff_rh hBaezDuarte)
  exact ⟨packet_mass_iff_closure.trans hc, packet_norm_iff_closure.trans hc,
    packetCoordinate_limits_iff_rh hBaezDuarte⟩

end RiemannResearch.RH.QRamanujanCanonicalOptimizer
