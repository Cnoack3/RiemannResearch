import RiemannResearch.RH.PrimeSupportAlgebraDescent
import RiemannResearch.RH.PrimeSupportParityQuotient
import RiemannResearch.RH.CenteredMeanQuotients
import RiemannResearch.RH.MixedConductorMetricCokernel
import RiemannResearch.RH.MixedConductorMetricLifting
import RiemannResearch.RH.ParetoParityNormBounds
import RiemannResearch.RH.RamanujanGramDeterminants
import RiemannResearch.RH.BaezDuarteNaturalApproximation
import RiemannResearch.RH.CauchyAnnihilatorRH
import RiemannResearch.RH.XiTaylorDiskRadius
import RiemannResearch.Analysis.ActualSelbergSlopeRH
import RiemannResearch.Analysis.ActualZeroSecondEnergy
import RiemannResearch.Analysis.MontgomerySharpWeilSeparator
import Mathlib.Tactic.TFAE

/-!
# Equivalent formulations for the centered tower and for RH

The first equivalence list identifies thirteen tests on the actual Pareto spaces.
It needs no analytic premise. Each of its conditions implies RH. For the
reverse implication, the required input is precisely Báez-Duarte's natural
approximation from RH, formalized here as an explicit implication. See
Bagchi, Theorem 1, https://arxiv.org/abs/math/0607733, for the published
discrete criterion.

The second list records direct RH equivalences already proved in this repository.
It includes the finite Mellin product test at budget one, a Pareto Cauchy
pairing, and independent criteria for the actual zeros. Neither list asserts
that any of its equivalent conditions holds.
-/

noncomputable section

open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake
open CoefficientStabilization MixedConductorBasis

open scoped LegalMeanAlgebra

/-- Centering the ambient space at its constant gives the usual square-zero extension
product on the scalar component and the mean-zero component. -/
def ambientProduct (x y : ThresholdHilbert) : ThresholdHilbert :=
  hilbertMeanContinuous x • y + hilbertMeanContinuous y • x -
    (hilbertMeanContinuous x * hilbertMeanContinuous y) • hilbertOne

private theorem ambientMean_coe (x : closedSpace) :
    hilbertMeanContinuous (x : ThresholdHilbert) = legalPacketMean x := by
  change inner ℝ hilbertOne x.val = inner ℝ x.val hilbertOne
  exact real_inner_comm _ _

/-- The failure of the inclusion to preserve a product recovers the actual vector
`1_H - u` with coefficient `C(x) C(y)`. -/
theorem inclusion_product_defect (x y : closedSpace) :
    ((x * y : closedSpace) : ThresholdHilbert) - ambientProduct x.val y.val =
      (legalPacketMean x * legalPacketMean y) • (hilbertOne - normalizedScreenedTwo) := by
  have hu : (screenedMeanSection 1 : ThresholdHilbert) = normalizedScreenedTwo := one_smul ℝ _
  change (legalPacketMean x • y.val + legalPacketMean y • x.val -
      (legalPacketMean x * legalPacketMean y) • (screenedMeanSection 1 : ThresholdHilbert)) -
      ambientProduct x.val y.val = _
  rw [ambientProduct, ambientMean_coe, ambientMean_coe, hu, smul_sub]
  abel

/-- The actual legal packet, with the membership proof supplied by its finite divisor sum. -/
def legalRamanujan (q : ℕ) (hq : 1 < q) : closedSpace :=
  ⟨ramanujanPacketHilbert q, packet_mem_closedSpace q hq⟩

theorem legalRamanujan_mean (q : ℕ) (hq : 1 < q) :
    legalPacketMean (legalRamanujan q hq) = ArithmeticFunction.vonMangoldt q := by
  change inner ℝ (ramanujanPacketHilbert q) hilbertOne = _
  rw [hilbert_inner_one, hilbertSequence_ramanujanPacketHilbert, paretoMean_ramanujanPacket]

/-- Compare the screened product with the ambient square-zero product on two raw packets. -/
def packetProductAgrees (q r : ℕ) (hq : 1 < q) (hr : 1 < r) : Prop :=
  ((legalRamanujan q hq * legalRamanujan r hr : closedSpace) : ThresholdHilbert) =
    ambientProduct (ramanujanPacketHilbert q) (ramanujanPacketHilbert r)

/-- Mixed conductors give agreement automatically. A pair of pure prime powers
detects precisely whether the screened unit is the ambient constant. -/
theorem packetProductAgrees_iff (q r : ℕ) (hq : 1 < q) (hr : 1 < r) :
    packetProductAgrees q r hq hr ↔
      ¬ IsPrimePow q ∨ ¬ IsPrimePow r ∨ normalizedScreenedTwo = hilbertOne := by
  change ((legalRamanujan q hq * legalRamanujan r hr : closedSpace) : ThresholdHilbert) =
    ambientProduct (legalRamanujan q hq).val (legalRamanujan r hr).val ↔ _
  rw [← sub_eq_zero, inclusion_product_defect, legalRamanujan_mean, legalRamanujan_mean,
    smul_eq_zero, mul_eq_zero, ArithmeticFunction.vonMangoldt_eq_zero_iff,
    ArithmeticFunction.vonMangoldt_eq_zero_iff, sub_eq_zero, or_assoc,
    eq_comm (a := hilbertOne) (b := normalizedScreenedTwo)]

theorem two_three_product_iff_screened :
    packetProductAgrees 2 3 (by decide) (by decide) ↔ normalizedScreenedTwo = hilbertOne := by
  rw [packetProductAgrees_iff]
  simp [show IsPrimePow 2 by exact Nat.prime_two.isPrimePow,
    show IsPrimePow 3 by exact Nat.prime_three.isPrimePow]

/-- The class of the scalar unit in any support quotient detects the entire snake boundary. -/
theorem stageUnit_zero_iff_boundary (n : ℕ) :
    stageMeanBoundary n 1 = 0 ↔ boundary = 0 := by
  have h : stageMeanBoundary n 1 = boundary 1 := by
    rw [stageMeanBoundary_unit, boundary_apply, one_smul]
  rw [h, boundary_one_eq_zero_iff_one_mem, boundary_eq_zero_iff_one_mem]

/-- Every entry detects membership of the ambient constant in the legal space. -/
theorem categoricalMean_tfae (n : ℕ) :
    List.TFAE [
      stageMeanBoundary n 1 = 0,
      boundary = 0,
      normalizedScreenedTwo = hilbertOne,
      hilbertOne ∈ closedSpace,
      limitEnergy = 0,
      Subsingleton BoundaryTarget,
      ∃ s : ℝ →L[ℝ] closedSpace,
        legalPacketMean.comp s = ContinuousLinearMap.id ℝ ℝ ∧ ‖s‖ ≤ 1,
      LegalMeanFactorizationBound 1,
      ∀ ε : ℝ, 0 < ε → ∃ k, ‖parityQuotientClass k‖ ^ 2 < ε,
      BaezDuarte.NaturalApproximation,
      normalizedParityCapture = Real.sqrt (1 / Real.log 2 - 1),
      Tendsto (fun k => packetHeadDeterminant k 1) atTop (𝓝 0),
      packetProductAgrees 2 3 (by decide) (by decide)] := by
  tfae_have 1 ↔ 2 := stageUnit_zero_iff_boundary n
  tfae_have 2 ↔ 3 := boundary_eq_zero_iff_screened
  tfae_have 2 ↔ 4 := boundary_eq_zero_iff_one_mem
  tfae_have 5 ↔ 4 := limitEnergy_zero_iff_mem
  tfae_have 6 ↔ 4 := boundaryTarget_subsingleton_iff_one_mem
  tfae_have 7 ↔ 5 := exists_contractive_legalMeanSection_iff_limitEnergy_zero
  tfae_have 8 ↔ 10 := legalMean_contractive_cokernel_iff_naturalApproximation
  tfae_have 2 ↔ 9 := boundary_eq_zero_iff_small_parity_quotients
  tfae_have 2 ↔ 10 := boundary_eq_zero_iff_naturalApproximation
  tfae_have 11 ↔ 5 := normalizedParityCapture_eq_upper_iff
  tfae_have 12 ↔ 4 := packetHeadDeterminant_zero_iff_one_mem
  tfae_have 13 ↔ 3 := two_three_product_iff_screened
  tfae_finish

/-- A single descended unit of zero class suffices for Mathlib's actual RH statement. -/
theorem riemannHypothesis_of_stageUnit_zero {n : ℕ} (h : stageMeanBoundary n 1 = 0) :
    RiemannHypothesis := riemannHypothesis_of_boundary_eq_zero ((stageUnit_zero_iff_boundary n).1 h)

/-- For any proved RH equivalent, the converse to the tower criterion is precisely
the natural approximation implication; the choice of analytic test does not alter it. -/
theorem criterion_to_stageUnit_iff_naturalApproximation (n : ℕ) {P : Prop}
    (hP : P ↔ RiemannHypothesis) :
    (P → stageMeanBoundary n 1 = 0) ↔ (RiemannHypothesis → BaezDuarte.NaturalApproximation) := by
  have h := (stageUnit_zero_iff_boundary n).trans boundary_eq_zero_iff_naturalApproximation
  exact ⟨fun f hRH => h.mp (f (hP.mpr hRH)), fun f hp => h.mpr (f (hP.mp hp))⟩

/-- The published converse is visible in the type of the two-way RH criterion. -/
theorem stageUnit_zero_iff_riemannHypothesis (n : ℕ)
    (hBD : RiemannHypothesis → BaezDuarte.NaturalApproximation) :
    stageMeanBoundary n 1 = 0 ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_stageUnit_zero,
    (criterion_to_stageUnit_iff_naturalApproximation n Iff.rfl).2 hBD⟩

open RiemannResearch.Analysis.ActualZeroOrdinate
open RiemannResearch.Analysis.ActualZeroHorizontalEnergy
open RiemannResearch.Analysis.MontgomeryHorizontalTransfer
open RiemannResearch.RH.RationalZeroFreeDisks
open RiemannResearch.RH.Pareto.SpectralObstruction

/-- Six independently formalized characterizations with no external converse in their types. -/
theorem analyticRiemannHypothesis_tfae :
    List.TFAE [
      RiemannHypothesis,
      ∀ (n : ℕ) (z : Fin n → ℂ), Function.Injective z →
        (∀ i, riemannZeta (z i) = 0) → (∀ i, (1 / 2 : ℝ) < (z i).re) →
        (∀ i, z i ≠ 1) → 1 ≤ mellinCenteredProduct z 1,
      ∀ (δ : NNReal) (γ : ℝ), δ ≠ 0 → (δ : ℝ) < 1 / 2 →
        SpectralObstruction.residuePairing (cauchyMellinMixture δ γ) 2 ≠ 0,
      horizontalSecondEnergy = 0,
      ∀ A : ℝ, ∃ a : ℝ, A < a ∧ UniformSelbergDensity a,
      RationalTaylorDisks (1 / 2),
      CofinalSharpPolynomialUpper] := by
  tfae_have 1 ↔ 2 := riemannHypothesis_iff_unit_finite_zero_products
  tfae_have 1 ↔ 3 := riemannHypothesis_iff_cauchy_generator_detected
  tfae_have 4 ↔ 1 := horizontalSecondEnergy_eq_zero_iff_RH
  tfae_have 1 ↔ 5 := riemannHypothesis_iff_cofinal_uniformSelbergDensity
  tfae_have 1 ↔ 6 := riemannHypothesis_iff_rationalTaylorDisks
  tfae_have 7 ↔ 1 := cofinalSharpPolynomialUpper_iff_riemannHypothesis
  tfae_finish

end RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake
