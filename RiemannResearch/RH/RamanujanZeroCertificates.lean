import RiemannResearch.RH.RamanujanSaturationCriteria
import RiemannResearch.RH.RamanujanCanonicalOptimizer
import RiemannResearch.RH.ParetoBeurlingMellinObstruction
import RiemannResearch.RH.ParetoMellinFiniteGram
import RiemannResearch.RH.ParetoMellinZeroPairObstruction
import RiemannResearch.RH.MobiusCoefficientStabilization
import RiemannResearch.Analysis.FiniteHilbertGramProjection
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Quantitative zero certificates for canonical Ramanujan approximants

Source: user-requested duality program, 23 October 2026, and the existing
continuous Mellin zero certificates. J.-F. Burnol, arXiv:math/9910055,
supports the finite-zero obstruction strategy.

Arbitrary finite families of actual right-hand zeros provide exact energy
identities with every signed Gram term and the full integral remainder.
Repeated zeros and singular dictionaries are permitted: no inverse is used.
The explicit conjugate-pair charge strictly improves the single-zero floor.
No vanishing-error or zero-free assertion is assumed or established.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.RamanujanZeroCertificates
open Pareto Pareto.CoefficientStabilization
open ParetoBeurlingMellinObstruction RamanujanCanonicalOptimizer
open RiemannResearch.Analysis.FiniteHilbertGram

/-- Every finite packet competitor belongs to the literal normalized-residue span. -/
theorem packetSynthesis_mem_normalizedResidueSpan (n : ℕ) (a : Fin n → ℝ) :
    Fintype.linearCombination ℝ
      (fun i : Fin n => ramanujanPacketHilbert (i.val + 2)) a ∈
        normalizedResidueSpan := by
  have h := synthesis_mem
    (fun i : Fin n => ramanujanPacketHilbert (i.val + 2)) a
  change Fintype.linearCombination ℝ
      (fun i : Fin n => ramanujanPacketHilbert (i.val + 2)) a ∈
    Submodule.span ℝ
      (Set.range (fun i : Fin n => ramanujanPacketHilbert (i.val + 2))) at h
  rw [finitePacket_span_eq] at h
  have hle : Submodule.span ℝ (Set.range (fun i : Fin n => residueAtom i.val)) ≤
      normalizedResidueSpan := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨⟨i.val + 2, by omega⟩, rfl⟩
  exact hle h

theorem packetCandidate_mem_normalizedResidueClosure (n : ℕ) :
    packetCandidate n ∈ normalizedResidueClosure := by
  apply subset_closure
  exact packetSynthesis_mem_normalizedResidueSpan n (packetCoefficients n)

/-- A signed finite zero test, with the complete Cauchy Gram quadratic. -/
def zeroTestCharge {ι : Type*} [Fintype ι] (z c : ι → ℂ) : ℝ :=
  2 * (∑ i, starRingEnd ℂ (c i) * (1 / z i)).re -
    (mellinGramQuadratic z c).re

/-- Exact full error, for arbitrary finite zero tests including singular families. -/
theorem packet_zeroTest_energy_exact {ι : Type*} [Fintype ι]
    (z c : ι → ℂ) (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re)
    (hz1 : ∀ i, z i ≠ 1) (hzero : ∀ i, riemannZeta (z i) = 0) (n : ℕ) :
    1 - packetMass n = zeroTestCharge z c +
      ∫ x in Ioi (1 : ℝ),
        ‖mellinWeightedStep (hilbertOne - packetCandidate n) x -
          starRingEnd ℂ (finiteMellinKernel z c x)‖ ^ 2 := by
  have h := finiteMellinKernel_remainder (hilbertOne - packetCandidate n) z c hzre
  have hsignature (i : ι) :
      paretoMellin (hilbertOne - packetCandidate n) (z i) = 1 / z i :=
    paretoMellin_normalizedResidue_error_identity (z i) (hzre i) (hz1 i)
      (hzero i) (packetCandidate n) (packetCandidate_mem_normalizedResidueClosure n)
  simp_rw [hsignature] at h
  rw [packet_error] at h
  unfold zeroTestCharge
  linarith

/-- Exact decomposition for every legal competitor: zero charge, full Mellin
remainder of the canonical residual, and its complete Gram displacement. -/
theorem packet_zeroTest_completion {ι : Type*} [Fintype ι]
    (z c : ι → ℂ) (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re)
    (hz1 : ∀ i, z i ≠ 1) (hzero : ∀ i, riemannZeta (z i) = 0)
    (n : ℕ) (a : Fin n → ℝ) :
    ‖hilbertOne - Fintype.linearCombination ℝ
      (fun i : Fin n => ramanujanPacketHilbert (i.val + 2)) a‖ ^ 2 =
    zeroTestCharge z c +
      (∫ x in Ioi (1 : ℝ),
        ‖mellinWeightedStep (hilbertOne - packetCandidate n) x -
          starRingEnd ℂ (finiteMellinKernel z c x)‖ ^ 2) +
      ‖Fintype.linearCombination ℝ
        (fun i : Fin n => ramanujanPacketHilbert (i.val + 2))
        (a - packetCoefficients n)‖ ^ 2 := by
  rw [packet_completion, packet_zeroTest_energy_exact z c hzre hz1 hzero n]

/-- Dropping only the nonnegative integral gives the variational floor. -/
theorem packet_zeroTest_floor {ι : Type*} [Fintype ι]
    (z c : ι → ℂ) (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re)
    (hz1 : ∀ i, z i ≠ 1) (hzero : ∀ i, riemannZeta (z i) = 0) (n : ℕ) :
    zeroTestCharge z c ≤ 1 - packetMass n := by
  rw [packet_zeroTest_energy_exact z c hzre hz1 hzero n]
  exact le_add_of_nonneg_right (integral_nonneg (fun _ => sq_nonneg _))

/-- Every actual right-hand zero test bounds all finite optimizer masses. -/
theorem packetMass_le_zeroTest {ι : Type*} [Fintype ι]
    (z c : ι → ℂ) (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re)
    (hz1 : ∀ i, z i ≠ 1) (hzero : ∀ i, riemannZeta (z i) = 0) (n : ℕ) :
    packetMass n ≤ 1 - zeroTestCharge z c := by
  linarith [packet_zeroTest_floor z c hzre hz1 hzero n]

/-- The finite competitor's complete Gram excess survives the zero obstruction. -/
theorem packet_zeroTest_with_excess {ι : Type*} [Fintype ι]
    (z c : ι → ℂ) (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re)
    (hz1 : ∀ i, z i ≠ 1) (hzero : ∀ i, riemannZeta (z i) = 0)
    (n : ℕ) (a : Fin n → ℝ) :
    zeroTestCharge z c + ‖Fintype.linearCombination ℝ
      (fun i : Fin n => ramanujanPacketHilbert (i.val + 2))
      (a - packetCoefficients n)‖ ^ 2 ≤
    ‖hilbertOne - Fintype.linearCombination ℝ
      (fun i : Fin n => ramanujanPacketHilbert (i.val + 2)) a‖ ^ 2 := by
  rw [packet_completion]
  linarith [packet_zeroTest_floor z c hzre hz1 hzero n]

/-- The single-zero mass obstruction, with its actual zero explicitly assumed. -/
theorem packetMass_le_single_zero (z : ℂ) (hzre : (1 / 2 : ℝ) < z.re)
    (hz1 : z ≠ 1) (hzero : riemannZeta z = 0) (n : ℕ) :
    packetMass n ≤ 1 - (2 * z.re - 1) / ‖z‖ ^ 2 := by
  have h := normalizedResidue_error_sq_lower_bound_of_zeta_zero z hzre hz1 hzero
    (packetCandidate n) (packetCandidate_mem_normalizedResidueClosure n)
  rw [packet_error] at h
  linarith

/-- The conjugate pair gives a stronger exact identity, retaining its remainder. -/
theorem packet_zeroPair_energy_exact (z : ℂ) (hzre : (1 / 2 : ℝ) < z.re)
    (hzim : z.im ≠ 0) (hzero : riemannZeta z = 0) (n : ℕ) :
    1 - packetMass n = mellinZeroPairCharge z +
      ∫ x in Ioi (1 : ℝ),
        ‖mellinWeightedStep (hilbertOne - packetCandidate n) x -
          starRingEnd ℂ (mellinTwoKernel z (starRingEnd ℂ z)
            (mellinZeroPairCoefficient z)
            (starRingEnd ℂ (mellinZeroPairCoefficient z)) x)‖ ^ 2 := by
  have h := normalizedResidue_error_zeroPair_identity z hzre hzim hzero
    (packetCandidate n) (packetCandidate_mem_normalizedResidueClosure n)
  rwa [packet_error] at h

/-- The optimized conjugate-pair charge is a uniform obstruction to mass one. -/
theorem packetMass_le_zeroPair (z : ℂ) (hzre : (1 / 2 : ℝ) < z.re)
    (hzim : z.im ≠ 0) (hzero : riemannZeta z = 0) (n : ℕ) :
    packetMass n ≤ 1 - mellinZeroPairCharge z := by
  have h := normalizedResidue_error_zeroPair_lower_bound z hzre hzim hzero
    (packetCandidate n) (packetCandidate_mem_normalizedResidueClosure n)
  rw [packet_error] at h
  linarith

/-- For a nonreal zero, the pair obstruction strictly improves the single-zero bound. -/
theorem packetMass_lt_single_zero (z : ℂ) (hzre : (1 / 2 : ℝ) < z.re)
    (hzim : z.im ≠ 0) (hzero : riemannZeta z = 0) (n : ℕ) :
    packetMass n < 1 - (2 * z.re - 1) / ‖z‖ ^ 2 := by
  have hmass := packetMass_le_zeroPair z hzre hzim hzero n
  have hstrict := mellinZeroPairCharge_gt_single z hzre hzim
  linarith

/-- Pair obstruction plus the exact displacement from the optimizer. -/
theorem packet_zeroPair_with_excess (z : ℂ) (hzre : (1 / 2 : ℝ) < z.re)
    (hzim : z.im ≠ 0) (hzero : riemannZeta z = 0) (n : ℕ) (a : Fin n → ℝ) :
    mellinZeroPairCharge z + ‖Fintype.linearCombination ℝ
      (fun i : Fin n => ramanujanPacketHilbert (i.val + 2))
      (a - packetCoefficients n)‖ ^ 2 ≤
    ‖hilbertOne - Fintype.linearCombination ℝ
      (fun i : Fin n => ramanujanPacketHilbert (i.val + 2)) a‖ ^ 2 := by
  rw [packet_completion]
  linarith [packetMass_le_zeroPair z hzre hzim hzero n]

/-- A finite actual optimizer exceeding the pair threshold excludes that zero. -/
theorem zeta_ne_zero_of_packetMass_gt_zeroPair (z : ℂ)
    (hzre : (1 / 2 : ℝ) < z.re) (hzim : z.im ≠ 0) (n : ℕ)
    (hmass : 1 - mellinZeroPairCharge z < packetMass n) : riemannZeta z ≠ 0 := by
  intro hzero
  exact (not_lt_of_ge (packetMass_le_zeroPair z hzre hzim hzero n)) hmass

/-- Every signed finite zero test bounds the actual limiting energy. -/
theorem zeroTestCharge_le_limitEnergy {ι : Type*} [Fintype ι]
    (z c : ι → ℂ) (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re)
    (hz1 : ∀ i, z i ≠ 1) (hzero : ∀ i, riemannZeta (z i) = 0) :
    zeroTestCharge z c ≤ limitEnergy := by
  have h := le_of_tendsto' packetMass_tendsto
    (packetMass_le_zeroTest z c hzre hz1 hzero)
  linarith

theorem singleZero_le_limitEnergy (z : ℂ) (hzre : (1 / 2 : ℝ) < z.re)
    (hz1 : z ≠ 1) (hzero : riemannZeta z = 0) :
    (2 * z.re - 1) / ‖z‖ ^ 2 ≤ limitEnergy := by
  have h := le_of_tendsto' packetMass_tendsto
    (packetMass_le_single_zero z hzre hz1 hzero)
  linarith

theorem zeroPairCharge_le_limitEnergy (z : ℂ) (hzre : (1 / 2 : ℝ) < z.re)
    (hzim : z.im ≠ 0) (hzero : riemannZeta z = 0) :
    mellinZeroPairCharge z ≤ limitEnergy := by
  have h := le_of_tendsto' packetMass_tendsto
    (packetMass_le_zeroPair z hzre hzim hzero)
  linarith

/-- The conjugate-pair improvement survives in the limiting energy. -/
theorem singleZero_lt_limitEnergy (z : ℂ) (hzre : (1 / 2 : ℝ) < z.re)
    (hzim : z.im ≠ 0) (hzero : riemannZeta z = 0) :
    (2 * z.re - 1) / ‖z‖ ^ 2 < limitEnergy :=
  lt_of_lt_of_le (mellinZeroPairCharge_gt_single z hzre hzim)
    (zeroPairCharge_le_limitEnergy z hzre hzim hzero)

theorem limitEnergy_pos_of_single_zero (z : ℂ) (hzre : (1 / 2 : ℝ) < z.re)
    (hz1 : z ≠ 1) (hzero : riemannZeta z = 0) : 0 < limitEnergy := by
  have hz0 : z ≠ 0 := by
    intro h
    simp only [h, Complex.zero_re] at hzre
    norm_num at hzre
  have hden : 0 < ‖z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hz0)
  have hdelta : 0 < (2 * z.re - 1) / ‖z‖ ^ 2 :=
    div_pos (by linarith) hden
  exact lt_of_lt_of_le hdelta (singleZero_le_limitEnergy z hzre hz1 hzero)

/-- An actual right-hand zero forces at least one stabilized coefficient defect. -/
theorem exists_limitCoefficient_defect_of_single_zero
    (z : ℂ) (hzre : (1 / 2 : ℝ) < z.re)
    (hz1 : z ≠ 1) (hzero : riemannZeta z = 0) :
    ∃ m : ℕ, 1 < m ∧
      limitCoefficient m ≠ -(ArithmeticFunction.moebius m : ℝ) := by
  classical
  by_contra h
  have hall : ∀ m : ℕ, 1 < m →
      limitCoefficient m = -(ArithmeticFunction.moebius m : ℝ) := by
    intro m hm
    by_contra hne
    exact h ⟨m, hm, hne⟩
  have he : limitEnergy = 0 :=
    limitEnergy_zero_iff_mem.mpr (limitCoefficients_eq_mobius_iff_mem.mp hall)
  exact (ne_of_gt (limitEnergy_pos_of_single_zero z hzre hz1 hzero)) he

/-- This is a defect in the convergent signed multiple coordinate.
No convergence of individual synthesis coefficients is asserted. -/
theorem exists_packetMultipleCoefficient_not_tendsto_of_single_zero
    (z : ℂ) (hzre : (1 / 2 : ℝ) < z.re)
    (hz1 : z ≠ 1) (hzero : riemannZeta z = 0) :
    ∃ m : ℕ, 1 < m ∧
      ¬ Tendsto (fun n => packetMultipleCoefficient n m) atTop
        (𝓝 (-(ArithmeticFunction.moebius m : ℝ))) := by
  obtain ⟨m, hm, hdef⟩ :=
    exists_limitCoefficient_defect_of_single_zero z hzre hz1 hzero
  refine ⟨m, hm, ?_⟩
  intro ht
  exact hdef (tendsto_nhds_unique (packetMultipleCoefficient_tendsto m hm) ht)

end RiemannResearch.RH.RamanujanZeroCertificates
