import RiemannResearch.RH.PrimePowerRamanujanLimits
import RiemannResearch.RH.GlobalLogDilation
import RiemannResearch.RH.RamanujanZeroCertificates
import Mathlib.Tactic.Linarith

/-!
# Joining Ramanujan screening, global logarithms, and zero certificates

The source/covariance identity is connected to finite actual zeta-zero tests,
with their entire Mellin remainders. These tests require Re(z) > 1/2 and
actual zeros; critical-line ordinates alone are not bounded detectors here.

The global logarithmic filter retains prime-power source sparsity and
convergence of the screened packets. Filtering both target and competitor
gives explicit two-sided bounds for the original complete covariance error.
The transformed target is F(1), not an unjustified replacement by 1.

Provenance: the full-conductor research agenda, the local Ramanujan Schur
modules, the global dilation calculus, and RamanujanZeroCertificates
(which records the classical Mellin/zero-obstruction sources).
-/
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto.RamanujanSchurLogZero
open CoefficientStabilization PrimePowerSchur GlobalLogDilation
open RiemannResearch.Analysis.ExhaustiveWalk
open RiemannResearch.RH.ParetoBeurlingMellinObstruction
open RiemannResearch.RH.RamanujanZeroCertificates

theorem closedSpace_eq_normalizedResidueClosure :
    (closedSpace : Set ThresholdHilbert) = normalizedResidueClosure := by
  have hrange : Set.range residueAtom = normalizedResidueAtoms := by
    ext f
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨⟨i + 2, by omega⟩, rfl⟩
    · rintro ⟨⟨d, hd⟩, rfl⟩
      refine ⟨d - 2, ?_⟩
      have he : d - 2 + 2 = d := by omega
      simp only [residueAtom, he]
  change closure ((Submodule.span ℝ (Set.range residueAtom)) : Set ThresholdHilbert) =
    closure ((Submodule.span ℝ normalizedResidueAtoms) : Set ThresholdHilbert)
  rw [hrange]

theorem screened_zeroTest_energy_exact {ι : Type*} [Fintype ι]
    (z c : ι → ℂ) (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re)
    (hz1 : ∀ i, z i ≠ 1) (hzero : ∀ i, riemannZeta (z i) = 0)
    (s : Finset ℕ) (hs : ∀ q ∈ s, 1 < q) (a : primeConductors s → ℝ) :
    (1 - screenedSource s a) ^ 2 + screenedCovariance s a =
      zeroTestCharge z c +
        ∫ x in Ioi (1 : ℝ),
          ‖mellinWeightedStep (hilbertOne - screenedCombination s a) x -
            starRingEnd ℂ (finiteMellinKernel z c x)‖ ^ 2 := by
  have hmem : screenedCombination s a ∈ normalizedResidueClosure := by
    rw [← closedSpace_eq_normalizedResidueClosure]
    exact screenedCombination_mem_closedSpace s hs a
  have h := finiteMellinKernel_remainder (hilbertOne - screenedCombination s a) z c hzre
  have hsig (i : ι) :
      paretoMellin (hilbertOne - screenedCombination s a) (z i) = 1 / z i :=
    paretoMellin_normalizedResidue_error_identity (z i) (hzre i) (hz1 i)
      (hzero i) (screenedCombination s a) hmem
  simp_rw [hsig] at h
  rw [screened_error_mean_covariance] at h
  unfold zeroTestCharge
  linarith

theorem screened_covariance_zeroTest_floor {ι : Type*} [Fintype ι]
    (z c : ι → ℂ) (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re)
    (hz1 : ∀ i, z i ≠ 1) (hzero : ∀ i, riemannZeta (z i) = 0)
    (s : Finset ℕ) (hs : ∀ q ∈ s, 1 < q) (a : primeConductors s → ℝ)
    (hsource : screenedSource s a = 1) :
    zeroTestCharge z c ≤ screenedCovariance s a := by
  have h := screened_zeroTest_energy_exact z c hzre hz1 hzero s hs a
  rw [hsource, sub_self, zero_pow (by norm_num : 2 ≠ 0), zero_add] at h
  rw [h]
  exact le_add_of_nonneg_right (integral_nonneg (fun _ => sq_nonneg _))

theorem logFilter_screenedPacket_tendsto (q : ℕ) :
    Tendsto (fun N => logFilter (screenedPacket (Finset.Icc 2 N) q)) atTop
      (𝓝 (logFilter (limitScreenedPacket q))) :=
  logFilter.continuous.continuousAt.tendsto.comp (screenedPacket_tendsto q)

theorem logFilter_screenedPacket_inner_one (s : Finset ℕ) (q : ℕ) :
    inner ℝ (logFilter (screenedPacket s q)) hilbertOne =
      (1 - meanFactor 2) * ArithmeticFunction.vonMangoldt q := by
  rw [logFilter_inner_one, screenedPacket_inner_one]

theorem logFilter_limitScreenedPacket_inner_one (q : ℕ) :
    inner ℝ (logFilter (limitScreenedPacket q)) hilbertOne =
      (1 - meanFactor 2) * ArithmeticFunction.vonMangoldt q := by
  rw [logFilter_inner_one, limitScreenedPacket_inner_one]

theorem logFilter_screenedCombination_mem (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (a : primeConductors s → ℝ) :
    logFilter (screenedCombination s a) ∈ closedSpace :=
  (logFilter_mem_iff _).mpr (screenedCombination_mem_closedSpace s hs a)

/-- Filtering both target and competitor retains uniform comparison with the
entire source/covariance error. There is no discarded cross-term or tail. -/
theorem logFilter_screened_error_bounds (s : Finset ℕ) (a : primeConductors s → ℝ) :
    (1 / 16) * ((1 - screenedSource s a) ^ 2 + screenedCovariance s a) ≤
      ‖logFilter hilbertOne - logFilter (screenedCombination s a)‖ ^ 2 ∧
    ‖logFilter hilbertOne - logFilter (screenedCombination s a)‖ ^ 2 ≤
      (49 / 16) * ((1 - screenedSource s a) ^ 2 + screenedCovariance s a) := by
  have hl := logFilter_norm_lower (hilbertOne - screenedCombination s a)
  have hu := logFilter_norm_upper (hilbertOne - screenedCombination s a)
  rw [map_sub] at hl hu
  have hls := (sq_le_sq₀ (by positivity) (norm_nonneg _)).mpr hl
  have hus := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hu
  have he := screened_error_mean_covariance s a
  constructor <;> nlinarith

theorem logFilter_tendsto_iff (f : ℕ → ThresholdHilbert) :
    Tendsto (fun N => logFilter (f N)) atTop (𝓝 (logFilter hilbertOne)) ↔
      Tendsto f atTop (𝓝 hilbertOne) := by
  constructor
  · intro h
    have ht := logFilterInverse.continuous.continuousAt.tendsto.comp h
    have hi (v : ThresholdHilbert) : logFilterInverse (logFilter v) = v := by
      change (logFilterInverse * logFilter) v = v
      rw [logFilter_inverse_mul, ContinuousLinearMap.one_apply]
    simpa only [Function.comp_def, hi] using ht
  · intro h
    exact logFilter.continuous.continuousAt.tendsto.comp h

end RiemannResearch.RH.Pareto.RamanujanSchurLogZero
