import RiemannResearch.LinearAlgebra.CauchyInverseProduct
import RiemannResearch.RH.ParetoMellinNonsingular
import RiemannResearch.RH.ParetoMellinEnlargement
import RiemannResearch.RH.RamanujanUnitMean
import Mathlib.Topology.Order.MonotoneConvergence
import RiemannResearch.RH.ParetoMellinGramOptimization
import RiemannResearch.RH.RamanujanMellinOptimization
import RiemannResearch.RH.RamanujanSaturationCriteria
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exact finite zero products for the Ramanujan dual

Source: user-requested third Ramanujan development, October 2026.
J.-F. Burnol, https://arxiv.org/abs/math/9910055, motivates the finite-zero
product obstruction. The algebraic Cauchy determinant identity gives the exact
finite capacity here. The complete Mellin integral and packet displacement
remain in the error identity. Actual right-half-plane zeros are explicit
hypotheses; no such zero or vanishing error is asserted.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace RiemannResearch.RH.Pareto
open RiemannResearch.LinearAlgebra.CauchyProduct
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def mellinZeroProduct (s : ι → ℂ) : ℝ :=
  ∏ i, ‖(s i - 1) / s i‖ ^ 2

/-- The complete optimized finite-zero capacity is a finite Blaschke product defect. -/
theorem mellinInverseCapacity_zeroSource_product (s : ι → ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re) (hinj : Function.Injective s) :
    mellinInverseCapacity s (fun i => 1 / s i) = 1 - mellinZeroProduct s := by
  classical
  have hconj (z : ℂ) : starRingEnd ℂ (starRingEnd ℂ z) = z := by
    change star (star z) = z
    exact star_star z
  have hs0 : ∀ i, s i ≠ 0 := by
    intro i hz
    have h := hs i
    rw [hz, Complex.zero_re] at h
    norm_num at h
  have hc0 : ∀ i, starRingEnd ℂ (s i) ≠ 0 := by
    intro i hz
    apply hs0 i
    have h := congrArg (starRingEnd ℂ) hz
    simpa only [hconj, map_zero] using h
  have hden : ∀ i j, s i + starRingEnd ℂ (s j) - 1 ≠ 0 := by
    intro i j hz
    have h := congrArg Complex.re hz
    simp only [Complex.sub_re, Complex.add_re, Complex.conj_re,
      Complex.one_re, Complex.zero_re] at h
    linarith [hs i, hs j]
  have hdet : (cauchy s (fun i => starRingEnd ℂ (s i))).det ≠ 0 :=
    (mellinCauchyGram_det_ne_zero_iff_injective s hs).mpr hinj
  have hp := cauchy_inverse_pairing_product s (fun i => starRingEnd ℂ (s i))
    hs0 hc0 hden hdet
  let c := mellinInverseCoefficients s (fun i => 1 / s i)
  change (∑ i, (1 / starRingEnd ℂ (s i)) * c i) =
    1 - (∏ i, (s i - 1) / s i) *
      (∏ i, (starRingEnd ℂ (s i) - 1) / starRingEnd ℂ (s i)) at hp
  have hc : starRingEnd ℂ (∑ i, (1 / starRingEnd ℂ (s i)) * c i) =
      ∑ i, starRingEnd ℂ (c i) * (1 / s i) := by
    simp only [map_sum, map_mul, map_div₀, map_one, hconj]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hleft : mellinInverseCapacity s (fun i => 1 / s i) =
      (∑ i, (1 / starRingEnd ℂ (s i)) * c i).re := by
    have h := congrArg Complex.re hc
    simpa only [Complex.conj_re, mellinInverseCapacity, c] using h.symm
  have hnorm (t : Finset ι) :
      ‖∏ i ∈ t, (s i - 1) / s i‖ ^ 2 =
        ∏ i ∈ t, ‖(s i - 1) / s i‖ ^ 2 := by
    induction t using Finset.induction_on with
    | empty => simp
    | @insert i t hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi, norm_mul, mul_pow, ih]
  have hprod :
      ((∏ i, (s i - 1) / s i) *
        (∏ i, (starRingEnd ℂ (s i) - 1) / starRingEnd ℂ (s i))).re =
      mellinZeroProduct s := by
    have he : (∏ i, (starRingEnd ℂ (s i) - 1) / starRingEnd ℂ (s i)) =
        starRingEnd ℂ (∏ i, (s i - 1) / s i) := by
      simp only [map_prod, map_div₀, map_sub, map_one]
    rw [he, Complex.mul_conj, Complex.ofReal_re, ← Complex.sq_norm]
    exact hnorm Finset.univ
  have h := congrArg Complex.re hp
  rw [Complex.sub_re, Complex.one_re, hprod] at h
  exact hleft.trans h


/-- Prefix zero products decrease for every injective strict-half-plane sequence. -/
theorem mellinZeroProduct_prefix_antitone (s : ℕ → ℂ)
    (hs : ∀ j, (1 / 2 : ℝ) < (s j).re) (hinj : Function.Injective s) :
    Antitone (fun n => mellinZeroProduct (fun i : Fin n => s i.val)) := by
  intro n m hnm
  have hn : Function.Injective (fun i : Fin n => s i.val) := by
    intro i j hij
    exact Fin.ext (hinj hij)
  have hm : Function.Injective (fun i : Fin m => s i.val) := by
    intro i j hij
    exact Fin.ext (hinj hij)
  have h := mellinInverseCapacity_prefix_mono_of_injective s
    (fun j => 1 / s j) hs hinj hnm
  dsimp only at h
  rw [mellinInverseCapacity_zeroSource_product
    (fun i : Fin n => s i.val) (fun i => hs i.val) hn,
    mellinInverseCapacity_zeroSource_product
      (fun i : Fin m => s i.val) (fun i => hs i.val) hm] at h
  linarith

def mellinZeroProductLimit (s : ℕ → ℂ) : ℝ :=
  ⨅ n, mellinZeroProduct (fun i : Fin n => s i.val)

theorem mellinZeroProduct_prefix_tendsto (s : ℕ → ℂ)
    (hs : ∀ j, (1 / 2 : ℝ) < (s j).re) (hinj : Function.Injective s) :
    Filter.Tendsto (fun n => mellinZeroProduct (fun i : Fin n => s i.val))
      Filter.atTop (nhds (mellinZeroProductLimit s)) := by
  apply tendsto_atTop_ciInf (mellinZeroProduct_prefix_antitone s hs hinj)
  refine ⟨0, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact Finset.prod_nonneg (fun _ _ => sq_nonneg _)

theorem mellinZeroProductLimit_bounds (s : ℕ → ℂ)
    (hs : ∀ j, (1 / 2 : ℝ) < (s j).re) (hinj : Function.Injective s) :
    0 ≤ mellinZeroProductLimit s ∧ mellinZeroProductLimit s ≤ 1 := by
  have ht := mellinZeroProduct_prefix_tendsto s hs hinj
  constructor
  · exact ge_of_tendsto' ht (fun _ => Finset.prod_nonneg (fun _ _ => sq_nonneg _))
  · apply le_of_tendsto' ht
    intro n
    have h := mellinZeroProduct_prefix_antitone s hs hinj (Nat.zero_le n)
    simpa [mellinZeroProduct] using h

end RiemannResearch.RH.Pareto

namespace RiemannResearch.RH.RamanujanZeroCertificates
open Pareto Pareto.CoefficientStabilization RamanujanCanonicalOptimizer
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Every finite actual zero family gives an exact product and full Mellin remainder. -/
theorem packet_zeroProduct_energy_exact (z : ι → ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (hinj : Function.Injective z)
    (hz1 : ∀ i, z i ≠ 1) (hzero : ∀ i, riemannZeta (z i) = 0) (n : ℕ) :
    1 - packetMass n = 1 - mellinZeroProduct z +
      ∫ x in Ioi (1 : ℝ),
        ‖mellinWeightedStep (hilbertOne - packetCandidate n) x -
          starRingEnd ℂ (finiteMellinKernel z
            (mellinInverseCoefficients z (fun i => 1 / z i)) x)‖ ^ 2 := by
  have h := packet_zeroInverse_energy_exact z hzre hz1 hzero
    ((mellinCauchyGram_det_ne_zero_iff_injective z hzre).mpr hinj) n
  rwa [mellinInverseCapacity_zeroSource_product z hzre hinj] at h

/-- The finite product bounds the actual Ramanujan captured mass. -/
theorem packetMass_le_zeroProduct (z : ι → ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (hinj : Function.Injective z)
    (hz1 : ∀ i, z i ≠ 1) (hzero : ∀ i, riemannZeta (z i) = 0) (n : ℕ) :
    packetMass n ≤ mellinZeroProduct z := by
  have h := packet_zeroProduct_energy_exact z hzre hinj hz1 hzero n
  have hn : 0 ≤ ∫ x in Ioi (1 : ℝ),
      ‖mellinWeightedStep (hilbertOne - packetCandidate n) x -
        starRingEnd ℂ (finiteMellinKernel z
          (mellinInverseCoefficients z (fun i => 1 / z i)) x)‖ ^ 2 :=
    integral_nonneg (fun _ => sq_nonneg _)
  linarith

/-- Complete arbitrary-competitor decomposition: product defect, full Mellin
remainder, and the entire packet Gram displacement. -/
theorem packet_zeroProduct_completion (z : ι → ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (hinj : Function.Injective z)
    (hz1 : ∀ i, z i ≠ 1) (hzero : ∀ i, riemannZeta (z i) = 0)
    (n : ℕ) (a : Fin n → ℝ) :
    ‖hilbertOne - Fintype.linearCombination ℝ
      (fun i : Fin n => ramanujanPacketHilbert (i.val + 2)) a‖ ^ 2 =
      1 - mellinZeroProduct z +
      (∫ x in Ioi (1 : ℝ),
        ‖mellinWeightedStep (hilbertOne - packetCandidate n) x -
          starRingEnd ℂ (finiteMellinKernel z
            (mellinInverseCoefficients z (fun i => 1 / z i)) x)‖ ^ 2) +
      ‖Fintype.linearCombination ℝ
        (fun i : Fin n => ramanujanPacketHilbert (i.val + 2))
        (a - packetCoefficients n)‖ ^ 2 := by
  rw [packet_completion, packet_zeroProduct_energy_exact z hzre hinj hz1 hzero n]

theorem zeroProduct_limitEnergy_lower_bound (z : ι → ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (hinj : Function.Injective z)
    (hz1 : ∀ i, z i ≠ 1) (hzero : ∀ i, riemannZeta (z i) = 0) :
    1 - mellinZeroProduct z ≤ limitEnergy := by
  have h := zeroInverseCapacity_le_limitEnergy z hzre hz1 hzero
    ((mellinCauchyGram_det_ne_zero_iff_injective z hzre).mpr hinj)
  rwa [mellinInverseCapacity_zeroSource_product z hzre hinj] at h

/-- A concrete packet mass rules out the proposed family consisting entirely of zeros. -/
theorem exists_zeta_ne_zero_of_packetMass_gt_zeroProduct (z : ι → ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (hinj : Function.Injective z)
    (hz1 : ∀ i, z i ≠ 1) (n : ℕ)
    (hmass : mellinZeroProduct z < packetMass n) :
    ∃ i, riemannZeta (z i) ≠ 0 := by
  classical
  by_contra hn
  have hzero : ∀ i, riemannZeta (z i) = 0 := by
    intro i
    by_contra hi
    exact hn ⟨i, hi⟩
  exact (not_lt_of_ge (packetMass_le_zeroProduct z hzre hinj hz1 hzero n)) hmass


/-- The entire decreasing zero-product limit bounds every finite captured mass. -/
theorem packetMass_le_zeroProductLimit (z : ℕ → ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (hinj : Function.Injective z)
    (hz1 : ∀ i, z i ≠ 1) (hzero : ∀ i, riemannZeta (z i) = 0) (n : ℕ) :
    packetMass n ≤ mellinZeroProductLimit z := by
  apply ge_of_tendsto' (mellinZeroProduct_prefix_tendsto z hzre hinj)
  intro k
  have hi : Function.Injective (fun i : Fin k => z i.val) := by
    intro i j hij
    exact Fin.ext (hinj hij)
  exact packetMass_le_zeroProduct (fun i : Fin k => z i.val)
    (fun i => hzre i.val) hi (fun i => hz1 i.val) (fun i => hzero i.val) n

/-- Countably many distinct actual zeros still leave the full unresolved residual budget. -/
theorem zeroProductLimit_limitEnergy_lower_bound (z : ℕ → ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (hinj : Function.Injective z)
    (hz1 : ∀ i, z i ≠ 1) (hzero : ∀ i, riemannZeta (z i) = 0) :
    1 - mellinZeroProductLimit z ≤ limitEnergy := by
  have h := le_of_tendsto' packetMass_tendsto
    (packetMass_le_zeroProductLimit z hzre hinj hz1 hzero)
  linarith

/-- Actual zero sequences have a strictly positive product, forced by one legal packet stage. -/
theorem zeroProductLimit_pos (z : ℕ → ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (hinj : Function.Injective z)
    (hz1 : ∀ i, z i ≠ 1) (hzero : ∀ i, riemannZeta (z i) = 0) :
    0 < mellinZeroProductLimit z :=
  lt_of_lt_of_le (packetMass_pos 1 (by decide))
    (packetMass_le_zeroProductLimit z hzre hinj hz1 hzero 1)

end RiemannResearch.RH.RamanujanZeroCertificates
