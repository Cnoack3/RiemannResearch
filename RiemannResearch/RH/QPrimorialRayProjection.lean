/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QPrimorialRayAssembly
import RiemannResearch.RH.QPrimorialMatchedGram
import RiemannResearch.RH.QPrimorialMatchedDisplacement
import RiemannResearch.RH.QSquarefreeDisplacementRigidity
import RiemannResearch.RH.QPrimeCarryProjection
import RiemannResearch.RH.QPrimeProjectionControl
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Choose

/-!
# Actual ray coefficients, projected feedback, and normalized boundaries

Source: user-provided *Squarefree projection displacement and infinite CRT
carries*, 9 November 2026, Sections 10 and 12.3. The branch weights are the
actual complete inverse-Gram coefficient differences. The signed sums
converge after the stated projections, and a diagonal can control any
prescribed normalized conductor test, however rapidly its conductor grows.
No vanishing of the limiting prime or carry component is asserted.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QPrimorialRayProjection
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer
open QPrimorialRayAssembly QPrimorialMatchedGram QPrimorialMatchedDisplacement
open QPrimeCarryProjection QSquarefreeDisplacementRigidity QSquarefreeFiniteDisplacement

def assembledPrime (n N : ℕ) : QHilbert :=
  primeSum n (displacementCoefficients n) N +
    primeClosure.starProjection (carrySum n (displacementCoefficients n) N)

def assembledCarry (n N : ℕ) : QHilbert :=
  primeClosureᗮ.starProjection (carrySum n (displacementCoefficients n) N)

theorem assembledPrime_exact (n N : ℕ) :
    assembledPrime n N = primeClosure.starProjection
      (stageDisplacement n - boundarySum n (displacementCoefficients n) N) := by
  rw [canonical_telescope n N, add_sub_cancel_right, map_add,
    primeClosure.starProjection_eq_self_iff.mpr (primeSum_mem n _ N)]
  rfl

theorem assembledCarry_exact (n N : ℕ) :
    assembledCarry n N = primeClosureᗮ.starProjection
      (stageDisplacement n - boundarySum n (displacementCoefficients n) N) := by
  rw [canonical_telescope n N, add_sub_cancel_right, map_add,
    Submodule.starProjection_orthogonal_apply_eq_zero (primeSum_mem n _ N), zero_add]
  rfl

theorem assembledPrime_tendsto (D : ℕ → ℕ)
    (hb : Tendsto (fun n => boundarySum n (displacementCoefficients n) (D n))
      atTop (𝓝 0)) :
    Tendsto (fun n => assembledPrime n (D n)) atTop (𝓝 primeDisplacement) := by
  have ht : Tendsto
      (fun n => stageDisplacement n - boundarySum n (displacementCoefficients n) (D n))
      atTop (𝓝 displacement) := by
    simpa only [sub_zero] using stageDisplacement_tendsto.sub hb
  have hp := (primeClosure.starProjection.continuous.tendsto displacement).comp ht
  apply hp.congr'
  exact Eventually.of_forall fun n => (assembledPrime_exact n (D n)).symm

theorem assembledCarry_tendsto (D : ℕ → ℕ)
    (hb : Tendsto (fun n => boundarySum n (displacementCoefficients n) (D n))
      atTop (𝓝 0)) :
    Tendsto (fun n => assembledCarry n (D n)) atTop (𝓝 carryDisplacement) := by
  have ht : Tendsto
      (fun n => stageDisplacement n - boundarySum n (displacementCoefficients n) (D n))
      atTop (𝓝 displacement) := by
    simpa only [sub_zero] using stageDisplacement_tendsto.sub hb
  have hp := (primeClosureᗮ.starProjection.continuous.tendsto displacement).comp ht
  have he : primeClosureᗮ.starProjection displacement = carryDisplacement := by
    rw [Submodule.starProjection_orthogonal]
    change displacement - primeClosure.starProjection displacement = carryDisplacement
    exact carryDisplacement_eq_sub.symm
  rw [he] at hp
  apply hp.congr'
  exact Eventually.of_forall fun n => (assembledCarry_exact n (D n)).symm

theorem assembledPrime_tendsto_zero_iff (D : ℕ → ℕ)
    (hb : Tendsto (fun n => boundarySum n (displacementCoefficients n) (D n))
      atTop (𝓝 0)) :
    Tendsto (fun n => assembledPrime n (D n)) atTop (𝓝 0) ↔ displacement = 0 := by
  constructor
  · intro h
    exact primeDisplacement_eq_zero_iff.mp
      (tendsto_nhds_unique (assembledPrime_tendsto D hb) h)
  · intro hd
    simpa only [primeDisplacement_eq_zero_iff.mpr hd] using assembledPrime_tendsto D hb

theorem normalized_test_bound (m : ℕ) (hm : 2 ≤ m) (f : QHilbert) :
    |(zetaTwo * (m : ℝ)) * inner ℝ (qResidue m) f| ≤
      Real.sqrt (2 * zetaTwo * (m : ℝ)) * ‖f‖ := by
  have hmR : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  calc
    _ = (zetaTwo * (m : ℝ)) * |inner ℝ (qResidue m) f| := by
      rw [abs_mul, abs_of_nonneg (mul_nonneg zetaTwo_pos.le hmR)]
    _ ≤ (zetaTwo * (m : ℝ)) * (‖qResidue m‖ * ‖f‖) :=
      mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _)
        (mul_nonneg zetaTwo_pos.le hmR)
    _ = ((zetaTwo * (m : ℝ)) * ‖qResidue m‖) * ‖f‖ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (scaled_qResidue_norm_le m hm) (norm_nonneg _)

/-- The diagonal controls both the vector boundary and a prescribed,
arbitrarily large normalized conductor test. -/
theorem exists_normalized_diagonal (m : ℕ → ℕ) :
    ∃ D : ℕ → ℕ,
      (∀ n, ‖boundarySum n (displacementCoefficients n) (D n)‖ < (1 / 2 : ℝ) ^ n) ∧
      (∀ n, 2 ≤ m n →
        |(zetaTwo * (m n : ℝ)) * inner ℝ (qResidue (m n))
          (boundarySum n (displacementCoefficients n) (D n))| < (1 / 2 : ℝ) ^ n) := by
  let w : ℕ → ℝ := fun n => Real.sqrt (2 * zetaTwo * (m n : ℝ))
  have hw (n : ℕ) : 0 ≤ w n := Real.sqrt_nonneg _
  have hex (n : ℕ) : ∃ k,
      ‖boundarySum n (displacementCoefficients n) k‖ <
        (1 / 2 : ℝ) ^ n / (1 + w n) := by
    have hp : 0 < (1 / 2 : ℝ) ^ n / (1 + w n) := by positivity
    have he := (boundarySum_tendsto n (displacementCoefficients n)).eventually
      (Metric.ball_mem_nhds 0 hp)
    simpa only [Metric.mem_ball, dist_zero_right] using he.exists
  choose D hD using hex
  have hprod (n : ℕ) :
      ‖boundarySum n (displacementCoefficients n) (D n)‖ * (1 + w n) <
        (1 / 2 : ℝ) ^ n := (lt_div_iff₀ (by linarith [hw n])).mp (hD n)
  refine ⟨D, ?_, ?_⟩
  · intro n
    have hnonneg := mul_nonneg (norm_nonneg (boundarySum n (displacementCoefficients n) (D n))) (hw n)
    nlinarith only [hprod n, hnonneg]
  · intro n hn
    have htest := normalized_test_bound (m n) hn
      (boundarySum n (displacementCoefficients n) (D n))
    change _ ≤ w n * ‖boundarySum n (displacementCoefficients n) (D n)‖ at htest
    nlinarith only [htest, hprod n,
      norm_nonneg (boundarySum n (displacementCoefficients n) (D n))]

def branchPairing (n m N : ℕ) : ℝ :=
  (zetaTwo * (m : ℝ)) * inner ℝ (qResidue m)
    (primeSum n (displacementCoefficients n) N + carrySum n (displacementCoefficients n) N)

/-- The original canonical Gram row, with the signed boundary retained. -/
theorem branchPairing_exact (n m N : ℕ) :
    branchPairing n m N = normalizedPairing n m -
      (zetaTwo * (m : ℝ)) * inner ℝ (qResidue m)
        (boundarySum n (displacementCoefficients n) N) := by
  rw [normalizedPairing, canonical_telescope n N, inner_add_right, mul_add,
    add_sub_cancel_right]
  rfl

/-- All actual coefficients are retained, while the boundary is negligible
even for a moving normalized conductor. No projection convergence rate is used. -/
theorem exists_diagonal_energy_detection (m : ℕ → ℕ)
    (hm : Tendsto m atTop atTop)
    (hmem : ∀ᶠ n in atTop,
      qResidue (m n) ∈ QSquarefreePrimorialCofinality.primorialStage n) :
    ∃ D : ℕ → ℕ,
      (∀ n, ‖boundarySum n (displacementCoefficients n) (D n)‖ < (1 / 2 : ℝ) ^ n) ∧
      Tendsto (fun n => assembledPrime n (D n)) atTop (𝓝 primeDisplacement) ∧
      Tendsto (fun n => assembledCarry n (D n)) atTop (𝓝 carryDisplacement) ∧
      Tendsto (fun n => branchPairing n (m n) (D n)) atTop
        (𝓝 (‖toPareto pResidual‖ ^ 2)) := by
  obtain ⟨D, hD, htest⟩ := exists_normalized_diagonal m
  have hg : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).tendsto_atTop_zero
  have hb : Tendsto (fun n => boundarySum n (displacementCoefficients n) (D n))
      atTop (𝓝 0) := squeeze_zero_norm (fun n => (hD n).le) hg
  have ht : Tendsto (fun n => (zetaTwo * (m n : ℝ)) * inner ℝ (qResidue (m n))
      (boundarySum n (displacementCoefficients n) (D n))) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hg
    filter_upwards [hm.eventually (eventually_ge_atTop 2)] with n hn
    rw [Real.norm_eq_abs]
    exact (htest n hn).le
  refine ⟨D, hD, assembledPrime_tendsto D hb, assembledCarry_tendsto D hb, ?_⟩
  have hlim := (normalizedPairing_tendsto id m tendsto_id hm hmem).sub ht
  rw [sub_zero] at hlim
  apply hlim.congr'
  exact Eventually.of_forall fun n => (branchPairing_exact n (m n) (D n)).symm

end RiemannResearch.RH.QPrimorialRayProjection
