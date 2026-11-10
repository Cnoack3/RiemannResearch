/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QEuclidCarryRay
import RiemannResearch.RH.QPrimorialMatchedGram
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Positivity

/-!
# Weighted Euclid rays for the actual matched primorial displacement

Source: *Squarefree projection displacement and infinite CRT carries*,
9 November 2026, Sections 10 and 12.3. The weights are the coefficients of
the actual matched displacement, including every divisor conductor. A
finite stage admits a common depth making the combined boundary arbitrarily
small. The signed prime/carry combination remains.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.QPrimorialRayAssembly

open ZetaTwoHilbert QEuclidCarryRay QPrimeCarryProjection
open QPrimorialMatchedDisplacement QSquarefreePrimorialCofinality QPrimorialMatchedGram

def primeSum (n : ℕ) (c : DivisorIndex n → ℝ) (N : ℕ) : QHilbert :=
  ∑ i, c i • ∑ k ∈ Finset.range N, primeBranch (divisorConductor n i) k

def carrySum (n : ℕ) (c : DivisorIndex n → ℝ) (N : ℕ) : QHilbert :=
  ∑ i, c i • ∑ k ∈ Finset.range N, carryBranch (divisorConductor n i) k

def boundarySum (n : ℕ) (c : DivisorIndex n → ℝ) (N : ℕ) : QHilbert :=
  ∑ i, c i • boundary (divisorConductor n i) N

theorem primeSum_mem (n : ℕ) (c : DivisorIndex n → ℝ) (N : ℕ) :
    primeSum n c N ∈ primeClosure := by
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro k _
  unfold primeBranch
  apply Submodule.smul_mem
  exact qResidue_mem_primeClosure _ (radix_prime _ (divisorConductor_gt_one n i) k)

theorem weighted_telescope (n : ℕ) (c : DivisorIndex n → ℝ) (N : ℕ) :
    primeSum n c N + carrySum n c N + boundarySum n c N =
      ∑ i, c i • qResidue (divisorConductor n i) := by
  unfold primeSum carrySum boundarySum
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← smul_add, ← smul_add, sum_branches]

theorem boundarySum_tendsto (n : ℕ) (c : DivisorIndex n → ℝ) :
    Tendsto (boundarySum n c) atTop (𝓝 0) := by
  have h : ∀ i : DivisorIndex n,
      Tendsto (fun N => c i • boundary (divisorConductor n i) N) atTop (𝓝 0) := by
    intro i
    simpa only [smul_zero] using
      (tendsto_const_nhds (x := c i)).smul
        (boundary_tendsto _ (divisorConductor_gt_one n i))
  change Tendsto (fun N => ∑ i, c i • boundary (divisorConductor n i) N) atTop (𝓝 0)
  simpa only [Finset.sum_const_zero] using
    tendsto_finsetSum Finset.univ (fun i _ => h i)

/-- The exact signed telescope for the difference of the two complete solves. -/
theorem canonical_telescope (n N : ℕ) :
    stageDisplacement n = primeSum n (displacementCoefficients n) N +
      carrySum n (displacementCoefficients n) N + boundarySum n (displacementCoefficients n) N :=
  (stageDisplacement_expansion n).trans (weighted_telescope n _ N).symm

/-- A diagonal choice of depths makes the actual total boundary arbitrarily
small while retaining the entire canonical signed combination. -/
theorem exists_diagonal_branch_decomposition :
    let c := displacementCoefficients
    ∃ N : ℕ → ℕ,
      (∀ n, stageDisplacement n =
        primeSum n (c n) (N n) + carrySum n (c n) (N n) + boundarySum n (c n) (N n)) ∧
      (∀ n, ‖boundarySum n (c n) (N n)‖ < (1 / 2 : ℝ) ^ n) ∧
      Tendsto (fun n => primeSum n (c n) (N n) + carrySum n (c n) (N n))
        atTop (𝓝 QSquarefreeDisplacementRigidity.displacement) := by
  let c := displacementCoefficients
  change ∃ N : ℕ → ℕ, _
  have hN (n : ℕ) : ∃ k, ‖boundarySum n (c n) k‖ < (1 / 2 : ℝ) ^ n := by
    have hrad : 0 < (1 / 2 : ℝ) ^ n := by positivity
    have he := (boundarySum_tendsto n (c n)).eventually (Metric.ball_mem_nhds 0 hrad)
    simpa only [Metric.mem_ball, dist_zero_right] using he.exists
  choose N hN using hN
  refine ⟨N, fun n => canonical_telescope n (N n), hN, ?_⟩
  have hgeo : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).tendsto_atTop_zero
  have hb : Tendsto (fun n => boundarySum n (c n) (N n)) atTop (𝓝 0) :=
    squeeze_zero_norm (fun n => (hN n).le) hgeo
  have ht := stageDisplacement_tendsto.sub hb
  rw [sub_zero] at ht
  apply ht.congr'
  exact Eventually.of_forall fun n => by
    change stageDisplacement n - boundarySum n (displacementCoefficients n) (N n) =
      primeSum n (displacementCoefficients n) (N n) + carrySum n (displacementCoefficients n) (N n)
    rw [canonical_telescope n (N n)] <;> abel

end RiemannResearch.RH.QPrimorialRayAssembly
