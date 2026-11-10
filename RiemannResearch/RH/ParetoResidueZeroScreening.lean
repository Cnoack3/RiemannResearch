import RiemannResearch.Analysis.ProjectionPairingSplit
import RiemannResearch.Analysis.FiniteHilbertGramMatrix
import RiemannResearch.RH.ParetoLCMRamanujanCertificate
import RiemannResearch.RH.ParetoResidueCriticalNormalLimit
import RiemannResearch.RH.ParetoResidueMovingCertificate
import RiemannResearch.RH.ParetoLCMZeroCertificate
import RiemannResearch.RH.ParetoBeurlingMellinObstruction
import Mathlib.Tactic.Linarith

/-!
# Zero-screened residue tests and the primal/dual Gram gap

Source: the user's complete-error research request, 9 November 2026.
The zero projection uses the already formalized finite residue version of
Burnol's zero-test strategy (Adv. Math. 170 (2002), 56-70, Section 5,
https://arxiv.org/abs/math/0103058). The new pairing estimates are standard
orthogonal-decomposition consequences, retaining both projected energies.
The complete Pareto norm, sparse Ramanujan source, and zero Gram are literal
existing objects, not independent surrogate matrices.

The final absorption criterion is a conditional research reduction. Its
uniform target-specific remainder estimate is Open. Critical-line statistics
and finite computations do not discharge it.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto.ResidueMellin
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.ProjectionPairingSplit
open RiemannResearch.Analysis.ResidualizedProjectionKernel (residual_norm_sq)
open MellinFrequency (criticalPoint)
variable {ι : Type*} [Fintype ι]

/-- The canonical zero certificate is the projection of every legal error. -/
theorem certificate_eq_error_projection {N : ℕ} {f : ThresholdHilbert}
    (hf : f ∈ trialSpace (N + 1)) (z : ι → ℂ)
    (hs : ∀ i, 0 < (z i).re) (hs1 : ∀ i, z i ≠ 1)
    (hz : ∀ i, riemannZeta (z i) = 0) :
    certificateVector N z =
      (synthesisSpan (rowVector N z)).starProjection (errorVector N f) := by
  obtain ⟨a, ha⟩ := exists_zero_normal N z hs hs1 hz
  change (synthesisSpan (rowVector N z)).starProjection (errorVector N 0) = _
  rw [← certificate_eq_projection ((trialSpace (N + 1)).zero_mem) z hs hs1 hz a ha,
    certificate_eq_projection hf z hs hs1 hz a ha]

/-- A signed known zero component plus the pairing of the two remaining vectors. -/
theorem zero_test_pairing_split {N : ℕ} {f : ThresholdHilbert}
    (hf : f ∈ trialSpace (N + 1)) (z : ι → ℂ)
    (hs : ∀ i, 0 < (z i).re) (hs1 : ∀ i, z i ≠ 1)
    (hz : ∀ i, riemannZeta (z i) = 0) (h : EuclideanSpace ℝ (Fin N)) :
    inner ℝ (errorVector N f) h =
      inner ℝ (certificateVector N z) ((synthesisSpan (rowVector N z)).starProjection h) +
      inner ℝ (errorVector N f - certificateVector N z)
        (h - (synthesisSpan (rowVector N z)).starProjection h) := by
  have he := pairing_split (synthesisSpan (rowVector N z)) (errorVector N f) h
  rw [← certificate_eq_error_projection hf z hs hs1 hz] at he
  exact he

/-- Both the target's remaining energy and the test's remaining energy enter. -/
theorem zero_test_pairing_remainder_sq_le {N : ℕ} {f : ThresholdHilbert}
    (hf : f ∈ trialSpace (N + 1)) (z : ι → ℂ)
    (hs : ∀ i, 0 < (z i).re) (hs1 : ∀ i, z i ≠ 1)
    (hz : ∀ i, riemannZeta (z i) = 0) (h : EuclideanSpace ℝ (Fin N)) :
    (inner ℝ (errorVector N f) h -
      inner ℝ (certificateVector N z) ((synthesisSpan (rowVector N z)).starProjection h)) ^ 2 ≤
      ‖errorVector N f - certificateVector N z‖ ^ 2 *
        (‖h‖ ^ 2 - ‖(synthesisSpan (rowVector N z)).starProjection h‖ ^ 2) := by
  have he := residual_pairing_sq_le (synthesisSpan (rowVector N z)) (errorVector N f) h
  rw [← residual_norm_sq (synthesisSpan (rowVector N z)) (errorVector N f),
    ← certificate_eq_error_projection hf z hs hs1 hz] at he
  exact he

/-- Literal primal Ramanujan and dual zero inverse Grams in one complete bound. -/
theorem lcm_primal_dual_gram_pairing_bound [DecidableEq ι]
    (M : ℕ) (z : ι → ℂ)
    (hs : ∀ i, 0 < (z i).re) (hs1 : ∀ i, z i ≠ 1)
    (hz : ∀ i, riemannZeta (z i) = 0)
    (hi : LinearIndependent ℝ (rowVector (lcmResidueIndex M) z))
    (h : EuclideanSpace ℝ (Fin (lcmResidueIndex M))) :
    let N := lcmResidueIndex M
    let v := rowVector N z
    let Z := gramMatrix v
    let b := source N z
    let k := cross v h
    let L := Nat.lcmUpto M
    (inner ℝ (errorVector N (lcmBest M)) h - dotProduct b (Z⁻¹.mulVec k)) ^ 2 ≤
      (1 - dotProduct (packetSource L) ((packetGram L)⁻¹.mulVec (packetSource L)) -
        classWeight N (Fin.last N) - dotProduct b (Z⁻¹.mulVec b)) *
      (‖h‖ ^ 2 - dotProduct k (Z⁻¹.mulVec k)) := by
  dsimp only
  have hf : lcmBest M ∈ trialSpace (lcmResidueIndex M + 1) := by
    rw [lcmResidueIndex_succ]
    exact lcmBest_mem M
  have hc : cross (rowVector (lcmResidueIndex M) z)
      (errorVector (lcmResidueIndex M) (lcmBest M)) = source (lcmResidueIndex M) z := by
    funext i
    exact error_observation hf z i (hs i.1) (hs1 i.1) (hz i.1)
  have he := error_norm_sq_split hf
  rw [lcm_error_eq_one_sub_packet_inverse] at he
  have hn : ‖errorVector (lcmResidueIndex M) (lcmBest M)‖ ^ 2 =
      1 - dotProduct (packetSource (Nat.lcmUpto M))
        ((packetGram (Nat.lcmUpto M))⁻¹.mulVec (packetSource (Nat.lcmUpto M))) -
        classWeight (lcmResidueIndex M) (Fin.last (lcmResidueIndex M)) := by
    linarith
  have hb := gram_pairing_remainder_sq_le hi
    (errorVector (lcmResidueIndex M) (lcmBest M)) h
  rw [hc, hn] at hb
  exact hb

/-- Conditional research reduction: a strict relative remainder estimate,
up to any vanishing additive budget, is enough. No optimal rate is required. -/
theorem riemannHypothesis_of_remainder_absorption (γ : ι → ℝ)
    (hγ : Function.Injective γ) (hpos : ∀ i, 0 < γ i)
    (hz : ∀ i, riemannZeta (criticalPoint (γ i)) = 0)
    (θ : ℝ) (hθ : θ < 1) (B : ℕ → ℝ) (hB : Tendsto B atTop (𝓝 0))
    (habsorb : ∀ᶠ M in atTop,
      lcmRemainder (fun i => criticalPoint (γ i)) M ≤ θ * lcmError M + B M) :
    RiemannHypothesis := by
  let E := ‖hilbertOne -
    ParetoBeurlingMellinObstruction.normalizedResidueSpan.topologicalClosure.starProjection hilbertOne‖ ^ 2
  have hE : Tendsto lcmError atTop (𝓝 E) := lcmError_tendsto
  have hR : Tendsto (lcmRemainder (fun i => criticalPoint (γ i))) atTop (𝓝 E) :=
    lcmRemainder_tendsto_limit γ hγ hpos hz
  have hup : Tendsto (fun M => θ * lcmError M + B M) atTop (𝓝 (θ * E)) := by
    simpa only [add_zero] using (hE.const_mul θ).add hB
  have hle : E ≤ θ * E := le_of_tendsto_of_tendsto hR hup habsorb
  have hzero : E = 0 := by
    have hn : 0 ≤ E := sq_nonneg _
    nlinarith
  apply riemannHypothesis_of_lcm_remainder γ hγ hpos hz
  simpa only [hzero] using hR


/-- A finite target-specific absorption estimate gives a complete error upper bound. -/
theorem lcm_error_le_of_remainder_absorption (M : ℕ) (z : ι → ℂ)
    (hs : ∀ i, 0 < (z i).re) (hs1 : ∀ i, z i ≠ 1)
    (hz : ∀ i, riemannZeta (z i) = 0) (θ B : ℝ) (hθ : θ < 1)
    (habsorb : lcmRemainder z M ≤ θ * lcmError M + B) :
    lcmError M ≤
      (classWeight (lcmResidueIndex M) (Fin.last (lcmResidueIndex M)) +
        certificateEnergy (lcmResidueIndex M) z + B) / (1 - θ) := by
  have he := lcm_best_error_eq M z hs hs1 hz
  change lcmError M = _ at he
  apply (le_div_iff₀ (sub_pos.mpr hθ)).mpr
  nlinarith

/-- The actual relative zero Gram row bound supplies the certificate part of
a complete error upper budget. The absorption premise is still Open. -/
theorem lcm_error_le_of_critical_gram_absorption [DecidableEq ι]
    (M : ℕ) (hN : 0 < lcmResidueIndex M) (γ : ι → ℝ)
    (hz : ∀ i, riemannZeta (criticalPoint (γ i)) = 0)
    (d : ℝ) (hd : 0 ≤ d) (hd' : d < 1 / 2)
    (hrow : ∀ i, (∑ j, |relativeCriticalGram γ (lcmResidueIndex M) i j -
      (if i = j then 1 / 2 else 0)|) ≤ d)
    (θ B : ℝ) (hθ : θ < 1)
    (habsorb : lcmRemainder (fun i => criticalPoint (γ i)) M ≤ θ * lcmError M + B) :
    lcmError M ≤
      (classWeight (lcmResidueIndex M) (Fin.last (lcmResidueIndex M)) +
        relativeCriticalSourceSq γ (lcmResidueIndex M) / (1 / 2 - d) /
          Chebyshev.psi (M : ℝ) + B) / (1 - θ) := by
  have hn : 0 < (lcmResidueIndex M : ℝ) := by exact_mod_cast hN
  have hl : 0 < Real.log ((lcmResidueIndex M : ℝ) + 1) :=
    Real.log_pos (by linarith)
  have hc := (critical_certificate_energy_bounds γ (lcmResidueIndex M) hN hz
    d hd hd' hrow).2
  have hup : certificateEnergy (lcmResidueIndex M) (fun i => criticalPoint (γ i)) ≤
      relativeCriticalSourceSq γ (lcmResidueIndex M) / (1 / 2 - d) /
        Chebyshev.psi (M : ℝ) := by
    rw [← lcm_log_eq_psi]
    exact (le_div_iff₀ hl).mpr (by simpa only [mul_comm] using hc)
  exact (lcm_error_le_of_remainder_absorption M (fun i => criticalPoint (γ i))
    (fun i => by simp) (fun i => MellinFrequency.criticalPoint_ne_one (γ i))
    hz θ B hθ habsorb).trans
      (div_le_div_of_nonneg_right (by linarith) (sub_pos.mpr hθ).le)

end RiemannResearch.RH.Pareto.ResidueMellin
