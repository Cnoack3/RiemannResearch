/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.MonotoneAbelConvergence
import RiemannResearch.RH.DampedMobiusHalfHilbertConvergence

/-!
# Uniform convergence over the entire half-damping range

Full natural-order convergence at epsilon = 1/2 supplies a single
approximation modulus and norm bound for every epsilon >= 1/2.
The actual arithmetic Hilbert vectors and their energies are norm
continuous from the right at the endpoint, and conductor cutoffs may
grow at any independent rate while damping approaches one half.

The arithmetic input is the checked endpoint theorem in
`DampedMobiusHalfHilbertConvergence`. The transfer uses exact Abel
summation with positive decreasing weights (n+1)^(-(epsilon-1/2));
cancellation is retained inside each complete vector prefix.

Source for the underlying endpoint membership statement: J.-F. Burnol,
"On an analytic estimate in the theory of the Riemann zeta function and
a theorem of Baez-Duarte", Section 4, Lemma 4.1,
https://arxiv.org/abs/math/0202166. The uniform truncation transfer is
proved here explicitly; no mathematical novelty claim is made.
Subhalf finite energy and RH are not asserted.
-/

noncomputable section
open Filter Set
open scoped Topology BigOperators

namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis

/-- Exact conductorwise factorization into endpoint atoms and extra damping. -/
theorem dampedMobiusResidue_from_half (ε : ℝ) (m : ℕ) :
    arithmeticResidueTerm (dampedMobiusWeight ε) m =
      ((m + 1 : ℕ) : ℝ) ^ (-(ε - 1 / 2)) •
        arithmeticResidueTerm (dampedMobiusWeight (1 / 2)) m := by
  unfold arithmeticResidueTerm dampedMobiusWeight
  rw [smul_smul]
  congr 1
  have hp : ((m + 1 : ℕ) : ℝ) ^ (-ε) =
      ((m + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) *
        ((m + 1 : ℕ) : ℝ) ^ (-(ε - 1 / 2)) := by
    rw [← Real.rpow_add (by positivity)]
    congr 1
    ring
  rw [hp]
  ring

/-- Exact finite Abel input, retaining the signs of the endpoint atoms. -/
theorem dampedMobiusPartial_from_half (ε : ℝ) (M : ℕ) :
    arithmeticFloorHilbertPartial (dampedMobiusWeight ε) M =
      ∑ m ∈ Finset.range M, ((m + 1 : ℕ) : ℝ) ^ (-(ε - 1 / 2)) •
        (-arithmeticResidueTerm (dampedMobiusWeight (1 / 2)) m) := by
  simp only [arithmeticFloorHilbertPartial, dampedMobiusResidue_from_half ε,
    smul_neg, Finset.sum_neg_distrib]

/-- Extra power damping is decreasing in conductor throughout the half range. -/
theorem halfDampingWeights_antitone {ε : ℝ} (hε : (1 / 2 : ℝ) ≤ ε) :
    Antitone (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-(ε - 1 / 2))) := by
  intro i j hij
  exact Real.rpow_le_rpow_of_nonpos (by positivity)
    (by exact_mod_cast Nat.add_le_add_right hij 1) (by linarith)

/-- A single norm bound holds throughout the entire unconditional damping
range and for every conductor cutoff. -/
theorem dampedMobius_half_range_uniform_norm_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, (1 / 2 : ℝ) ≤ ε → ∀ M : ℕ,
      ‖arithmeticFloorHilbertPartial (dampedMobiusWeight ε) M‖ ≤ C := by
  obtain ⟨f, _, hf⟩ := dampedMobius_half_cutoffs_converge
  have h := hf.norm
  rw [← Nat.cofinite_eq_atTop] at h
  obtain ⟨C, hC⟩ := h.bddAbove_range_of_cofinite
  have hb (M : ℕ) :
      ‖arithmeticFloorHilbertPartial (dampedMobiusWeight (1 / 2)) M‖ ≤ C :=
    hC (Set.mem_range_self M)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hb 0)
  refine ⟨C, hC0, fun ε hε M => ?_⟩
  rw [dampedMobiusPartial_from_half]
  have hp (n : ℕ) :
      ‖signedVectorPrefix (fun m => -arithmeticResidueTerm (dampedMobiusWeight (1 / 2)) m) n‖ ≤ C := by
    simpa only [signedVectorPrefix, Finset.sum_neg_distrib,
      arithmeticFloorHilbertPartial] using hb n
  have h := signedVector_monotone_weight_norm_le
    (fun m => -arithmeticResidueTerm (dampedMobiusWeight (1 / 2)) m)
    _ (halfDampingWeights_antitone hε) (fun n => by positivity) hC0 hp M
  simpa only [Nat.zero_add, Nat.cast_one, Real.one_rpow, one_mul] using h

/-- The canonical arithmetic Hilbert vector on the unconditional half range. -/
def dampedMobiusHalfRangeLimit (ε : ℝ) (hε : (1 / 2 : ℝ) ≤ ε) : ThresholdHilbert :=
  (dampedMobius_cutoffs_converge_of_half_le hε).choose

theorem dampedMobiusHalfRangeLimit_spec (ε : ℝ) (hε : (1 / 2 : ℝ) ≤ ε) :
    (∀ n : ℕ, hilbertSequence (dampedMobiusHalfRangeLimit ε hε) n =
      dampedMobiusPrefix ε n - (n : ℝ) * (1 / riemannZeta (1 + (ε : ℂ))).re) ∧
    Tendsto (arithmeticFloorHilbertPartial (dampedMobiusWeight ε)) atTop
      (𝓝 (dampedMobiusHalfRangeLimit ε hε)) :=
  (dampedMobius_cutoffs_converge_of_half_le hε).choose_spec

/-- The full Hilbert approximations converge uniformly over all epsilon >=
one half, including the endpoint and with no upper bound on epsilon. -/
theorem dampedMobius_half_range_uniform_approximation :
    ∀ η : ℝ, 0 < η → ∃ K : ℕ, ∀ ε : ℝ, ∀ hε : (1 / 2 : ℝ) ≤ ε,
      ∀ M : ℕ, K ≤ M →
        ‖arithmeticFloorHilbertPartial (dampedMobiusWeight ε) M -
          dampedMobiusHalfRangeLimit ε hε‖ ≤ η := by
  obtain ⟨f, _, hf⟩ := dampedMobius_half_cutoffs_converge
  have hp : Tendsto (signedVectorPrefix
      (fun m => -arithmeticResidueTerm (dampedMobiusWeight (1 / 2)) m)) atTop (𝓝 f) := by
    convert hf using 1
    funext n
    simp only [signedVectorPrefix, Finset.sum_neg_distrib, arithmeticFloorHilbertPartial]
  intro η hη
  obtain ⟨K, hK⟩ := signedVector_monotone_weights_uniform_error _ hp η hη
  refine ⟨K, fun ε hε M hM => ?_⟩
  have hg := (dampedMobiusHalfRangeLimit_spec ε hε).2
  have hid := funext (dampedMobiusPartial_from_half ε)
  rw [hid] at hg
  rw [dampedMobiusPartial_from_half]
  exact hK _ (halfDampingWeights_antitone hε) (fun n => by positivity)
    (by simp) _ hg M hM

/-- One energy budget works for all dampings and all finite cutoffs. -/
theorem dampedMobius_half_range_uniform_energy_and_signed_bounds :
    ∃ B : ℝ, ∀ ε : ℝ, ∀ hε : (1 / 2 : ℝ) ≤ ε,
      (‖dampedMobiusHalfRangeLimit ε hε‖ ^ 2 ≤ B) ∧
      (∀ M : ℕ, dampedMobiusGramOffDiagonal ε M ≤ B) ∧
      (∀ H M : ℕ, dampedMobiusHeadOffDiagonal ε H M ≤ B) := by
  obtain ⟨C, hC, hb⟩ := dampedMobius_half_range_uniform_norm_bound
  refine ⟨C ^ 2, fun ε hε => ?_⟩
  have hn : ‖dampedMobiusHalfRangeLimit ε hε‖ ≤ C :=
    le_of_tendsto ((dampedMobiusHalfRangeLimit_spec ε hε).2.norm)
      (Eventually.of_forall (hb ε hε))
  have hsq (M : ℕ) :
      ‖arithmeticFloorHilbertPartial (dampedMobiusWeight ε) M‖ ^ 2 ≤ C ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hC).mpr (hb ε hε M)
  refine ⟨(sq_le_sq₀ (norm_nonneg _) hC).mpr hn,
    fun M => (dampedMobius_offDiagonal_le_partial_norm_sq ε M).trans (hsq M),
    fun H M => ?_⟩
  have hp := paretoHeadPairing_self_le H
    (arithmeticFloorHilbertPartial (dampedMobiusWeight ε) M)
  rw [dampedMobius_partial_head_eq_signed] at hp
  linarith [dampedMobiusHeadDiagonal_nonneg ε H M, hsq M]

/-- Damping may approach one half while the natural conductor cutoff grows
at any independent rate. The limit is the actual half-damped vector. -/
theorem dampedMobius_joint_damping_cutoff_tendsto :
    ∃ f : ThresholdHilbert,
      (∀ n : ℕ, hilbertSequence f n = dampedMobiusPrefix (1 / 2) n -
        (n : ℝ) * (1 / riemannZeta (1 + ((1 / 2 : ℝ) : ℂ))).re) ∧
      ∀ ε : ℕ → ℝ, (∀ j, (1 / 2 : ℝ) ≤ ε j) →
        Tendsto ε atTop (𝓝 (1 / 2)) →
        ∀ M : ℕ → ℕ, Tendsto M atTop atTop →
          Tendsto (fun j => arithmeticFloorHilbertPartial (dampedMobiusWeight (ε j)) (M j))
            atTop (𝓝 f) := by
  obtain ⟨f, hcoord, hf⟩ := dampedMobius_half_cutoffs_converge
  refine ⟨f, hcoord, fun ε hε hεlim M hM => ?_⟩
  have hp : Tendsto (signedVectorPrefix
      (fun m => -arithmeticResidueTerm (dampedMobiusWeight (1 / 2)) m)) atTop (𝓝 f) := by
    convert hf using 1
    funext n
    simp only [signedVectorPrefix, Finset.sum_neg_distrib, arithmeticFloorHilbertPartial]
  have hwlim (n : ℕ) :
      Tendsto (fun j => ((n + 1 : ℕ) : ℝ) ^ (-(ε j - 1 / 2))) atTop (𝓝 1) := by
    have h := (Real.continuous_const_rpow
      (by positivity : (((n + 1 : ℕ) : ℝ)) ≠ 0)).tendsto (0 : ℝ)
    simpa only [Function.comp_def, sub_self, neg_zero, Real.rpow_zero] using
      h.comp (by simpa only [sub_self, neg_zero] using (hεlim.sub_const (1 / 2)).neg)
  simpa only [dampedMobiusPartial_from_half] using
    signedVector_monotone_weights_joint_tendsto _ hp
      (fun j n => ((n + 1 : ℕ) : ℝ) ^ (-(ε j - 1 / 2)))
      (fun j => halfDampingWeights_antitone (hε j))
      (fun j n => by positivity) (fun j => by simp) hwlim M hM

/-- Uniform approximation permits arbitrary varying damping parameters
throughout the half range, even when they have no limit. -/
theorem dampedMobius_varying_damping_error_tendsto
    (ε : ℕ → ℝ) (hε : ∀ j, (1 / 2 : ℝ) ≤ ε j)
    (M : ℕ → ℕ) (hM : Tendsto M atTop atTop) :
    Tendsto (fun j =>
      ‖arithmeticFloorHilbertPartial (dampedMobiusWeight (ε j)) (M j) -
        dampedMobiusHalfRangeLimit (ε j) (hε j)‖) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro η hη
  obtain ⟨K, hK⟩ := dampedMobius_half_range_uniform_approximation (η / 2) (by positivity)
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (hM.eventually (eventually_ge_atTop K))
  refine ⟨J, fun j hj => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  exact (hK (ε j) (hε j) (M j) (hJ j hj)).trans_lt (by linarith)

/-- The actual arithmetic Hilbert vector is norm-continuous from the right
at half damping. No domination or bounded-energy hypothesis is assumed. -/
theorem dampedMobius_limit_tendsto_half
    (ε : ℕ → ℝ) (hε : ∀ j, (1 / 2 : ℝ) ≤ ε j)
    (hεlim : Tendsto ε atTop (𝓝 (1 / 2))) :
    Tendsto (fun j => dampedMobiusHalfRangeLimit (ε j) (hε j))
      atTop (𝓝 (dampedMobiusHalfRangeLimit (1 / 2) le_rfl)) := by
  obtain ⟨f, _, hjoint⟩ := dampedMobius_joint_damping_cutoff_tendsto
  have heq : f = dampedMobiusHalfRangeLimit (1 / 2) le_rfl :=
    tendsto_nhds_unique
      (hjoint (fun _ => 1 / 2) (fun _ => le_rfl) tendsto_const_nhds id tendsto_id)
      (dampedMobiusHalfRangeLimit_spec (1 / 2) le_rfl).2
  have hF := hjoint ε hε hεlim id tendsto_id
  have herr : Tendsto (fun j =>
      arithmeticFloorHilbertPartial (dampedMobiusWeight (ε j)) j -
        dampedMobiusHalfRangeLimit (ε j) (hε j)) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr
      (dampedMobius_varying_damping_error_tendsto ε hε id tendsto_id)
  simpa only [id_eq, sub_sub_cancel, sub_zero, heq] using hF.sub herr

/-- The complete arithmetic energy also tends to its endpoint value. -/
theorem dampedMobius_energy_tendsto_half
    (ε : ℕ → ℝ) (hε : ∀ j, (1 / 2 : ℝ) ≤ ε j)
    (hεlim : Tendsto ε atTop (𝓝 (1 / 2))) :
    Tendsto (fun j => ∑' n : ℕ, positiveWeight n *
      (dampedMobiusPrefix (ε j) n - (n : ℝ) *
        (1 / riemannZeta (1 + ((ε j) : ℂ))).re) ^ 2) atTop
      (𝓝 (∑' n : ℕ, positiveWeight n *
        (dampedMobiusPrefix (1 / 2) n - (n : ℝ) *
          (1 / riemannZeta (1 + ((1 / 2 : ℝ) : ℂ))).re) ^ 2)) := by
  have h := (dampedMobius_limit_tendsto_half ε hε hεlim).norm.pow 2
  simpa only [hilbert_norm_weighted_sq, (dampedMobiusHalfRangeLimit_spec _ _).1] using h

end RiemannResearch.RH.Pareto
