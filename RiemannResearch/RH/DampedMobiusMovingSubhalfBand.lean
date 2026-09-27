/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.IncreasingAbelConvergence
import RiemannResearch.RH.DampedMobiusUniformHalfRange

/-!
# Natural-order convergence in a shrinking subhalf band

The half-damped Möbius cutoff limit remains valid when damping approaches
one half from below and the conductor amplification stays bounded.
In particular, every fixed logarithmic band
  0 ≤ 1/2 - ε ≤ A / log(M+1)
has the same limit as M tends to infinity.

The unconditional arithmetic input is the previously checked half-damping
Hilbert convergence. The proof retains the signs in complete vector
prefixes and uses increasing-weight Abel regularity. This does not prove
finite energy at any fixed damping below one half, and does not approach
the zero-damping hypothesis needed for RH.

Source for the underlying endpoint membership statement: J.-F. Burnol,
"On an analytic estimate in the theory of the Riemann zeta function and
a theorem of Baez-Duarte", Section 4, Lemma 4.1,
https://arxiv.org/abs/math/0202166. The moving-band transfer is a direct
finite Abel argument; no mathematical novelty claim is made.
-/

noncomputable section
open Filter Set
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis

/-- Subhalf damping may move with the conductor cutoff, with any common
finite bound on its multiplicative conductor amplification. -/
theorem dampedMobius_moving_subhalf_tendsto
    (ε : ℕ → ℝ) (hε : ∀ j, ε j ≤ (1 / 2 : ℝ))
    (hεlim : Tendsto ε atTop (𝓝 (1 / 2)))
    (M : ℕ → ℕ) (hM : Tendsto M atTop atTop)
    {B : ℝ} (hB : 0 < B)
    (hband : ∀ j, ((M j + 1 : ℕ) : ℝ) ^ ((1 / 2 : ℝ) - ε j) ≤ B) :
    Tendsto (fun j => arithmeticFloorHilbertPartial (dampedMobiusWeight (ε j)) (M j))
      atTop (𝓝 (dampedMobiusHalfRangeLimit (1 / 2) le_rfl)) := by
  have hf := (dampedMobiusHalfRangeLimit_spec (1 / 2) le_rfl).2
  have hp : Tendsto (signedVectorPrefix
      (fun m => -arithmeticResidueTerm (dampedMobiusWeight (1 / 2)) m)) atTop
        (𝓝 (dampedMobiusHalfRangeLimit (1 / 2) le_rfl)) := by
    convert hf using 1
    funext n
    simp only [signedVectorPrefix, Finset.sum_neg_distrib, arithmeticFloorHilbertPartial]
  have hw (j : ℕ) : Monotone
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ ((1 / 2 : ℝ) - ε j)) := by
    intro i k hik
    exact Real.rpow_le_rpow (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hik 1) (sub_nonneg.mpr (hε j))
  have hwlim (n : ℕ) :
      Tendsto (fun j => ((n + 1 : ℕ) : ℝ) ^ ((1 / 2 : ℝ) - ε j))
        atTop (𝓝 1) := by
    have h := (Real.continuous_const_rpow
      (by positivity : (((n + 1 : ℕ) : ℝ)) ≠ 0)).tendsto (0 : ℝ)
    simpa only [Function.comp_def, Real.rpow_zero] using
      h.comp (by simpa using hεlim.const_sub (1 / 2 : ℝ))
  have h := signedVector_increasing_weights_joint_tendsto _ hp
    (fun j n => ((n + 1 : ℕ) : ℝ) ^ ((1 / 2 : ℝ) - ε j)) hw
    (fun j n => by positivity) hwlim M hM hB hband
  simpa only [dampedMobiusPartial_from_half,
    show ∀ j, -(ε j - 1 / 2) = (1 / 2 : ℝ) - ε j by intro j; ring] using h

/-- The damping convergence follows automatically from a common bound on
(1/2-epsilon) log(M+1). Thus a full band of width A/log(M+1) below the
endpoint has the endpoint's full signed Hilbert limit. -/
theorem dampedMobius_logarithmic_subhalf_band_tendsto
    (ε : ℕ → ℝ) (hε : ∀ j, ε j ≤ (1 / 2 : ℝ))
    (M : ℕ → ℕ) (hM : Tendsto M atTop atTop)
    (A : ℝ)
    (hband : ∀ j, ((1 / 2 : ℝ) - ε j) * Real.log ((M j + 1 : ℕ) : ℝ) ≤ A) :
    Tendsto (fun j => arithmeticFloorHilbertPartial (dampedMobiusWeight (ε j)) (M j))
      atTop (𝓝 (dampedMobiusHalfRangeLimit (1 / 2) le_rfl)) := by
  have hlog : Tendsto (fun j => Real.log ((M j + 1 : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hM))
  have hrecip : Tendsto (fun j => A / Real.log ((M j + 1 : ℕ) : ℝ))
      atTop (𝓝 0) := by
    simpa only [mul_zero, div_eq_mul_inv, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp hlog).const_mul A
  have hd : Tendsto (fun j => (1 / 2 : ℝ) - ε j) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun j => sub_nonneg.mpr (hε j))) _ hrecip
    filter_upwards [hlog.eventually (eventually_gt_atTop (0 : ℝ))] with j hj
    exact (le_div_iff₀ hj).mpr (hband j)
  have hεlim : Tendsto ε atTop (𝓝 (1 / 2)) := by
    have h := hd.const_sub (1 / 2)
    simpa only [sub_sub_cancel, sub_zero] using h
  apply dampedMobius_moving_subhalf_tendsto ε hε hεlim M hM (Real.exp_pos A)
  intro j
  rw [Real.rpow_def_of_pos (by positivity)]
  exact Real.exp_le_exp.mpr (by simpa only [mul_comm] using hband j)

/-- The entire logarithmic band converges uniformly. The conductor and the
damping are independently quantified inside the band, and the bound uses
the complete infinite physical Hilbert norm. -/
theorem dampedMobius_logarithmic_subhalf_band_uniform
    (A : ℝ) :
    ∀ η : ℝ, 0 < η → ∃ J : ℕ, ∀ M : ℕ, J ≤ M → ∀ ε : ℝ,
      ε ≤ (1 / 2 : ℝ) →
      ((1 / 2 : ℝ) - ε) * Real.log ((M + 1 : ℕ) : ℝ) ≤ A →
      ‖arithmeticFloorHilbertPartial (dampedMobiusWeight ε) M -
        dampedMobiusHalfRangeLimit (1 / 2) le_rfl‖ ≤ η := by
  intro η hη
  by_contra h
  push Not at h
  choose M hMJ ε hε hband hbad using h
  have hM : Tendsto M atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop b] with j hj
    exact hj.trans (hMJ j)
  have hc := dampedMobius_logarithmic_subhalf_band_tendsto ε hε M hM A hband
  obtain ⟨J, hJ⟩ := Metric.tendsto_atTop.mp hc η hη
  have hgood : ‖arithmeticFloorHilbertPartial (dampedMobiusWeight (ε J)) (M J) -
      dampedMobiusHalfRangeLimit (1 / 2) le_rfl‖ < η := by
    simpa only [dist_eq_norm] using hJ J le_rfl
  linarith [hbad J]

/-- A single signed energy budget works for every finite cutoff in a
fixed logarithmic subhalf band. The budget also bounds every finite
physical signed off-diagonal head independently of its head cutoff. -/
theorem dampedMobius_logarithmic_subhalf_band_signed_bounds
    (A : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, ∀ ε : ℝ, ε ≤ (1 / 2 : ℝ) →
      ((1 / 2 : ℝ) - ε) * Real.log ((M + 1 : ℕ) : ℝ) ≤ A →
      (‖arithmeticFloorHilbertPartial (dampedMobiusWeight ε) M‖ ≤ C) ∧
      (dampedMobiusGramOffDiagonal ε M ≤ C ^ 2) ∧
      ∀ H : ℕ, dampedMobiusHeadOffDiagonal ε H M ≤ C ^ 2 := by
  obtain ⟨B, hB, hb⟩ := dampedMobius_half_range_uniform_norm_bound
  refine ⟨2 * Real.exp A * B, by positivity, fun M ε hε hband => ?_⟩
  have hp (n : ℕ) :
      ‖signedVectorPrefix
        (fun m => -arithmeticResidueTerm (dampedMobiusWeight (1 / 2)) m) n‖ ≤ B := by
    simpa only [signedVectorPrefix, Finset.sum_neg_distrib,
      arithmeticFloorHilbertPartial] using hb (1 / 2) le_rfl n
  have hw : Monotone (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ ((1 / 2 : ℝ) - ε)) := by
    intro i j hij
    exact Real.rpow_le_rpow (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hij 1) (sub_nonneg.mpr hε)
  have ht : ((M + 1 : ℕ) : ℝ) ^ ((1 / 2 : ℝ) - ε) ≤ Real.exp A := by
    rw [Real.rpow_def_of_pos (by positivity)]
    exact Real.exp_le_exp.mpr (by simpa only [mul_comm] using hband)
  have hn : ‖arithmeticFloorHilbertPartial (dampedMobiusWeight ε) M‖ ≤
      2 * Real.exp A * B := by
    rw [dampedMobiusPartial_from_half, show -(ε - 1 / 2) = (1 / 2 : ℝ) - ε by ring]
    apply (signedVector_increasing_weight_norm_le _ _ hw
      (fun n => by positivity) hB hp M).trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht (by norm_num)) hB
  have hsq : ‖arithmeticFloorHilbertPartial (dampedMobiusWeight ε) M‖ ^ 2 ≤
      (2 * Real.exp A * B) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hn
  refine ⟨hn, (dampedMobius_offDiagonal_le_partial_norm_sq ε M).trans hsq, fun H => ?_⟩
  have hphead := paretoHeadPairing_self_le H
    (arithmeticFloorHilbertPartial (dampedMobiusWeight ε) M)
  rw [dampedMobius_partial_head_eq_signed] at hphead
  linarith [dampedMobiusHeadDiagonal_nonneg ε H M]

/-- The whole finite signed Gram energy also converges in the logarithmic
subhalf band; the conclusion is about cutoff vectors, not a hypothetical
infinite vector at a fixed subhalf damping. -/
theorem dampedMobius_logarithmic_subhalf_band_energy_tendsto
    (ε : ℕ → ℝ) (hε : ∀ j, ε j ≤ (1 / 2 : ℝ))
    (M : ℕ → ℕ) (hM : Tendsto M atTop atTop)
    (A : ℝ)
    (hband : ∀ j, ((1 / 2 : ℝ) - ε j) * Real.log ((M j + 1 : ℕ) : ℝ) ≤ A) :
    Tendsto (fun j =>
      ‖arithmeticFloorHilbertPartial (dampedMobiusWeight (ε j)) (M j)‖ ^ 2) atTop
      (𝓝 (∑' n : ℕ, positiveWeight n *
        (dampedMobiusPrefix (1 / 2) n - (n : ℝ) *
          (1 / riemannZeta (1 + ((1 / 2 : ℝ) : ℂ))).re) ^ 2)) := by
  have h := (dampedMobius_logarithmic_subhalf_band_tendsto ε hε M hM A hband).norm.pow 2
  simpa only [hilbert_norm_weighted_sq,
    (dampedMobiusHalfRangeLimit_spec (1 / 2) le_rfl).1] using h

end RiemannResearch.RH.Pareto
