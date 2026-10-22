/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.RoughComponentProjection
import RiemannResearch.RH.ParetoArithmeticRepair
import RiemannResearch.RH.ThresholdInfiniteCertificate
import RiemannResearch.RH.TwoSeedExactHeadEnergy
import RiemannResearch.Analysis.DestructiveComponentEnergy

/-!
# Linear root-component energy and necessary signed cancellation

Source: continuation of the full two-seed exact-head energy research,
14 September 2026. The component is the actual arithmetic projection onto
the 2,3-smooth root component; it is assembled algebraically from the legal
packet. No continuous extension of this projection is asserted. The exact
head forces its four-floor profile, whose head energy is asymptotic to N/9.
Thus every sublinear full-energy witness must use increasingly complete
cancellation with its complementary arithmetic components.
-/

namespace RiemannResearch.RH.Pareto.RootComponentExactHeadEnergy

open scoped BigOperators Topology
open Filter TwoSeedThreshold
open RiemannResearch.Analysis.DestructiveComponentEnergy

noncomputable section
attribute [local instance] Classical.propDecidable

private theorem seeds_pos : ∀ a ∈ ({2, 3} : Set ℕ), 0 < a := by
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl <;> omega

theorem roughComponentProjection_zero (q : ℕ) :
    roughComponentProjection q (0 : ℕ → ℝ) = 0 := by
  funext n
  simp [roughComponentProjection, mobiusDifference]

theorem roughComponentProjection_add (q : ℕ) (f g : ℕ → ℝ) :
    roughComponentProjection q (f + g) =
      roughComponentProjection q f + roughComponentProjection q g := by
  funext n
  change (∑ d ∈ Finset.Icc 1 n, if InRoughComponent q d then
    mobiusDifference d (fun k => f k + g k) * OneBoundaryRepair.floorBlock d n else 0) =
    (∑ d ∈ Finset.Icc 1 n, if InRoughComponent q d then
      mobiusDifference d f * OneBoundaryRepair.floorBlock d n else 0) +
    (∑ d ∈ Finset.Icc 1 n, if InRoughComponent q d then
      mobiusDifference d g * OneBoundaryRepair.floorBlock d n else 0)
  simp_rw [mobiusDifference_add_fn]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  split_ifs <;> ring

theorem roughComponentProjection_smul (q : ℕ) (c : ℝ) (f : ℕ → ℝ) :
    roughComponentProjection q (c • f) = c • roughComponentProjection q f := by
  funext n
  change (∑ d ∈ Finset.Icc 1 n, if InRoughComponent q d then
    mobiusDifference d (fun k => c * f k) * OneBoundaryRepair.floorBlock d n else 0) =
    c * (∑ d ∈ Finset.Icc 1 n, if InRoughComponent q d then
      mobiusDifference d f * OneBoundaryRepair.floorBlock d n else 0)
  simp_rw [mobiusDifference_const_mul_fn]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  split_ifs <;> ring

/-- The root projection selects complete generators and stays in the finite
legal span. This supplies its existence in the actual Hilbert space. -/
theorem rootProjection_mem_legal {f : ℕ → ℝ}
    (hf : f ∈ legalSeedSpan ({2, 3} : Set ℕ)) :
    roughComponentProjection 1 f ∈ legalSeedSpan ({2, 3} : Set ℕ) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, ha, m, hm, rfl⟩ := hf
    have ha' : a = 2 ∨ a = 3 := by simpa using ha
    have he : certificateGenerator a m = dilation m (residue a) := by
      funext k
      exact certificateGenerator_eq_dilation a m k
    have hp : roughComponentProjection 1 (dilation m (residue a)) =
        if InRoughComponent 1 m then dilation m (residue a) else 0 := by
      funext k
      have h := roughComponentProjection_generator 1 a m k (by omega)
        (by decide) ha' hm
      by_cases hm' : InRoughComponent 1 m <;> simpa only [he, hm', ↓reduceIte, Pi.zero_apply] using h
    rw [hp]
    split_ifs
    · exact dilation_generator_mem _ ha hm
    · exact (legalSeedSpan ({2, 3} : Set ℕ)).zero_mem
  | zero =>
    rw [roughComponentProjection_zero]
    exact (legalSeedSpan ({2, 3} : Set ℕ)).zero_mem
  | add f g hf hg ihf ihg =>
    rw [roughComponentProjection_add]
    exact (legalSeedSpan ({2, 3} : Set ℕ)).add_mem ihf ihg
  | smul c f hf ih =>
    rw [roughComponentProjection_smul]
    exact (legalSeedSpan ({2, 3} : Set ℕ)).smul_mem c ih

private theorem rootComponent_exists (f : ThresholdHilbert)
    (hf : f ∈ hilbertLegalSubspace ({2, 3} : Set ℕ)) :
    ∃ u : ThresholdHilbert, u ∈ hilbertLegalSubspace ({2, 3} : Set ℕ) ∧
      hilbertSequence u = roughComponentProjection 1 (hilbertSequence f) := by
  exact legalSeedSpan_exists_hilbert ({2, 3} : Set ℕ) seeds_pos
    (rootProjection_mem_legal hf)

/-- The unique Hilbert realization of the algebraic root projection. Its
definition is only on finite legal vectors, where existence is proved. -/
def rootComponent (f : ThresholdHilbert)
    (hf : f ∈ hilbertLegalSubspace ({2, 3} : Set ℕ)) : ThresholdHilbert :=
  (rootComponent_exists f hf).choose

theorem rootComponent_mem (f : ThresholdHilbert)
    (hf : f ∈ hilbertLegalSubspace ({2, 3} : Set ℕ)) :
    rootComponent f hf ∈ hilbertLegalSubspace ({2, 3} : Set ℕ) :=
  (rootComponent_exists f hf).choose_spec.1

theorem rootComponent_sequence (f : ThresholdHilbert)
    (hf : f ∈ hilbertLegalSubspace ({2, 3} : Set ℕ)) :
    hilbertSequence (rootComponent f hf) =
      roughComponentProjection 1 (hilbertSequence f) :=
  (rootComponent_exists f hf).choose_spec.2

/-- Initial coordinates determine the actual projected initial coordinates. -/
theorem roughComponentProjection_congr_initial {F G : ℕ → ℝ} {N n : ℕ}
    (q : ℕ) (hn : n ≤ N) (hhead : ∀ k ≤ N, F k = G k) :
    roughComponentProjection q F n = roughComponentProjection q G n := by
  unfold roughComponentProjection
  apply Finset.sum_congr rfl
  intro d hd
  rw [mobiusDifference_congr_initial
    ((Finset.mem_Icc.mp hd).2.trans hn) hhead]

/-- No component-profile hypothesis is supplied: the exact legal head forces it. -/
theorem rootComponent_exact_head {N : ℕ} (f : ThresholdHilbert)
    (hf : f ∈ hilbertLegalSubspace ({2, 3} : Set ℕ))
    (hhead : ∀ k, 0 < k → k ≤ N → hilbertSequence f k = 1)
    (n : ℕ) (hn : n ≤ N) :
    hilbertSequence (rootComponent f hf) n = roughHeadProfile 1 n := by
  rw [rootComponent_sequence]
  have hinit : ∀ k ≤ N,
      hilbertSequence f k = (if k = 0 then 0 else (1 : ℝ)) := by
    intro k hk
    by_cases hk0 : k = 0
    · simp [hk0, hilbertSequence_zero]
    · simpa only [if_neg hk0] using hhead k (Nat.pos_of_ne_zero hk0) hk
  rw [roughComponentProjection_congr_initial 1 hn hinit]
  simpa using roughComponentProjection_one 1 (by omega) (by decide) n

/-- The entire forced head, and therefore its asymptotic N/9 cost, lies inside
the root component's full norm. The remaining tail has not been dropped from
the definition of the norm. -/
theorem root_head_energy_le_norm_sq {N : ℕ} (f : ThresholdHilbert)
    (hf : f ∈ hilbertLegalSubspace ({2, 3} : Set ℕ))
    (hhead : ∀ k, 0 < k → k ≤ N → hilbertSequence f k = 1) :
    (N : ℝ) * roughComponentAverage 1 N ≤ ‖rootComponent f hf‖ ^ 2 := by
  let u := rootComponent f hf
  have hs := (summable_nat_add_iff 1).2 (hilbertSequence_square_summable u)
  have hl := hs.sum_le_tsum (Finset.range N)
    (fun k _ => mul_nonneg (positiveWeight_nonneg _) (sq_nonneg _))
  have hsum : (∑ k ∈ Finset.range N,
      positiveWeight (k + 1) * hilbertSequence u (k + 1) ^ 2) =
      ∑ k ∈ Finset.range N,
        positiveWeight (k + 1) * roughHeadProfile 1 (k + 1) ^ 2 := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [rootComponent_exact_head f hf hhead (k + 1)
      (by have := Finset.mem_range.mp hk; omega)]
  have hnorm : (∑' k, positiveWeight (k + 1) * hilbertSequence u (k + 1) ^ 2) =
      ‖u‖ ^ 2 := by
    simpa only [hilbertSequence_weighted_square] using (hilbert_norm_sq u).symm
  rw [hsum, hnorm] at hl
  have havg : (N : ℝ) * roughComponentAverage 1 N =
      ∑ k ∈ Finset.range N,
        positiveWeight (k + 1) * roughHeadProfile 1 (k + 1) ^ 2 := by
    by_cases hN : N = 0
    · simp [hN, roughComponentAverage]
    · have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN
      simp [roughComponentAverage, hNR]
  rw [havg]
  exact hl

/-- Uniform over every actual legal witness, with no bound on its dilation
budget. The numerical 1/18 is any convenient constant below the exact 1/9. -/
theorem eventual_root_linear_lower :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ f : ThresholdHilbert,
      ∀ hf : f ∈ hilbertLegalSubspace ({2, 3} : Set ℕ),
      (∀ k, 0 < k → k ≤ N → hilbertSequence f k = 1) →
      (N : ℝ) / 18 ≤ ‖rootComponent f hf‖ ^ 2 := by
  have ht := roughComponentAverage_tendsto 1 (by omega)
  have he : ∀ᶠ N : ℕ in atTop, (1 / 18 : ℝ) < roughComponentAverage 1 N :=
    ht.eventually (lt_mem_nhds (by norm_num))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp he
  refine ⟨N₀, ?_⟩
  intro N hN f hf hhead
  calc
    (N : ℝ) / 18 = (N : ℝ) * (1 / 18) := by ring
    _ ≤ (N : ℝ) * roughComponentAverage 1 N :=
      mul_le_mul_of_nonneg_left (hN₀ N hN).le (Nat.cast_nonneg N)
    _ ≤ _ := root_head_energy_le_norm_sq f hf hhead

/-- A uniform lower angle between the root and its complement would force
linear full-energy growth. Thus such a coercivity estimate cannot prove
subpolynomial upper bounds. -/
theorem eventual_full_linear_lower_of_angle (ρ : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ f : ThresholdHilbert,
      ∀ hf : f ∈ hilbertLegalSubspace ({2, 3} : Set ℕ),
      (∀ k, 0 < k → k ≤ N → hilbertSequence f k = 1) →
      (-(ρ * (‖rootComponent f hf‖ * ‖f - rootComponent f hf‖)) ≤
        inner ℝ (rootComponent f hf) (f - rootComponent f hf)) →
      (1 - ρ) * ((N : ℝ) / 18) ≤ ‖f‖ ^ 2 := by
  obtain ⟨N₀, hN₀⟩ := eventual_root_linear_lower
  refine ⟨N₀, ?_⟩
  intro N hN f hf hhead hangle
  have hroot := hN₀ N hN f hf hhead
  have hfull := full_energy_lower_of_angle f (rootComponent f hf) ρ hρ hangle
  have hpos : 0 ≤ 1 - ρ := by linarith
  have htail := mul_nonneg hpos (sq_nonneg ‖f - rootComponent f hf‖)
  have hh := mul_le_mul_of_nonneg_left hroot hpos
  nlinarith

/-- Quantitative necessary cancellation for actual legal exact-head vectors. -/
theorem root_mixed_deviation_sq_le (f : ThresholdHilbert)
    (hf : f ∈ hilbertLegalSubspace ({2, 3} : Set ℕ)) :
    (inner ℝ (rootComponent f hf) (f - rootComponent f hf) +
      ‖rootComponent f hf‖ ^ 2) ^ 2 ≤ ‖rootComponent f hf‖ ^ 2 * ‖f‖ ^ 2 :=
  mixed_deviation_sq_le f (rootComponent f hf)

/-- An explicit rate for the compulsory cancellation, measured against the
root component's own energy. The right side uses the actual full energy. -/
theorem eventual_normalized_root_cancellation :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ f : ThresholdHilbert,
      ∀ hf : f ∈ hilbertLegalSubspace ({2, 3} : Set ℕ),
      (∀ k, 0 < k → k ≤ N → hilbertSequence f k = 1) →
      (inner ℝ (rootComponent f hf) (f - rootComponent f hf) /
        ‖rootComponent f hf‖ ^ 2 + 1) ^ 2 ≤ 18 * (‖f‖ ^ 2 / (N : ℝ)) := by
  obtain ⟨N₀, hN₀⟩ := eventual_root_linear_lower
  refine ⟨max N₀ 1, ?_⟩
  intro N hN f hf hhead
  have hNpos : 0 < N := by omega
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hNpos
  have hroot := hN₀ N (by omega) f hf hhead
  have hD : 0 < ‖rootComponent f hf‖ ^ 2 :=
    (div_pos hNR (by norm_num : (0 : ℝ) < 18)).trans_le hroot
  have hu : rootComponent f hf ≠ 0 := by
    intro hz
    simp [hz] at hD
  have hratio : ‖f‖ ^ 2 / ‖rootComponent f hf‖ ^ 2 ≤
      18 * (‖f‖ ^ 2 / (N : ℝ)) := by
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ hD hNR).mpr
    have hm := mul_le_mul_of_nonneg_left hroot (sq_nonneg ‖f‖)
    nlinarith
  exact (normalized_mixed_deviation_sq_le f (rootComponent f hf) hu).trans hratio

/-- Every sublinear full-energy family has asymptotically complete destructive
mixing with the actual root component. The squared expression tends to zero,
so its signed normalized mixed product tends to minus one. -/
theorem normalized_root_mixed_deviation_tendsto_zero
    (F : ℕ → ThresholdHilbert)
    (hlegal : ∀ N, F N ∈ hilbertLegalSubspace ({2, 3} : Set ℕ))
    (hhead : ∀ N k, 0 < k → k ≤ N → hilbertSequence (F N) k = 1)
    (hsub : Tendsto (fun N : ℕ => ‖F N‖ ^ 2 / (N : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ =>
      (inner ℝ (rootComponent (F N) (hlegal N))
        (F N - rootComponent (F N) (hlegal N)) /
          ‖rootComponent (F N) (hlegal N)‖ ^ 2 + 1) ^ 2)
      atTop (𝓝 0) := by
  obtain ⟨N₀, hN₀⟩ := eventual_normalized_root_cancellation
  have hrhs : Tendsto (fun N : ℕ => 18 * (‖F N‖ ^ 2 / (N : ℝ)))
      atTop (𝓝 0) := by simpa only [mul_zero] using hsub.const_mul 18
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ => sq_nonneg _) _ hrhs
  filter_upwards [eventually_ge_atTop N₀] with N hN
  exact hN₀ N hN (F N) (hlegal N) (hhead N)

/-- Any sublinear full-energy family must violate each fixed angle bound.
The tail and every signed mixed product remain in the statement. -/
theorem no_uniform_root_angle_of_sublinear_energy
    (F : ℕ → ThresholdHilbert)
    (hlegal : ∀ N, F N ∈ hilbertLegalSubspace ({2, 3} : Set ℕ))
    (hhead : ∀ N k, 0 < k → k ≤ N → hilbertSequence (F N) k = 1)
    (hsub : Tendsto (fun N : ℕ => ‖F N‖ ^ 2 / (N : ℝ)) atTop (𝓝 0)) :
    ¬ ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ N : ℕ,
      -(ρ * (‖rootComponent (F N) (hlegal N)‖ *
        ‖F N - rootComponent (F N) (hlegal N)‖)) ≤
      inner ℝ (rootComponent (F N) (hlegal N))
        (F N - rootComponent (F N) (hlegal N)) := by
  rintro ⟨ρ, hρ, hρ1, hangle⟩
  obtain ⟨N₀, hN₀⟩ := eventual_full_linear_lower_of_angle ρ hρ hρ1
  have hp : 0 < (1 - ρ) / 18 := div_pos (sub_pos.mpr hρ1) (by norm_num)
  have he := hsub.eventually_lt_const hp
  obtain ⟨N, hN, hsmall⟩ :=
    ((eventually_ge_atTop (max N₀ 1)).and he).exists
  have hNpos : 0 < N := by omega
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hNpos
  have hlarge := hN₀ N (by omega) (F N) (hlegal N) (hhead N) (hangle N)
  have hsmall' := (div_lt_iff₀ hNR).mp hsmall
  nlinarith

end
end RiemannResearch.RH.Pareto.RootComponentExactHeadEnergy
