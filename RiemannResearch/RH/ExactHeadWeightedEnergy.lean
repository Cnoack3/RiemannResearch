import RiemannResearch.Analysis.WeightedMellinHeadTail
import RiemannResearch.RH.ParetoMellinHardyEndpoint

/-!
# Exact-head weighted energy of the canonical Mobius family

Source: the user's September 24, 2026 moving-Hardy-bound research request.
The actual physical step function and Mellin transform are the repository's
existing ones. All infinite tails are retained, including the exact nonnegative
weight defect. This module supplies weighted inequalities, not an RH proof.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace RiemannResearch.RH.Pareto
open WeightedMellin

theorem complexPhysicalStep_critical_energy (f : ThresholdHilbert) :
    energy (complexPhysicalStep f) 1 = ‖f‖^2 := by
  rw [← mellinWeightedStep_energy]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  dsimp only
  rw [mellinWeightedStep_norm_sq]
  simp only [complexPhysicalStep, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  norm_num [Real.rpow_neg hx0.le]
  ring

theorem zeroHead_weightedEnergy_le (f : ThresholdHilbert) (N : ℕ)
    (hhead : ∀ k, 0 < k → k ≤ N → hilbertSequence f k = 0)
    (u : ℝ) (hu : 1 ≤ u) :
    energy (complexPhysicalStep f) u ≤ ((N : ℝ)+1)^(1-u) * ‖f‖^2 := by
  rw [← complexPhysicalStep_critical_energy]
  apply energy_le_power_mul_of_zero_head (complexPhysicalStep_finiteEnergy f) hu
    (by linarith [Nat.cast_nonneg (α := ℝ) N])
  intro x hx hxb
  have hfloor : 0 < ⌊x⌋₊ := Nat.floor_pos.mpr hx.le
  have hle : ⌊x⌋₊ ≤ N := by
    have hf := Nat.floor_le (by linarith : 0 ≤ x)
    have : (⌊x⌋₊ : ℝ) < (N : ℝ)+1 := lt_of_le_of_lt hf hxb
    have hlt : ⌊x⌋₊ < N+1 := by
      exact_mod_cast (show (⌊x⌋₊ : ℝ) < ((N+1 : ℕ) : ℝ) by simpa using this)
    omega
  simp [complexPhysicalStep, hhead _ hfloor hle]

theorem canonicalMobiusResidual_weightedEnergy_le (N : ℕ) (u : ℝ) (hu : 1 ≤ u) :
    energy (complexPhysicalStep (hilbertOne - canonicalMobiusHilbert N)) u ≤
      ((N : ℝ)+1)^(1-u) * ‖hilbertOne - canonicalMobiusHilbert N‖^2 := by
  apply zeroHead_weightedEnergy_le _ N _ u hu
  intro k hk hkN
  change hilbertSequenceLinear (hilbertOne - canonicalMobiusHilbert N) k = 0
  rw [map_sub]
  change hilbertSequence hilbertOne k - hilbertSequence (canonicalMobiusHilbert N) k = 0
  rw [hilbertOne_sequence, canonicalMobiusHilbert_exact N k hk hkN]
  simp [zeroAnchor, Nat.ne_of_gt hk]

theorem canonicalMobiusResidual_hardyLine_le (N : ℕ) (u σ : ℝ)
    (hu : 1 ≤ u) (hσ : u/2 < σ) :
    (∫ w : ℝ, ‖paretoMellin (hilbertOne - canonicalMobiusHilbert N)
      (verticalPoint σ w)‖^2) ≤
      ((N : ℝ)+1)^(1-u) * ‖hilbertOne - canonicalMobiusHilbert N‖^2 := by
  have hf := finiteEnergy_mono
    (complexPhysicalStep_finiteEnergy (hilbertOne - canonicalMobiusHilbert N)) hu
  have h := hardy_energy_le hf hσ
  rw [complexPhysicalStep_transform] at h
  exact h.trans (canonicalMobiusResidual_weightedEnergy_le N u hu)
end RiemannResearch.RH.Pareto


namespace RiemannResearch.RH.Pareto
open MeasureTheory Set Filter
open scoped Topology

theorem complexPhysicalStep_exact_head_ae {f : ThresholdHilbert} (N : ℕ)
    (hhead : ∀ k : ℕ, 1 ≤ k → k ≤ N → hilbertSequence f k = 1) :
    ∀ᵐ x ∂volume.restrict (Ioc 1 ((N : ℝ) + 1)),
      complexPhysicalStep f x = 1 := by
  have hne : ∀ᵐ x : ℝ ∂volume, x ≠ (N : ℝ) + 1 := by
    rw [ae_iff]
    simp
  filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae hne] with x hx hxb
  have hx0 : 0 ≤ x := le_trans zero_le_one hx.1.le
  have hfloor1 : 1 ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx0).2 (by simpa using hx.1.le)
  have hfloorN : ⌊x⌋₊ ≤ N := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt hx0).2
    simpa only [Nat.cast_succ] using lt_of_le_of_ne hx.2 hxb
  simp only [complexPhysicalStep, hhead _ hfloor1 hfloorN, Complex.ofReal_one]

theorem canonicalMobius_weighted_energy_sharp (N : ℕ) {u : ℝ} (hu : 1 ≤ u) :
    WeightedMellin.energy (complexPhysicalStep (canonicalMobiusHilbert N)) u ≤
      (1 - ((N : ℝ) + 1) ^ (-u)) / u +
      ((N : ℝ) + 1) ^ (1 - u) *
        (WeightedMellin.energy (complexPhysicalStep (canonicalMobiusHilbert N)) 1 -
          1 + 1 / ((N : ℝ) + 1)) := by
  apply WeightedMellin.energy_le_exact_head_add_power_tail
    (complexPhysicalStep_finiteEnergy _) (by linarith [Nat.cast_nonneg (α := ℝ) N]) hu
  exact complexPhysicalStep_exact_head_ae N (canonicalMobiusHilbert_exact N)

theorem canonicalMobius_weighted_energy_exact (N : ℕ) {u : ℝ} (hu : 1 ≤ u) :
    WeightedMellin.energy (complexPhysicalStep (canonicalMobiusHilbert N)) u =
      (1 - ((N : ℝ) + 1) ^ (-u)) / u +
      ((N : ℝ) + 1) ^ (1 - u) *
        (WeightedMellin.energy (complexPhysicalStep (canonicalMobiusHilbert N)) 1 -
          1 + 1 / ((N : ℝ) + 1)) -
        WeightedMellin.headTailWeightDefect
          (complexPhysicalStep (canonicalMobiusHilbert N)) ((N : ℝ) + 1) u := by
  apply WeightedMellin.energy_eq_exact_head_add_power_tail_sub_defect
    (complexPhysicalStep_finiteEnergy _) (by linarith [Nat.cast_nonneg (α := ℝ) N]) hu
  exact complexPhysicalStep_exact_head_ae N (canonicalMobiusHilbert_exact N)

theorem canonicalMobius_hardy_line_sharp (N : ℕ) {u σ : ℝ}
    (hu : 1 ≤ u) (hσ : u / 2 < σ) :
    (∫ w : ℝ, ‖paretoMellin (canonicalMobiusHilbert N)
      (WeightedMellin.verticalPoint σ w)‖ ^ 2) ≤
      (1 - ((N : ℝ) + 1) ^ (-u)) / u +
      ((N : ℝ) + 1) ^ (1 - u) *
        (WeightedMellin.energy (complexPhysicalStep (canonicalMobiusHilbert N)) 1 -
          1 + 1 / ((N : ℝ) + 1)) := by
  calc
    _ ≤ WeightedMellin.energy (complexPhysicalStep (canonicalMobiusHilbert N)) u := by
      rw [← complexPhysicalStep_transform]
      exact WeightedMellin.hardy_energy_le
        (WeightedMellin.finiteEnergy_mono (complexPhysicalStep_finiteEnergy _) hu) hσ
    _ ≤ _ := canonicalMobius_weighted_energy_sharp N hu

/-- Exact signed decomposition of each ordinary angular Hardy line integral. -/
theorem canonicalMobius_angular_line_exact (N : ℕ) {σ : ℝ} (hσ : 1 / 2 < σ) :
    (1 / (2 * Real.pi)) *
      (∫ t : ℝ, ‖paretoMellin (canonicalMobiusHilbert N)
        ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) =
      (1 - ((N : ℝ) + 1) ^ (-(2 * σ))) / (2 * σ) +
      ((N : ℝ) + 1) ^ (1 - 2 * σ) *
        (WeightedMellin.energy (complexPhysicalStep (canonicalMobiusHilbert N)) 1 -
          1 + 1 / ((N : ℝ) + 1)) -
        WeightedMellin.headTailWeightDefect
          (complexPhysicalStep (canonicalMobiusHilbert N)) ((N : ℝ) + 1) (2 * σ) := by
  rw [← complexPhysicalStep_transform,
    WeightedMellin.angular_plancherel (complexPhysicalStep_finiteEnergy _) hσ]
  exact canonicalMobius_weighted_energy_exact N (by linarith)

end RiemannResearch.RH.Pareto
