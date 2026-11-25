import RiemannResearch.RH.CenteredMeanMovingGramTail
import RiemannResearch.RH.ParetoCompactCutoffLimits
import RiemannResearch.RH.ParetoResidualShell

/-!
# Arbitrarily slowly exhausting physical windows for actual Gram drift

At a fixed base solve and physical starting point, the difference to the
later solve converges strongly. Truncating its tail at any window length
tending to infinity therefore discards vanishing energy. The scaled cofinal
criterion needs no minimum growth rate for this length relative to the later
solve or its period.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.DigammaSection
open CoefficientStabilization RamanujanCanonicalOptimizer

/-- The complete Pareto energy of the change of solve on the actual sites
`N + 1` through `N + H`. -/
def finiteSectionDriftWindow (B A N H : ℕ) : ℝ :=
  ∑ j ∈ Finset.range H, paretoWeight (j + N) *
    (sectionCoordinate (B + 1) (j + N + 1) - sectionCoordinate (A + 1) (j + N + 1)) ^ 2

/-- The finite window and its complete remaining physical tail partition the
localized change between the two actual digamma solves. -/
theorem finiteSectionDriftWindow_partition (B A N H : ℕ) (hBA : B ≤ A) :
    finiteSectionDriftWindow B A N H +
      ‖hilbertTailShift (packetUnitMean B - packetUnitMean A) (N + H)‖ ^ 2 =
        finiteSectionTailDrift B A N := by
  have h := hilbert_tail_shell_pairing (packetUnitMean B - packetUnitMean A)
    (packetUnitMean B - packetUnitMean A) N H
  simpa only [finiteSectionTailDrift_eq B A N hBA, finiteSectionDriftWindow,
    real_inner_self_eq_norm_sq, hilbertShellPairing_weighted, positiveWeight_succ,
    hilbertSequence_sub, Pi.sub_apply, sectionCoordinate_eq, pow_two] using h

private theorem tail_norm_sq_eq_complement (f : ThresholdHilbert) (N : ℕ) :
    ‖hilbertTailShift f N‖ ^ 2 = ‖f - compactHead N f‖ ^ 2 := by
  have h := compactHead_pythagoras N f
  simp only [compactHead_norm_sq_eq_physical_sum, hilbertGibbsPhysical_square] at h
  rw [hilbertTailShift_norm_sq]
  linarith only [h]

/-- For each fixed base solve and starting point, every cofinal window length
captures the entire later-solve drift asymptotically. The assertion is
unconditional, including when the centered boundary is nonzero. -/
theorem finiteSectionDriftWindow_omitted_tendsto_zero (B N : ℕ) (H : ℕ → ℕ)
    (hH : Tendsto H atTop atTop) :
    Tendsto (fun A : ℕ => finiteSectionTailDrift B A N - finiteSectionDriftWindow B A N (H A))
      atTop (𝓝 0) := by
  let f := fun A => packetUnitMean B - packetUnitMean A
  have hcut : Tendsto (fun A => N + H A) atTop atTop := by
    apply tendsto_atTop_mono (fun A => ?_) hH
    exact Nat.le_add_left _ _
  have hv := compactHead_moving_cofinal_tail_norm_tendsto_zero f
    (packetUnitMean B - packetUnitMeanLimit) (packetUnitMean_tendsto.const_sub _) _ hcut
  have ht : Tendsto (fun A => ‖f A - compactHead (N + H A) (f A)‖ ^ 2) atTop (𝓝 0) := by
    simpa only [zero_pow (by decide : 2 ≠ 0)] using hv.pow 2
  apply ht.congr'
  filter_upwards [eventually_ge_atTop B] with A hBA
  have h := finiteSectionDriftWindow_partition B A N (H A) hBA
  rw [tail_norm_sq_eq_complement] at h
  change ‖packetUnitMean B - packetUnitMean A -
    compactHead (N + H A) (packetUnitMean B - packetUnitMean A)‖ ^ 2 = _
  linarith only [h]

/-- The window can be prescribed before any later solve. For each base it
may grow arbitrarily slowly with the later cutoff. One common scaled bound on
these finite windows is necessary and sufficient for vanishing of the boundary. -/
theorem exists_scale_boundary_zero_iff_cofinal_driftWindow :
    ∃ b : ℝ, 0 < b ∧ ∀ K : ℕ → ℕ, CalibratedPhysicalSchedule b K →
      ∀ H : ℕ → ℕ → ℕ, (∀ B, Tendsto (H B) atTop atTop) →
      (boundary = 0 ↔ ∃ C : ℝ, ∃ᶠ B : ℕ in atTop, ∃ᶠ A : ℕ in atTop,
        (K B : ℝ) * sectionTailDamping b (K B) *
          finiteSectionDriftWindow B A (K B) (H B A) ≤ C) := by
  obtain ⟨b, hb, htest⟩ := exists_scale_boundary_zero_iff_cofinal_tailDrift
  refine ⟨b, hb, fun K hK H hH => ?_⟩
  rw [(htest K hK).2]
  let w := fun B : ℕ => (K B : ℝ) * sectionTailDamping b (K B)
  have hw B : 0 ≤ w B := mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le
  constructor
  · rintro ⟨C, h⟩
    refine ⟨C, h.mono fun B hB => ?_⟩
    apply (hB.and_eventually (eventually_ge_atTop B)).mono
    rintro A ⟨hA, hBA⟩
    have hpart := finiteSectionDriftWindow_partition B A (K B) (H B A) hBA
    have hwin : finiteSectionDriftWindow B A (K B) (H B A) ≤ finiteSectionTailDrift B A (K B) :=
      (le_add_of_nonneg_right (sq_nonneg _)).trans hpart.le
    exact (mul_le_mul_of_nonneg_left hwin (hw B)).trans hA
  · rintro ⟨C, h⟩
    refine ⟨C + 1, h.mono fun B hB => ?_⟩
    have ht := (finiteSectionDriftWindow_omitted_tendsto_zero B (K B) (H B) (hH B)).const_mul
      (w B)
    rw [mul_zero] at ht
    apply (hB.and_eventually (ht.eventually_lt_const (by norm_num : (0 : ℝ) < 1))).mono
    rintro A ⟨hA, hsmall⟩
    change w B * finiteSectionDriftWindow B A (K B) (H B A) ≤ C at hA
    change w B * (finiteSectionTailDrift B A (K B) -
      finiteSectionDriftWindow B A (K B) (H B A)) < 1 at hsmall
    change w B * finiteSectionTailDrift B A (K B) ≤ _
    linarith only [hA, hsmall]

/-- The positive exponent supplied by the cofinal window criterion. -/
def driftWindowExponent : {b : ℝ // 0 < b} :=
  ⟨exists_scale_boundary_zero_iff_cofinal_driftWindow.choose,
    exists_scale_boundary_zero_iff_cofinal_driftWindow.choose_spec.1⟩

/-- One common bound for the actual finite windows, at the supplied exponent,
implies Mathlib's Riemann hypothesis. -/
theorem riemannHypothesis_of_bounded_driftWindows (K : ℕ → ℕ)
    (hK : CalibratedPhysicalSchedule driftWindowExponent.val K)
    (H : ℕ → ℕ → ℕ) (hH : ∀ B, Tendsto (H B) atTop atTop)
    (C : ℝ) (hC : ∃ᶠ B : ℕ in atTop, ∃ᶠ A : ℕ in atTop,
      (K B : ℝ) * sectionTailDamping driftWindowExponent.val (K B) *
        finiteSectionDriftWindow B A (K B) (H B A) ≤ C) : RiemannHypothesis := by
  apply riemannHypothesis_of_boundary_eq_zero
  exact (exists_scale_boundary_zero_iff_cofinal_driftWindow.choose_spec.2 K hK H hH).mpr ⟨C, hC⟩

/-- info:
'RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.DigammaSection.riemannHypothesis_of_bounded_driftWindows'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms riemannHypothesis_of_bounded_driftWindows

end RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.DigammaSection
