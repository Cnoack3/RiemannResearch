import RiemannResearch.RH.CenteredMeanDriftWindows
import RiemannResearch.RH.ParetoMobiusHeadInterpolation

/-!
# Period-free finite Gram drift estimates

Möbius head interpolation controls the physical amplitude of every legal
cutoff vector by a polynomial in the dictionary cutoff. For the normalized
Gram sections their complete squared change is an exact reciprocal-mass drop.
Thus the tail estimate for two actual solves uses the gain and the later
dictionary cutoff, with no least common multiple. Prescribed finite ranges
of later solves can all meet any positive stretched budget unconditionally.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.DigammaSection
open CoefficientStabilization RamanujanCanonicalOptimizer
open RiemannResearch.Analysis.ExhaustiveWalk

/-- Squared amplification of normalized Möbius head interpolation at solve
cutoff `A`, whose dictionary ends at conductor `A + 2`. -/
def gramCutoffAmplification (A : ℕ) : ℝ :=
  4 * (2 * ((A : ℝ) + 1) + 1) ^ 2 * ((A : ℝ) + 1)

theorem gramCutoffAmplification_mono : Monotone gramCutoffAmplification := by
  intro A B h
  unfold gramCutoffAmplification
  gcongr

private theorem legal_physical_tail_le (A N : ℕ) (f : ThresholdHilbert)
    (hf : f ∈ finiteSpace (A + 1)) :
    ‖hilbertTailShift f N‖ ^ 2 ≤ gramCutoffAmplification A * ‖f‖ ^ 2 / ((N : ℝ) + 1) := by
  rw [tail_norm_sq_eq_complement]
  simpa only [gramCutoffAmplification, Nat.cast_add, Nat.cast_one] using
    finiteSpace_complete_tail_norm_sq_le (A + 1) N f hf

/-- Every two-solve tail is bounded by the smaller of the exact full gain
and the cutoff-dependent fraction of the same gain. -/
theorem finiteSectionTailDrift_le_cutoffGain (B A N : ℕ) (hBA : B ≤ A) :
    finiteSectionTailDrift B A N ≤
      min ((packetMass (B + 1))⁻¹ - (packetMass (A + 1))⁻¹)
        (gramCutoffAmplification A * ((packetMass (B + 1))⁻¹ - (packetMass (A + 1))⁻¹) /
          ((N : ℝ) + 1)) := by
  let f := packetUnitMean B - packetUnitMean A
  have hv : f ∈ finiteSpace (A + 1) :=
    (finiteSpace (A + 1)).sub_mem
      (walkSpan_mono residueAtom id (Nat.add_le_add_right hBA 1) (packetUnitMean_legal B))
      (packetUnitMean_legal A)
  rw [finiteSectionTailDrift_eq B A N hBA, ← packetUnitMean_nested_distance B A hBA]
  apply le_min
  · rw [hilbertTailShift_norm_sq]
    exact sub_le_self _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  · exact legal_physical_tail_le A N f hv

/-- The base section's physical tail admits a polynomial-in-cutoff budget
at every physical site, including sites before its arithmetic period. -/
theorem finiteSectionTailCost_le_cutoffMass (B N : ℕ) :
    finiteSectionTailCost B N ≤
      (2 + 2 * gramCutoffAmplification B * (packetMass (B + 1))⁻¹) / ((N : ℝ) + 1) := by
  let x := hilbertTailShift (packetUnitMean B) N
  let y := hilbertTailShift hilbertOne N
  have he : hilbertTailShift (packetUnitMean B - hilbertOne) N = x - y := by ext j; rfl
  have hplus := sq_nonneg ‖x + y‖
  rw [norm_add_sq_real] at hplus
  have hdiff : ‖x - y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
    rw [norm_sub_sq_real]
    linarith only [hplus]
  have hx := legal_physical_tail_le B N (packetUnitMean B) (packetUnitMean_legal B)
  rw [packetUnitMean_energy] at hx
  have hy : ‖y‖ ^ 2 = 1 / ((N : ℝ) + 1) := tailShift_one_norm_sq N
  rw [finiteSectionTailCost_eq, he]
  apply hdiff.trans
  rw [hy]
  change 2 * ‖hilbertTailShift (packetUnitMean B) N‖ ^ 2 + _ ≤ _
  calc
    _ ≤ 2 * (gramCutoffAmplification B * (packetMass (B + 1))⁻¹ /
        ((N : ℝ) + 1)) + 2 * (1 / ((N : ℝ) + 1)) := by linarith only [hx]
    _ = _ := by ring

private theorem scaled_bound (s x C : ℝ) (N : ℕ) (hs : 0 ≤ s) (hx : 0 ≤ x)
    (h : x ≤ C / ((N : ℝ) + 1)) : (N : ℝ) * s * x ≤ s * C := by
  have hm := (le_div_iff₀ (by positivity)).mp h
  have hn : (N : ℝ) * x ≤ C := by linarith only [hm, hx]
  linarith only [mul_le_mul_of_nonneg_left hn hs]

/-- The scaled later-solve cost retains its actual reciprocal-mass gain. -/
theorem finiteSectionTailDrift_scaled_le_cutoffGain (b : ℝ) (B A N : ℕ) (hBA : B ≤ A) :
    (N : ℝ) * sectionTailDamping b N * finiteSectionTailDrift B A N ≤
      sectionTailDamping b N * gramCutoffAmplification A *
        ((packetMass (B + 1))⁻¹ - (packetMass (A + 1))⁻¹) := by
  have hd : 0 ≤ finiteSectionTailDrift B A N := by
    rw [finiteSectionTailDrift_eq B A N hBA]
    exact sq_nonneg _
  have h := (finiteSectionTailDrift_le_cutoffGain B A N hBA).trans (min_le_right _ _)
  simpa only [mul_assoc] using scaled_bound (sectionTailDamping b N) _ _ N (Real.exp_pos _).le hd h

/-- The stretched scaled base cost is controlled by a polynomial and the
single exact base mass, independently of its period. -/
theorem finiteSectionTailCost_scaled_le_cutoffMass (b : ℝ) (B N : ℕ) :
    (N : ℝ) * sectionTailDamping b N * finiteSectionTailCost B N ≤
      sectionTailDamping b N * (2 + 2 * gramCutoffAmplification B * (packetMass (B + 1))⁻¹) := by
  have hd : 0 ≤ finiteSectionTailCost B N := by rw [finiteSectionTailCost_eq]; positivity
  exact scaled_bound (sectionTailDamping b N) _ _ N (Real.exp_pos _).le hd
    (finiteSectionTailCost_le_cutoffMass B N)


/-- Fix any finite later-solve horizon `F(B)`, any physical lower cutoff, and any
positive tolerance at each base solve. A moving physical schedule makes the base
cost and all changes through that horizon fit the tolerance simultaneously.
The schedule can be selected from the base mass and an explicit polynomial. -/
theorem exists_schedule_uniform_finite_solve_drift (b : ℝ) (hb : 0 < b)
    (F lower : ℕ → ℕ) (ε : ℕ → ℝ) (hε : ∀ B, 0 < ε B) :
    ∃ K : ℕ → ℕ, ∀ B : ℕ, max B (lower B) ≤ K B ∧
      sectionTailDamping b (K B) * (2 + 2 * gramCutoffAmplification (max B (F B)) *
        (packetMass (B + 1))⁻¹) ≤ ε B ∧
      (K B : ℝ) * sectionTailDamping b (K B) * finiteSectionTailCost B (K B) ≤ ε B ∧
      ∀ A : ℕ, B ≤ A → A ≤ F B →
        (K B : ℝ) * sectionTailDamping b (K B) * finiteSectionTailDrift B A (K B) ≤ ε B := by
  classical
  let cap := fun B : ℕ => 2 + 2 * gramCutoffAmplification (max B (F B)) * (packetMass (B + 1))⁻¹
  have hcut B : ∃ N : ℕ, max B (lower B) ≤ N ∧ sectionTailDamping b N * cap B ≤ ε B := by
    have ht := (sectionTailDamping_tendsto b hb).mul_const (cap B)
    rw [zero_mul] at ht
    exact ((eventually_ge_atTop (max B (lower B))).and
      ((ht.eventually_lt_const (hε B)).mono fun _ h => h.le)).exists
  let K := fun B => (hcut B).choose
  refine ⟨K, fun B => ?_⟩
  let s := sectionTailDamping b (K B)
  have hs : 0 ≤ s := (Real.exp_pos _).le
  have hmB : 0 ≤ (packetMass (B + 1))⁻¹ := (inv_pos.mpr (packetMass_pos _ (Nat.succ_pos _))).le
  have hcap : s * cap B ≤ ε B := (hcut B).choose_spec.2
  have hamp : 0 ≤ gramCutoffAmplification (max B (F B)) := by
    unfold gramCutoffAmplification
    positivity
  refine ⟨(hcut B).choose_spec.1, hcap, ?_, ?_⟩
  · have hcost : 0 ≤ finiteSectionTailCost B (K B) := by rw [finiteSectionTailCost_eq]; positivity
    apply (scaled_bound s _ _ _ hs hcost (finiteSectionTailCost_le_cutoffMass B (K B))).trans
    apply (mul_le_mul_of_nonneg_left ?_ hs).trans hcap
    dsimp only [cap]
    gcongr
    exact gramCutoffAmplification_mono (le_max_left _ _)
  · intro A hBA hAF
    have hd : 0 ≤ finiteSectionTailDrift B A (K B) := by
      rw [finiteSectionTailDrift_eq B A (K B) hBA]; positivity
    have h := (finiteSectionTailDrift_le_cutoffGain B A (K B) hBA).trans (min_le_right _ _)
    apply (scaled_bound s _ _ _ hs hd h).trans
    apply (mul_le_mul_of_nonneg_left ?_ hs).trans hcap
    have hA : 0 ≤ gramCutoffAmplification A := by unfold gramCutoffAmplification; positivity
    have hM : 0 ≤ (packetMass (A + 1))⁻¹ := (inv_pos.mpr (packetMass_pos _ (Nat.succ_pos _))).le
    have hfac := gramCutoffAmplification_mono (hAF.trans (le_max_right B (F B)))
    dsimp only [cap]
    linarith only [mul_nonneg hA hM, mul_le_mul_of_nonneg_right hfac hmB, mul_nonneg hamp hmB]

end RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.DigammaSection
