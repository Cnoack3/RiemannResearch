import RiemannResearch.Analysis.StretchedExponentialBounds
import RiemannResearch.RH.CenteredMeanPeriodicGramTail
import RiemannResearch.RH.MixedConductorGramBoundary
import RiemannResearch.RH.MixedConductorRankOne

/-!
# Moving physical cutoffs and localized differences of Gram solves

A physical cutoff can be chosen at or beyond the period of each base solve so
that the stretched scaling absorbs its actual periodic mean. The only
remaining bound concerns the complete tail of the change to a later solve.
Both masses and every coordinate in its head subtraction are finite Gram data.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.DigammaSection
open CoefficientStabilization RamanujanCanonicalOptimizer PacketGramBoundary
open RiemannResearch.Analysis

/-- At ordered solve cutoffs, remove exactly the physical head of their
difference from the difference in reciprocal masses. -/
def finiteSectionTailDrift (B A N : ℕ) : ℝ :=
  (packetMass (B + 1))⁻¹ - (packetMass (A + 1))⁻¹ -
    ∑ j ∈ Finset.range N, paretoWeight j *
      (sectionCoordinate (B + 1) (j + 1) - sectionCoordinate (A + 1) (j + 1)) ^ 2

theorem finiteSectionTailDrift_eq (B A N : ℕ) (hBA : B ≤ A) :
    finiteSectionTailDrift B A N =
      ‖hilbertTailShift (packetUnitMean B - packetUnitMean A) N‖ ^ 2 := by
  rw [finiteSectionTailDrift, hilbertTailShift_norm_sq, packetUnitMean_nested_distance B A hBA]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  simpa only [positiveWeight_succ, hilbertSequence_sub, Pi.sub_apply, sectionCoordinate_eq] using
    hilbertSequence_weighted_square (packetUnitMean B - packetUnitMean A) j

private theorem laterCost_le (B A N : ℕ) (hBA : B ≤ A) :
    finiteSectionTailCost A N ≤
      2 * finiteSectionTailCost B N + 2 * finiteSectionTailDrift B A N := by
  let x := hilbertTailShift (packetUnitMean B - hilbertOne) N
  let y := hilbertTailShift (packetUnitMean B - packetUnitMean A) N
  rw [later_finiteSectionTailCost_identity B A N, finiteSectionTailCost_eq B N,
    finiteSectionTailDrift_eq B A N hBA]
  change ‖x‖ ^ 2 - 2 * inner ℝ x y + ‖y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2
  have hpos := sq_nonneg ‖x + y‖
  rw [norm_add_sq_real] at hpos
  linarith only [hpos]

/-- If the centered boundary vanishes, each fixed base solve and physical
cutoff has the finite base-tail cost as its later-solve drift limit. -/
theorem finiteSectionTailDrift_tendsto_of_boundary_zero (B N : ℕ) (hb : boundary = 0) :
    Tendsto (fun A => finiteSectionTailDrift B A N) atTop (𝓝 (finiteSectionTailCost B N)) := by
  have hu := boundary_eq_zero_iff_screened.mp hb
  have he := limitEnergy_zero_iff_mem.mpr (boundary_eq_zero_iff_one_mem.mp hb)
  have hm := packetMass_tendsto.comp (tendsto_add_atTop_nat 1)
  rw [he, sub_zero] at hm
  have hm' := hm.inv₀ one_ne_zero
  have hpoint (j : ℕ) : Tendsto (fun A => sectionCoordinate (A + 1) (j + 1)) atTop (𝓝 1) := by
    simpa only [hu, hilbertOne_sequence, zeroAnchor, Nat.succ_ne_zero, if_false] using
      sectionCoordinate_tendsto (j + 1)
  have hs := tendsto_finsetSum (Finset.range N) fun j _ =>
    (((hpoint j).const_sub (sectionCoordinate (B + 1) (j + 1))).pow 2).const_mul (paretoWeight j)
  have hv : (packetMass (B + 1))⁻¹ - 1 = (1 - packetMass (B + 1)) / packetMass (B + 1) := by
    field_simp [(packetMass_pos (B + 1) (Nat.succ_pos B)).ne']
  simpa only [finiteSectionTailDrift, finiteSectionTailCost, finiteSectionShell, Nat.add_zero,
    Function.comp_def, inv_one, hv] using (hm'.const_sub ((packetMass (B + 1))⁻¹)).sub hs

/-- The arithmetic damping factor, before multiplication by the physical cutoff. -/
def sectionTailDamping (b : ℝ) (N : ℕ) : ℝ :=
  Real.exp (-b * logProductPower (1 / 11) (6 + Real.log (N : ℝ)))

private theorem sectionTailDamping_tendsto (b : ℝ) (hb : 0 < b) :
    Tendsto (sectionTailDamping b) atTop (𝓝 0) := by
  have hL : Tendsto (fun N : ℕ => 6 + Real.log (N : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left atTop 6
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hφ := (tendsto_logProductPower_atTop (1 / 11) (by norm_num)).comp hL
  exact Real.tendsto_exp_comp_nhds_zero.mpr (hφ.const_mul_atTop_of_neg (neg_lt_zero.mpr hb))

/-- For each fixed solve, the stretched scaled cost tends to zero at large
physical cutoffs. This gives the reversed quantifier order unconditionally. -/
theorem fixedSolve_stretched_finiteSectionTailCost_tendsto (b : ℝ) (hb : 0 < b) (B : ℕ) :
    Tendsto (fun N : ℕ => (N : ℝ) * sectionTailDamping b N * finiteSectionTailCost B N)
      atTop (𝓝 0) := by
  have ht := (sectionTailDamping_tendsto b hb).mul
    (scaled_finiteSectionTailCost_tendsto_periodMean B)
  rw [zero_mul] at ht
  apply squeeze_zero (fun N => ?_) (fun N => ?_) ht
  · rw [finiteSectionTailCost_eq]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le) (sq_nonneg _)
  · have hc : 0 ≤ finiteSectionTailCost B N := by rw [finiteSectionTailCost_eq]; positivity
    have hw : 0 ≤ sectionTailDamping b N := (Real.exp_pos _).le
    change (N : ℝ) * sectionTailDamping b N * finiteSectionTailCost B N ≤
      sectionTailDamping b N * (((N : ℝ) + 1) * finiteSectionTailCost B N)
    linarith only [mul_nonneg hw hc]

/-- A schedule lies beyond the base period and damps its finite period mean. -/
def CalibratedPhysicalSchedule (b : ℝ) (K : ℕ → ℕ) : Prop :=
  ∀ B : ℕ, B ≤ K B ∧ Nat.lcmUpto (B + 2) ≤ K B ∧
    sectionTailDamping b (K B) * sectionPeriodMean B ≤ 1

/-- Every positive damping coefficient admits calibrated physical schedules. -/
theorem exists_calibrated_physicalSchedule (b : ℝ) (hb : 0 < b) :
    ∃ K : ℕ → ℕ, CalibratedPhysicalSchedule b K := by
  classical
  have h B : ∃ N : ℕ, B ≤ N ∧ Nat.lcmUpto (B + 2) ≤ N ∧
      sectionTailDamping b N * sectionPeriodMean B ≤ 1 := by
    have ht := (sectionTailDamping_tendsto b hb).mul_const (sectionPeriodMean B)
    rw [zero_mul] at ht
    exact ((eventually_ge_atTop B).and ((eventually_ge_atTop (Nat.lcmUpto (B + 2))).and
      ((ht.eventually_lt_const (by norm_num : (0 : ℝ) < 1)).mono fun _ h => h.le))).exists
  exact ⟨fun B => (h B).choose, fun B => (h B).choose_spec⟩

private theorem scaled_baseCost_le (b : ℝ) (B N : ℕ) (hL : Nat.lcmUpto (B + 2) ≤ N)
    (hμ : sectionTailDamping b N * sectionPeriodMean B ≤ 1) :
    (N : ℝ) * sectionTailDamping b N * finiteSectionTailCost B N ≤ 2 := by
  have hpos : 0 ≤ sectionPeriodMean B :=
    (by positivity : 0 ≤ 1 / (Nat.lcmUpto (B + 2) : ℝ)).trans (sectionPeriodMean_lower B)
  have he : (Nat.lcmUpto (B + 2) : ℝ) * sectionPeriodMean B / ((N : ℝ) + 2) ≤
      sectionPeriodMean B := by
    apply (div_le_iff₀ (by positivity)).mpr
    have hLR : (Nat.lcmUpto (B + 2) : ℝ) ≤ N := by exact_mod_cast hL
    nlinarith only [mul_le_mul_of_nonneg_right hLR hpos, hpos]
  have hraw := (le_abs_self _).trans ((finiteSectionTailCost_period_error B N).trans he)
  have hcost : 0 ≤ finiteSectionTailCost B N := by rw [finiteSectionTailCost_eq]; positivity
  have hh : (N : ℝ) * finiteSectionTailCost B N ≤ 2 * sectionPeriodMean B := by
    linarith only [hraw, hcost]
  have hw : 0 ≤ sectionTailDamping b N := (Real.exp_pos _).le
  linarith only [mul_le_mul_of_nonneg_left hh hw, hμ]

/-- At one positive damping coefficient, every calibrated physical schedule gives
the same test. The centered boundary vanishes exactly when the scaled, localized
change between two finite Gram solves has one cofinal bound. Every base solve
already satisfies its scaled tail budget. -/
theorem exists_scale_boundary_zero_iff_cofinal_tailDrift :
    ∃ b : ℝ, 0 < b ∧ ∀ K : ℕ → ℕ, CalibratedPhysicalSchedule b K →
      (∀ B, (K B : ℝ) * sectionTailDamping b (K B) * finiteSectionTailCost B (K B) ≤ 2) ∧
      (boundary = 0 ↔ ∃ C : ℝ, ∃ᶠ B : ℕ in atTop, ∃ᶠ A : ℕ in atTop,
        (K B : ℝ) * sectionTailDamping b (K B) * finiteSectionTailDrift B A (K B) ≤ C) := by
  obtain ⟨b, hb, hzero⟩ := exists_boundary_zero_of_stretched_coordinateLossTail
  refine ⟨b, hb, ?_⟩
  intro K hK
  have hbase B := scaled_baseCost_le b B (K B) (hK B).2.1 (hK B).2.2
  refine ⟨hbase, ?_⟩
  constructor
  · intro h
    refine ⟨3, (Eventually.of_forall fun B => ?_).frequently⟩
    have ht := (finiteSectionTailDrift_tendsto_of_boundary_zero B (K B) h).const_mul
      ((K B : ℝ) * sectionTailDamping b (K B))
    exact ((ht.eventually_lt_const ((hbase B).trans_lt (by norm_num : (2 : ℝ) < 3))).mono
      fun _ h => h.le).frequently
  · rintro ⟨C, h⟩
    apply hzero ((4 + 2 * C) / (1 + ‖defect‖ ^ 2))
    apply frequently_atTop.mpr
    intro N₀
    obtain ⟨B, hB, hA⟩ := frequently_atTop.mp h N₀
    refine ⟨K B, hB.trans (hK B).1, ?_⟩
    let s := (K B : ℝ) * sectionTailDamping b (K B)
    have hs : 0 ≤ s := mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le
    have hf : ∃ᶠ A : ℕ in atTop, s * finiteSectionTailCost A (K B) ≤ 4 + 2 * C := by
      apply (hA.and_eventually (eventually_ge_atTop B)).mono
      rintro A ⟨hbudget, hBA⟩
      have ht := mul_le_mul_of_nonneg_left (laterCost_le B A (K B) hBA) hs
      change s * finiteSectionTailDrift B A (K B) ≤ C at hbudget
      have hbase' : s * finiteSectionTailCost B (K B) ≤ 2 := hbase B
      linarith only [ht, hbase', hbudget]
    have ht := le_of_tendsto_of_frequently
      ((finiteSectionTailCost_tendsto (K B)).const_mul s) hf
    change s * coordinateLossTail (K B) ≤ _
    rw [coordinateLossTail_eq, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right ht (by positivity)

end RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.DigammaSection
