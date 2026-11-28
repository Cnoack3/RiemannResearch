import RiemannResearch.Analysis.GLSSZeroCounts
import RiemannResearch.Analysis.MontgomeryArgumentWindowVariance
import RiemannResearch.Analysis.MontgomeryWindowVarianceCriterion
import RiemannResearch.Analysis.MontgomeryWindowPairCorrelation
import RiemannResearch.Analysis.ActualZeroCountNormalization
import RiemannResearch.Analysis.ActualZeroCollisionMultiplicity
import RiemannResearch.Analysis.GaussianGapReconstruction
import RiemannResearch.Analysis.GaussianOrdinateSimplicity
import RiemannResearch.Analysis.OrdinateCollisionCertificate

/-!
# Fixed-width argument increments and the GLSS horizontal diagonal

Goldston, Lee, Schettler and Suriajaya, arXiv:2503.15449v4, equations
(4.3), (5.4) and (5.6), distinguish strict positive gaps from the entire
equal-height atom. We identify the exact fixed-width input for their joint
conclusion and recover the atom from Gaussian powers of the signed Landau
reconstruction. The fixed-width sine variance remains an analytic hypothesis.
-/

noncomputable section
open Filter MeasureTheory Zeta23 Asymptotics
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.MontgomeryPositiveGap
open ActualZeroOrdinate ActualZeroCollisionCertificate OrdinateCollisionCertificate

/-- The sine limit for the bare count-discrepancy second moment on rational
microscopic widths is equivalent to the joint PCC and GLSS count conclusions. -/
theorem positiveGapPCC_and_glss_iff_rationalArgumentVariance :
    PositiveGapPCC ∧ GLSSCountAsymptotics ↔ ∀ q : ℚ, 0 < q →
      Tendsto (fun T : ℝ => pureArgumentWidthMoment T q) atTop
        (𝓝 (sineWindowEnergy q - (q : ℝ)^2)) := by
  have hN := isEquivalent_of_tendsto_one (u := fun T : ℝ => (Ncount 0 T : ℝ))
    (v := fun T => T * Real.log T / (2 * Real.pi)) tendsto_count_div_mainTerm
  constructor
  · rintro ⟨hp, hg⟩ q hq
    have hc : (fun T : ℝ => (actualCollision T : ℝ)) ~[atTop]
        (fun T => T * Real.log T / (2 * Real.pi)) := by
      simpa only [actualCollision_eq_sum_multiplicity_sq, Nat.cast_sum, Nat.cast_pow] using
        hg.horizontal.trans hN
    have hD : ∀ᶠ T : ℝ in atTop, T * Real.log T / (2 * Real.pi) ≠ 0 := by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
      exact (div_pos (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT)) (by positivity)).ne'
    have hC := (isEquivalent_iff_tendsto_one hD).mp hc
    have hA := positiveGapPCC_iff_collisionCorrectedPureArgument.mp hp q hq
    have h := (hA.add ((hC.sub_const 1).const_mul (q : ℝ))).add_const
      (sineWindowEnergy q - (q : ℝ)^2)
    simpa only [Pi.div_apply, sub_self, mul_zero, add_zero, zero_add, sub_add_cancel] using h
  · intro h
    have hs : SineWindowMoment := by
      apply sineWindowMoment_of_rational
      intro q hq
      have hr : 0 ≤ (q : ℝ) := by exact_mod_cast hq.le
      have ht := ((unfoldedWindowEnergy_sub_sq_sub_pureArgument_tendsto hr).add
        (h q hq)).add_const ((q : ℝ)^2)
      simpa only [zero_add, sub_add_cancel] using ht
    refine ⟨positiveGapPCC_of_sineWindowMoment hs, glss_counts_of_horizontal_multiplicity ?_⟩
    have hc := isEquivalent_of_tendsto_one (u := fun T : ℝ => (actualCollision T : ℝ))
      (v := fun T => T * Real.log T / (2 * Real.pi)) (collision_limit_of_sineWindowMoment hs)
    simpa only [actualCollision_eq_sum_multiplicity_sq, Nat.cast_sum, Nat.cast_pow] using
      hc.trans hN.symm

/-- In the presence of the fixed-width upper estimate furnished by GLSS
Proposition 2, the same rational variance law characterizes PCC alone. -/
theorem positiveGapPCC_iff_rationalArgumentVariance_of_fujii (hf : FujiiArgumentIncrementUpper) :
    PositiveGapPCC ↔ ∀ q : ℚ, 0 < q →
      Tendsto (fun T : ℝ => pureArgumentWidthMoment T q) atTop
        (𝓝 (sineWindowEnergy q - (q : ℝ)^2)) :=
  ⟨fun hp => positiveGapPCC_and_glss_iff_rationalArgumentVariance.mp
    ⟨hp, glss_counts_of_positiveGapPCC hp hf⟩,
    fun h => (positiveGapPCC_and_glss_iff_rationalArgumentVariance.mpr h).1⟩

/-- At fixed height, increasing precision removes every Gaussian term at
unequal ordinates, regardless of the minimum nonzero spacing. -/
theorem unequalGaussian_tendsto_zero_at_fixed_height {T : ℝ} (hT : 1 < T) :
    Tendsto (fun k : ℕ => unequalOrdinateGaussianMoment ((k : ℝ)+1) T) atTop (𝓝 0) := by
  classical
  let d (i j : Copies T) := Real.log T / (2*Real.pi) * (copyOrdinate T i - copyOrdinate T j)
  let f (k : ℕ) (i j : Copies T) :=
    if copyOrdinate T i = copyOrdinate T j then (0 : ℝ) else Real.exp (-((k : ℝ)+1)*(d i j)^2)
  have hf (i j : Copies T) : Tendsto (fun k => f k i j) atTop (𝓝 0) := by
    by_cases he : copyOrdinate T i = copyOrdinate T j
    · simp [f, he]
    simp only [f, if_neg he]
    have hd : 0 < (d i j)^2 := sq_pos_of_ne_zero
      (mul_ne_zero (div_pos (Real.log_pos hT) (by positivity)).ne' (sub_ne_zero.mpr he))
    have hk : Tendsto (fun k : ℕ => (k : ℝ)+1) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    apply Real.tendsto_exp_atBot.comp
    simpa only [Function.comp_def, neg_mul] using (tendsto_neg_atTop_atBot.comp (hk.atTop_mul_const hd))
  have hs (i : Copies T) := tendsto_finsetSum (Finset.univ.erase i) (fun j _ => hf i j)
  have ht := tendsto_finsetSum (Finset.univ : Finset (Copies T)) (fun i _ => hs i)
  simpa [unequalOrdinateGaussianMoment, f, d] using ht.div_const (Ncount 0 T : ℝ)

/-- The infimum of the reconstructed Gaussian power over positive integer
precisions estimates the GLSS collision count per actual occurrence. -/
def reconstructedCollisionMass (T : ℝ) : ℝ :=
  sInf (Set.range fun k : ℕ => reconstructedGaussianPower ((k : ℝ)+1) T)

theorem reconstructedCollisionMass_error {T : ℝ} (hT : 1 < T) (hN : 0 < Ncount 0 T) :
    |reconstructedCollisionMass T - (actualCollision T : ℝ) / (Ncount 0 T : ℝ)| ≤ 3/T := by
  let c := (actualCollision T : ℝ) / (Ncount 0 T : ℝ)
  let v (k : ℕ) := reconstructedGaussianPower ((k : ℝ)+1) T
  let u (k : ℕ) := unequalOrdinateGaussianMoment ((k : ℝ)+1) T
  have hn : (Ncount 0 T : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hc : c = 1 + (occurrenceExcess (copyOrdinate T) : ℝ) / (Ncount 0 T : ℝ) := by
    simp only [c, actualCollision, occurrenceCollision_eq_card_add_excess, card_copies,
      Nat.cast_add, add_div, div_self hn]
  have hpair (k : ℕ) : c + u k - 3/T ≤ v k ∧ v k ≤ c + u k + 3/T := by
    have h := abs_le.mp (gaussianFactorialMoment_reconstruction hT hN
      (show 0 < (k : ℝ)+1 by positivity))
    rw [gaussianFactorialMoment_split] at h
    rw [hc]
    dsimp only [u, v]
    constructor <;> linarith only [h.1, h.2]
  have hlo (k : ℕ) : c - 3/T ≤ v k := by
    have hp : 0 ≤ u k := by
      unfold u unequalOrdinateGaussianMoment
      apply div_nonneg _ (Nat.cast_nonneg _)
      exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by split <;> positivity
    linarith only [hp, (hpair k).1]
  have hb : BddBelow (Set.range v) := ⟨c-3/T, by rintro _ ⟨k, rfl⟩; exact hlo k⟩
  have hl := le_csInf (Set.range_nonempty v) (by rintro _ ⟨k, rfl⟩; exact hlo k)
  have hu : Tendsto u atTop (𝓝 0) := unequalGaussian_tendsto_zero_at_fixed_height hT
  have ht : Tendsto (fun k => c + u k + 3/T) atTop (𝓝 (c + 3/T)) := by
    simpa only [add_zero] using ((tendsto_const_nhds (x := c)).add hu).add_const (3/T)
  have hhi := ge_of_tendsto' ht (fun k => (csInf_le hb (Set.mem_range_self k)).trans (hpair k).2)
  change |sInf (Set.range v) - c| ≤ 3/T
  exact abs_le.mpr ⟨by linarith only [hl], by linarith only [hhi]⟩

/-- Quantitative version of GLSS (5.4) with the equal-height atom read from
Gaussian powers. All strictly positive pairs remain in the integrated count. -/
theorem glss_triangle_reconstructed_error {T q : ℝ} (hT : 1 < T) (hN : 0 < Ncount 0 T)
    (hq : 0 ≤ q) :
    |unfoldedWindowEnergy T q - 2 * (∫ u in (0 : ℝ)..q, positiveGapMass T u) -
      q * ((Ncount 0 T : ℝ) / (T * Real.log T / (2*Real.pi))) * reconstructedCollisionMass T| ≤
      q * ((Ncount 0 T : ℝ) / (T * Real.log T / (2*Real.pi))) * (3/T) := by
  let D := T * Real.log T / (2*Real.pi)
  have hn : (Ncount 0 T : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hd : 0 < D := div_pos (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT)) (by positivity)
  have hw : 0 ≤ q * ((Ncount 0 T : ℝ) / D) :=
    mul_nonneg hq (div_nonneg (Nat.cast_nonneg _) hd.le)
  have h := mul_le_mul_of_nonneg_left (reconstructedCollisionMass_error hT hN) hw
  rw [unfoldedWindowEnergy, physicalTriangle_eq_collision_add_positive_gaps hT hq,
    add_sub_cancel_right]
  have he : q * ((actualCollision T : ℝ)/D) - q * ((Ncount 0 T : ℝ)/D) *
      reconstructedCollisionMass T = q * ((Ncount 0 T : ℝ)/D) *
      ((actualCollision T : ℝ)/(Ncount 0 T : ℝ) - reconstructedCollisionMass T) := by
    field_simp [hn, hd.ne'] <;> ring
  change |q * ((actualCollision T : ℝ)/D) - q * ((Ncount 0 T : ℝ)/D) *
      reconstructedCollisionMass T| ≤ _
  rw [he, abs_mul, abs_of_nonneg hw, abs_sub_comm]
  exact h

/-- The exact GLSS variance criterion with its horizontal multiplicity read
from the reconstructed spectrum. No separate simplicity premise occurs. -/
theorem positiveGapPCC_iff_reconstructedCollisionVariance :
    PositiveGapPCC ↔ ∀ q : ℚ, 0 < q → Tendsto (fun T : ℝ =>
      pureArgumentWidthMoment T q - (sineWindowEnergy q - (q : ℝ)^2) -
        (q : ℝ) * ((Ncount 0 T : ℝ) / (T * Real.log T / (2*Real.pi)) *
          reconstructedCollisionMass T - 1)) atTop (𝓝 0) := by
  let D := fun T : ℝ => T * Real.log T / (2*Real.pi)
  have herr : Tendsto (fun T : ℝ => reconstructedCollisionMass T -
      (actualCollision T : ℝ)/(Ncount 0 T : ℝ)) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [eventually_count_pos, eventually_gt_atTop (max 1 (3/ε))] with T hN hT
    have h1 := (le_max_left _ _).trans_lt hT
    rw [Real.dist_eq, sub_zero]
    apply (reconstructedCollisionMass_error h1 hN).trans_lt
    apply (div_lt_iff₀ (zero_lt_one.trans h1)).2
    linarith only [(div_lt_iff₀ hε).1 ((le_max_right _ _).trans_lt hT)]
  have hcal : Tendsto (fun T : ℝ => (Ncount 0 T : ℝ)/D T * reconstructedCollisionMass T -
      (actualCollision T : ℝ)/D T) atTop (𝓝 0) := by
    have h := tendsto_count_div_mainTerm.mul herr
    rw [mul_zero] at h
    apply h.congr'
    filter_upwards [eventually_count_pos] with T hN
    have hn : (Ncount 0 T : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    dsimp [D]
    field_simp [hn]
  rw [positiveGapPCC_iff_collisionCorrectedPureArgument]
  constructor <;> intro h q hq
  · have ht := (h q hq).sub (hcal.const_mul (q : ℝ))
    simp only [mul_zero, sub_zero] at ht
    apply ht.congr'
    filter_upwards with T
    dsimp [D]
    ring
  · have ht := (h q hq).add (hcal.const_mul (q : ℝ))
    simp only [mul_zero, add_zero] at ht
    apply ht.congr'
    filter_upwards with T
    dsimp [D]
    ring

/-- info: 'RiemannResearch.Analysis.MontgomeryPositiveGap.positiveGapPCC_and_glss_iff_rationalArgumentVariance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms positiveGapPCC_and_glss_iff_rationalArgumentVariance

/-- info: 'RiemannResearch.Analysis.MontgomeryPositiveGap.reconstructedCollisionMass_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reconstructedCollisionMass_error

/-- info: 'RiemannResearch.Analysis.MontgomeryPositiveGap.glss_triangle_reconstructed_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms glss_triangle_reconstructed_error

/-- info: 'RiemannResearch.Analysis.MontgomeryPositiveGap.positiveGapPCC_iff_reconstructedCollisionVariance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms positiveGapPCC_iff_reconstructedCollisionVariance

end RiemannResearch.Analysis.MontgomeryPositiveGap
