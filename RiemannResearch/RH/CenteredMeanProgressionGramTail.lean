import RiemannResearch.RH.CenteredMeanMovingGramTail
import RiemannResearch.RH.ParetoPeriodicRegrouping

/-!
# Positive arithmetic enclosure for moving Gram-section drift

After a physical cutoff, regroup the positive squares of the difference between
two solves by the period of the later solve. Each progression mass has an upper
bound with rational weights and relative factor two, uniform in both cutoffs and
the period. All Gram coordinates are evaluated at sites in a single later period.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.DigammaSection
open CoefficientStabilization RamanujanCanonicalOptimizer
open RiemannResearch.Analysis.ExhaustiveWalk

/-- An elementary upper mass for the full progression starting at the physical
site `r`. The first site can be arbitrarily far beyond the period. -/
def progressionUpperMass (P r : ℕ) : ℝ :=
  positiveWeight r + 1 / ((P : ℝ) * ((r : ℝ) + 1))

theorem progressionUpperMass_bounds (P r : ℕ) (hP : 0 < P) (hr : 0 < r) :
    progressionWeight P r ≤ progressionUpperMass P r ∧
      progressionUpperMass P r ≤ 2 * progressionWeight P r := by
  refine ⟨progressionWeight_upper_one P r hP, ?_⟩
  have h₁ := positiveWeight_le_progressionWeight P r hP
  have h₂ := (progressionWeight_certificate_bounds P r hP hr).1
  unfold progressionUpperMass
  linarith

private theorem hilbertTailShift_periodic_norm_sq (f : ThresholdHilbert) (P N : ℕ) (hP : 0 < P)
    (hp : ∀ k, hilbertSequence f (k + P) = hilbertSequence f k) :
    ‖hilbertTailShift f N‖ ^ 2 = ∑ r : Fin P, progressionWeight P (r.val + N + 1) *
      hilbertSequence f (r.val + N + 1) ^ 2 := by
  cases P with
  | zero => omega
  | succ m =>
    let g := fun k : ℕ => ((hilbertTailShift f N) k) ^ 2
    have hs : Summable g := hilbert_coordinate_square_summable _
    rw [hilbert_norm_sq]
    change (∑' k, g k) = _
    rw [Nat.sumByResidueClasses hs (m + 1)]
    apply Finset.sum_congr rfl
    intro r _
    have he (j : ℕ) : g (r.val + (m + 1) * j) =
        positiveWeight (r.val + N + 1 + (m + 1) * j) * hilbertSequence f (r.val + N + 1) ^ 2 := by
      change (f (r.val + (m + 1) * j + N)) ^ 2 = _
      rw [← hilbertSequence_weighted_square]
      have h : r.val + (m + 1) * j + N + 1 = r.val + N + 1 + (m + 1) * j := by omega
      rw [h, periodic_add_mul (m + 1) (hilbertSequence f) hp]
    simp_rw [he]
    exact (progressionWeight_summable (m + 1) (r.val + N + 1) hP).tsum_mul_right _

/-- The positive period sum encloses the true localized difference between
the two Gram solves. Each term uses rational weights and two site evaluations. -/
def finiteSectionTailDriftUpper (B A N : ℕ) : ℝ :=
  let P := Nat.lcmUpto (A + 2)
  ∑ r : Fin P, progressionUpperMass P (r.val + N + 1) *
    (sectionCoordinate (B + 1) (r.val + N + 1) - sectionCoordinate (A + 1) (r.val + N + 1)) ^ 2

/-- Regrouping the localized difference after an arbitrary physical cutoff
gives exactly one finite, positive-weight period sum. -/
theorem finiteSectionTailDrift_eq_progressionSum (B A N : ℕ) (hBA : B ≤ A) :
    finiteSectionTailDrift B A N =
      ∑ r : Fin (Nat.lcmUpto (A + 2)), progressionWeight (Nat.lcmUpto (A + 2)) (r.val + N + 1) *
        (sectionCoordinate (B + 1) (r.val + N + 1) -
          sectionCoordinate (A + 1) (r.val + N + 1)) ^ 2 := by
  have hv : packetUnitMean B - packetUnitMean A ∈ finiteSpace (A + 1) :=
    (finiteSpace (A + 1)).sub_mem
      (walkSpan_mono residueAtom id (Nat.add_le_add_right hBA 1) (packetUnitMean_legal B))
      (packetUnitMean_legal A)
  rw [finiteSectionTailDrift_eq B A N hBA]
  simpa only [hilbertSequence_sub, Pi.sub_apply, sectionCoordinate_eq] using
    hilbertTailShift_periodic_norm_sq (packetUnitMean B - packetUnitMean A) (Nat.lcmUpto (A + 2))
      N (Nat.pos_of_ne_zero (Nat.lcmUpto_ne_zero _)) (finiteSpace_lcmUpto_period (A + 1) hv)

/-- Relative factor two holds uniformly even when the later period exceeds
the physical cutoff. No signed cancellation enters either side of the estimate. -/
theorem finiteSectionTailDriftUpper_bounds (B A N : ℕ) (hBA : B ≤ A) :
    finiteSectionTailDrift B A N ≤ finiteSectionTailDriftUpper B A N ∧
      finiteSectionTailDriftUpper B A N ≤ 2 * finiteSectionTailDrift B A N := by
  rw [finiteSectionTailDrift_eq_progressionSum B A N hBA, Finset.mul_sum]
  unfold finiteSectionTailDriftUpper
  have hp : 0 < Nat.lcmUpto (A + 2) := Nat.pos_of_ne_zero (Nat.lcmUpto_ne_zero _)
  constructor
  · exact Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_right
      (progressionUpperMass_bounds _ (r.val + N + 1) hp (by omega)).1 (sq_nonneg _)
  · apply Finset.sum_le_sum
    intro r _
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right
      (progressionUpperMass_bounds _ (r.val + N + 1) hp (by omega)).2 (sq_nonneg _)

/-- The actual physical energy in the first complete period after the cutoff. -/
def firstPeriodTailDrift (B A N : ℕ) : ℝ :=
  ∑ r : Fin (Nat.lcmUpto (A + 2)), positiveWeight (r.val + N + 1) *
    (sectionCoordinate (B + 1) (r.val + N + 1) -
      sectionCoordinate (A + 1) (r.val + N + 1)) ^ 2

private theorem progressionUpperMass_le_three_atoms (P r : ℕ) (hP : 0 < P) (hr : 0 < r)
    (hrP : r ≤ 2 * P) : progressionUpperMass P r ≤ 3 * positiveWeight r := by
  have hP' : (0 : ℝ) < P := by exact_mod_cast hP
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hrP' : (r : ℝ) ≤ 2 * (P : ℝ) := by exact_mod_cast hrP
  have h : 1 / ((P : ℝ) * ((r : ℝ) + 1)) ≤ 2 / ((r : ℝ) * ((r : ℝ) + 1)) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    linarith only [mul_le_mul_of_nonneg_right hrP' (by positivity : 0 ≤ (r : ℝ) + 1)]
  unfold progressionUpperMass positiveWeight
  simp only [div_eq_mul_inv, one_mul] at h ⊢
  linarith only [h]

/-- Once the physical cutoff lies within the later period, its first actual
block of Pareto atoms is at least one third of the complete tail. -/
theorem firstPeriodTailDrift_bounds (B A N : ℕ) (hBA : B ≤ A) (hN : N ≤ Nat.lcmUpto (A + 2)) :
    firstPeriodTailDrift B A N ≤ finiteSectionTailDrift B A N ∧
      finiteSectionTailDrift B A N ≤ 3 * firstPeriodTailDrift B A N := by
  have hp : 0 < Nat.lcmUpto (A + 2) := Nat.pos_of_ne_zero (Nat.lcmUpto_ne_zero _)
  rw [finiteSectionTailDrift_eq_progressionSum B A N hBA]
  unfold firstPeriodTailDrift
  constructor
  · exact Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_right
      (positiveWeight_le_progressionWeight _ _ hp) (sq_nonneg _)
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r _
    rw [← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    exact ((progressionUpperMass_bounds _ _ hp (by omega)).1).trans
      (progressionUpperMass_le_three_atoms _ _ hp (by omega) (by have := r.isLt; omega))

/-- Cofinal control of actual physical blocks, each of length just the later
period, suffices for the boundary. The period eventually exceeds any fixed
base-stage cutoff, so the complete positive infinite tail has a uniform comparison. -/
theorem exists_scale_boundary_zero_iff_cofinal_firstPeriodTailDrift :
    ∃ b : ℝ, 0 < b ∧ ∀ K : ℕ → ℕ, CalibratedPhysicalSchedule b K →
      (boundary = 0 ↔ ∃ C : ℝ, ∃ᶠ B : ℕ in atTop, ∃ᶠ A : ℕ in atTop,
        (K B : ℝ) * sectionTailDamping b (K B) * firstPeriodTailDrift B A (K B) ≤ C) := by
  obtain ⟨b, hb, htest⟩ := exists_scale_boundary_zero_iff_cofinal_tailDrift
  refine ⟨b, hb, fun K hK => ?_⟩
  rw [(htest K hK).2]
  have hw B : 0 ≤ (K B : ℝ) * sectionTailDamping b (K B) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le
  have hlate B : ∀ᶠ A : ℕ in atTop, B ≤ A ∧ K B ≤ Nat.lcmUpto (A + 2) := by
    filter_upwards [eventually_ge_atTop B, eventually_ge_atTop (K B)] with A hBA hKA
    refine ⟨hBA, hKA.trans ((by omega : A ≤ A + 2).trans ?_)⟩
    exact Nat.le_of_dvd (Nat.lcmUpto_pos _)
      (Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩))
  constructor
  · rintro ⟨C, h⟩
    refine ⟨C, h.mono fun B hB => ?_⟩
    apply (hB.and_eventually (hlate B)).mono
    rintro A ⟨hA, hBA, hKBA⟩
    exact (mul_le_mul_of_nonneg_left (firstPeriodTailDrift_bounds B A (K B) hBA hKBA).1
      (hw B)).trans hA
  · rintro ⟨C, h⟩
    refine ⟨3 * C, h.mono fun B hB => ?_⟩
    apply (hB.and_eventually (hlate B)).mono
    rintro A ⟨hA, hBA, hKBA⟩
    have ht := mul_le_mul_of_nonneg_left (firstPeriodTailDrift_bounds B A (K B) hBA hKBA).2
      (hw B)
    linarith only [ht, hA]

end RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.DigammaSection
