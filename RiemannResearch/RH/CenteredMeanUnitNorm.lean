import RiemannResearch.RH.CenteredMeanSquarefreeConverse
import RiemannResearch.RH.CenteredMeanStageSnake
import RiemannResearch.RH.MixedCaptureLegalTrials
import RiemannResearch.RH.MixedConductorBilinear
import RiemannResearch.RH.MixedConductorGramBoundary
import RiemannResearch.RH.MixedConductorGramZeroFree
import RiemannResearch.RH.RamanujanGramDeterminants
import RiemannResearch.RH.RamanujanSaturationCriteria
import RiemannResearch.RH.RamanujanUnitMean
import RiemannResearch.RH.ScreenedMeanDilationTests
import RiemannResearch.RH.ThresholdHilbertDilation
import RiemannResearch.RH.ThresholdHilbertProjection
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.TFAE

/-!
# The centered stage snake and the unit norm of its legal section

At any mixed denominator the snake norm polarizes the legal defect form.
The dilation orbit computes a Gram matrix with a common unknown scalar.
The complete arithmetic packet dictionaries determine that scalar by a
determinant cut. A strict halving of the finite excess at every positive
cutoff is equivalent to the unit bound. Constructing these extensions is
the remaining arithmetic problem.

Source: the user's bilinear, prime-tower, and lifting questions.
-/

noncomputable section
open Filter
open scoped Topology Matrix

namespace RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake
open CoefficientStabilization RamanujanCanonicalOptimizer PacketGramBoundary

/-- The signed defect pairing is determined by the two stage boundary norms. -/
theorem stage_polarization_defect (S : Submodule ℝ mixedClosure) (v w : closedSpace) :
    4 * Bilinear.defectForm v.val w.val =
      ‖Stage.connecting S (legalPacketMean v + legalPacketMean w)‖ ^ 2 -
      ‖Stage.connecting S (legalPacketMean v - legalPacketMean w)‖ ^ 2 := by
  rw [Bilinear.defectForm_legal, Stage.norm_connecting, Stage.norm_connecting,
    mul_pow, mul_pow, sq_abs, sq_abs]
  ring

/-- The nested dilation Gram matrix, valid in particular at every prime base. -/
theorem screened_power_dilation_gram (p i j : ℕ) (hp : 0 < p) (hij : i ≤ j) :
    inner ℝ (hilbertDilation (p ^ i) (pow_pos hp i) normalizedScreenedTwo)
      (hilbertDilation (p ^ j) (pow_pos hp j) normalizedScreenedTwo) =
      (p : ℝ) ^ i * ‖normalizedScreenedTwo‖ ^ 2 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  have hcomp : hilbertDilation (p ^ (i + k)) (pow_pos hp _) normalizedScreenedTwo =
      hilbertDilation (p ^ i) (pow_pos hp _)
        (hilbertDilation (p ^ k) (pow_pos hp _) normalizedScreenedTwo) := by
    simpa only [pow_add] using (hilbertDilation_comp (p ^ i) (p ^ k)
      (pow_pos hp i) (pow_pos hp k) normalizedScreenedTwo).symm
  have hpair : inner ℝ normalizedScreenedTwo
      (hilbertDilation (p ^ k) (pow_pos hp k) normalizedScreenedTwo) =
      ‖normalizedScreenedTwo‖ ^ 2 := by
    rw [real_inner_comm, inner_dilation_screenedTwo
      (screenedPrimeClosure_le_closedSpace normalizedScreenedTwo_mem_screenedPrimeClosure),
      real_inner_self_eq_norm_sq]
  rw [hcomp, hilbertDilation_inner, hpair, Nat.cast_pow]

/-- The lower cut of the exact squared norm uses the finite arithmetic pencils alone. -/
theorem screened_norm_sq_gram_cut (t : ℝ) :
    t ≤ ‖normalizedScreenedTwo‖ ^ 2 ↔ ∀ n : ℕ, 0 ≤ (meanPencil n t).det := by
  have hprod : ‖normalizedScreenedTwo‖ ^ 2 * (1 - limitEnergy) = 1 := by
    rw [mul_comm, normalizedScreenedTwo_energy_product]
  constructor
  · intro ht n
    rw [det_meanPencil]
    apply mul_nonneg (finitePacketGram_det_pos n).le
    apply sub_nonneg.mpr
    calc
      t * packetMass n ≤ ‖normalizedScreenedTwo‖ ^ 2 * packetMass n :=
        mul_le_mul_of_nonneg_right ht (packetMass_bounds n).1
      _ ≤ ‖normalizedScreenedTwo‖ ^ 2 * (1 - limitEnergy) :=
        mul_le_mul_of_nonneg_left (packetMass_lt_limitMass n).le (sq_nonneg _)
      _ = 1 := hprod
  · intro hall
    by_contra! hgt
    have hl := mul_lt_mul_of_pos_right hgt one_sub_limitEnergy_pos
    rw [hprod] at hl
    have ht := (tendsto_const_nhds (x := t)).mul packetMass_tendsto
    obtain ⟨n, hn⟩ := ((tendsto_order.mp ht).1 (1 : ℝ) hl).exists
    exact (not_lt_of_ge (hall n)) (by
      rw [det_meanPencil]
      exact mul_neg_of_pos_of_neg (finitePacketGram_det_pos n) (sub_neg.mpr hn))

/-- Chase the two arrows adjoining the boundary in the stage long exact sequence. -/
theorem stage_lift_unit_norm_tfae (S : Submodule ℝ mixedClosure) :
    [Function.Injective (Stage.toCokernel S),
     ∃! k : (Stage.middleVertical S).ker, Stage.kernelMean S k = 1,
     ‖normalizedScreenedTwo‖ ≤ 1,
     normalizedScreenedTwo = hilbertOne,
     RiemannHypothesis].TFAE := by
  let Z := Stage.connecting S 1 = 0
  have hmono : Function.Injective (Stage.toCokernel S) ↔ Z := by
    constructor
    · intro hi
      apply hi
      exact ((Stage.exact_connecting_toCokernel S _).2 ⟨1, rfl⟩).trans (map_zero _).symm
    · intro hz x y hxy
      apply sub_eq_zero.mp
      have hx : Stage.toCokernel S (x - y) = 0 := by rw [map_sub, hxy, sub_self]
      obtain ⟨a, ha⟩ := (Stage.exact_connecting_toCokernel S _).1 hx
      rw [← ha]
      calc
        Stage.connecting S a = Stage.connecting S (a • (1 : ℝ)) := by simp
        _ = 0 := by rw [map_smul, show Stage.connecting S 1 = 0 from hz, smul_zero]
  have hlift : Z ↔ ∃! k : (Stage.middleVertical S).ker, Stage.kernelMean S k = 1 := by
    constructor
    · intro hz
      obtain ⟨k, hk⟩ := (Stage.exact_kernelMean_connecting S 1).1 hz
      exact ⟨k, hk, fun l hl => Stage.kernelMean_injective S (hl.trans hk.symm)⟩
    · rintro ⟨k, hk, _⟩
      exact (Stage.exact_kernelMean_connecting S 1).2 ⟨k, hk⟩
  have hnorm : ‖normalizedScreenedTwo‖ ≤ 1 ↔ Z := by
    calc
      ‖normalizedScreenedTwo‖ ≤ 1 ↔ ‖normalizedScreenedTwo‖ = 1 :=
        ⟨fun h => le_antisymm h one_le_norm_normalizedScreenedTwo, fun h => h.le⟩
      _ ↔ limitEnergy = 0 := normalizedScreenedTwo_norm_eq_one_iff
      _ ↔ hilbertOne ∈ closedSpace := limitEnergy_zero_iff_mem
      _ ↔ Z := (Stage.connecting_one_eq_zero_iff S).symm
  have hseed : Z ↔ normalizedScreenedTwo = hilbertOne := by
    constructor
    · intro hz
      have hn := hnorm.mpr hz
      have he := norm_sub_sq_real normalizedScreenedTwo hilbertOne
      rw [normalizedScreenedTwo_mean, hilbertOne_norm_sq] at he
      have hu := le_antisymm hn one_le_norm_normalizedScreenedTwo
      rw [hu] at he
      apply sub_eq_zero.mp
      apply norm_eq_zero.mp
      nlinarith only [he]
    · intro he
      apply (Stage.connecting_one_eq_zero_iff S).mpr
      exact he ▸ screenedPrimeClosure_le_closedSpace normalizedScreenedTwo_mem_screenedPrimeClosure
  have hrh : Z ↔ RiemannHypothesis :=
    (Stage.connecting_one_eq_zero_iff S).trans
      (boundary_eq_zero_iff_one_mem.symm.trans
        ((stageUnit_zero_iff_boundary 0).symm.trans (stageUnit_zero_iff_RH 0)))
  tfae_have 1 ↔ 2 := hmono.trans hlift
  tfae_have 2 ↔ 3 := hlift.symm.trans hnorm.symm
  tfae_have 3 ↔ 4 := hnorm.trans hseed
  tfae_have 4 ↔ 5 := hseed.symm.trans hrh
  tfae_finish

/-- The endpoint is equivalent to halving the excess cost of every nonempty finite
mean-one Gram lift in a further finite dictionary. The thresholds use only its mass. -/
theorem unit_norm_iff_finite_gram_halving :
    ‖normalizedScreenedTwo‖ ≤ 1 ↔
      ∀ n : ℕ, ∃ m : ℕ,
        (meanPencil m ((1 + (packetMass (n + 1))⁻¹) / 2)).det < 0 := by
  have hneg (t : ℝ) : ‖normalizedScreenedTwo‖ ^ 2 < t ↔
      ∃ m : ℕ, (meanPencil m t).det < 0 := by
    classical
    rw [lt_iff_not_ge, screened_norm_sq_gram_cut]
    push_neg
    rfl
  constructor
  · intro hu n
    apply (hneg _).mp
    have hp := packetMass_pos (n + 1) (Nat.zero_lt_succ n)
    have hs : 1 < (packetMass (n + 1))⁻¹ := by
      rw [inv_eq_one_div, lt_div_iff₀ hp, one_mul]
      exact (packetMass_bounds _).2
    rw [le_antisymm hu one_le_norm_normalizedScreenedTwo]
    linarith
  · intro hall
    have hlim : Tendsto (fun n : ℕ => (packetMass (n + 1))⁻¹) atTop
        (𝓝 (‖normalizedScreenedTwo‖ ^ 2)) := by
      simpa only [← packetUnitMean_energy, packetUnitMeanLimit_eq_screened] using
        (packetUnitMean_tendsto.norm.pow 2)
    have hlim' := ((tendsto_const_nhds (x := (1 : ℝ))).add hlim).div_const (2 : ℝ)
    have hu : ‖normalizedScreenedTwo‖ ^ 2 ≤ (1 + ‖normalizedScreenedTwo‖ ^ 2) / 2 :=
      le_of_tendsto_of_tendsto' tendsto_const_nhds hlim' (fun n => ((hneg _).mpr (hall n)).le)
    nlinarith only [hu, norm_nonneg normalizedScreenedTwo]

/--
info: 'RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.stage_polarization_defect' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms stage_polarization_defect

/--
info: 'RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.screened_power_dilation_gram' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms screened_power_dilation_gram

/--
info: 'RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.screened_norm_sq_gram_cut' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms screened_norm_sq_gram_cut

/--
info: 'RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.stage_lift_unit_norm_tfae' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms stage_lift_unit_norm_tfae

/--
info: 'RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.unit_norm_iff_finite_gram_halving' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms unit_norm_iff_finite_gram_halving

end RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake
