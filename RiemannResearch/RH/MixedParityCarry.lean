import RiemannResearch.RH.AllCertifiedCarrySpan
import RiemannResearch.RH.PhysicalPrimePowerCarryProjection
import RiemannResearch.RH.MixedCanonicalCarryCapture
import RiemannResearch.RH.RamanujanMixedCaptureBudget
import RiemannResearch.RH.ParetoGroupedResidueMass

/-!
# Mixed parity capture in the Pareto carry presentation

The two adjacent certificates realize the parity packet. All certified Pareto
carry words give a dense presentation of the legal space, and their target
approximation criterion controls the normalized mixed projection of parity.

Source: Christian Noack's atom-to-carry question for the mixed projection of parity.
-/

noncomputable section
namespace RiemannResearch.RH.Pareto.MixedParityCarry
open CoefficientStabilization PrimePowerSchur UniversalAtomCarry
open PhysicalPrimePowerCarryProjection
open GroupedResidueMass.Conductor241

/-- The finite real span of all certified floor carries in the Pareto Hilbert space. -/
def carrySpan : Submodule ℝ ThresholdHilbert :=
  Submodule.span ℝ (Set.range (certifiedVector pAtom))

private theorem carry_mem (c : Certificate) : certifiedVector pAtom c ∈ carrySpan :=
  Submodule.subset_span ⟨c, rfl⟩

/-- Recover each physical residue atom by changing the charge of an adjacent carry. -/
theorem adjacent_difference (d : ℕ) (hd : 1 < d) :
    certifiedVector pAtom (adjacentPlus d hd) - certifiedVector pAtom (adjacentMinus d hd) =
      (d : ℝ) • pAtom d := by
  apply hilbertSequence_injective
  change hilbertSequenceLinear (_ - _) = hilbertSequenceLinear (_ • _)
  rw [map_sub, map_smul, pAtom_sequence d (by omega)]
  change hilbertSequence (certifiedVector pAtom _) - hilbertSequence (certifiedVector pAtom _) = _
  rw [(physical_certified_floors _).1, (physical_certified_floors _).1, adjacent_carry_difference]

/-- Both certificates have output six. Their difference is exactly the packet at two. -/
theorem adjacent_difference_two :
    certifiedVector pAtom (adjacentPlus 2 (by decide)) -
        certifiedVector pAtom (adjacentMinus 2 (by decide)) = ramanujanPacketHilbert 2 := by
  rw [adjacent_difference]
  apply hilbertSequence_injective
  change hilbertSequenceLinear ((2 : ℝ) • pAtom 2) = _
  rw [map_smul, pAtom_sequence 2 (by decide), hilbertSequence_ramanujanPacketHilbert,
    ramanujanPacket_prime_eq_residue 2 Nat.prime_two]
  funext n
  change (2 : ℝ) * ((n % 2 : ℕ) / (2 : ℝ)) = (n % 2 : ℕ)
  ring

/-- Passing from residue atoms to all certified carries preserves the closed legal space. -/
theorem carrySpan_closure : carrySpan.topologicalClosure = closedSpace := by
  rw [← physical_full_closures.1]
  apply le_antisymm
  · apply Submodule.topologicalClosure_mono
    apply Submodule.span_le.mpr
    rintro _ ⟨c, rfl⟩
    let S := Submodule.span ℝ (Set.range (fun a : Atom => pAtom a.val))
    have ha (d : ℕ) (hd : 1 < d) : pAtom d ∈ S :=
      Submodule.subset_span ⟨⟨d, hd⟩, rfl⟩
    exact S.sub_mem (S.sum_mem fun i _ => S.smul_mem _ (ha _ (c.input_gt_one i)))
      (ha _ c.output_gt_one)
  · apply Submodule.topologicalClosure_mono
    apply Submodule.span_le.mpr
    rintro _ ⟨d, rfl⟩
    change pAtom d.val ∈ carrySpan
    have h := carrySpan.sub_mem (carry_mem (adjacentPlus d.val d.property))
      (carry_mem (adjacentMinus d.val d.property))
    rw [adjacent_difference] at h
    have hd : (d.val : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := d.property; omega)
    simpa only [smul_smul, inv_mul_cancel₀ hd, one_smul] using
      carrySpan.smul_mem (d.val : ℝ)⁻¹ h

/-- The centered difference of the two physical carries lies in the mixed space
exactly when the constant lies in the legal space. -/
theorem centered_adjacent_mem_iff :
    certifiedVector pAtom (adjacentPlus 2 (by decide)) -
        certifiedVector pAtom (adjacentMinus 2 (by decide)) - Real.log 2 • hilbertOne ∈
        mixedClosure ↔ hilbertOne ∈ closedSpace := by
  rw [adjacent_difference_two, mem_mixedClosure_iff_mem_closedSpace_and_mean_zero]
  have hj := packet_mem_closedSpace 2 (by decide)
  have hl := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  constructor
  · rintro ⟨h, _⟩
    have hs := closedSpace.sub_mem hj h
    rw [sub_sub_cancel] at hs
    simpa only [smul_smul, inv_mul_cancel₀ hl, one_smul] using
      closedSpace.smul_mem (Real.log 2)⁻¹ hs
  · intro h
    refine ⟨closedSpace.sub_mem hj (closedSpace.smul_mem _ h), ?_⟩
    rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hilbertOne_norm_sq,
      mul_one, hilbert_inner_one, hilbertSequence_ramanujanPacketHilbert, paretoMean_ramanujanPacket,
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    norm_num

/-- Normalized Pareto projection of the parity packet onto the mixed packet space. -/
def projectedParity : ThresholdHilbert :=
  (Real.log 2)⁻¹ • mixedClosure.starProjection (ramanujanPacketHilbert 2)

/-- Exact squared capture, retaining the error of the normalized screened vector. -/
theorem norm_sq_add_error :
    ‖projectedParity‖ ^ 2 + ‖normalizedScreenedTwo - hilbertOne‖ ^ 2 =
      (Real.log 2)⁻¹ - 1 := by
  have hl := (Real.log_pos (by norm_num : (1:ℝ) < 2)).ne'
  have h := (div_eq_iff (pow_ne_zero 2 hl)).mpr
    (fullTwoCapture_deficit.trans (mul_comm _ _))
  rw [normalizedScreenedTwo_error_sq_eq_limitEnergy, ← h, projectedParity, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs, ← fullTwoCapture]
  field_simp [hl]
  ring

/-- The complete conductor-241 certificate gives both endpoints of a rigorous enclosure. -/
theorem norm_sq_bounds :
    (Real.log 2)⁻¹ - 1 - (628101568132839 : ℝ) / 64908898431867161 ≤
      ‖projectedParity‖ ^ 2 ∧ ‖projectedParity‖ ^ 2 ≤ (Real.log 2)⁻¹ - 1 := by
  have h := screenedTwo_squared_distance_le_mod30
  rw [norm_sub_rev] at h
  constructor <;> linarith [norm_sq_add_error, sq_nonneg ‖normalizedScreenedTwo - hilbertOne‖]

theorem norm_sq_endpoint_iff_mem :
    ‖projectedParity‖ ^ 2 = (Real.log 2)⁻¹ - 1 ↔ hilbertOne ∈ closedSpace := by
  rw [one_mem_closedSpace_iff_normalizedScreenedTwo]
  constructor
  · intro h
    have hz : ‖normalizedScreenedTwo - hilbertOne‖ ^ 2 = 0 := by linarith [norm_sq_add_error]
    rw [pow_two, mul_eq_zero, or_self, norm_eq_zero, sub_eq_zero] at hz
    exact hz
  · intro h
    simpa only [h, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero] using norm_sq_add_error

/-- Attaining the endpoint is equivalent to arbitrarily accurate finite carry synthesis. -/
theorem norm_sq_endpoint_iff_carry_trials :
    ‖projectedParity‖ ^ 2 = (Real.log 2)⁻¹ - 1 ↔
      ∀ ε : ℝ, 0 < ε → ∃ v ∈ carrySpan, ‖hilbertOne - v‖ < ε := by
  rw [norm_sq_endpoint_iff_mem, ← carrySpan_closure]
  change hilbertOne ∈ closure (carrySpan : Set ThresholdHilbert) ↔ _
  simp only [Metric.mem_closure_iff, dist_eq_norm, SetLike.mem_coe]

/-- The exact norm endpoint expressed through finite corrected-carry projections. -/
theorem norm_sq_endpoint_iff_corrected_capture :
    ‖projectedParity‖ ^ 2 = (Real.log 2)⁻¹ - 1 ↔
      Filter.Tendsto (fun N : ℕ =>
        ‖(correctedCarrySpace N).starProjection (ramanujanPacketHilbert 2)‖ ^ 2)
        Filter.atTop (nhds (Real.log 2 - (Real.log 2) ^ 2)) :=
  norm_sq_endpoint_iff_mem.trans correctedCarry_capture_tendsto_iff.symm

end RiemannResearch.RH.Pareto.MixedParityCarry
