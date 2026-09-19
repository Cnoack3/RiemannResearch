import RiemannResearch.RH.TwoSeedContrastObstruction
import RiemannResearch.RH.IntegratedRamanujanHilbert

/-!
# The exact omitted-prime obstruction for integrated Ramanujan packets

Source: user-provided `RH_Controlled_Conductor_Schur_2026-09-10.md`,
Section 6. The functional is the existing continuous Möbius coordinate,
and its representer is the existing actual Pareto Hilbert Riesz vector.
The finite packet generators, their closed span, and every complete norm
below are concrete. No asymptotic arithmetic hypothesis is assumed.

The proof does not concern the unrestricted two-seed space: arbitrary
integer dilations can introduce conductors divisible by the omitted prime.
-/

open scoped BigOperators
noncomputable section
namespace RiemannResearch.RH.Pareto

/-- At a prime the zero-anchored Möbius coordinate is precisely the
three-coordinate functional appearing in the paper. -/
theorem mobiusDifference_prime_eq (p : ℕ) (hp : p.Prime)
    (f : ℕ → ℝ) (hf0 : f 0 = 0) :
    mobiusDifference p f = f p - f (p - 1) - f 1 := by
  rw [mobiusDifference, hp.divisors,
    Finset.sum_insert (by simpa using hp.ne_one.symm), Finset.sum_singleton]
  simp [ArithmeticFunction.moebius_apply_prime hp, Nat.div_self hp.pos, hf0]
  ring

theorem mobiusDifferenceCLM_prime_eq (p : ℕ) (hp : p.Prime)
    (f : ThresholdHilbert) :
    mobiusDifferenceCLM p f =
      hilbertSequence f p - hilbertSequence f (p - 1) - hilbertSequence f 1 := by
  rw [mobiusDifferenceCLM_apply]
  exact mobiusDifference_prime_eq p hp _ (hilbertSequence_zero f)

namespace OmittedPrimePacket

/-- Equation (6.1), retaining the sign and the exact Möbius coefficient. -/
theorem packet_difference (p q : ℕ) (hp : p.Prime) (hq : 0 < q) :
    ramanujanPacket q p - ramanujanPacket q (p - 1) - ramanujanPacket q 1 =
      if p ∣ q then -(p : ℝ) * (ArithmeticFunction.moebius (q / p) : ℝ)
      else 0 := by
  rw [← mobiusDifference_prime_eq p hp (ramanujanPacket q)
    (by simp [ramanujanPacket, residue])]
  exact mobiusDifference_packet p q hp.one_lt hq

/-- Every conductor greater than one that avoids the fixed prime is allowed. -/
def span (p : ℕ) : Submodule ℝ ThresholdHilbert :=
  Submodule.span ℝ {f : ThresholdHilbert | ∃ q : ℕ,
    1 < q ∧ ¬ p ∣ q ∧ f = ramanujanPacketHilbert q}

theorem span_le_kernel (p : ℕ) (hp : p.Prime) :
    span p ≤ (mobiusDifferenceCLM p).ker := by
  apply Submodule.span_le.mpr
  rintro _ ⟨q, hq, hnot, rfl⟩
  change mobiusDifferenceCLM p (ramanujanPacketHilbert q) = 0
  rw [mobiusDifferenceCLM_ramanujanPacketHilbert p q hp.one_lt (by omega),
    if_neg hnot]

/-- The same exact zero coordinate holds throughout the Hilbert closure. -/
theorem closure_le_kernel (p : ℕ) (hp : p.Prime) :
    (span p).topologicalClosure ≤ (mobiusDifferenceCLM p).ker := by
  apply Submodule.topologicalClosure_minimal
  · exact span_le_kernel p hp
  · exact (mobiusDifferenceCLM p).isClosed_ker

theorem finite_combination_mem (p : ℕ) (s : Finset ℕ) (c : ℕ → ℝ)
    (hs : ∀ q ∈ s, 1 < q ∧ ¬ p ∣ q) :
    (∑ q ∈ s, c q • ramanujanPacketHilbert q) ∈ span p := by
  apply (span p).sum_mem
  intro q hq
  exact (span p).smul_mem _ (Submodule.subset_span
    ⟨q, (hs q hq).1, (hs q hq).2, rfl⟩)

theorem one_not_mem_closure (p : ℕ) (hp : p.Prime) :
    hilbertOne ∉ (span p).topologicalClosure := by
  intro hf
  have hz : mobiusDifferenceCLM p hilbertOne = 0 := closure_le_kernel p hp hf
  rw [ContrastObstruction.prime_coordinate_one p hp] at hz
  norm_num at hz

private theorem dualCoeff_at_one (p : ℕ) (hp : p.Prime) (hp2 : 2 < p) :
    dualCoeff p 1 = -1 := by
  have hnd2 : ¬ 2 ∣ p := by
    intro hd
    rcases (Nat.dvd_prime hp).mp hd with h | h <;> omega
  simp [dualCoeff, hnd2, ArithmeticFunction.moebius_apply_prime hp]

private theorem dualCoeff_at_previous (p : ℕ) (hp : p.Prime) (hp2 : 2 < p) :
    dualCoeff p (p - 1) = -1 := by
  have hnd : ¬ p - 1 ∣ p := by
    intro hd
    rcases (Nat.dvd_prime hp).mp hd with h | h <;> omega
  simp [dualCoeff, hnd, Nat.sub_add_cancel (show 1 ≤ p by omega),
    Nat.div_self hp.pos]

private theorem dualCoeff_at_prime (p : ℕ) (hp : p.Prime) :
    dualCoeff p p = 1 := by
  have hnd : ¬ p + 1 ∣ p := by
    intro hd
    have := Nat.le_of_dvd hp.pos hd
    omega
  simp [dualCoeff, hnd, Nat.div_self hp.pos]

/-- The Riesz vector's value at physical coordinate one. -/
theorem riesz_at_one (p : ℕ) (hp : p.Prime) (hp2 : 2 < p) :
    hilbertSequence (mobiusRieszHilbert p) 1 = -2 := by
  rw [mobiusRieszHilbert_sequence p 1 hp.pos, dualCoeff_at_one p hp hp2]
  norm_num

/-- The Riesz vector's negative value at the preceding physical coordinate. -/
theorem riesz_at_previous (p : ℕ) (hp : p.Prime) (hp2 : 2 < p) :
    hilbertSequence (mobiusRieszHilbert p) (p - 1) =
      -(p : ℝ) * ((p : ℝ) - 1) := by
  rw [mobiusRieszHilbert_sequence p (p - 1) hp.pos,
    dualCoeff_at_previous p hp hp2, Nat.cast_sub (show 1 ≤ p by omega)]
  push_cast
  ring

/-- The Riesz vector's positive value at the prime coordinate. -/
theorem riesz_at_prime (p : ℕ) (hp : p.Prime) :
    hilbertSequence (mobiusRieszHilbert p) p = (p : ℝ) * ((p : ℝ) + 1) := by
  rw [mobiusRieszHilbert_sequence p p hp.pos, dualCoeff_at_prime p hp]
  norm_num

/-- All remaining physical coordinates of the representer vanish. -/
theorem riesz_elsewhere (p k : ℕ) (hp : p.Prime)
    (hk1 : k ≠ 1) (hkprev : k ≠ p - 1) (hkp : k ≠ p) :
    hilbertSequence (mobiusRieszHilbert p) k = 0 := by
  by_cases hk0 : k = 0
  · simp [hk0]
  have hnd : ¬ k ∣ p := by
    intro hd
    rcases (Nat.dvd_prime hp).mp hd with h | h
    · exact hk1 h
    · exact hkp h
  have hnds : ¬ k + 1 ∣ p := by
    intro hd
    rcases (Nat.dvd_prime hp).mp hd with h | h
    · omega
    · apply hkprev
      omega
  simp [mobiusRieszHilbert_sequence p k hp.pos, dualCoeff, hnd, hnds]

/-- The exact Hilbert norm includes all three physical coordinate weights. -/
theorem riesz_norm_sq (p : ℕ) (hp : p.Prime) (hp2 : 2 < p) :
    ‖mobiusRieszHilbert p‖ ^ 2 = 2 * ((p : ℝ) ^ 2 + 1) := by
  rw [mobiusRieszHilbert_norm, mobiusDifferenceCLM_prime_norm_sq p hp hp2]

/-- Equation (6.2) for the whole closed packet family, with its full Pareto norm. -/
theorem error_identity (p : ℕ) (hp : p.Prime) (hp2 : 2 < p)
    (F : ThresholdHilbert) (hF : F ∈ (span p).topologicalClosure) :
    ‖hilbertOne - F‖ ^ 2 = 1 / (2 * ((p : ℝ) ^ 2 + 1)) +
      ‖hilbertOne - F + (1 / (2 * ((p : ℝ) ^ 2 + 1))) •
        mobiusRieszHilbert p‖ ^ 2 := by
  have hz : mobiusDifferenceCLM p F = 0 := closure_le_kernel p hp hF
  have hi : inner ℝ (hilbertOne - F) (mobiusRieszHilbert p) = -1 := by
    rw [real_inner_comm, mobiusRieszHilbert_inner, map_sub,
      ContrastObstruction.prime_coordinate_one p hp, hz]
    ring
  rw [norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_smul_right, hi, riesz_norm_sq p hp hp2]
  have hn : 2 * ((p : ℝ) ^ 2 + 1) ≠ 0 := by positivity
  field_simp [hn]
  ring

/-- The obstruction is positive and persists after arbitrary closure limits. -/
theorem error_floor (p : ℕ) (hp : p.Prime) (hp2 : 2 < p)
    (F : ThresholdHilbert) (hF : F ∈ (span p).topologicalClosure) :
    0 < 1 / (2 * ((p : ℝ) ^ 2 + 1)) ∧
      1 / (2 * ((p : ℝ) ^ 2 + 1)) ≤ ‖hilbertOne - F‖ ^ 2 := by
  constructor
  · positivity
  · rw [error_identity p hp hp2 F hF]
    exact le_add_of_nonneg_right (sq_nonneg _)

end OmittedPrimePacket
end RiemannResearch.RH.Pareto
