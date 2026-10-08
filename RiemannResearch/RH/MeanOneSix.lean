/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ArithmeticPacketCore
import RiemannResearch.RH.ParetoFiniteCertificates
import Mathlib.Tactic.FinCases

/-! Exact physical mean-one optimizer at conductor six. -/

noncomputable section
open Matrix
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.MeanOneSix
open RiemannResearch.RH.Pareto
open PhysicalPacketCore

def packetSet : Finset ℕ := {2, 3, 6}
def coefficients (q : packetSet) : ℝ :=
  if q.val = 2 then 2/3 else if q.val = 3 then 1/2 else 1/6

private def qTwo : packetSet := ⟨2, by decide⟩
private def qThree : packetSet := ⟨3, by decide⟩
private def qSix : packetSet := ⟨6, by decide⟩

/-- Enumerates the actual subtype, so proof-dependent summands also reduce. -/
private theorem sum_packetSet (f : packetSet → ℝ) :
    (∑ q : packetSet, f q) = f qTwo + f qThree + f qSix := by
  classical
  have he : (Finset.univ : Finset packetSet) = {qTwo, qThree, qSix} := by
    ext q
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    have hq := q.property
    simp only [packetSet, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with hq | hq | hq
    · left
      exact Subtype.ext hq
    · right; left
      exact Subtype.ext hq
    · right; right
      exact Subtype.ext hq
  rw [he]
  simp [qTwo, qThree, qSix, add_assoc]

private theorem totient_two : Nat.totient 2 = 1 := by decide
private theorem totient_three : Nat.totient 3 = 2 := by decide
private theorem totient_six : Nat.totient 6 = 2 := by decide

private theorem coreEntry_finset_expansion (Q d e : ℕ) :
    packetDifferenceCotangentCoreEntry Q d e =
      ∑ a ∈ d.divisors, ∑ b ∈ e.divisors,
        (ArithmeticFunction.moebius (d/a) : ℝ) *
          (ArithmeticFunction.moebius (e/b) : ℝ) * residueDifferenceCotangentCore Q a b := by
  unfold packetDifferenceCotangentCoreEntry
  calc
    _ = ∑ a : d.divisors, ∑ b ∈ e.divisors,
        (ArithmeticFunction.moebius (d/a.val) : ℝ) *
          (ArithmeticFunction.moebius (e/b) : ℝ) * residueDifferenceCotangentCore Q a.val b := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_coe_sort e.divisors (fun b : ℕ =>
        (ArithmeticFunction.moebius (d/a.val) : ℝ) *
          (ArithmeticFunction.moebius (e/b) : ℝ) * residueDifferenceCotangentCore Q a.val b)
    _ = _ := Finset.sum_coe_sort d.divisors (fun a : ℕ =>
      ∑ b ∈ e.divisors, (ArithmeticFunction.moebius (d/a) : ℝ) *
        (ArithmeticFunction.moebius (e/b) : ℝ) * residueDifferenceCotangentCore Q a b)

private theorem packetSet_legal : ∀ q ∈ packetSet, 1 < q := by
  intro q hq
  simp only [packetSet, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl <;> norm_num

private theorem packetSet_period : ∀ q ∈ packetSet, q ∣ 6 := by
  intro q hq
  simp only [packetSet, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl <;> norm_num

private theorem packetSet_odd : ∃ p ∈ packetSet, p.Prime ∧ 2 < p := by
  exact ⟨3, by simp [packetSet], by norm_num, by norm_num⟩

theorem cotangent_six_zero : periodCotangent 6 0 = 0 := by
  norm_num [periodCotangent]

theorem cotangent_six_one : periodCotangent 6 1 = Real.sqrt 3 := by
  unfold periodCotangent
  norm_num only [Nat.cast_ofNat, mul_one]
  rw [Real.cos_pi_div_six, Real.sin_pi_div_six]
  ring

theorem cotangent_six_two : periodCotangent 6 2 = 1 / Real.sqrt 3 := by
  change Real.cos (Real.pi * 2 / 6) / Real.sin (Real.pi * 2 / 6) = _
  rw [show Real.pi * 2 / 6 = Real.pi / 3 by ring,
    Real.cos_pi_div_three, Real.sin_pi_div_three]
  field_simp [ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3))]

theorem cotangent_six_three : periodCotangent 6 3 = 0 := by
  change Real.cos (Real.pi * 3 / 6) / Real.sin (Real.pi * 3 / 6) = _
  rw [show Real.pi * 3 / 6 = Real.pi / 2 by ring,
    Real.cos_pi_div_two, Real.sin_pi_div_two]
  norm_num

theorem cotangent_six_four : periodCotangent 6 4 = -1 / Real.sqrt 3 := by
  change Real.cos (Real.pi * 4 / 6) / Real.sin (Real.pi * 4 / 6) = _
  rw [show Real.pi * 4 / 6 = Real.pi - Real.pi / 3 by ring,
    Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_pi_div_three, Real.sin_pi_div_three]
  field_simp [ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3))]

theorem cotangent_six_five : periodCotangent 6 5 = -Real.sqrt 3 := by
  change Real.cos (Real.pi * 5 / 6) / Real.sin (Real.pi * 5 / 6) = _
  rw [show Real.pi * 5 / 6 = Real.pi - Real.pi / 6 by ring,
    Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_pi_div_six, Real.sin_pi_div_six]
  ring

theorem cotangent_six_six : periodCotangent 6 6 = 0 := by
  change Real.cos (Real.pi * 6 / 6) / Real.sin (Real.pi * 6 / 6) = _
  rw [show Real.pi * 6 / 6 = Real.pi by ring, Real.cos_pi, Real.sin_pi]
  norm_num

def coreTable (d e : ℕ) : ℝ :=
  if d = 2 then
    if e = 2 then 0 else if e = 3 then -1/(3*Real.sqrt 3) else -1/(2*Real.sqrt 3)
  else if d = 3 then
    if e = 2 then -1/(3*Real.sqrt 3) else if e = 3 then -1/(3*Real.sqrt 3)
      else -2/(3*Real.sqrt 3)
  else
    if e = 2 then -1/(2*Real.sqrt 3) else if e = 3 then -2/(3*Real.sqrt 3)
      else 1/Real.sqrt 3

-- Nine closed finite entries expand two divisor lists and the six residue slots.
set_option maxHeartbeats 1500000 in
/-- Exact finite arithmetic core table, without evaluating a numerical Gram. -/
theorem packet_core_table (d e : ℕ) (hd : d ∈ packetSet) (he : e ∈ packetSet) :
    packetDifferenceCotangentCoreEntry 6 d e = coreTable d e := by
  rw [coreEntry_finset_expansion]
  simp only [packetSet, Finset.mem_insert, Finset.mem_singleton] at hd he
  rcases hd with rfl | rfl | rfl <;> rcases he with rfl | rfl | rfl <;>
    norm_num [
      show (2 : ℕ).divisors = {1,2} by decide,
      show (3 : ℕ).divisors = {1,3} by decide,
      show (6 : ℕ).divisors = {1,2,3,6} by decide,
      ArithmeticFunction.moebius_apply_prime (by decide : Nat.Prime 2),
      ArithmeticFunction.moebius_apply_prime (by decide : Nat.Prime 3),
      residueDifferenceCotangentCore, Fin.sum_univ_succ, centeredResidueProduct, residue,
      cotangent_six_zero, cotangent_six_one, cotangent_six_two, cotangent_six_three,
      cotangent_six_four, cotangent_six_five, cotangent_six_six, coreTable]
  all_goals
    have hs : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
    field_simp [ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3))]
    nlinarith

theorem coefficients_mean_one : ramanujanTotientVector packetSet ⬝ᵥ coefficients = 2 := by
  unfold dotProduct
  rw [sum_packetSet]
  norm_num [qTwo, qThree, qSix, coefficients, ramanujanTotientVector,
    totient_two, totient_three, totient_six]

theorem packet_six_residue (k : ℕ) :
    ramanujanPacket 6 k = residue 6 k - residue 3 k - residue 2 k := by
  rw [ramanujanPacket, show (6 : ℕ).divisors = {1,2,3,6} by decide]
  norm_num [ArithmeticFunction.moebius_apply_prime (by decide : Nat.Prime 2),
    ArithmeticFunction.moebius_apply_prime (by decide : Nat.Prime 3), residue, Nat.mod_one]
  ring

/-- The packet vector is the familiar physical approximant `g₂+g₃+g₆`. -/
theorem synthesis_eq_three_atoms (k : ℕ) : synthesis packetSet coefficients k =
    residue 2 k / 2 + residue 3 k / 3 + residue 6 k / 6 := by
  unfold synthesis FiniteSchur.combination
  rw [sum_packetSet]
  norm_num [qTwo, qThree, qSix, coefficients,
    ramanujanPacket_prime_eq_residue 2 (by norm_num),
    ramanujanPacket_prime_eq_residue 3 (by norm_num), packet_six_residue]
  ring

/-- Exact signed stationarity in the actual physical core. -/
theorem coefficients_core_stationary : derivedCore packetSet *ᵥ coefficients =
    (-1/(4*Real.sqrt 3)) • ramanujanTotientVector packetSet := by
  rw [← arithmeticPacketCore_eq_derivedCore 6 packetSet (by norm_num)
    packetSet_legal packetSet_period]
  funext i
  have hentry (j : packetSet) := packet_core_table i.val j.val i.property j.property
  change (∑ j : packetSet, packetDifferenceCotangentCoreEntry 6 i.val j.val * coefficients j) = _
  simp_rw [hentry]
  rw [sum_packetSet]
  have hi := i.property
  simp only [packetSet, Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with hi | hi | hi <;>
    norm_num [hi, qTwo, qThree, qSix, coefficients, coreTable,
      ramanujanTotientVector, Pi.smul_apply, smul_eq_mul,
      totient_two, totient_three, totient_six]
  all_goals
    field_simp [ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3))]
    ring

/-- The inverse-core charge is exactly `-8 sqrt(3)`. -/
theorem inverseCharge_six : inverseCharge packetSet = -8 * Real.sqrt 3 := by
  have hdet := derivedCore_det_ne_zero packetSet packetSet_legal packetSet_odd
  have hinv : (derivedCore packetSet)⁻¹ * derivedCore packetSet = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet)
  have he := congrArg (fun v => (derivedCore packetSet)⁻¹ *ᵥ v) coefficients_core_stationary
  rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec, Matrix.mulVec_smul] at he
  have hd := congrArg (fun v => ramanujanTotientVector packetSet ⬝ᵥ v) he
  rw [coefficients_mean_one, dotProduct_smul, smul_eq_mul] at hd
  change 2 = (-1/(4*Real.sqrt 3)) * inverseCharge packetSet at hd
  have hs : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  field_simp [ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3))] at hd
  nlinarith

theorem coefficients_eq_optimizer : coefficients = constrainedOptimizer packetSet := by
  have hdet := derivedCore_det_ne_zero packetSet packetSet_legal packetSet_odd
  have hinv : (derivedCore packetSet)⁻¹ * derivedCore packetSet = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet)
  have he := congrArg (fun v => (derivedCore packetSet)⁻¹ *ᵥ v) coefficients_core_stationary
  rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec, Matrix.mulVec_smul] at he
  rw [constrainedOptimizer, inverseCharge_six]
  convert he using 1
  congr 1
  field_simp [ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3))]
  ring

/-- Literal exact complete physical minimum. -/
theorem minimum_error_six : paretoError (synthesis packetSet coefficients) =
    1 - Real.pi/(2*Real.sqrt 3) := by
  rw [coefficients_eq_optimizer, constrainedOptimizer_error packetSet packetSet_legal
    packetSet_odd, inverseCharge_six]
  field_simp [ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3))]
  ring

theorem minimum_error_six_unique (c : packetSet → ℝ)
    (hc : ramanujanTotientVector packetSet ⬝ᵥ c = 2) :
    1 - Real.pi/(2*Real.sqrt 3) ≤ paretoError (synthesis packetSet c) ∧
      (paretoError (synthesis packetSet c) = 1 - Real.pi/(2*Real.sqrt 3) ↔
        c = coefficients) := by
  have h := constrainedOptimizer_unique_minimum packetSet packetSet_legal packetSet_odd c hc
  rw [inverseCharge_six, ← coefficients_eq_optimizer] at h
  have he : 1 + 4*Real.pi/(-8*Real.sqrt 3) = 1-Real.pi/(2*Real.sqrt 3) := by
    field_simp [ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3))]
    ring
  rwa [he] at h

end RiemannResearch.RH.Pareto.MeanOneSix
