import RiemannResearch.RH.TwoSeedContrastObstruction

/-!
# Joint prime-coordinate certificates for two-seed contrasts

This strengthens the single-prime certificate by retaining every cross term
between a finite set of prime-coordinate Riesz vectors.  Their only common
physical coordinate is 1, so the Gram matrix has an exact rank-one correction.
The resulting completed-square identity applies to the actual Pareto norm.

Source: the user's uploaded
`RH_Zero_Ordinates_Haar_and_Actual_Residual_Gain_Consolidated_2026-10-11 (1).md`,
Section 12. The joint finite certificate strengthens that section's individual
prime obstruction. No Riemann-hypothesis or prime-density assumption is used.
-/

open scoped BigOperators
noncomputable section

namespace RiemannResearch.RH.Pareto
open AdjacentPacket FiniteTwoSeedCompletion RamanujanLaguerre

/-- The prime Möbius coordinate is an actual three-point difference. -/
theorem prime_mobius_coordinate_apply (q : ℕ) (hq : q.Prime)
    (f : ThresholdHilbert) :
    mobiusDifferenceCLM q f =
      hilbertSequence f q - hilbertSequence f (q - 1) - hilbertSequence f 1 := by
  rw [mobiusDifferenceCLM_apply]
  unfold mobiusDifference
  rw [hq.divisors]
  simp [Finset.sum_insert, Finset.sum_singleton, hq.ne_one.symm,
    ArithmeticFunction.moebius_apply_prime hq, Nat.div_self hq.pos]
  ring

/-- Distinct odd primes cannot have overlapping adjacent physical coordinates. -/
private theorem odd_prime_mod_two (q : ℕ) (hq : q.Prime) (hq3 : 3 < q) :
    q % 2 = 1 := by
  have hn : ¬ 2 ∣ q := by
    intro hd
    rcases (Nat.dvd_prime hq).mp hd with h | h <;> omega
  have hm : q % 2 ≠ 0 := by simpa only [Nat.dvd_iff_mod_eq_zero] using hn
  have hl := Nat.mod_lt q (by omega : 0 < 2)
  omega

/-- Exact Gram entries, including the shared coordinate at 1. -/
theorem prime_mobiusRiesz_inner (q r : ℕ) (hq : q.Prime) (hr : r.Prime)
    (hq3 : 3 < q) (hr3 : 3 < r) :
    inner ℝ (mobiusRieszHilbert q) (mobiusRieszHilbert r) =
      if q = r then 2 * ((q : ℝ)^2 + 1) else 2 := by
  by_cases hqr : q = r
  · subst r
    rw [if_pos rfl, real_inner_self_eq_norm_sq, mobiusRieszHilbert_norm,
      mobiusDifferenceCLM_prime_norm_sq q hq (by omega)]
  · rw [if_neg hqr, mobiusRieszHilbert_inner,
      prime_mobius_coordinate_apply q hq]
    have hqm := odd_prime_mod_two q hq hq3
    have hrm := odd_prime_mod_two r hr hr3
    have hnd2 : ¬ 2 ∣ r := by
      intro hd
      rcases (Nat.dvd_prime hr).mp hd with h | h <;> omega
    have hnq : ¬ q ∣ r := by
      intro hd
      rcases (Nat.dvd_prime hr).mp hd with h | h <;> omega
    have hnqs : ¬ q + 1 ∣ r := by
      intro hd
      rcases (Nat.dvd_prime hr).mp hd with h | h <;> omega
    have hnqp : ¬ q - 1 ∣ r := by
      intro hd
      rcases (Nat.dvd_prime hr).mp hd with h | h <;> omega
    have hqp : q - 1 + 1 = q := by omega
    rw [mobiusRieszHilbert_sequence r q hr.pos,
      mobiusRieszHilbert_sequence r (q - 1) hr.pos,
      mobiusRieszHilbert_sequence r 1 hr.pos]
    simp [dualCoeff, hnq, hnqs, hnqp, hqp, hnd2,
      ArithmeticFunction.moebius_apply_prime hr]
    norm_num

namespace ContrastObstruction

def jointPrimeMass (S : Finset ℕ) : ℝ :=
  ∑ q ∈ S, 1 / (q : ℝ)^2

def jointPrimeRiesz (S : Finset ℕ) : ThresholdHilbert :=
  ∑ q ∈ S, (1 / (q : ℝ)^2) • mobiusRieszHilbert q

theorem jointPrimeMass_nonneg (S : Finset ℕ) : 0 ≤ jointPrimeMass S := by
  unfold jointPrimeMass
  positivity

/-- The entire finite Gram quadratic form, with the rank-one term intact. -/
theorem weighted_primeRiesz_norm_sq (S : Finset ℕ) (x : ℕ → ℝ)
    (hS : ∀ q ∈ S, q.Prime ∧ 3 < q) :
    ‖∑ q ∈ S, x q • mobiusRieszHilbert q‖^2 =
      2 * ((∑ q ∈ S, (q : ℝ)^2 * (x q)^2) + (∑ q ∈ S, x q)^2) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert q S hqS ih =>
    have hq := hS q (Finset.mem_insert_self q S)
    have hrest : ∀ r ∈ S, r.Prime ∧ 3 < r := by
      intro r hr
      exact hS r (Finset.mem_insert_of_mem hr)
    have hi : inner ℝ (mobiusRieszHilbert q)
        (∑ r ∈ S, x r • mobiusRieszHilbert r) = 2 * (∑ r ∈ S, x r) := by
      rw [inner_sum]
      simp_rw [real_inner_smul_right]
      calc
        (∑ r ∈ S, x r * inner ℝ (mobiusRieszHilbert q) (mobiusRieszHilbert r)) =
            ∑ r ∈ S, x r * 2 := by
          apply Finset.sum_congr rfl
          intro r hr
          have hqr : q ≠ r := by
            intro he
            apply hqS
            simpa only [he] using hr
          rw [prime_mobiusRiesz_inner q r hq.1 (hrest r hr).1 hq.2
            (hrest r hr).2, if_neg hqr]
        _ = _ := by rw [← Finset.sum_mul]; ring
    rw [Finset.sum_insert hqS, Finset.sum_insert hqS, Finset.sum_insert hqS,
      norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      real_inner_smul_left, hi, mobiusRieszHilbert_norm,
      mobiusDifferenceCLM_prime_norm_sq q hq.1 (by omega), ih hrest]
    ring

theorem jointPrimeRiesz_norm_sq (S : Finset ℕ)
    (hS : ∀ q ∈ S, q.Prime ∧ 3 < q) :
    ‖jointPrimeRiesz S‖^2 = 2 * jointPrimeMass S * (1 + jointPrimeMass S) := by
  rw [jointPrimeRiesz, weighted_primeRiesz_norm_sq S _ hS]
  have he : (∑ q ∈ S, (q : ℝ)^2 * (1 / (q : ℝ)^2)^2) = jointPrimeMass S := by
    apply Finset.sum_congr rfl
    intro q hq
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (hS q hq).1.ne_zero
    field_simp [hq0]
  rw [he]
  change 2 * (jointPrimeMass S + (jointPrimeMass S)^2) = _
  ring

theorem completedBudget_jointPrime_pairing (M : ℕ) (S : Finset ℕ)
    (hS : ∀ q ∈ S, q.Prime ∧ 3 < q ∧ M < q)
    (F : ThresholdHilbert) (hF : F ∈ completedBudget M) :
    inner ℝ (hilbertOne - F) (jointPrimeRiesz S) = -jointPrimeMass S := by
  rw [jointPrimeRiesz, inner_sum]
  simp_rw [real_inner_smul_right]
  rw [jointPrimeMass, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  obtain ⟨hp, hq3, hMq⟩ := hS q hq
  have hz : mobiusDifferenceCLM q F = 0 :=
    completedBudget_le_coordinate_kernel M q hp hq3 hMq hF
  rw [real_inner_comm, mobiusRieszHilbert_inner, map_sub,
    prime_coordinate_one q hp, hz]
  ring

/-- Simultaneous prime constraints give an exact, stronger full-energy certificate. -/
theorem completedBudget_jointPrime_error_identity (M : ℕ) (S : Finset ℕ)
    (hS : ∀ q ∈ S, q.Prime ∧ 3 < q ∧ M < q)
    (F : ThresholdHilbert) (hF : F ∈ completedBudget M) :
    ‖hilbertOne - F‖^2 = jointPrimeMass S / (2 * (1 + jointPrimeMass S)) +
      ‖hilbertOne - F + (1 / (2 * (1 + jointPrimeMass S))) • jointPrimeRiesz S‖^2 := by
  have hnonneg := jointPrimeMass_nonneg S
  have hpos : 0 < 1 + jointPrimeMass S := by positivity
  rw [norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_smul_right, completedBudget_jointPrime_pairing M S hS F hF,
    jointPrimeRiesz_norm_sq S (fun q hq => ⟨(hS q hq).1, (hS q hq).2.1⟩)]
  field_simp [ne_of_gt hpos]
  ring

theorem completedBudget_jointPrime_error_floor (M : ℕ) (S : Finset ℕ)
    (hS : ∀ q ∈ S, q.Prime ∧ 3 < q ∧ M < q)
    (F : ThresholdHilbert) (hF : F ∈ completedBudget M) :
    jointPrimeMass S / (2 * (1 + jointPrimeMass S)) ≤ ‖hilbertOne - F‖^2 := by
  rw [completedBudget_jointPrime_error_identity M S hS F hF]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem actual_distance_jointPrime_lower_bound (M : ℕ) (S : Finset ℕ)
    (hS : ∀ q ∈ S, q.Prime ∧ 3 < q ∧ M < q) :
    jointPrimeMass S / (2 * (1 + jointPrimeMass S)) ≤ CoupledResidual.distance M := by
  apply completedBudget_jointPrime_error_floor M S hS (CoupledResidual.fit M)
  apply (budgetHilbert M ⊔ contrastSpan).le_topologicalClosure
  exact (show budgetHilbert M ≤ budgetHilbert M ⊔ contrastSpan from le_sup_left)
    ((budgetHilbert M).starProjection_apply_mem _)

end ContrastObstruction
end RiemannResearch.RH.Pareto

/-!
The following continuation proves optimality within the finite affine system of
prime-coordinate constraints.  Source: the uploaded
`RH_Zero_Ordinates_Haar_and_Actual_Residual_Gain_Consolidated_2026-10-11 (1).md`,
Section 12, strengthened by combining the representers with their exact
shared-coordinate Gram entries.  The minimizing model below is not asserted to
be an actual residual from the completed contrast budget.
-/

namespace RiemannResearch.RH.Pareto.ContrastObstruction

/-- Every selected prime sees the same exact charge of the joint certificate. -/
theorem jointPrimeRiesz_coordinate (S : Finset ℕ)
    (hS : ∀ r ∈ S, r.Prime ∧ 3 < r) (q : ℕ) (hqS : q ∈ S) :
    mobiusDifferenceCLM q (jointPrimeRiesz S) = 2 * (1 + jointPrimeMass S) := by
  rw [← mobiusRieszHilbert_inner q, jointPrimeRiesz, inner_sum]
  simp_rw [real_inner_smul_right]
  have hterm (r : ℕ) (hrS : r ∈ S) :
      (1 / (r : ℝ)^2) * inner ℝ (mobiusRieszHilbert q) (mobiusRieszHilbert r) =
        2 * (1 / (r : ℝ)^2) + if q = r then 2 else 0 := by
    rw [prime_mobiusRiesz_inner q r (hS q hqS).1 (hS r hrS).1
      (hS q hqS).2 (hS r hrS).2]
    by_cases hqr : q = r
    · subst r
      have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (hS q hqS).1.ne_zero
      simp only [ite_true]
      field_simp [hq0]
      ring
    · simp only [if_neg hqr]
      ring
  calc
    (∑ r ∈ S, (1 / (r : ℝ)^2) *
        inner ℝ (mobiusRieszHilbert q) (mobiusRieszHilbert r)) =
        ∑ r ∈ S, (2 * (1 / (r : ℝ)^2) + if q = r then 2 else 0) := by
      apply Finset.sum_congr rfl
      intro r hrS
      exact hterm r hrS
    _ = 2 * jointPrimeMass S + 2 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp [jointPrimeMass, hqS]
    _ = _ := by ring

def jointPrimeModel (S : Finset ℕ) : ThresholdHilbert :=
  -(1 / (2 * (1 + jointPrimeMass S))) • jointPrimeRiesz S

/-- A feasible model attains every selected prime-coordinate constraint. -/
theorem jointPrimeModel_coordinate (S : Finset ℕ)
    (hS : ∀ q ∈ S, q.Prime ∧ 3 < q) (q : ℕ) (hqS : q ∈ S) :
    mobiusDifferenceCLM q (jointPrimeModel S) = -1 := by
  have hnonneg := jointPrimeMass_nonneg S
  have hpos : 0 < 1 + jointPrimeMass S := by positivity
  rw [jointPrimeModel, map_smul, jointPrimeRiesz_coordinate S hS q hqS]
  simp only [smul_eq_mul]
  field_simp [ne_of_gt hpos]

theorem jointPrimeModel_norm_sq (S : Finset ℕ)
    (hS : ∀ q ∈ S, q.Prime ∧ 3 < q) :
    ‖jointPrimeModel S‖^2 = jointPrimeMass S / (2 * (1 + jointPrimeMass S)) := by
  have hnonneg := jointPrimeMass_nonneg S
  have hpos : 0 < 1 + jointPrimeMass S := by positivity
  simp only [jointPrimeModel, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, neg_sq]
  rw [jointPrimeRiesz_norm_sq S hS]
  field_simp [ne_of_gt hpos]

/-- This certificate is sharp for the finite system, without a legality claim. -/
theorem jointPrime_constraints_error_identity (S : Finset ℕ)
    (hS : ∀ q ∈ S, q.Prime ∧ 3 < q)
    (r : ThresholdHilbert) (hr : ∀ q ∈ S, mobiusDifferenceCLM q r = -1) :
    ‖r‖^2 = jointPrimeMass S / (2 * (1 + jointPrimeMass S)) +
      ‖r - jointPrimeModel S‖^2 := by
  have hi : inner ℝ r (jointPrimeRiesz S) = -jointPrimeMass S := by
    rw [jointPrimeRiesz, inner_sum]
    simp_rw [real_inner_smul_right]
    rw [jointPrimeMass, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro q hqS
    rw [real_inner_comm, mobiusRieszHilbert_inner, hr q hqS]
    ring
  have hnonneg := jointPrimeMass_nonneg S
  have hpos : 0 < 1 + jointPrimeMass S := by positivity
  rw [jointPrimeModel, neg_smul, sub_neg_eq_add, norm_add_sq_real,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, real_inner_smul_right,
    hi, jointPrimeRiesz_norm_sq S hS]
  field_simp [ne_of_gt hpos]
  ring

theorem jointPrimeModel_minimizes (S : Finset ℕ)
    (hS : ∀ q ∈ S, q.Prime ∧ 3 < q)
    (r : ThresholdHilbert) (hr : ∀ q ∈ S, mobiusDifferenceCLM q r = -1) :
    ‖jointPrimeModel S‖^2 ≤ ‖r‖^2 := by
  rw [jointPrimeModel_norm_sq S hS, jointPrime_constraints_error_identity S hS r hr]
  exact le_add_of_nonneg_right (sq_nonneg _)

@[simp] theorem jointPrimeMass_singleton (q : ℕ) :
    jointPrimeMass {q} = 1 / (q : ℝ)^2 := by
  simp [jointPrimeMass]

/-- The strengthened finite certificate recovers the old single-prime formula. -/
theorem jointPrime_floor_singleton (q : ℕ) (hq : 0 < q) :
    jointPrimeMass {q} / (2 * (1 + jointPrimeMass {q})) =
      1 / (2 * ((q : ℝ)^2 + 1)) := by
  rw [jointPrimeMass_singleton]
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hq
  have hp : 0 < (q : ℝ)^2 + 1 := by positivity
  have hm : 0 < 1 + 1 / (q : ℝ)^2 := by positivity
  field_simp [hq0, ne_of_gt hp, ne_of_gt hm]

end RiemannResearch.RH.Pareto.ContrastObstruction
