import RiemannResearch.RH.MobiusHilbertCoordinates
import RiemannResearch.RH.CoupledResidualCorrections
/-!
# Prime-coordinate obstruction to future two-seed contrasts

Source: the actual two-seed setup in the user-provided RH_Dyadic_Two_Seed_Pareto_Residual_Gain_Work_Handoff_2026-09-18(1).md, Sections 2--4 and 13. The prime contrast obstruction and its exact error decomposition were derived in the 2026-09-19 continuation. The proof uses existing Mobius-residue duality and the full Pareto norm. This excludes only a fixed old budget plus future seed differences, not the complete dyadic legal family. No mathematical novelty claim is intended.
-/

open scoped BigOperators
noncomputable section
namespace RiemannResearch.RH.Pareto
open AdjacentPacket FiniteTwoSeedCompletion RamanujanLaguerre

theorem mobius_generator_coordinate (q p m : ℕ) (hq : 1 < q)
    (hp : 0 < p) (hm : 0 < m) :
    mobiusDifferenceCLM q (generator p m hp hm) =
      (if q = p*m then -((p*m : ℕ) : ℝ) else 0) -
        (if q = m then -(m : ℝ) else 0) := by
  rw [mobiusDifferenceCLM_apply]
  have he : hilbertSequence (generator p m hp hm) =
      fun n => residue (p*m) n - residue m n :=
    funext (generator_sequence_apply p m hp hm)
  rw [he]
  have hsub : mobiusDifference q (fun n => residue (p*m) n-residue m n) =
      mobiusDifference q (residue (p*m))-mobiusDifference q (residue m) := by
    unfold mobiusDifference
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  rw [hsub, mobiusDifference_residue q (p*m) hq,
    mobiusDifference_residue q m hq]

theorem prime_mobius_generator_coordinate (q p m : ℕ)
    (hq : q.Prime) (hq3 : 3 < q) (hp : 0 < p) (hm : 0 < m)
    (hseed : p = 2 ∨ p = 3) :
    mobiusDifferenceCLM q (generator p m hp hm) =
      if q = m then (m : ℝ) else 0 := by
  have hneq : q ≠ p*m := by
    intro he
    have hd : p ∣ q := by
      rw [he]
      exact Nat.dvd_mul_right p m
    have hh := (Nat.dvd_prime hq).mp hd
    rcases hseed with rfl | rfl <;> omega
  rw [mobius_generator_coordinate q p m (by omega) hp hm, if_neg hneq]
  split_ifs <;> ring

theorem mobiusDifferenceCLM_prime_norm_sq (q : ℕ)
    (hq : q.Prime) (hq3 : 3 < q) :
    ‖mobiusDifferenceCLM q‖ ^ 2 = 2 * ((q : ℝ)^2 + 1) := by
  classical
  have hnd2 : ¬ 2 ∣ q := by
    intro hd
    rcases (Nat.dvd_prime hq).mp hd with h | h <;> omega
  have hndprev : ¬ q - 1 ∣ q := by
    intro hd
    rcases (Nat.dvd_prime hq).mp hd with h | h <;> omega
  have hndsucc : ¬ q + 1 ∣ q := by
    intro hd
    have := Nat.le_of_dvd hq.pos hd
    omega
  have hd1 : dualCoeff q 1 = -1 := by
    simp [dualCoeff, hnd2, ArithmeticFunction.moebius_apply_prime hq]
  have hdp : dualCoeff q (q - 1) = -1 := by
    simp [dualCoeff, hndprev, Nat.sub_add_cancel (show 1 ≤ q by omega), Nat.div_self hq.pos]
  have hdq : dualCoeff q q = 1 := by
    simp [dualCoeff, hndsucc, Nat.div_self hq.pos]
  let f : ℕ → ℝ := fun j =>
    (j : ℝ) * ((j : ℝ) + 1) * (dualCoeff q j : ℝ)^2
  have hsub : ({1, q - 1, q} : Finset ℕ) ⊆ Finset.Icc 1 q := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl <;> simp only [Finset.mem_Icc] <;> omega
  have hsum : (∑ j ∈ Finset.Icc 1 q, f j) =
      ∑ j ∈ ({1, q - 1, q} : Finset ℕ), f j := by
    symm
    apply Finset.sum_subset hsub
    intro j hj hjnot
    have hjpos : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hj1 : j ≠ 1 := by
      intro he
      apply hjnot
      simp [he]
    have hjp : j ≠ q - 1 := by
      intro he
      apply hjnot
      simp [he]
    have hjq : j ≠ q := by
      intro he
      apply hjnot
      simp [he]
    have hnj : ¬ j ∣ q := by
      intro hd
      rcases (Nat.dvd_prime hq).mp hd with h | h
      · exact hj1 h
      · exact hjq h
    have hnjs : ¬ j + 1 ∣ q := by
      intro hd
      rcases (Nat.dvd_prime hq).mp hd with h | h
      · omega
      · apply hjp
        omega
    simp [f, dualCoeff, hnj, hnjs]
  have hp1 : q - 1 ≠ 1 := by omega
  have hq1 : q ≠ 1 := by omega
  have hpq : q - 1 ≠ q := by omega
  have hcast : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ q by omega)]
    norm_num
  rw [mobiusDifferenceCLM_norm_sq q hq.pos]
  change (∑ j ∈ Finset.Icc 1 q, f j) = _
  rw [hsum]
  simp [f, hd1, hdp, hdq, hp1.symm, hq1.symm, hpq, hcast]
  ring

namespace ContrastObstruction

def contrast (m : {m : ℕ // 0 < m}) : ThresholdHilbert :=
  generator 3 m.val (by omega) m.property -
    generator 2 m.val (by omega) m.property

def contrastSpan : Submodule ℝ ThresholdHilbert :=
  Submodule.span ℝ (Set.range contrast)

def completedBudget (M : ℕ) : Submodule ℝ ThresholdHilbert :=
  (budgetHilbert M ⊔ contrastSpan).topologicalClosure

theorem contrast_coordinate_zero (q : ℕ) (hq : q.Prime) (hq3 : 3 < q)
    (m : {m : ℕ // 0 < m}) :
    mobiusDifferenceCLM q (contrast m) = 0 := by
  unfold contrast
  rw [map_sub,
    prime_mobius_generator_coordinate q 3 m.val hq hq3
      (by omega) m.property (Or.inr rfl),
    prime_mobius_generator_coordinate q 2 m.val hq hq3
      (by omega) m.property (Or.inl rfl), sub_self]

theorem budget_le_coordinate_kernel (M q : ℕ) (hq : q.Prime)
    (hq3 : 3 < q) (hMq : M < q) :
    budgetHilbert M ≤ (mobiusDifferenceCLM q).ker := by
  rw [← canonicalHilbertFamily_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  obtain ⟨hm, hmM, hs⟩ := (mem_canonicalIndices M i.val).mp i.property
  have hseed : i.val.1 = 2 ∨ i.val.1 = 3 := by
    rcases hs with h | ⟨h, _⟩
    · exact Or.inr h
    · exact Or.inl h
  change mobiusDifferenceCLM q (canonicalHilbertFamily M i) = 0
  unfold canonicalHilbertFamily
  rw [prime_mobius_generator_coordinate _ _ _ hq hq3 _ _ hseed]
  simp [show q ≠ i.val.2 by omega]

theorem completedBudget_le_coordinate_kernel (M q : ℕ) (hq : q.Prime)
    (hq3 : 3 < q) (hMq : M < q) :
    completedBudget M ≤ (mobiusDifferenceCLM q).ker := by
  apply Submodule.topologicalClosure_minimal
  · apply sup_le (budget_le_coordinate_kernel M q hq hq3 hMq)
    apply Submodule.span_le.mpr
    rintro _ ⟨m, rfl⟩
    exact contrast_coordinate_zero q hq hq3 m
  · exact (mobiusDifferenceCLM q).isClosed_ker

theorem prime_coordinate_one (q : ℕ) (hq : q.Prime) :
    mobiusDifferenceCLM q hilbertOne = -1 := by
  rw [mobius_coordinate_one q hq.pos, ArithmeticFunction.moebius_apply_prime hq]
  norm_num

theorem completedBudget_one_not_mem (M q : ℕ) (hq : q.Prime)
    (hq3 : 3 < q) (hMq : M < q) :
    hilbertOne ∉ completedBudget M := by
  intro hf
  have hz : mobiusDifferenceCLM q hilbertOne = 0 :=
    completedBudget_le_coordinate_kernel M q hq hq3 hMq hf
  rw [prime_coordinate_one q hq] at hz
  norm_num at hz


theorem prime_coordinate_norm_pos (q : ℕ) (hq : q.Prime) :
    0 < ‖mobiusDifferenceCLM q‖ := by
  apply norm_pos_iff.mpr
  intro he
  have h := prime_coordinate_one q hq
  rw [he] at h
  norm_num at h

/-- An exact full-norm decomposition, not a truncated coordinate estimate. -/
theorem completedBudget_error_identity (M q : ℕ) (hq : q.Prime)
    (hq3 : 3 < q) (hMq : M < q) (F : ThresholdHilbert)
    (hF : F ∈ completedBudget M) :
    ‖hilbertOne-F‖^2 = 1 / ‖mobiusDifferenceCLM q‖^2 +
      ‖hilbertOne-F + (1/‖mobiusDifferenceCLM q‖^2) •
        mobiusRieszHilbert q‖^2 := by
  have hz : mobiusDifferenceCLM q F = 0 :=
    completedBudget_le_coordinate_kernel M q hq hq3 hMq hF
  have hi : inner ℝ (hilbertOne-F) (mobiusRieszHilbert q) = -1 := by
    rw [real_inner_comm, mobiusRieszHilbert_inner, map_sub,
      prime_coordinate_one q hq, hz]
    ring
  rw [norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_smul_right, hi, mobiusRieszHilbert_norm]
  field_simp [ne_of_gt (prime_coordinate_norm_pos q hq)]
  ring

theorem screened_contrast_coordinate_zero (M q : ℕ) (hq : q.Prime)
    (hq3 : 3 < q) (hMq : M < q) (m : {m : ℕ // 0 < m}) :
    mobiusDifferenceCLM q
      (contrast m-(budgetHilbert M).starProjection (contrast m)) = 0 := by
  have hz : mobiusDifferenceCLM q
      ((budgetHilbert M).starProjection (contrast m)) = 0 :=
    budget_le_coordinate_kernel M q hq hq3 hMq
      ((budgetHilbert M).starProjection_apply_mem _)
  rw [map_sub, contrast_coordinate_zero q hq hq3 m, hz, sub_self]

theorem actual_residual_prime_coordinate (M q : ℕ) (hq : q.Prime)
    (hq3 : 3 < q) (hMq : M < q) :
    mobiusDifferenceCLM q (CoupledResidual.error M) = -1 := by
  have hz : mobiusDifferenceCLM q (CoupledResidual.fit M) = 0 :=
    budget_le_coordinate_kernel M q hq hq3 hMq
      ((budgetHilbert M).starProjection_apply_mem _)
  rw [CoupledResidual.error, map_sub, prime_coordinate_one q hq, hz, sub_zero]

theorem completedBudget_error_floor (M q : ℕ) (hq : q.Prime)
    (hq3 : 3 < q) (hMq : M < q) (F : ThresholdHilbert)
    (hF : F ∈ completedBudget M) :
    1 / ‖mobiusDifferenceCLM q‖^2 ≤ ‖hilbertOne-F‖^2 := by
  have hz : mobiusDifferenceCLM q F = 0 :=
    completedBudget_le_coordinate_kernel M q hq hq3 hMq hF
  have hn : 0 < ‖mobiusDifferenceCLM q‖ := by
    apply norm_pos_iff.mpr
    intro he
    have h := prime_coordinate_one q hq
    rw [he] at h
    norm_num at h
  have hb := (mobiusDifferenceCLM q).le_opNorm (hilbertOne-F)
  rw [map_sub, prime_coordinate_one q hq, hz] at hb
  norm_num at hb
  apply (div_le_iff₀ (sq_pos_of_pos hn)).mpr
  nlinarith [sq_nonneg (‖mobiusDifferenceCLM q‖*‖hilbertOne-F‖-1)]

theorem new_prime_generator_escapes (q : ℕ) (hq : q.Prime) (hq3 : 3 < q) :
    mobiusDifferenceCLM q (generator 2 q (by omega) hq.pos) = (q : ℝ) := by
  rw [prime_mobius_generator_coordinate q 2 q hq hq3
    (by omega) hq.pos (Or.inl rfl)]
  simp


theorem completedBudget_prime_error_identity (M q : ℕ) (hq : q.Prime)
    (hq3 : 3 < q) (hMq : M < q) (F : ThresholdHilbert)
    (hF : F ∈ completedBudget M) :
    ‖hilbertOne-F‖^2 = 1 / (2*((q : ℝ)^2+1)) +
      ‖hilbertOne-F + (1/(2*((q : ℝ)^2+1))) •
        mobiusRieszHilbert q‖^2 := by
  simpa only [mobiusDifferenceCLM_prime_norm_sq q hq hq3] using
    completedBudget_error_identity M q hq hq3 hMq F hF

theorem completedBudget_prime_error_floor (M q : ℕ) (hq : q.Prime)
    (hq3 : 3 < q) (hMq : M < q) (F : ThresholdHilbert)
    (hF : F ∈ completedBudget M) :
    1 / (2*((q : ℝ)^2+1)) ≤ ‖hilbertOne-F‖^2 := by
  simpa only [mobiusDifferenceCLM_prime_norm_sq q hq hq3] using
    completedBudget_error_floor M q hq hq3 hMq F hF

theorem actual_distance_prime_lower_bound (M q : ℕ) (hq : q.Prime)
    (hq3 : 3 < q) (hMq : M < q) :
    1 / (2*((q : ℝ)^2+1)) ≤ CoupledResidual.distance M := by
  apply completedBudget_prime_error_floor M q hq hq3 hMq (CoupledResidual.fit M)
  apply (budgetHilbert M ⊔ contrastSpan).le_topologicalClosure
  exact (show budgetHilbert M ≤ budgetHilbert M ⊔ contrastSpan from le_sup_left)
    ((budgetHilbert M).starProjection_apply_mem _)

theorem prime_coefficient_sum (q : ℕ) (hq : q.Prime) (hq3 : 3 < q) (a b : ℝ) :
    mobiusDifferenceCLM q
      (a • generator 2 q (by omega) hq.pos +
        b • generator 3 q (by omega) hq.pos) = (q : ℝ)*(a+b) := by
  rw [map_add, map_smul, map_smul,
    prime_mobius_generator_coordinate q 2 q hq hq3 _ _ (Or.inl rfl),
    prime_mobius_generator_coordinate q 3 q hq hq3 _ _ (Or.inr rfl)]
  simp only [ite_true, smul_eq_mul]
  ring

end ContrastObstruction
end RiemannResearch.RH.Pareto
