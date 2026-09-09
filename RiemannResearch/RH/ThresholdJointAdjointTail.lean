import RiemannResearch.RH.ThresholdHilbertAdjoint

/-!
# Weighted-tail identities for two-seed adjoint rigidity

Source: Christian Noack, RH_Two_Seed_Threshold.tex, September 8, 2026,
Lemma 4.1 (joint adjoint rigidity), first weighted-tail step.
These identities apply to the actual weighted Hilbert space. They do not
assert joint rigidity or the Riemann-hypothesis equivalence.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
noncomputable section

/-- Dilating a physical tail indicator gives the exactly scaled later tail. -/
theorem hilbertDilation_tail (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    hilbertDilation m hm (hilbertTail n hn) =
      (m : ℝ) • hilbertTail (m*n) (Nat.mul_pos hm hn) := by
  unfold hilbertTail
  change hilbertDilationContinuous m hm
      ((1 / (n : ℝ)) • hilbertDilation n hn hilbertOne) = _
  rw [map_smul]
  simp only [hilbertDilationContinuous_apply]
  rw [hilbertDilation_comp, smul_smul]
  congr 1
  push_cast
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  field_simp

/-- The Hilbert pairing is precisely the absolutely convergent weighted tail. -/
theorem hilbertTail_inner_series (f : ThresholdHilbert) (n : ℕ) (hn : 0 < n) :
    inner ℝ (hilbertTail n hn) f =
      ∑' k, if n ≤ k then positiveWeight k * hilbertSequence f k else 0 := by
  rw [hilbert_inner_weighted, hilbertTail_sequence]
  unfold paretoInner
  apply tsum_congr
  intro k
  split_ifs <;> simp_all

theorem hilbertTail_series_summable (f : ThresholdHilbert) (n : ℕ) (hn : 0 < n) :
    Summable (fun k => if n ≤ k then
      positiveWeight k * hilbertSequence f k else 0) := by
  have h := weighted_product_summable_of_square
    (hilbertSequence_square_summable (hilbertTail n hn))
    (hilbertSequence_square_summable f)
  rw [hilbertTail_sequence] at h
  apply h.congr
  intro k
  split_ifs <;> simp_all

/-- Exact tail scaling forced by one genuine adjoint fixed equation. -/
theorem hilbertTail_inner_scaling (f : ThresholdHilbert)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hfix : hilbertDilationAdjoint m hm f = f) :
    (m : ℝ) * inner ℝ (hilbertTail (m*n) (Nat.mul_pos hm hn)) f =
      inner ℝ (hilbertTail n hn) f := by
  have h := ContinuousLinearMap.adjoint_inner_right
    (hilbertDilationContinuous m hm) (hilbertTail n hn) f
  change inner ℝ (hilbertTail n hn) (hilbertDilationAdjoint m hm f) =
      inner ℝ (hilbertDilation m hm (hilbertTail n hn)) f at h
  rw [hfix, hilbertDilation_tail, real_inner_smul_left] at h
  exact h.symm

/-- Iterated scaling gives the exact values on the shrinking recovery cells. -/
theorem hilbertTail_inner_pow_scaling (f : ThresholdHilbert)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hfix : hilbertDilationAdjoint m hm f = f) (j : ℕ) :
    (m : ℝ)^j * inner ℝ
      (hilbertTail (m^j*n) (Nat.mul_pos (pow_pos hm j) hn)) f =
      inner ℝ (hilbertTail n hn) f := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h := hilbertTail_inner_scaling f m (m^j*n) hm
      (Nat.mul_pos (pow_pos hm j) hn) hfix
    have hscaled := congrArg (fun x : ℝ => (m : ℝ)^j*x) h
    simpa [pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm,
      mul_assoc, mul_left_comm, mul_comm] using hscaled.trans ih

/-- Exact finite block between two weighted tails, retaining every term. -/
theorem hilbertTail_inner_sub (f : ThresholdHilbert)
    (p r : ℕ) (hp : 0 < p) (hpr : p ≤ r) :
    inner ℝ (hilbertTail p hp) f - inner ℝ (hilbertTail r (by omega)) f =
      ∑ k ∈ Finset.Ico p r, positiveWeight k * hilbertSequence f k := by
  rw [← inner_sub_left, hilbert_inner_weighted, hilbertSequence_sub,
    hilbertTail_sequence, hilbertTail_sequence]
  unfold paretoInner
  simp only [Pi.sub_apply]
  rw [tsum_eq_sum (s := Finset.Ico p r) (fun k hk => by
    have hk' : ¬ (p ≤ k ∧ k < r) := by simpa only [Finset.mem_Ico] using hk
    split_ifs <;> simp_all
    all_goals omega)]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_Ico.mp hk
  simp [hk'.1, Nat.not_le.mpr hk'.2]

/-- Consecutive weighted tails recover each physical coordinate exactly. -/
theorem hilbertTail_inner_successor (f : ThresholdHilbert)
    (n : ℕ) (hn : 0 < n) :
    inner ℝ (hilbertTail n hn) f - inner ℝ (hilbertTail (n+1) (by omega)) f =
      positiveWeight n * hilbertSequence f n := by
  rw [hilbertTail_inner_sub f n (n+1) hn (by omega)]
  simp

/-- The precise finite-cell Cauchy--Schwarz estimate in joint rigidity. -/
theorem hilbertTail_inner_sub_sq_le (f : ThresholdHilbert)
    (p r : ℕ) (hp : 0 < p) (hpr : p ≤ r) :
    (inner ℝ (hilbertTail p hp) f -
      inner ℝ (hilbertTail r (by omega)) f)^2 ≤
      (1 / (p : ℝ) - 1 / (r : ℝ)) *
        ∑ k ∈ Finset.Ico p r, positiveWeight k * hilbertSequence f k^2 := by
  rw [hilbertTail_inner_sub f p r hp hpr]
  have hsqrt (k : ℕ) : (Real.sqrt (positiveWeight k))^2 = positiveWeight k :=
    Real.sq_sqrt (by unfold positiveWeight; positivity)
  have hprod (k : ℕ) :
      Real.sqrt (positiveWeight k) *
        (Real.sqrt (positiveWeight k) * hilbertSequence f k) =
          positiveWeight k * hilbertSequence f k := by
    rw [← mul_assoc, ← pow_two, hsqrt]
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Ico p r)
    (fun k => Real.sqrt (positiveWeight k))
    (fun k => Real.sqrt (positiveWeight k) * hilbertSequence f k)
  simp only [hprod, mul_pow, hsqrt] at h
  rw [positiveWeight_interval p r hp hpr] at h
  exact h

/-- The entire remaining squared-norm tail, with the original Pareto weight. -/
def hilbertTailEnergy (f : ThresholdHilbert) (N : ℕ) : ℝ :=
  ∑' k, positiveWeight (k+N) * hilbertSequence f (k+N)^2

theorem hilbertTailEnergy_nonneg (f : ThresholdHilbert) (N : ℕ) :
    0 ≤ hilbertTailEnergy f N := by
  apply tsum_nonneg
  intro k
  unfold positiveWeight
  positivity

/-- Exact head plus complete tail, before taking any limit. -/
theorem hilbert_head_add_tailEnergy (f : ThresholdHilbert) (N : ℕ) :
    (∑ k ∈ Finset.range N, positiveWeight k * hilbertSequence f k^2) +
      hilbertTailEnergy f N = ‖f‖^2 := by
  rw [hilbert_norm_weighted_sq]
  exact (hilbertSequence_square_summable f).sum_add_tsum_nat_add N

theorem hilbertTailEnergy_tendsto_zero (f : ThresholdHilbert) :
    Filter.Tendsto (hilbertTailEnergy f) Filter.atTop (nhds 0) := by
  have h := (hilbertSequence_square_summable f).tendsto_sum_tsum_nat
  rw [← hilbert_norm_weighted_sq] at h
  have heq : hilbertTailEnergy f = fun N =>
      ‖f‖^2 - ∑ k ∈ Finset.range N, positiveWeight k * hilbertSequence f k^2 := by
    funext N
    linarith [hilbert_head_add_tailEnergy f N]
  rw [heq]
  have hc : Filter.Tendsto (fun _ : ℕ => ‖f‖^2) Filter.atTop (nhds (‖f‖^2)) :=
    tendsto_const_nhds
  simpa using hc.sub h

/-- Exact disjoint-block splitting of the full tail energy. -/
theorem hilbertTailEnergy_eq_block_add (f : ThresholdHilbert)
    (p r : ℕ) (hpr : p ≤ r) :
    hilbertTailEnergy f p =
      (∑ k ∈ Finset.Ico p r, positiveWeight k * hilbertSequence f k^2) +
        hilbertTailEnergy f r := by
  rw [Finset.sum_Ico_eq_sub _ hpr]
  linarith [hilbert_head_add_tailEnergy f p, hilbert_head_add_tailEnergy f r]

/-- Finite-cell tail differences are controlled by a budget tending to zero. -/
theorem hilbertTail_inner_sub_sq_le_tailEnergy (f : ThresholdHilbert)
    (p r : ℕ) (hp : 0 < p) (hpr : p ≤ r) :
    (inner ℝ (hilbertTail p hp) f -
      inner ℝ (hilbertTail r (by omega)) f)^2 ≤
      (1 / (p : ℝ) - 1 / (r : ℝ)) * hilbertTailEnergy f p := by
  apply (hilbertTail_inner_sub_sq_le f p r hp hpr).trans
  apply mul_le_mul_of_nonneg_left
  · linarith [hilbertTailEnergy_eq_block_add f p r hpr,
      hilbertTailEnergy_nonneg f r]
  · rw [← positiveWeight_interval p r hp hpr]
    apply Finset.sum_nonneg
    intro k hk
    unfold positiveWeight
    positivity

end
end RiemannResearch.RH.Pareto
