import RiemannResearch.RH.ParetoSublinearResidualTail

/-!
# Signed averages of actual canonical Möbius candidates

Source: user-provided `Pareto_Direct_Attempt_Sublinear_Energy_2026-09-22.md`,
Section 7, for the proposed family and its complete tail-covariance criterion.
The weights may have either sign. All covariance entries retain the entire
infinite physical Pareto tail. No boundedness provider is asserted.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.RH.Pareto

/-- Finite signed combinations of the genuine Hilbert-space candidates. -/
def signedMobiusAverage (s : Finset ℕ) (a : ℕ → ℝ) : ThresholdHilbert :=
  ∑ k ∈ s, a k • canonicalMobiusHilbert k

theorem signedMobiusAverage_sequence (s : Finset ℕ) (a : ℕ → ℝ) (j : ℕ) :
    hilbertSequence (signedMobiusAverage s a) j =
      ∑ k ∈ s, a k * canonicalMobiusHead k j := by
  change hilbertSequenceLinear (signedMobiusAverage s a) j = _
  unfold signedMobiusAverage
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change (∑ k ∈ s, a k * hilbertSequence (canonicalMobiusHilbert k) j) = _
  simp_rw [canonicalMobiusHilbert_sequence]

theorem signedMobiusAverage_exact (s : Finset ℕ) (a : ℕ → ℝ) (N : ℕ)
    (hsum : ∑ k ∈ s, a k = 1) (hindex : ∀ k ∈ s, N ≤ k)
    (j : ℕ) (hj : 0 < j) (hjN : j ≤ N) :
    hilbertSequence (signedMobiusAverage s a) j = 1 := by
  rw [signedMobiusAverage_sequence]
  calc
    _ = ∑ k ∈ s, a k := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [canonicalMobiusHead_exact k j hj (hjN.trans (hindex k hk)), mul_one]
    _ = 1 := hsum

/-- The physical tail shift is linear; no tail truncation is performed. -/
def hilbertTailShiftLinear (N : ℕ) : ThresholdHilbert →ₗ[ℝ] ThresholdHilbert where
  toFun f := hilbertTailShift f N
  map_add' f g := by ext n; rfl
  map_smul' a f := by ext n; rfl

theorem hilbertTailShift_inner_weighted (f g : ThresholdHilbert) (N : ℕ) :
    inner ℝ (hilbertTailShift f N) (hilbertTailShift g N) =
      ∑' n : ℕ, positiveWeight (n + N + 1) *
        (hilbertSequence f (n + N + 1) * hilbertSequence g (n + N + 1)) := by
  rw [lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  rw [RCLike.inner_apply']
  change f (n + N) * g (n + N) = _
  rw [positiveWeight_succ, hilbertSequence_succ, hilbertSequence_succ,
    div_mul_div_comm, ← pow_two, Real.sq_sqrt (by unfold paretoWeight; positivity)]
  have hw : paretoWeight (n + N) ≠ 0 := by unfold paretoWeight; positivity
  field_simp

/-- An exact head has known energy, leaving precisely the complete tail norm. -/
theorem exact_head_norm_sq_split (f : ThresholdHilbert) (N : ℕ)
    (hhead : ∀ j, 0 < j → j ≤ N → hilbertSequence f j = 1) :
    ‖f‖ ^ 2 = (N : ℝ) / ((N : ℝ) + 1) + ‖hilbertTailShift f N‖ ^ 2 := by
  rw [hilbert_norm_weighted_sq,
    ← (hilbertSequence_square_summable f).sum_add_tsum_nat_add (N + 1)]
  congr 1
  · calc
      _ = ∑ k ∈ Finset.range (N + 1), positiveWeight k := by
        apply Finset.sum_congr rfl
        intro k hk
        by_cases hk0 : k = 0
        · simp [hk0, positiveWeight]
        · rw [hhead k (by omega) (by have := Finset.mem_range.mp hk; omega)]
          ring
      _ = _ := by
        rw [positiveWeight_sum_range (N + 1) (Nat.succ_pos _)]
        push_cast
        field_simp
        ring
  · rw [hilbert_norm_sq]
    apply tsum_congr
    intro k
    change positiveWeight (k + (N + 1)) *
      hilbertSequence f (k + (N + 1)) ^ 2 = (f (k + N)) ^ 2
    simpa only [Nat.add_assoc] using hilbertSequence_weighted_square f (k + N)

/-- Covariance at cutoff N, including every physical coordinate larger than N. -/
def canonicalMobiusTailCovariance (N k l : ℕ) : ℝ :=
  inner ℝ (hilbertTailShift (canonicalMobiusHilbert k) N)
    (hilbertTailShift (canonicalMobiusHilbert l) N)

theorem canonicalMobiusTailCovariance_weighted (N k l : ℕ) :
    canonicalMobiusTailCovariance N k l =
      ∑' j : ℕ, positiveWeight (j + N + 1) *
        (canonicalMobiusHead k (j + N + 1) * canonicalMobiusHead l (j + N + 1)) := by
  unfold canonicalMobiusTailCovariance
  rw [hilbertTailShift_inner_weighted]
  simp_rw [canonicalMobiusHilbert_sequence]

theorem canonicalMobiusTailCovariance_symm (N k l : ℕ) :
    canonicalMobiusTailCovariance N k l = canonicalMobiusTailCovariance N l k :=
  real_inner_comm _ _

/-- Exact signed Gram expansion, retaining every cross term. -/
theorem signedMobiusAverage_tail_energy (s : Finset ℕ) (a : ℕ → ℝ) (N : ℕ) :
    ‖hilbertTailShift (signedMobiusAverage s a) N‖ ^ 2 =
      ∑ k ∈ s, ∑ l ∈ s, a k * a l * canonicalMobiusTailCovariance N k l := by
  have he : hilbertTailShift (signedMobiusAverage s a) N =
      ∑ k ∈ s, a k • hilbertTailShift (canonicalMobiusHilbert k) N := by
    change hilbertTailShiftLinear N (∑ k ∈ s, a k • canonicalMobiusHilbert k) = _
    simp only [map_sum, map_smul]
    rfl
  rw [he, ← real_inner_self_eq_norm_sq]
  simp_rw [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
  simp only [mul_assoc, canonicalMobiusTailCovariance]

theorem canonicalMobiusTailCovariance_nonneg (s : Finset ℕ) (a : ℕ → ℝ) (N : ℕ) :
    0 ≤ ∑ k ∈ s, ∑ l ∈ s, a k * a l * canonicalMobiusTailCovariance N k l := by
  rw [← signedMobiusAverage_tail_energy]
  exact sq_nonneg _

theorem signedMobiusAverage_norm_sq (s : Finset ℕ) (a : ℕ → ℝ) (N : ℕ)
    (hsum : ∑ k ∈ s, a k = 1) (hindex : ∀ k ∈ s, N ≤ k) :
    ‖signedMobiusAverage s a‖ ^ 2 = (N : ℝ) / ((N : ℝ) + 1) +
      ∑ k ∈ s, ∑ l ∈ s, a k * a l * canonicalMobiusTailCovariance N k l := by
  rw [exact_head_norm_sq_split _ N (signedMobiusAverage_exact s a N hsum hindex),
    signedMobiusAverage_tail_energy]

/-- The manuscript's dyadic average, with the N=0 value harmlessly defined as zero. -/
def dyadicMobiusAverage (N : ℕ) : ThresholdHilbert :=
  signedMobiusAverage (Finset.Ico N (2 * N)) (fun _ => 1 / (N : ℝ))

theorem dyadicMobiusAverage_weights (N : ℕ) (hN : 0 < N) :
    ∑ _k ∈ Finset.Ico N (2 * N), (1 / (N : ℝ)) = 1 := by
  simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
  have hsub : 2 * N - N = N := by omega
  rw [hsub]
  have hne : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  field_simp

theorem dyadicMobiusAverage_exact (N j : ℕ) (hN : 0 < N)
    (hj : 0 < j) (hjN : j ≤ N) : hilbertSequence (dyadicMobiusAverage N) j = 1 := by
  apply signedMobiusAverage_exact _ _ N (dyadicMobiusAverage_weights N hN) _ j hj hjN
  intro k hk
  exact (Finset.mem_Ico.mp hk).1

namespace CoefficientStabilization

theorem signedMobiusAverage_mem_finiteSpace (s : Finset ℕ) (a : ℕ → ℝ) (M : ℕ)
    (hupper : ∀ k ∈ s, k ≤ M) : signedMobiusAverage s a ∈ finiteSpace M := by
  unfold signedMobiusAverage
  apply (finiteSpace M).sum_mem
  intro k hk
  apply (finiteSpace M).smul_mem
  exact RiemannResearch.Analysis.ExhaustiveWalk.walkSpan_mono residueAtom id
    (hupper k hk) (canonicalMobiusHilbert_mem_finiteSpace k)

theorem signedMobiusAverage_mem_closedSpace (s : Finset ℕ) (a : ℕ → ℝ) :
    signedMobiusAverage s a ∈ closedSpace := by
  unfold signedMobiusAverage
  apply closedSpace.sum_mem
  intro k hk
  exact closedSpace.smul_mem (a k) (canonicalMobiusHilbert_mem_closedSpace k)

/-- Conditional research reduction: only a bounded cofinal subsequence of the
actual signed covariance energies is needed. The bound is the open provider. -/
theorem riemannHypothesis_of_frequently_bounded_signed_covariance
    (s : ℕ → Finset ℕ) (a : ℕ → ℕ → ℝ)
    (hsum : ∀ N, ∑ k ∈ s N, a N k = 1)
    (hindex : ∀ N k, k ∈ s N → N ≤ k)
    (C : ℝ)
    (hbounded : ∃ᶠ N in atTop,
      (∑ k ∈ s N, ∑ l ∈ s N, a N k * a N l * canonicalMobiusTailCovariance N k l) ≤ C) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_frequently_bounded_exact_head_energy
    (fun N => signedMobiusAverage (s N) (a N))
    (fun N => signedMobiusAverage_mem_closedSpace (s N) (a N))
    (fun N => signedMobiusAverage_exact (s N) (a N) N (hsum N) (hindex N)) (1 + C)
  apply hbounded.mono
  intro N hN
  rw [signedMobiusAverage_norm_sq (s N) (a N) N (hsum N) (hindex N)]
  have hm : (N : ℝ) / ((N : ℝ) + 1) ≤ 1 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) + 1)).2
    linarith
  linarith

end CoefficientStabilization
end RiemannResearch.RH.Pareto
