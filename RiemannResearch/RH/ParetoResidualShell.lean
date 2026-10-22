import RiemannResearch.RH.CanonicalMobiusSignedAverages

/-!
# Exact residual shells and signed arithmetic observations

Source: user-provided `RH_Research_Agenda_2026-09-24(1).md`, Priority 3,
for the dyadic bookkeeping target. The bilinear refinements below are direct
Hilbert-space and finite-sum arguments. No claim of novelty is made.

All tail inner products retain the complete infinite Pareto tail. Arithmetic
orthogonality is used for the actual projection residual. The resulting
observation inequalities give lower constraints on the residual tail; they do
not supply the cofinal normalized-tail upper bound needed for RH.
-/

noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.RH.Pareto

/-- The physical shell `N < k ≤ N + M`, expressed in weighted l2 coordinates. -/
def hilbertShellPairing (f g : ThresholdHilbert) (N M : ℕ) : ℝ :=
  ∑ n ∈ Finset.range M, f (n + N) * g (n + N)

theorem hilbert_head_tail_pairing (f g : ThresholdHilbert) (N : ℕ) :
    hilbertShellPairing f g 0 N +
      inner ℝ (hilbertTailShift f N) (hilbertTailShift g N) = inner ℝ f g := by
  have h := (hilbert_coordinate_mul_summable f g).sum_add_tsum_nat_add N
  simpa only [hilbertShellPairing, Nat.add_zero, lp.inner_eq_tsum,
    RCLike.inner_apply, conj_trivial, mul_comm, hilbertTailShift] using h

theorem hilbertTailShift_add (f : ThresholdHilbert) (N M : ℕ) :
    hilbertTailShift (hilbertTailShift f N) M = hilbertTailShift f (N + M) := by
  apply Subtype.ext
  funext n
  change f ((n + M) + N) = f (n + (N + M))
  exact congrArg (fun k : ℕ => f k) (by omega)

theorem hilbert_tail_shell_pairing (f g : ThresholdHilbert) (N M : ℕ) :
    hilbertShellPairing f g N M +
      inner ℝ (hilbertTailShift f (N + M)) (hilbertTailShift g (N + M)) =
      inner ℝ (hilbertTailShift f N) (hilbertTailShift g N) := by
  have h := hilbert_head_tail_pairing (hilbertTailShift f N) (hilbertTailShift g N) M
  rw [hilbertTailShift_add, hilbertTailShift_add] at h
  exact h

theorem hilbertShellPairing_weighted (f g : ThresholdHilbert) (N M : ℕ) :
    hilbertShellPairing f g N M =
      ∑ n ∈ Finset.range M, positiveWeight (n + N + 1) *
        (hilbertSequence f (n + N + 1) * hilbertSequence g (n + N + 1)) := by
  unfold hilbertShellPairing
  apply Finset.sum_congr rfl
  intro n hn
  rw [positiveWeight_succ, hilbertSequence_succ, hilbertSequence_succ,
    div_mul_div_comm, ← pow_two, Real.sq_sqrt (by unfold paretoWeight; positivity)]
  have hw : paretoWeight (n + N) ≠ 0 := by unfold paretoWeight; positivity
  field_simp

theorem hilbertShellPairing_self_nonneg (f : ThresholdHilbert) (N M : ℕ) :
    0 ≤ hilbertShellPairing f f N M := by
  apply Finset.sum_nonneg
  intro n hn
  exact mul_self_nonneg _

theorem exactHead_coordinate_eq_one {f : ThresholdHilbert} {N : ℕ}
    (hhead : ∀ k, 0 < k → k ≤ N → hilbertSequence f k = 1)
    (n : ℕ) (hn : n < N) : f n = hilbertOne n := by
  have hs := hhead (n + 1) (by omega) (by omega)
  have hone : hilbertSequence hilbertOne (n + 1) = 1 := by
    rw [hilbertOne_sequence]
    simp [zeroAnchor]
  have hsame : hilbertSequence hilbertOne (n + 1) = hilbertSequence f (n + 1) :=
    hone.trans hs.symm
  have hw : Real.sqrt (paretoWeight n) ≠ 0 := by
    apply ne_of_gt
    apply Real.sqrt_pos.mpr
    unfold paretoWeight
    positivity
  exact ((div_left_inj' hw).mp hsame).symm

namespace CoefficientStabilization

/-- Exact dyadic bookkeeping for the actual complete residual tail. -/
theorem residualTailEnergy_dyadic (N : ℕ) :
    ((2 * N : ℕ) : ℝ) * residualTailEnergy (2 * N) =
      2 * (N : ℝ) * residualTailEnergy N -
        2 * (N : ℝ) * hilbertShellPairing limitResidual limitResidual N N := by
  have h := hilbert_tail_shell_pairing limitResidual limitResidual N N
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  change hilbertShellPairing limitResidual limitResidual N N +
    residualTailEnergy (N + N) = residualTailEnergy N at h
  rw [← two_mul N] at h
  push_cast
  rw [← h]
  ring

/-- Arithmetic head observations equal the negative complete tail observations. -/
theorem residual_legal_head_tail_observation {f : ThresholdHilbert}
    (hf : f ∈ closedSpace) (N : ℕ) :
    hilbertShellPairing limitResidual f 0 N =
      -inner ℝ (hilbertTailShift limitResidual N) (hilbertTailShift f N) := by
  have h := hilbert_head_tail_pairing limitResidual f N
  have ho : inner ℝ limitResidual f = 0 := by
    rw [real_inner_comm]
    exact (closedSpace.mem_orthogonal _).mp limitResidual_mem_orthogonal _ hf
  rw [ho] at h
  linarith

/-- Finite signed observations impose a lower constraint on the tail energy. -/
theorem residual_legal_head_observation_sq_le {f : ThresholdHilbert}
    (hf : f ∈ closedSpace) (N : ℕ) :
    (hilbertShellPairing limitResidual f 0 N)^2 ≤
      residualTailEnergy N * ‖hilbertTailShift f N‖^2 := by
  rw [residual_legal_head_tail_observation hf, neg_sq]
  have h := abs_real_inner_le_norm (hilbertTailShift limitResidual N)
    (hilbertTailShift f N)
  have hs := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr h
  simpa only [sq_abs, mul_pow, residualTailEnergy] using hs

/-- Consecutive legal exact heads force an exact signed shell/tail cancellation. -/
theorem residual_exactHead_shell_pairing {f g : ThresholdHilbert}
    (hf : f ∈ closedSpace) (hg : g ∈ closedSpace) (N M : ℕ)
    (hfhead : ∀ k, 0 < k → k ≤ N → hilbertSequence f k = 1)
    (hghead : ∀ k, 0 < k → k ≤ N + M → hilbertSequence g k = 1) :
    hilbertShellPairing limitResidual (hilbertOne - f) N M =
      -inner ℝ (hilbertTailShift limitResidual (N + M))
        (hilbertTailShift (g - f) (N + M)) := by
  have hzero : ∀ n < N, (g - f) n = 0 := by
    intro n hn
    change g n - f n = 0
    rw [exactHead_coordinate_eq_one hghead n (by omega),
      exactHead_coordinate_eq_one hfhead n hn, sub_self]
  have ho : inner ℝ limitResidual (g - f) = 0 := by
    rw [real_inner_comm]
    exact (closedSpace.mem_orthogonal _).mp limitResidual_mem_orthogonal _
      (closedSpace.sub_mem hg hf)
  have h := hilbert_tail_shell_pairing limitResidual (g - f) N M
  rw [hilbertTailShift_inner limitResidual (g - f) N hzero, ho] at h
  have hs : hilbertShellPairing limitResidual (g - f) N M =
      hilbertShellPairing limitResidual (hilbertOne - f) N M := by
    apply Finset.sum_congr rfl
    intro n hn
    change limitResidual (n + N) * (g (n + N) - f (n + N)) =
      limitResidual (n + N) * (hilbertOne (n + N) - f (n + N))
    rw [exactHead_coordinate_eq_one hghead (n + N)
      (by have := Finset.mem_range.mp hn; omega)]
  rw [hs] at h
  linarith

/-- The shell observation is controlled by the entire later correction tail. -/
theorem residual_exactHead_shell_observation_sq_le {f g : ThresholdHilbert}
    (hf : f ∈ closedSpace) (hg : g ∈ closedSpace) (N M : ℕ)
    (hfhead : ∀ k, 0 < k → k ≤ N → hilbertSequence f k = 1)
    (hghead : ∀ k, 0 < k → k ≤ N + M → hilbertSequence g k = 1) :
    (hilbertShellPairing limitResidual (hilbertOne - f) N M)^2 ≤
      residualTailEnergy (N + M) * ‖hilbertTailShift (g - f) (N + M)‖^2 := by
  rw [residual_exactHead_shell_pairing hf hg N M hfhead hghead, neg_sq]
  have h := abs_real_inner_le_norm (hilbertTailShift limitResidual (N + M))
    (hilbertTailShift (g - f) (N + M))
  have hs := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr h
  simpa only [sq_abs, mul_pow, residualTailEnergy] using hs

/-- Concrete arithmetic specialization: the original exact-head Möbius family. -/
theorem residual_canonicalMobius_shell_pairing (N M : ℕ) :
    hilbertShellPairing limitResidual (hilbertOne - canonicalMobiusHilbert N) N M =
      -inner ℝ (hilbertTailShift limitResidual (N + M))
        (hilbertTailShift (canonicalMobiusHilbert (N + M) - canonicalMobiusHilbert N)
          (N + M)) :=
  residual_exactHead_shell_pairing (canonicalMobiusHilbert_mem_closedSpace N)
    (canonicalMobiusHilbert_mem_closedSpace (N + M)) N M
    (canonicalMobiusHilbert_exact N) (canonicalMobiusHilbert_exact (N + M))

end CoefficientStabilization
end RiemannResearch.RH.Pareto
