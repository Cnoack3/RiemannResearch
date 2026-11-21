import RiemannResearch.RH.ParetoParityAdjointCriterion
import RiemannResearch.RH.ParetoFiniteErrorObstruction
import RiemannResearch.RH.ParetoCoordinateBounds
import RiemannResearch.RH.ParetoMobiusHeadInterpolation
import RiemannResearch.RH.ExactHeadGcdAtoms

/-!
# Finite GCD lifts of the dyadic adjoint of parity

The divisor-class expansion identifies every prescribed coordinate of the
adjoint image. A uniform bound on the complete errors of finite legal lifts
along increasing heads is equivalent to attainment of the upper endpoint.
The tail-pairing identity gives the obstruction for any choice of lifts.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto.PrimePowerSchur
open CoefficientStabilization

/-- Every finite divisor dictionary loses at least its common-multiple site. -/
theorem parityAdjointPacket_finite_crt_gap (s : Finset ℕ) (c : ℕ → ℝ)
    {L : ℕ} (hL : 0 < L) (hdiv : ∀ d ∈ s, d ∣ L) :
    (L:ℝ) / (((L:ℝ)+1)*(2*(L:ℝ)+1)^2) ≤
      ‖parityAdjointPacket - ∑ d ∈ s, c d • ramanujanPacketHilbert d‖^2 := by
  have hz : hilbertSequence (∑ d ∈ s, c d • ramanujanPacketHilbert d) L = 0 := by
    rw [← anchoredEvaluationCLM_apply, map_sum]
    apply Finset.sum_eq_zero
    intro d hd
    rw [map_smul, smul_eq_mul, anchoredEvaluationCLM_apply, hilbertSequence_ramanujanPacketHilbert,
      ramanujanPacket_eq_zero_of_dvd (hdiv d hd), mul_zero]
  have hb := hilbertSequence_weighted_sq_le
    (parityAdjointPacket - ∑ d ∈ s, c d • ramanujanPacketHilbert d) L
  rw [hilbertSequence_sub,Pi.sub_apply,hz,sub_zero,parityAdjointPacket_coordinate] at hb
  apply le_trans (le_of_eq ?_) hb
  unfold positiveWeight
  have hn : (L:ℝ) ≠ 0 := by positivity
  field_simp

/-- All positive-site jumps, including the first, have one rational formula. -/
theorem parityAdjointPacket_jump (k : ℕ) (hk : 0 < k) :
    hilbertSequence parityAdjointPacket k - hilbertSequence parityAdjointPacket (k - 1) =
      1 / ((2 * (k : ℝ) - 1) * (2 * (k : ℝ) + 1)) := by
  cases k with
  | zero => omega
  | succ n =>
    rw [parityAdjointPacket_coordinate, parityAdjointPacket_coordinate]
    simp only [Nat.succ_sub_one, Nat.cast_succ]
    rw [show 2 * ((n : ℝ) + 1) - 1 = 2 * (n : ℝ) + 1 by ring]
    field_simp
    ring

/-- On a compatible head, cumulative exact GCD classes reconstruct the adjoint profile. -/
theorem parityAdjointPacket_gcd_head (P n : ℕ) (hP : P ≠ 0)
    (hdiv : ∀ k, 0 < k → k ≤ n → k ∣ P) :
    RiemannResearch.RH.ExactHeadGcdAtoms.synthesis P P.divisors
      (fun d => 1 / ((2 * (d : ℝ) - 1) * (2 * (d : ℝ) + 1))) n =
      hilbertSequence parityAdjointPacket n := by
  let a (d : ℕ) : ℝ := 1 / ((2 * (d : ℝ) - 1) * (2 * (d : ℝ) + 1))
  change RiemannResearch.RH.ExactHeadGcdAtoms.synthesis P P.divisors a n = _
  induction n with
  | zero => simp [hilbertSequence_zero]
  | succ n ih =>
    have hd := hdiv (n + 1) (Nat.succ_pos _) le_rfl
    have hi := ih (fun k hk hkn => hdiv k hk (hkn.trans (Nat.le_succ n)))
    have hs := RiemannResearch.RH.ExactHeadGcdAtoms.synthesis_divisor_jump P P.divisors a
      (n + 1) (Nat.mem_divisors.mpr ⟨hd, hP⟩) (Nat.succ_pos _) hd
    have hj := parityAdjointPacket_jump (n + 1) (Nat.succ_pos _)
    change RiemannResearch.RH.ExactHeadGcdAtoms.synthesis P P.divisors a (n + 1) -
      RiemannResearch.RH.ExactHeadGcdAtoms.synthesis P P.divisors a n = a (n + 1) at hs
    change hilbertSequence parityAdjointPacket (n + 1) -
      hilbertSequence parityAdjointPacket n = a (n + 1) at hj
    linarith only [hi, hs, hj]

/-- Divisor inversion produces a finite legal fit to every prescribed head of the adjoint. -/
theorem parityAdjointPacket_mobius_head (N : ℕ) :
    mobiusHeadInterpolation N parityAdjointPacket ∈ finiteSpace N ∧
    ∀ k ≤ N, hilbertSequence (mobiusHeadInterpolation N parityAdjointPacket) k =
      (k:ℝ)/(2*(k:ℝ)+1) :=
  ⟨mobiusHeadInterpolation_mem _ _, fun k hk =>
    (mobiusHeadInterpolation_exact _ _ _ hk).trans (parityAdjointPacket_coordinate k)⟩

/-- An exact finite head leaves the whole signed pairing in the physical tail. -/
theorem parityAdjointPacket_exactHead_pairing (N : ℕ) (v : ThresholdHilbert) (hv : v ∈ closedSpace)
    (hhead : compactHead N v = compactHead N parityAdjointPacket) :
    inner ℝ limitResidual parityAdjointPacket =
      inner ℝ (limitResidual - compactHead N limitResidual) (parityAdjointPacket-v) := by
  have ho := Submodule.inner_right_of_mem_orthogonal hv limitResidual_mem_orthogonal
  rw [real_inner_comm] at ho
  rw [inner_sub_left,compactHead_symmetric,compactHead_sub,hhead,sub_self,inner_zero_right,
    sub_zero,inner_sub_right,ho,sub_zero]

theorem parityAdjointPacket_exactHead_obstruction (N : ℕ) (v : ThresholdHilbert)
    (hv : v ∈ closedSpace)
    (hhead : compactHead N v = compactHead N parityAdjointPacket) :
    (limitEnergy/6)^2 ≤ hilbertTailEnergy limitResidual (N+1) * ‖parityAdjointPacket - v‖ ^ 2 := by
  have hb := parityAdjointPacket_residual_bounds.1
  rw [parityAdjointPacket_exactHead_pairing N v hv hhead] at hb
  have hh := hb.trans ((le_abs_self _).trans (abs_real_inner_le_norm _ _))
  have hE : 0 ≤ limitEnergy := sq_nonneg _
  have hs := (sq_le_sq₀ (show 0 ≤ limitEnergy / 6 by positivity)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hh
  simpa only [mul_pow,compactHead_complete_tail_norm_sq,hilbertTailEnergy] using hs

/-- Bounded full errors along arbitrarily long exact heads suffice for attainment. -/
theorem normalizedParityCapture_eq_upper_of_bounded_adjoint_heads
    (v : ℕ → ThresholdHilbert) (hlegal : ∀ n, v n ∈ closedSpace)
    (hhead : ∀ n, compactHead n (v n) = compactHead n parityAdjointPacket)
    (C : ℝ) (hbound : ∃ᶠ n : ℕ in atTop, ‖parityAdjointPacket - v n‖ ^ 2 ≤ C) :
    normalizedParityCapture = Real.sqrt (1/Real.log 2-1) := by
  apply normalizedParityCapture_eq_upper_iff.mpr
  by_contra hne
  have hp : 0 < limitEnergy := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hne)
  have ht : Tendsto (fun n : ℕ => hilbertTailEnergy limitResidual (n+1) * C) atTop (𝓝 0) := by
    simpa using ((hilbertTailEnergy_tendsto_zero limitResidual).comp
      (tendsto_add_atTop_nat 1)).mul_const C
  obtain ⟨n,hn,hlt⟩ := (hbound.and_eventually
    (ht.eventually_lt_const (sq_pos_of_pos (show 0 < limitEnergy / 6 by positivity)))).exists
  have hgap := parityAdjointPacket_exactHead_obstruction n (v n) (hlegal n) (hhead n)
  have htail := mul_le_mul_of_nonneg_left hn (hilbertTailEnergy_nonneg limitResidual (n+1))
  exact (not_lt_of_ge (hgap.trans htail)) hlt

/-- Finite algebraic lifts with a uniform complete error are exactly what the endpoint requires. -/
theorem normalizedParityCapture_eq_upper_iff_bounded_finite_adjoint_heads :
    normalizedParityCapture = Real.sqrt (1/Real.log 2-1) ↔
      ∃ C : ℝ, ∀ n : ℕ, ∃ m : ℕ, ∃ v : ThresholdHilbert,
        v ∈ finiteSpace m ∧ compactHead n v = compactHead n parityAdjointPacket ∧
        ‖parityAdjointPacket - v‖ ^ 2 ≤ C := by
  constructor
  · intro he
    have hg := normalizedParityCapture_eq_upper_iff_adjointParity_mem.mp he
    refine ⟨1, fun n => ?_⟩
    obtain ⟨m, _, x, hx, hcoord, herr⟩ :=
      exists_legal_exact_head_near parityAdjointPacket hg n 1 zero_lt_one
    refine ⟨m,x,hx,?_,by simpa only [norm_sub_rev parityAdjointPacket x] using herr.le⟩
    apply hilbertSequence_injective
    funext k
    rw [compactHead_sequence,compactHead_sequence]
    split_ifs with hk
    · rcases Nat.eq_zero_or_pos k with hz | hp
      · simp [hz]
      · exact hcoord k hp hk
    · rfl
  · rintro ⟨C,h⟩
    choose m v hv hh hb using h
    apply normalizedParityCapture_eq_upper_of_bounded_adjoint_heads v _ hh C
      (Eventually.of_forall hb).frequently
    intro n
    exact Submodule.le_topologicalClosure _
      (RiemannResearch.Analysis.ExhaustiveWalk.walkSpan_le residueAtom id (m n) (hv n))

end RiemannResearch.RH.Pareto.PrimePowerSchur
