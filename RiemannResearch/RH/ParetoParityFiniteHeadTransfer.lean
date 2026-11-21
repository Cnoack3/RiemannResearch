import RiemannResearch.RH.ParetoParityAdjointHeads
import RiemannResearch.RH.TailCapacityDilationCorrection

/-!
# Finite dilation transfer from constant heads to adjoint parity heads

The jumps of the coordinate profile of the adjoint parity packet determine a
finite linear combination of unscaled physical dilations. Applying it to any
finite legal vector agreeing with the constant on the first sites gives a
finite legal vector agreeing with the adjoint packet on those same sites.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.PrimePowerSchur
open CoefficientStabilization
open RiemannResearch.Analysis.ExhaustiveWalk

private def headProfile (n : ℕ) : ℝ := (n : ℝ) / (2 * (n : ℝ) + 1)

private def headJump (j : ℕ) : ℝ := headProfile (j + 1) - headProfile j

private theorem headJump_nonneg (j : ℕ) : 0 ≤ headJump j := by
  have hj := parityAdjointPacket_jump (j+1) (by omega)
  simp only [parityAdjointPacket_coordinate, Nat.add_sub_cancel] at hj
  change 0 ≤ headProfile (j+1) - headProfile j
  unfold headProfile
  rw [hj]
  push_cast
  have h : 0 < 2 * ((j:ℝ) + 1) - 1 := by linarith [Nat.cast_nonneg (α:=ℝ) j]
  positivity

private theorem headProfile_le_half (n : ℕ) : headProfile n ≤ 1/2 := by
  unfold headProfile
  apply (div_le_iff₀ (by positivity)).mpr
  linarith

private theorem headJump_sum (N : ℕ) :
    ∑ j ∈ Finset.range N, headJump j = headProfile N := by
  induction N with
  | zero => simp [headProfile]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, headJump]
    ring

/-- Apply the first N jumps of the adjoint packet as physical dilations of u. -/
def parityHeadTransfer (N : ℕ) (u : ThresholdHilbert) : ThresholdHilbert :=
  ∑ j ∈ Finset.range N, headJump j • unscaledResidueDilation (j+1) (by omega) u

/-- The transfer stays in an explicitly bounded finite legal dictionary. -/
theorem parityHeadTransfer_mem (N m : ℕ) (u : ThresholdHilbert) (hu : u ∈ finiteSpace m) :
    parityHeadTransfer N u ∈ finiteSpace (N * (m+1)) := by
  apply Submodule.sum_mem
  intro j hj
  apply Submodule.smul_mem
  have hjN := Finset.mem_range.mp hj
  have hmul := Nat.mul_le_mul_right (m+1) (show j+1 ≤ N by omega)
  by_cases hj0 : j = 0
  · subst j
    have hid : unscaledResidueDilation 1 (by decide) u = u := by
      apply hilbertSequence_injective
      funext k
      simp only [unscaledResidueDilation_sequence, Nat.div_one]
    rw [hid]
    simp only [zero_add, one_mul] at hmul
    exact walkSpan_mono residueAtom id ((Nat.le_succ m).trans hmul) hu
  · exact walkSpan_mono residueAtom id (show (j+1)*(m+1)-1 ≤ N*(m+1) by omega)
      (unscaledResidueDilation_mem_finiteSpace m (j+1) (by omega) u hu)

private theorem headDilation_contraction (d : ℕ) (hd : 0 < d) (u : ThresholdHilbert) :
    ‖unscaledResidueDilation d hd u‖ ≤ ‖u‖ := by
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hsq : ‖unscaledResidueDilation d hd u‖ ^ 2 ≤ ‖u‖ ^ 2 := by
    rw [unscaledResidueDilation_norm_sq]
    apply (div_le_iff₀ (by positivity)).mpr
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hd1 (sq_nonneg ‖u‖)
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- The operator norm is bounded by the finite jump sum, at most one half. -/
theorem parityHeadTransfer_norm_le (N : ℕ) (u : ThresholdHilbert) :
    ‖parityHeadTransfer N u‖ ≤ (1/2:ℝ) * ‖u‖ := by
  calc
    _ ≤ ∑ j ∈ Finset.range N, ‖headJump j • unscaledResidueDilation (j+1) (by omega) u‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range N, headJump j * ‖u‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (headJump_nonneg j)]
      exact mul_le_mul_of_nonneg_left (headDilation_contraction _ _ _) (headJump_nonneg j)
    _ ≤ _ := by
      rw [← Finset.sum_mul, headJump_sum]
      exact mul_le_mul_of_nonneg_right (headProfile_le_half _) (norm_nonneg _)

private theorem parityHeadTransfer_sub (N : ℕ) (u v : ThresholdHilbert) :
    parityHeadTransfer N (u-v) = parityHeadTransfer N u - parityHeadTransfer N v := by
  simp only [parityHeadTransfer, map_sub, smul_sub, Finset.sum_sub_distrib]

private theorem parityHeadTransfer_one_coordinate (N k : ℕ) :
    hilbertSequence (parityHeadTransfer N hilbertOne) k = headProfile (min k N) := by
  induction N with
  | zero =>
    simp [parityHeadTransfer, headProfile, ← anchoredEvaluationCLM_apply]
  | succ n ih =>
    have hstep : parityHeadTransfer (n+1) hilbertOne = parityHeadTransfer n hilbertOne +
        headJump n • unscaledResidueDilation (n+1) (by omega) hilbertOne := by
      simp only [parityHeadTransfer, Finset.sum_range_succ]
    rw [hstep, hilbertSequence_add, Pi.add_apply, ih, hilbertSequence_smul,
      Pi.smul_apply, smul_eq_mul, unscaledResidueDilation_sequence, hilbertOne_sequence]
    change headProfile (min k n) + headJump n * (if k / (n+1) = 0 then 0 else 1) =
      headProfile (min k (n+1))
    by_cases h : n+1 ≤ k
    · rw [if_neg (Nat.ne_of_gt (Nat.div_pos h (by omega))), min_eq_right (by omega : n ≤ k),
        min_eq_right h, mul_one, headJump]
      ring
    · rw [Nat.div_eq_of_lt (by omega : k < n+1), if_pos rfl, mul_zero, add_zero,
        min_eq_left (by omega : k ≤ n), min_eq_left (by omega : k ≤ n+1)]

/-- On the constant, the truncated transfer is exactly the profile clipped at N. -/
theorem parityHeadTransfer_one_sequence (N k : ℕ) :
    hilbertSequence (parityHeadTransfer N hilbertOne) k =
      ((min k N : ℕ):ℝ) / (2 * ((min k N : ℕ):ℝ) + 1) :=
  parityHeadTransfer_one_coordinate N k

/-- Agreement with the constant through N suffices for exact adjoint parity head agreement. -/
theorem parityHeadTransfer_exact (N : ℕ) (u : ThresholdHilbert)
    (hu : ∀ k ≤ N, hilbertSequence u k = hilbertSequence hilbertOne k) :
    compactHead N (parityHeadTransfer N u) = compactHead N parityAdjointPacket := by
  apply hilbertSequence_injective
  funext k
  rw [compactHead_sequence, compactHead_sequence]
  split_ifs with hk
  · have he : hilbertSequence (parityHeadTransfer N u) k =
        hilbertSequence (parityHeadTransfer N hilbertOne) k := by
      rw [← anchoredEvaluationCLM_apply k (parityHeadTransfer N u),
        ← anchoredEvaluationCLM_apply k (parityHeadTransfer N hilbertOne)]
      simp only [parityHeadTransfer, map_sum, map_smul, smul_eq_mul]
      simp only [anchoredEvaluationCLM_apply, unscaledResidueDilation_sequence]
      apply Finset.sum_congr rfl
      intro j _
      rw [hu (k / (j+1)) ((Nat.div_le_self _ _).trans hk)]
    rw [he, parityHeadTransfer_one_coordinate, min_eq_left hk, parityAdjointPacket_coordinate]
    rfl
  · rfl

private theorem parityHeadTransfer_truncation_le (N : ℕ) :
    ‖parityAdjointPacket - parityHeadTransfer N hilbertOne‖ ≤ 1 / (2 * (2*(N:ℝ)+1)) := by
  let c : ℝ := 1 / (2 * (2*(N:ℝ)+1))
  have hc : 0 ≤ c := by dsimp [c]; positivity
  let x := parityAdjointPacket - parityHeadTransfer N hilbertOne
  have hcoord (k : ℕ) :
      (hilbertSequence x k)^2 ≤ (hilbertSequence (c • hilbertOne) k)^2 := by
    change (hilbertSequence (parityAdjointPacket - parityHeadTransfer N hilbertOne) k)^2 ≤ _
    rw [hilbertSequence_sub, Pi.sub_apply, parityAdjointPacket_coordinate,
      parityHeadTransfer_one_coordinate, hilbertSequence_smul, Pi.smul_apply, smul_eq_mul,
      hilbertOne_sequence]
    by_cases hk : k ≤ N
    · rw [min_eq_left hk]
      change (headProfile k - headProfile k)^2 ≤ _
      rw [sub_self, zero_pow (by decide : 2 ≠ 0)]
      exact sq_nonneg _
    · have hkN : N ≤ k := by omega
      rw [min_eq_right hkN]
      change (headProfile k - headProfile N)^2 ≤ (c * (if k = 0 then 0 else 1))^2
      rw [if_neg (by omega : k ≠ 0), mul_one]
      have hmono : headProfile N ≤ headProfile k := by
        unfold headProfile
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        nlinarith only [show (N:ℝ) ≤ (k:ℝ) by exact_mod_cast hkN]
      have hc' : c = 1/2 - headProfile N := by
        dsimp [c, headProfile]
        field_simp
        ring
      apply (sq_le_sq₀ (sub_nonneg.mpr hmono) hc).mpr
      rw [hc']
      exact sub_le_sub_right (headProfile_le_half k) _
  have hsq : ‖x‖^2 ≤ ‖c • hilbertOne‖^2 := by
    rw [hilbert_norm_weighted_sq, hilbert_norm_weighted_sq]
    apply Summable.tsum_le_tsum _ (hilbertSequence_square_summable x)
      (hilbertSequence_square_summable (c • hilbertOne))
    intro k
    exact mul_le_mul_of_nonneg_left (hcoord k) (positiveWeight_nonneg k)
  have hnorm := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
  have ho : ‖hilbertOne‖ = 1 := by nlinarith [hilbertOne_norm_sq, norm_nonneg hilbertOne]
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc, ho, mul_one, x, c] using hnorm

/-- Exact signed decomposition into cutoff error and transferred input error. -/
theorem parityHeadTransfer_error_eq (N : ℕ) (u : ThresholdHilbert) :
    parityAdjointPacket - parityHeadTransfer N u =
      (parityAdjointPacket - parityHeadTransfer N hilbertOne) +
        parityHeadTransfer N (hilbertOne - u) := by
  rw [parityHeadTransfer_sub]
  abel

/-- Complete squared error with its signed cross term. -/
theorem parityHeadTransfer_error_sq_eq (N : ℕ) (u : ThresholdHilbert) :
    ‖parityAdjointPacket - parityHeadTransfer N u‖ ^ 2 =
      ‖parityAdjointPacket - parityHeadTransfer N hilbertOne‖ ^ 2 +
      2 * inner ℝ (parityAdjointPacket - parityHeadTransfer N hilbertOne)
        (parityHeadTransfer N (hilbertOne-u)) +
      ‖parityHeadTransfer N (hilbertOne-u)‖ ^ 2 := by
  rw [parityHeadTransfer_error_eq, norm_add_sq_real] <;> ring

/-- The complete error is bounded by the cutoff error and transferred input error. -/
theorem parityHeadTransfer_error_le (N : ℕ) (u : ThresholdHilbert) :
    ‖parityAdjointPacket - parityHeadTransfer N u‖ ≤
      1 / (2 * (2 * (N:ℝ) + 1)) + (1/2:ℝ) * ‖hilbertOne - u‖ := by
  rw [parityHeadTransfer_error_eq]
  exact (norm_add_le _ _).trans (add_le_add (parityHeadTransfer_truncation_le N)
    (parityHeadTransfer_norm_le N _))

/-- A uniform squared-error bound for a constant head transfers with an explicit constant. -/
theorem parityHeadTransfer_error_sq_le (N : ℕ) (u : ThresholdHilbert) :
    ‖parityAdjointPacket - parityHeadTransfer N u‖ ^ 2 ≤ (1 + ‖hilbertOne - u‖ ^ 2) / 2 := by
  have hcut : 1 / (2 * (2 * (N:ℝ) + 1)) ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith [Nat.cast_nonneg (α:=ℝ) N]
  have hlin : ‖parityAdjointPacket - parityHeadTransfer N u‖ ≤ (1 + ‖hilbertOne-u‖)/2 := by
    linarith [parityHeadTransfer_error_le N u]
  calc
    _ ≤ ((1 + ‖hilbertOne - u‖)/2)^2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hlin
    _ ≤ _ := by nlinarith [sq_nonneg (‖hilbertOne - u‖ - 1)]

end RiemannResearch.RH.Pareto.PrimePowerSchur
