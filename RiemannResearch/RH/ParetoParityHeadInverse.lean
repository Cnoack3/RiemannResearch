import RiemannResearch.RH.ParetoParityAdjointHeads
import RiemannResearch.RH.TailCapacityDilationCorrection

/-!
# Finite inverse for the parity adjoint head transfer

The unit-conductor jump is one third. All larger-conductor jumps together
have mass at most one sixth. Their action on a physical coordinate samples
strictly smaller positive sites. Finite Picard iteration can thus be stopped
after matching the prescribed head, with a bound independent of its length.
-/

noncomputable section
namespace RiemannResearch.RH.Pareto.PrimePowerSchur
open CoefficientStabilization
open RiemannResearch.Analysis.ExhaustiveWalk

private def site (k : ℕ) : ℝ := hilbertSequence parityAdjointPacket k

private theorem site_one : site 1 = 1/3 := by
  rw [site, parityAdjointPacket_coordinate]
  norm_num

private theorem site_le_half (k : ℕ) : site k ≤ 1/2 := by
  rw [site, parityAdjointPacket_coordinate]
  apply (div_le_iff₀ (by positivity)).mpr
  linarith

private def properJump (j : ℕ) : ℝ := site (j+2) - site (j+1)

private theorem properJump_nonneg (j : ℕ) : 0 ≤ properJump j := by
  have h := parityAdjointPacket_jump (j+2) (by omega)
  rw [show j+2-1 = j+1 by omega] at h
  change 0 ≤ hilbertSequence parityAdjointPacket (j+2) - hilbertSequence parityAdjointPacket (j+1)
  rw [h]
  push_cast
  have hj := Nat.cast_nonneg (α := ℝ) j
  exact div_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))

/-- The first N dilation terms with conductors strictly greater than one. -/
def parityProperTransfer : ℕ → ThresholdHilbert → ThresholdHilbert
  | 0, _ => 0
  | j+1, u => parityProperTransfer j u + properJump j •
      unscaledResidueDilation (j+2) (by omega) u

private theorem proper_norm (N : ℕ) (u : ThresholdHilbert) :
    ‖parityProperTransfer N u‖ ≤ (site (N+1)-site 1)*‖u‖ := by
  induction N with
  | zero => simp [parityProperTransfer]
  | succ j ih =>
    have hu : ‖unscaledResidueDilation (j+2) (by omega) u‖ ≤ ‖u‖ := by
      apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      rw [unscaledResidueDilation_norm_sq]
      apply (div_le_iff₀ (by positivity)).mpr
      apply le_mul_of_one_le_right (sq_nonneg _)
      exact_mod_cast (show 1 ≤ j+2 by omega)
    change ‖parityProperTransfer j u + properJump j • _‖ ≤ (site (j+2)-site 1)*‖u‖
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (properJump_nonneg j)]
    calc
      _ ≤ (site (j+1)-site 1)*‖u‖ + properJump j*‖u‖ :=
        add_le_add ih (mul_le_mul_of_nonneg_left hu (properJump_nonneg j))
      _ = _ := by unfold properJump; ring

theorem parityProperTransfer_norm_le (N : ℕ) (u : ThresholdHilbert) :
    ‖parityProperTransfer N u‖ ≤ (1/6:ℝ)*‖u‖ := by
  apply (proper_norm N u).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  rw [site_one]
  linarith [site_le_half (N+1)]

private theorem proper_one (N k : ℕ) :
    hilbertSequence (parityProperTransfer N hilbertOne) k = site (min k (N+1)) - site (min k 1) := by
  induction N with
  | zero =>
    have hz : hilbertSequence (0 : ThresholdHilbert) k = 0 := congrFun hilbertSequenceLinear.map_zero k
    simp [parityProperTransfer, hz]
  | succ j ih =>
    simp only [parityProperTransfer, hilbertSequence_add, Pi.add_apply, ih,
      hilbertSequence_smul, Pi.smul_apply, smul_eq_mul, unscaledResidueDilation_sequence, hilbertOne_sequence]
    change site (min k (j+1)) - site (min k 1) + properJump j *
      (if k/(j+2) = 0 then 0 else 1) = site (min k (j+2)) - site (min k 1)
    by_cases h : j+2 ≤ k
    · rw [if_neg (Nat.ne_of_gt (Nat.div_pos h (by omega))),
        min_eq_right (by omega : j+1 ≤ k), min_eq_right h, mul_one, properJump]
      ring
    · rw [Nat.div_eq_of_lt (by omega : k < j+2), if_pos rfl,
        min_eq_left (by omega : k ≤ j+1), min_eq_left (by omega : k ≤ j+2), mul_zero, add_zero]

private theorem proper_depends (N k : ℕ) (u v : ThresholdHilbert)
    (h : ∀ d ≥ 2, hilbertSequence u (k/d) = hilbertSequence v (k/d)) :
    hilbertSequence (parityProperTransfer N u) k = hilbertSequence (parityProperTransfer N v) k := by
  induction N with
  | zero => rfl
  | succ j ih =>
    simp only [parityProperTransfer, hilbertSequence_add, Pi.add_apply, ih, hilbertSequence_smul,
      Pi.smul_apply, smul_eq_mul, unscaledResidueDilation_sequence,
      h (j+2) (by omega)]

private theorem finite_add_of {u v : ThresholdHilbert}
    (hu : ∃ m, u ∈ finiteSpace m) (hv : ∃ m, v ∈ finiteSpace m) : ∃ m, u+v ∈ finiteSpace m := by
  obtain ⟨i,hi⟩ := hu
  obtain ⟨j,hj⟩ := hv
  exact ⟨max i j, (finiteSpace _).add_mem (walkSpan_mono residueAtom id (le_max_left _ _) hi)
    (walkSpan_mono residueAtom id (le_max_right _ _) hj)⟩

private theorem proper_finite (N : ℕ) {u : ThresholdHilbert} (hu : ∃ m, u ∈ finiteSpace m) :
    ∃ m, parityProperTransfer N u ∈ finiteSpace m := by
  induction N with
  | zero => exact ⟨0, (finiteSpace 0).zero_mem⟩
  | succ j ih =>
    obtain ⟨m,hm⟩ := hu
    apply finite_add_of ih
    exact ⟨_, (finiteSpace _).smul_mem _ (unscaledResidueDilation_mem_finiteSpace m (j+2) (by omega) u hm)⟩

/-- An unrolled inverse of the finite dilation system, started at zero. -/
def parityHeadInverse (N : ℕ) (v : ThresholdHilbert) : ℕ → ThresholdHilbert
  | 0 => 0
  | t+1 => (3:ℝ) • v + (-3:ℝ) • parityProperTransfer N (parityHeadInverse N v t)

theorem parityHeadInverse_norm_le (N t : ℕ) (v : ThresholdHilbert) :
    ‖parityHeadInverse N v t‖ ≤ 6*‖v‖ := by
  induction t with
  | zero =>
    change ‖(0 : ThresholdHilbert)‖ ≤ 6*‖v‖
    rw [norm_zero]
    positivity
  | succ j ih =>
    rw [parityHeadInverse]
    apply (norm_add_le _ _).trans
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    rw [show |(3:ℝ)| = 3 by norm_num, show |(-3:ℝ)| = 3 by norm_num]
    linarith only [parityProperTransfer_norm_le N (parityHeadInverse N v j), ih]

theorem parityHeadInverse_mem (N t : ℕ) {v : ThresholdHilbert} (hv : ∃ m, v ∈ finiteSpace m) :
    ∃ m, parityHeadInverse N v t ∈ finiteSpace m := by
  induction t with
  | zero => exact ⟨0, (finiteSpace 0).zero_mem⟩
  | succ j ih =>
    obtain ⟨m,hm⟩ := hv
    obtain ⟨i,hi⟩ := proper_finite N ih
    exact finite_add_of ⟨m, (finiteSpace m).smul_mem _ hm⟩ ⟨i, (finiteSpace i).smul_mem _ hi⟩

private theorem inverse_site (N : ℕ) (v : ThresholdHilbert)
    (hv : ∀ k ≤ N, hilbertSequence v k = hilbertSequence parityAdjointPacket k)
    (t k : ℕ) (hkN : k ≤ N) (hkt : k ≤ t ∨ k < 2^t) :
    hilbertSequence (parityHeadInverse N v t) k = hilbertSequence hilbertOne k := by
  induction t generalizing k with
  | zero =>
    have hk : k = 0 := by
      simp only [pow_zero] at hkt
      omega
    subst k
    simp only [hilbertSequence_zero]
  | succ t ih =>
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst k; simp only [hilbertSequence_zero]
    have hp := proper_depends N k (parityHeadInverse N v t) hilbertOne (by
      intro d hd
      apply ih (k/d) ((Nat.div_le_self _ _).trans hkN)
      rcases hkt with hj | hj
      · have hlt := Nat.div_lt_self hk (by omega : 1 < d)
        exact Or.inl (by omega)
      · apply Or.inr
        apply (Nat.div_lt_iff_lt_mul (by omega : 0 < d)).mpr
        rw [pow_succ] at hj
        exact hj.trans_le (Nat.mul_le_mul_left (2^t) hd))
    simp only [parityHeadInverse, hilbertSequence_add, Pi.add_apply, hilbertSequence_smul,
      Pi.smul_apply, smul_eq_mul, hp, proper_one, min_eq_left (by omega : k ≤ N+1),
      min_eq_right (show 1 ≤ k from hk), site_one, hv k hkN, hilbertOne_sequence]
    change 3 * site k + -3 * (site k - 1/3) = (if k = 0 then 0 else 1)
    rw [if_neg (by omega : k ≠ 0)]
    ring

/-- A finite legal adjoint head fit yields a finite legal constant head fit with
norm at most six times the norm of the supplied fit, uniformly in N. -/
theorem parityHeadInverse_exact (N : ℕ) (v : ThresholdHilbert)
    (hv : ∀ k ≤ N, hilbertSequence v k = hilbertSequence parityAdjointPacket k) :
    ∀ k ≤ N, hilbertSequence (parityHeadInverse N v N) k = hilbertSequence hilbertOne k :=
  fun k hk => inverse_site N v hv N k hk (Or.inl hk)

/-- A logarithmic number of steps suffices since every proper dilation at
least halves the site index. -/
theorem parityHeadInverse_exact_of_pow (N t : ℕ) (v : ThresholdHilbert)
    (hv : ∀ k ≤ N, hilbertSequence v k = hilbertSequence parityAdjointPacket k)
    (hNt : N < 2^t) :
    ∀ k ≤ N, hilbertSequence (parityHeadInverse N v t) k = hilbertSequence hilbertOne k :=
  fun k hk => inverse_site N v hv t k hk (Or.inr (hk.trans_lt hNt))

private theorem parityProperTransfer_sub (N : ℕ) (x y : ThresholdHilbert) :
    parityProperTransfer N (x-y) = parityProperTransfer N x - parityProperTransfer N y := by
  induction N with
  | zero => simp [parityProperTransfer]
  | succ j ih =>
    simp only [parityProperTransfer, ih, map_sub, smul_sub]
    abel

/-- The stopped inverse controls complete errors to any prescribed solution
of the finite dilation system. The initial error decays by one half per step. -/
theorem parityHeadInverse_error_le (N t : ℕ) (u v : ThresholdHilbert) :
    ‖u-parityHeadInverse N v t‖ ≤
      6*‖(1/3:ℝ) • u + parityProperTransfer N u - v‖ + (1/2:ℝ)^t * ‖u‖ := by
  induction t with
  | zero =>
    simp only [parityHeadInverse, sub_zero, pow_zero, one_mul]
    linarith [norm_nonneg ((1/3:ℝ) • u + parityProperTransfer N u - v)]
  | succ t ih =>
    have he : u - parityHeadInverse N v (t+1) =
        (3:ℝ) • ((1/3:ℝ) • u + parityProperTransfer N u - v) +
        (-3:ℝ) • parityProperTransfer N (u-parityHeadInverse N v t) := by
      simp only [parityHeadInverse, parityProperTransfer_sub, smul_sub, smul_add, smul_smul,
        show (3:ℝ)*(1/3) = 1 by norm_num, one_smul, neg_smul]
      abel
    rw [he]
    apply (norm_add_le _ _).trans
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, pow_succ]
    rw [show |(3:ℝ)| = 3 by norm_num, show |(-3:ℝ)| = 3 by norm_num]
    linarith only [parityProperTransfer_norm_le N (u-parityHeadInverse N v t), ih]

private theorem inverse_target_truncation (N : ℕ) :
    ‖parityAdjointPacket - ((1/3:ℝ) • hilbertOne + parityProperTransfer N hilbertOne)‖
      ≤ 1/(2*(2*((N+1:ℕ):ℝ)+1)) := by
  let y := parityAdjointPacket - ((1/3:ℝ) • hilbertOne + parityProperTransfer N hilbertOne)
  let c : ℝ := 1/(2*(2*((N+1:ℕ):ℝ)+1))
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hs (k : ℕ) : (hilbertSequence y k)^2 ≤ (hilbertSequence (c • hilbertOne) k)^2 := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst k; simp only [hilbertSequence_zero, le_refl]
    have hcoord : hilbertSequence y k = site k - site (min k (N+1)) := by
      dsimp only [y]
      rw [hilbertSequence_sub, Pi.sub_apply, hilbertSequence_add, Pi.add_apply, proper_one,
        hilbertSequence_smul, Pi.smul_apply, smul_eq_mul, hilbertOne_sequence,
        min_eq_right (show 1 ≤ k from hk), site_one]
      change site k - (1/3*(if k=0 then 0 else 1) + (site (min k (N+1))-1/3)) = _
      rw [if_neg (Nat.ne_of_gt hk)]
      ring
    rw [hcoord, hilbertSequence_smul, Pi.smul_apply, smul_eq_mul, hilbertOne_sequence]
    change (site k - site (min k (N+1)))^2 ≤ (c*(if k=0 then 0 else 1))^2
    rw [if_neg (Nat.ne_of_gt hk), mul_one]
    by_cases h : k ≤ N+1
    · rw [min_eq_left h, sub_self, zero_pow (by decide : 2 ≠ 0)]
      exact sq_nonneg _
    rw [min_eq_right (by omega : N+1 ≤ k)]
    have hmono : site (N+1) ≤ site k := by
      simp only [site, parityAdjointPacket_coordinate]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith only [show (((N+1):ℕ):ℝ) ≤ (k:ℝ) by exact_mod_cast (show N+1 ≤ k by omega)]
    apply (sq_le_sq₀ (sub_nonneg.mpr hmono) hc).mpr
    have he : c = 1/2 - site (N+1) := by
      simp only [c, site, parityAdjointPacket_coordinate]
      field_simp
      ring
    rw [he]
    exact sub_le_sub_right (site_le_half k) _
  have hs2 : ‖y‖^2 ≤ ‖c • hilbertOne‖^2 := by
    rw [hilbert_norm_weighted_sq, hilbert_norm_weighted_sq]
    apply Summable.tsum_le_tsum _ (hilbertSequence_square_summable y)
      (hilbertSequence_square_summable (c • hilbertOne))
    intro k
    exact mul_le_mul_of_nonneg_left (hs k) (positiveWeight_nonneg k)
  have h := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs2
  have h1 : ‖hilbertOne‖ = 1 := by nlinarith [hilbertOne_norm_sq, norm_nonneg hilbertOne]
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc, h1, mul_one, c, y] using h

/-- The complete constant-head error is controlled by the supplied parity-head
error, the explicit finite-jump tail, and the iteration error. -/
theorem parityHeadInverse_one_error_le (N t : ℕ) (v : ThresholdHilbert) :
    ‖hilbertOne - parityHeadInverse N v t‖ ≤ 6*‖parityAdjointPacket-v‖ +
      6/(2*(2*((N+1:ℕ):ℝ)+1)) + (1/2:ℝ)^t := by
  have h := parityHeadInverse_error_le N t hilbertOne v
  have ht := inverse_target_truncation N
  have h1 : ‖hilbertOne‖ = 1 := by nlinarith [hilbertOne_norm_sq, norm_nonneg hilbertOne]
  rw [h1, mul_one] at h
  have hs := dist_triangle ((1/3:ℝ) • hilbertOne + parityProperTransfer N hilbertOne) parityAdjointPacket v
  simp only [dist_eq_norm] at hs
  rw [norm_sub_rev ((1/3:ℝ) • hilbertOne + parityProperTransfer N hilbertOne)
    parityAdjointPacket] at hs
  calc
    _ ≤ 6 * ‖(1/3:ℝ) • hilbertOne + parityProperTransfer N hilbertOne - v‖ +
        (1/2:ℝ)^t := h
    _ ≤ 6 * (1/(2*(2*((N+1:ℕ):ℝ)+1)) + ‖parityAdjointPacket-v‖) + (1/2:ℝ)^t :=
      add_le_add (mul_le_mul_of_nonneg_left (hs.trans (add_le_add ht le_rfl)) (by norm_num)) le_rfl
    _ = _ := by ring

end RiemannResearch.RH.Pareto.PrimePowerSchur
