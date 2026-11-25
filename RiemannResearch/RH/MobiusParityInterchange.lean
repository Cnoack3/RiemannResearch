import RiemannResearch.RH.CanonicalMobiusPNT
import RiemannResearch.RH.ScreenedMeanDilationTests
import RiemannResearch.RH.ParetoPrimePowerCovariance
import RiemannResearch.RH.ParetoSignedSchurRemainder
import RiemannResearch.RH.ScreenedParityPhysicalBounds
import RiemannResearch.RH.MobiusResidualFirstCoordinate
import RiemannResearch.RH.ThresholdHilbertL1
import RiemannResearch.RH.ThresholdInterpolationCompleteness
import RiemannResearch.RH.ParetoTailAverages
import RiemannResearch.RH.ParetoGibbsTailBasis
import RiemannResearch.RH.ParetoAnnihilatorTail
import RiemannResearch.RH.ParetoCenteredFirstSite
import RiemannResearch.RH.ScreenedParityOneSided
import RiemannResearch.RH.CenteredMeanSnake
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Conditional interchange for natural Möbius sums of dilated parity

The natural sums converge in the Pareto space with norm `hilbertL1Norm` to
the first-site contrast. The proof uses the complete energy of the canonical
Möbius vector and its exact values on the initial interval. This gives the
interchange for every bounded physical test function. For the screened section
the signed error identity retains both the limiting projection residual and
the finite reciprocal Möbius sum.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto
namespace MobiusParityInterchange

/-- Natural Möbius sum of the parity dilates, represented in the Pareto space. -/
def paritySum (N : ℕ) : ThresholdHilbert :=
  canonicalMobiusHilbert N - hilbertDilation 2 (by decide) (canonicalMobiusHilbert N) +
    mobiusReciprocalSum N • hilbertDilation (N+1) (Nat.succ_pos N) (ramanujanPacketHilbert 2)

private theorem floorParity (n d : ℕ) :
    ((n / d : ℕ) : ℝ) - 2 * ((n / 2 / d : ℕ) : ℝ) = (((n / d) % 2 : ℕ) : ℝ) := by
  have he : n / 2 / d = n / d / 2 := by simp only [Nat.div_div_eq_div_mul, Nat.mul_comm 2 d]
  rw [he]
  have h : (((n / d) % 2 : ℕ) : ℝ) + 2 * ((n / d / 2 : ℕ) : ℝ) = ((n / d : ℕ) : ℝ) := by
    exact_mod_cast Nat.mod_add_div (n / d) 2
  linarith only [h]

theorem paritySum_coordinate (N n : ℕ) :
    hilbertSequence (paritySum N) n = ∑ d ∈ Finset.Icc 1 N,
      (ArithmeticFunction.moebius d : ℝ) * (((n/d) % 2 : ℕ) : ℝ) := by
  simp only [paritySum, hilbertSequence_add, hilbertSequence_sub, hilbertDilation_sequence,
    hilbertSequence_smul, canonicalMobiusHilbert_sequence, hilbertSequence_ramanujanPacketHilbert,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, dilation,
    canonicalMobiusHead_floor_expansion, ramanujanPacket_prime_eq_residue 2 Nat.prime_two, residue]
  push_cast
  have hsum :
      (∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ) * ((n / d : ℕ) : ℝ)) -
        2 * (∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ) *
          ((n / 2 / d : ℕ) : ℝ)) =
        ∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ) *
          (((n/d) % 2 : ℕ) : ℝ) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    rw [← floorParity]
    ring
  rw [← hsum, ← floorParity]
  ring

/-- At cutoff `N`, the parity sum already has its limiting value at every site
through `N`. -/
theorem paritySum_exact (N n : ℕ) (hn : n ≤ N) :
    hilbertSequence (paritySum N) n =
      hilbertSequence (hilbertOne - hilbertDilation 2 (by decide) hilbertOne) n := by
  have hcanonical (k : ℕ) (hk : k ≤ N) :
      hilbertSequence (canonicalMobiusHilbert N) k = hilbertSequence hilbertOne k := by
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · simp only [hilbertSequence_zero]
    · simp [canonicalMobiusHilbert_exact N k hpos hk, hilbertOne_sequence, zeroAnchor, hpos.ne']
  have hdiv : n / (N+1) = 0 := Nat.div_eq_of_lt (by omega)
  simp only [paritySum, hilbertSequence_add, hilbertSequence_sub, hilbertSequence_smul,
    hilbertDilation_sequence, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, dilation,
    hdiv, hilbertSequence_zero, mul_zero, add_zero]
  rw [hcanonical n hn, hcanonical (n / 2) ((Nat.div_le_self n 2).trans hn)]

private theorem canonical_error_L1 :
    Tendsto (fun N => hilbertL1Norm (hilbertOne - canonicalMobiusHilbert N)) atTop (𝓝 0) := by
  let e (N : ℕ) := hilbertOne - canonicalMobiusHilbert N
  have hl (N : ℕ) : hilbertL1Norm (e N) =
      ∑' k : ℕ, positiveWeight (k+N+1) * |hilbertSequence (e N) (k+N+1)| := by
    have hz : (∑ k ∈ Finset.range (N+1),
        positiveWeight k * |hilbertSequence (e N) k|) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rcases Nat.eq_zero_or_pos k with rfl | hpos
      · simp [hilbertSequence_zero]
      · have hkN : k ≤ N := by have := Finset.mem_range.mp hk; omega
        simp [e, hilbertSequence_sub, hilbertOne_sequence, zeroAnchor, hpos.ne',
          canonicalMobiusHilbert_exact N k hpos hkN]
    simpa only [hilbertL1Norm, hz, zero_add, Nat.add_assoc] using
      ((hilbertL1Norm_summable (e N)).sum_add_tsum_nat_add (N+1)).symm
  have henergy := error_energy_div_tendsto_zero_of_energy _ canonicalMobiusHilbert_sublinear
  have hb : ∀ᶠ N : ℕ in atTop, (hilbertL1Norm (e N))^2 ≤ ‖e N‖^2 / (N : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have ht : ‖hilbertTailShift (e N) N‖^2 ≤ ‖e N‖^2 := by
      rw [hilbertTailShift_norm_sq]
      exact sub_le_self _ (Finset.sum_nonneg fun n hn => sq_nonneg _)
    rw [hl N]
    exact (pareto_absolute_tail_sq_le (e N) N).trans
      ((div_le_div_of_nonneg_right ht (by positivity)).trans
        (div_le_div_of_nonneg_left (sq_nonneg _) hp (by linarith)))
  have hsq : Tendsto (fun N => (hilbertL1Norm (e N))^2) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun N => sq_nonneg _) hb henergy
  have hroot := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq (hilbertL1Norm_nonneg _), Real.sqrt_zero, e]
    using hroot

private theorem L1_dilation (m : ℕ) (hm : 0 < m) (f : ThresholdHilbert) :
    hilbertL1Norm (hilbertDilation m hm f) = hilbertL1Norm f := by
  have habs : hilbertAbs (hilbertDilation m hm f) = hilbertDilation m hm (hilbertAbs f) := by
    apply hilbertSequence_injective
    funext k
    simp only [hilbertAbs_sequence, hilbertDilation_sequence, dilation, abs_mul,
      abs_of_nonneg (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  rw [hilbertL1Norm_eq_inner_abs, habs, hilbert_inner_one, hilbertDilation_mean,
    ← hilbert_inner_one, ← hilbertL1Norm_eq_inner_abs]

private theorem L1_sub (f g : ThresholdHilbert) :
    hilbertL1Norm (f-g) ≤ hilbertL1Norm f + hilbertL1Norm g := by
  have h := hilbertL1Norm_sub_le (f-g) f
  rw [show (f-g)-f = -g by abel, hilbertL1Norm_neg] at h
  linarith only [h]

theorem paritySum_L1_interchange :
    Tendsto (fun N => hilbertL1Norm
      ((hilbertOne - hilbertDilation 2 (by decide) hilbertOne) - paritySum N))
      atTop (𝓝 0) := by
  let e (N : ℕ) := hilbertOne - canonicalMobiusHilbert N
  have hbound (N : ℕ) :
      hilbertL1Norm ((hilbertOne - hilbertDilation 2 (by decide) hilbertOne) - paritySum N) ≤
        2 * hilbertL1Norm (e N) +
          |mobiusReciprocalSum N| * hilbertL1Norm (ramanujanPacketHilbert 2) := by
    have hid : (hilbertOne - hilbertDilation 2 (by decide) hilbertOne) - paritySum N =
        (e N - hilbertDilation 2 (by decide) (e N)) -
          mobiusReciprocalSum N • hilbertDilation (N+1) (Nat.succ_pos N) (ramanujanPacketHilbert 2)
        := by
      change _ = (e N - hilbertDilationLinear 2 (by decide) (e N)) - _
      dsimp only [e]
      rw [map_sub]
      unfold paritySum
      change _ = (hilbertOne - canonicalMobiusHilbert N -
        (hilbertDilation 2 (by decide) hilbertOne -
          hilbertDilation 2 (by decide) (canonicalMobiusHilbert N))) - _
      abel
    rw [hid]
    apply (L1_sub _ _).trans
    rw [hilbertL1Norm_smul, L1_dilation]
    apply add_le_add _ le_rfl
    have hh := L1_sub (e N) (hilbertDilation 2 (by decide) (e N))
    have hd := L1_dilation 2 (by decide) (e N)
    linarith only [hh, hd]
  apply squeeze_zero (fun N => hilbertL1Norm_nonneg _) hbound
  simpa only [mul_zero, abs_zero, zero_mul, zero_add, e] using
    (canonical_error_L1.const_mul 2).add
      (mobiusReciprocalSum_tendsto_zero.abs.mul_const (hilbertL1Norm (ramanujanPacketHilbert 2)))

private theorem pairing_le_L1 (f g : ThresholdHilbert) (B : ℝ)
    (hf : ∀ k : ℕ, |hilbertSequence f k| ≤ B) :
    inner ℝ f g ≤ B * hilbertL1Norm g := by
  rw [hilbert_inner_weighted]
  change (∑' k, positiveWeight k * (hilbertSequence f k * hilbertSequence g k)) ≤ _
  rw [hilbertL1Norm, ← tsum_mul_left]
  apply Summable.tsum_le_tsum _
    (weighted_product_summable_of_square (hilbertSequence_square_summable f)
      (hilbertSequence_square_summable g))
    ((hilbertL1Norm_summable g).mul_left B)
  intro k
  calc
    _ ≤ positiveWeight k * (|hilbertSequence f k| * |hilbertSequence g k|) :=
      mul_le_mul_of_nonneg_left
        (by simpa only [abs_mul] using le_abs_self (hilbertSequence f k * hilbertSequence g k))
        (positiveWeight_nonneg k)
    _ ≤ positiveWeight k * (B * |hilbertSequence g k|) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hf k) (abs_nonneg _))
        (positiveWeight_nonneg k)
    _ = _ := by ring

private theorem contrast_pairing (f : ThresholdHilbert) :
    inner ℝ f (hilbertOne - hilbertDilation 2 (by decide) hilbertOne) =
      hilbertSequence f 1 - inner ℝ f hilbertOne := by
  have hp := congrArg (fun x : ThresholdHilbert => inner ℝ f x)
    CoefficientStabilization.firstPoint_eq_dilation_difference
  rw [paretoPoint_zero_inner, inner_sub_right, real_inner_smul_right] at hp
  rw [inner_sub_right]
  linarith only [hp]

/-- Testing the natural Möbius sums against any bounded physical probe gives the
same result as first inverting Möbius pointwise. -/
theorem bounded_probe_interchange (f : ThresholdHilbert) {B : ℝ}
    (hf : ∀ k : ℕ, |hilbertSequence f k| ≤ B) :
    Tendsto (fun N => inner ℝ f (paritySum N)) atTop
      (𝓝 (hilbertSequence f 1 - inner ℝ f hilbertOne)) := by
  let h := hilbertOne - hilbertDilation 2 (by decide) hilbertOne
  have hn (k : ℕ) : |hilbertSequence (-f) k| ≤ B := by
    have hnseq : hilbertSequence (-f) = -hilbertSequence f := hilbertSequenceLinear.map_neg f
    simpa only [hnseq, Pi.neg_apply, abs_neg] using hf k
  have habs (N : ℕ) : |inner ℝ f (h - paritySum N)| ≤ B * hilbertL1Norm (h - paritySum N) := by
    have hlo := pairing_le_L1 (-f) (h - paritySum N) B hn
    rw [inner_neg_left] at hlo
    exact abs_le.mpr ⟨by linarith only [hlo], pairing_le_L1 f _ B hf⟩
  have hzero : Tendsto (fun N => |inner ℝ f (h - paritySum N)|) atTop (𝓝 0) :=
    squeeze_zero (fun _ => abs_nonneg _) habs
      (by simpa only [mul_zero, h] using paritySum_L1_interchange.const_mul B)
  have hi : Tendsto (fun N => inner ℝ f (h - paritySum N)) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using hzero)
  have hx := (tendsto_const_nhds (x := inner ℝ f h)).sub hi
  rw [← contrast_pairing]
  change Tendsto (fun N => inner ℝ f (paritySum N)) atTop (𝓝 (inner ℝ f h))
  simpa only [inner_sub_right, sub_sub_cancel, sub_zero] using hx

/-- The screened pairing at a finite cutoff is a fixed multiple of the
ordinary reciprocal Möbius sum. -/
theorem screened_pairing (N : ℕ) :
    let u := PrimePowerSchur.normalizedScreenedTwo
    inner ℝ u (paritySum N) = mobiusReciprocalSum N * (Real.log 2 * ‖u‖^2) := by
  dsimp only
  let u := PrimePowerSchur.normalizedScreenedTwo
  have hpar : inner ℝ (ramanujanPacketHilbert 2) u = Real.log 2 * ‖u‖^2 := by
    have hh := PrimePowerSchur.dilated_parity_pairing_screenedTwo_sub_one 1 (by decide)
    rw [hilbertDilation_one, inner_sub_right, hilbert_inner_one,
      hilbertSequence_ramanujanPacketHilbert, paretoMean_ramanujanPacket,
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two, norm_sub_sq_real,
      PrimePowerSchur.normalizedScreenedTwo_mean, hilbertOne_norm_sq] at hh
    push_cast at hh
    change inner ℝ (ramanujanPacketHilbert 2) PrimePowerSchur.normalizedScreenedTwo = _
    dsimp only [u]
    linarith only [hh]
  change inner ℝ u (paritySum N) = mobiusReciprocalSum N * (Real.log 2 * ‖u‖^2)
  rw [real_inner_comm, paritySum, inner_add_left, inner_sub_left, real_inner_smul_left]
  dsimp only [u]
  rw [PrimePowerSchur.inner_dilation_screenedTwo
      (CoefficientStabilization.canonicalMobiusHilbert_mem_closedSpace N),
    PrimePowerSchur.inner_dilation_screenedTwo
      (PrimePowerSchur.packet_mem_closedSpace 2 (by decide)),
    sub_self, zero_add, hpar]

/-- The full signed error in the pairing with the screened mean section.
The Möbius reciprocal sum tends to zero. The term involving the limiting
projection residual is independent of the cutoff. -/
theorem screened_interchange_error (N : ℕ) :
    let u := PrimePowerSchur.normalizedScreenedTwo
    let E := CoefficientStabilization.limitEnergy
    (1-E) * inner ℝ u ((hilbertOne - hilbertDilation 2 (by decide) hilbertOne) - paritySum N) =
      E - hilbertSequence CoefficientStabilization.limitResidual 1 -
        Real.log 2 * mobiusReciprocalSum N := by
  dsimp only
  have he := PrimePowerSchur.normalizedScreenedTwo_energy_product
  have hr := PrimePowerSchur.limitResidual_at_pos_eq_screenedTwo 1 (by decide)
  rw [inner_sub_right, contrast_pairing, PrimePowerSchur.normalizedScreenedTwo_mean,
    screened_pairing]
  nlinarith only [hr, congrArg (fun t : ℝ => t * (Real.log 2 * mobiusReciprocalSum N)) he]

/-- Pair the screened section with each finite sum, then let the cutoff tend
to infinity. The prime number theorem gives zero in this order. -/
theorem screened_pairing_tendsto_zero :
    Tendsto (fun N => inner ℝ PrimePowerSchur.normalizedScreenedTwo (paritySum N))
      atTop (𝓝 0) := by
  simpa only [screened_pairing, zero_mul] using
    (mobiusReciprocalSum_tendsto_zero.mul_const
      (Real.log 2 * ‖PrimePowerSchur.normalizedScreenedTwo‖^2))

/-- The difference between pairing the coordinate limit and taking the
limit of the finite pairings is the exact first-site defect. -/
theorem screened_error_tendsto_firstSite :
    let u := PrimePowerSchur.normalizedScreenedTwo
    let h := hilbertOne - hilbertDilation 2 (by decide) hilbertOne
    Tendsto (fun N => inner ℝ u (h - paritySum N)) atTop (𝓝 (hilbertSequence u 1 - 1)) := by
  dsimp only
  let u := PrimePowerSchur.normalizedScreenedTwo
  let h := hilbertOne - hilbertDilation 2 (by decide) hilbertOne
  change Tendsto (fun N => inner ℝ u (h - paritySum N)) atTop (𝓝 (hilbertSequence u 1 - 1))
  have hcontrast : inner ℝ u h - 0 = hilbertSequence u 1 - 1 := by
    rw [sub_zero, contrast_pairing, PrimePowerSchur.normalizedScreenedTwo_mean]
  rw [← hcontrast]
  simpa only [inner_sub_right] using
    (tendsto_const_nhds (x := inner ℝ u h)).sub screened_pairing_tendsto_zero

/-- The whole signed pairing error is carried by sites strictly past the
cutoff. Its limit there is the first-site defect of the screened section. -/
theorem screened_tail_error_tendsto :
    let u := PrimePowerSchur.normalizedScreenedTwo
    let h := hilbertOne - hilbertDilation 2 (by decide) hilbertOne
    Tendsto (fun N => ∑' j : ℕ, positiveWeight (j+N+1) *
      (hilbertSequence u (j+N+1) * hilbertSequence (h - paritySum N) (j+N+1)))
      atTop (𝓝 (hilbertSequence u 1 - 1)) := by
  let u := PrimePowerSchur.normalizedScreenedTwo
  let h := hilbertOne - hilbertDilation 2 (by decide) hilbertOne
  apply screened_error_tendsto_firstSite.congr
  intro N
  have hhead : (∑ k ∈ Finset.range (N+1),
      positiveWeight k * (hilbertSequence u k * hilbertSequence (h - paritySum N) k)) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hkN : k ≤ N := by have := Finset.mem_range.mp hk; omega
    rw [hilbertSequence_sub, Pi.sub_apply, paritySum_exact N k hkN]
    simp only [h, sub_self, mul_zero]
  have hsplit := (weighted_product_summable_of_square (hilbertSequence_square_summable u)
    (hilbertSequence_square_summable (h - paritySum N))).sum_add_tsum_nat_add (N+1)
  rw [hhead, zero_add] at hsplit
  rw [hilbert_inner_weighted]
  change (∑' k, positiveWeight k *
    (hilbertSequence u k * hilbertSequence (h - paritySum N) k)) = _
  simpa only [Nat.add_assoc] using hsplit.symm


/-- Apply two consecutive dilations to the same natural Möbius approximant. -/
def adjacentContrast (n N : ℕ) : ThresholdHilbert :=
  hilbertDilation (n+1) (by omega) (canonicalMobiusHilbert N) -
    hilbertDilation (n+2) (by omega) (canonicalMobiusHilbert N)

/-- Dilating the canonical exact head gives a full initial interval growing
linearly in the smaller of the two dilation scales. -/
theorem adjacentContrast_exact_scaled (n N k : ℕ) (hk : k < (n + 1) * (N + 1)) :
    hilbertSequence (adjacentContrast n N) k = hilbertSequence (tailBasisHilbert n) k := by
  have hdiv₁ : k / (n+1) < N+1 := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by
    simpa only [Nat.mul_comm (N+1) (n+1)] using hk)
  have hdiv₂ : k / (n+2) < N+1 := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by
    have hle := Nat.mul_le_mul_right (N+1) (show n+1 ≤ n+2 by omega)
    simpa only [Nat.mul_comm (N+1) (n+2)] using hk.trans_le hle)
  have head (j : ℕ) (hj : j ≤ N) :
      hilbertSequence (canonicalMobiusHilbert N) j = hilbertSequence hilbertOne j := by
    rcases Nat.eq_zero_or_pos j with rfl | hp
    · simp
    · rw [canonicalMobiusHilbert_exact N j hp hj, hilbertOne_sequence]
      simp [zeroAnchor, hp.ne']
  simp only [adjacentContrast, tailBasisHilbert_eq_dilation_one, hilbertSequence_sub, Pi.sub_apply,
    hilbertDilation_sequence, dilation]
  rw [head _ (by omega : k / (n+1) ≤ N), head _ (by omega : k / (n+2) ≤ N)]

/-- The initial interval through the Möbius cutoff works at every scale. -/
theorem adjacentContrast_exact (n N k : ℕ) (hk : k ≤ N) :
    hilbertSequence (adjacentContrast n N) k = hilbertSequence (tailBasisHilbert n) k := by
  apply adjacentContrast_exact_scaled
  exact (Nat.lt_succ_of_le hk).trans_le (Nat.le_mul_of_pos_left _ (by omega))

/-- Complete L¹ error, uniformly over the adjacent scales. -/
theorem adjacentContrast_L1_le (n N : ℕ) :
    hilbertL1Norm (tailBasisHilbert n - adjacentContrast n N) ≤
      2 * hilbertL1Norm (hilbertOne - canonicalMobiusHilbert N) := by
  let e := hilbertOne - canonicalMobiusHilbert N
  have hid : tailBasisHilbert n - adjacentContrast n N =
      hilbertDilation (n+1) (by omega) e - hilbertDilation (n+2) (by omega) e := by
    rw [tailBasisHilbert_eq_dilation_one, adjacentContrast]
    change _ = hilbertDilationContinuous (n+1) (by omega) (hilbertOne - canonicalMobiusHilbert N) -
      hilbertDilationContinuous (n+2) (by omega) (hilbertOne - canonicalMobiusHilbert N)
    simp only [map_sub, hilbertDilationContinuous_apply]
    abel
  rw [hid]
  calc
    _ ≤ hilbertL1Norm (hilbertDilation (n+1) (by omega) e) +
          hilbertL1Norm (hilbertDilation (n+2) (by omega) e) := L1_sub _ _
    _ = _ := by rw [L1_dilation, L1_dilation, two_mul]

/-- The scale may depend arbitrarily on the cutoff in the L¹ estimate. -/
theorem adjacentContrast_L1_tendsto (m : ℕ → ℕ) :
    Tendsto (fun N => hilbertL1Norm (tailBasisHilbert (m N) - adjacentContrast (m N) N))
      atTop (𝓝 0) :=
  squeeze_zero (fun _ => hilbertL1Norm_nonneg _) (fun N => adjacentContrast_L1_le (m N) N)
    (by simpa only [mul_zero] using canonical_error_L1.const_mul 2)

/-- At each finite cutoff the entire signed contrast has zero screened pairing. -/
theorem adjacentContrast_screened (n N : ℕ) :
    inner ℝ (adjacentContrast n N) PrimePowerSchur.normalizedScreenedTwo = 0 := by
  rw [adjacentContrast, inner_sub_left,
    PrimePowerSchur.inner_dilation_screenedTwo
      (CoefficientStabilization.canonicalMobiusHilbert_mem_closedSpace N),
    PrimePowerSchur.inner_dilation_screenedTwo
      (CoefficientStabilization.canonicalMobiusHilbert_mem_closedSpace N), sub_self]

/-- Interchanging the screened pairing with every consecutive-dilation limit
is equivalent to equality of the screened unit and the ambient constant. -/
theorem adjacentContrast_interchange_iff_screened :
    (∀ n : ℕ, Tendsto
      (fun N => inner ℝ (adjacentContrast n N) PrimePowerSchur.normalizedScreenedTwo)
      atTop (𝓝 (inner ℝ (tailBasisHilbert n) PrimePowerSchur.normalizedScreenedTwo))) ↔
      PrimePowerSchur.normalizedScreenedTwo = hilbertOne := by
  constructor
  · intro h
    apply sub_eq_zero.mp
    apply tailBasis_total
    · rw [inner_sub_left, PrimePowerSchur.normalizedScreenedTwo_mean,
        real_inner_self_eq_norm_sq, hilbertOne_norm_sq, sub_self]
    · intro n
      have hzero : inner ℝ (tailBasisHilbert n) PrimePowerSchur.normalizedScreenedTwo = 0 := by
        apply tendsto_nhds_unique (h n)
        simpa only [adjacentContrast_screened] using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
      rw [real_inner_comm, inner_sub_right, hzero, tailBasis_inner_one, sub_self]
  · intro hu n
    rw [show inner ℝ (tailBasisHilbert n) PrimePowerSchur.normalizedScreenedTwo = 0 by
      rw [hu, tailBasis_inner_one]]
    simpa only [adjacentContrast_screened] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

/-- The simultaneous screened interchange closes the centered snake boundary. -/
theorem riemannHypothesis_of_adjacentContrast_interchange
    (h : ∀ n : ℕ, Tendsto
      (fun N => inner ℝ (adjacentContrast n N) PrimePowerSchur.normalizedScreenedTwo)
      atTop (𝓝 (inner ℝ (tailBasisHilbert n) PrimePowerSchur.normalizedScreenedTwo))) :
    RiemannHypothesis :=
  PrimePowerSchur.CenteredMeanSnake.riemannHypothesis_of_boundary_eq_zero
    (PrimePowerSchur.CenteredMeanSnake.boundary_eq_zero_iff_screened.mpr
      (adjacentContrast_interchange_iff_screened.mp h))


/-- Each cutoff has the same total squared screened interchange error. The
constant coordinate is accounted for by the normalization of the section. -/
theorem adjacentContrast_screened_error_parseval (N : ℕ) :
    ∑' n : ℕ, (inner ℝ (tailBasisHilbert n - adjacentContrast n N)
      PrimePowerSchur.normalizedScreenedTwo)^2 =
        CoefficientStabilization.limitEnergy / (1 - CoefficientStabilization.limitEnergy) := by
  let u := PrimePowerSchur.normalizedScreenedTwo
  have hs := fullTailBasis.hasSum_inner_mul_inner u u
  have hzero : inner ℝ u (fullTailBasis 0) * inner ℝ (fullTailBasis 0) u = 1 := by
    have h₁ : inner ℝ u hilbertOne = 1 := PrimePowerSchur.normalizedScreenedTwo_mean
    have h₂ : inner ℝ hilbertOne u = 1 := (real_inner_comm _ _).trans h₁
    simp only [fullTailBasis_apply, fullTailFamily, inner_neg_right, inner_neg_left, h₁, h₂]
    norm_num
  have hsucc (n : ℕ) : inner ℝ u (fullTailBasis (n+1)) * inner ℝ (fullTailBasis (n+1)) u =
      (inner ℝ (tailBasisHilbert n - adjacentContrast n N) u)^2 := by
    simp only [fullTailBasis_apply, fullTailFamily, inner_sub_left, u, adjacentContrast_screened,
      sub_zero, pow_two, real_inner_comm PrimePowerSchur.normalizedScreenedTwo (tailBasisHilbert n)]
  have hsum := hs.tsum_eq
  rw [hs.summable.tsum_eq_zero_add, hzero, real_inner_self_eq_norm_sq] at hsum
  simp_rw [hsucc] at hsum
  have hd := PrimePowerSchur.normalizedScreenedTwo_error_sq_eq_limitEnergy
  rw [norm_sub_sq_real, PrimePowerSchur.normalizedScreenedTwo_mean, hilbertOne_norm_sq] at hd
  dsimp only [u] at hsum
  linarith only [hsum, hd]


/-- Ignoring any fixed number of adjacent contrasts leaves a complete test
for the screened section. A vector with eventually vanishing wavelet
coefficients is eventually constant in physical coordinates. For this
section, even a one-sided physical bound forces equality with one. -/
theorem adjacentContrast_eventual_interchange_iff_screened :
    (∀ᶠ n : ℕ in atTop, Tendsto
      (fun N => inner ℝ (adjacentContrast n N) PrimePowerSchur.normalizedScreenedTwo)
      atTop (𝓝 (inner ℝ (tailBasisHilbert n) PrimePowerSchur.normalizedScreenedTwo))) ↔
      PrimePowerSchur.normalizedScreenedTwo = hilbertOne := by
  constructor
  · intro h
    let u := PrimePowerSchur.normalizedScreenedTwo
    obtain ⟨K, hK⟩ := eventually_atTop.mp h
    have hdiff (n : ℕ) (hn : K ≤ n) : tailAverage u n = tailAverage u (n+1) := by
      apply sub_eq_zero.mp
      rw [tailAverage_sub_succ, real_inner_comm]
      apply tendsto_nhds_unique (hK n hn)
      simpa only [u, adjacentContrast_screened] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    have hc (n : ℕ) (hn : K ≤ n) : tailAverage u n = tailAverage u K := by
      induction n, hn using Nat.le_induction with
      | base => rfl
      | succ n hn ih => exact (hdiff n hn).symm.trans ih
    have he : Tendsto (fun n : ℕ => hilbertSequence u (n+1)) atTop (𝓝 (tailAverage u K)) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop K] with n hn
      rw [← hilbertGibbsPhysical_eq, hardyCoordinates_reconstruction,
        hardyCoordinates_partial_sum, hardyCoordinates_succ, hdiff n hn, sub_self, mul_zero,
        zero_sub, neg_neg]
      exact (hc (n+1) (by omega)).symm
    rw [← Nat.cofinite_eq_atTop] at he
    obtain ⟨B, hB⟩ := he.bddAbove_range_of_cofinite
    apply PrimePowerSchur.normalizedScreenedTwo_eq_one_of_oneSidedBound
    refine Or.inr ⟨B, ?_⟩
    intro k hk
    cases k with
    | zero => omega
    | succ n => exact hB (Set.mem_range_self n)
  · intro h
    exact Eventually.of_forall (adjacentContrast_interchange_iff_screened.mpr h)


/-- Absolute summability of the signed Haar defects, together with a
one-sided bound on their linearly weighted positive peaks, suffices.
These regularity conditions follow whenever the screened section is one. -/
theorem screened_eq_one_iff_adjacent_regular :
    PrimePowerSchur.normalizedScreenedTwo = hilbertOne ↔
      Summable (fun n : ℕ => |inner ℝ PrimePowerSchur.normalizedScreenedTwo (tailBasisHilbert n)|) ∧
      (∃ C : ℝ, ∀ n : ℕ,
        ((n : ℝ)+1) * inner ℝ PrimePowerSchur.normalizedScreenedTwo (tailBasisHilbert n) ≤ C) := by
  let u := PrimePowerSchur.normalizedScreenedTwo
  let a (n : ℕ) := inner ℝ u (tailBasisHilbert n)
  constructor
  · intro hu
    have hz (n : ℕ) : inner ℝ PrimePowerSchur.normalizedScreenedTwo (tailBasisHilbert n) = 0 := by
      rw [hu, real_inner_comm, tailBasis_inner_one]
    simp only [hz, abs_zero, mul_zero, summable_zero, true_and]
    exact ⟨0, fun _ => le_rfl⟩
  · rintro ⟨hs, C, hC⟩
    have htel (n : ℕ) : tailAverage u n = 1 - ∑ j ∈ Finset.range n, a j := by
      induction n with
      | zero => simp only [tailAverage_zero, u, PrimePowerSchur.normalizedScreenedTwo_mean,
          Finset.range_zero, Finset.sum_empty, sub_zero]
      | succ n ih =>
        have h : tailAverage u n - tailAverage u (n+1) = a n := tailAverage_sub_succ u n
        rw [Finset.sum_range_succ, ← sub_sub, ← ih, ← h]
        ring
    apply PrimePowerSchur.normalizedScreenedTwo_eq_one_of_oneSidedBound
    refine Or.inr ⟨C + 1 + ∑' n, |a n|, ?_⟩
    intro k hk
    cases k with
    | zero => omega
    | succ n =>
      change hilbertSequence u (n+1) ≤ _
      rw [← hilbertGibbsPhysical_eq, hardyCoordinates_reconstruction,
        hardyCoordinates_partial_sum, hardyCoordinates_succ, tailAverage_sub_succ, sub_neg_eq_add,
        htel]
      have hb : -(∑ j ∈ Finset.range n, a j) ≤ ∑' j, |a j| :=
        (neg_le_abs _).trans ((Finset.abs_sum_le_sum_abs _ _).trans
          (hs.sum_le_tsum _ (fun i _ => abs_nonneg _)))
      linarith only [hC n, hb]


/-- Interchange of a screened pairing on every positive integer dilation of
a probe with formal limit `1 - U_p 1`. -/
def screenedDilationInterchange (p : ℕ) (hp : 0 < p) (G : ℕ → ThresholdHilbert) : Prop :=
  ∀ (m : ℕ) (hm : 0 < m),
    Tendsto (fun N => inner ℝ (hilbertDilation m hm (G N)) PrimePowerSchur.normalizedScreenedTwo)
      atTop (𝓝 (inner ℝ (hilbertDilation m hm (hilbertOne - hilbertDilation p hp hilbertOne))
        PrimePowerSchur.normalizedScreenedTwo))

/-- A zero screened limit for a sequence of legal probes with formal limit
`1 - U_p 1` interchanges on its whole dilation orbit exactly when the
ambient adjoint at `p` fixes the screened section. -/
theorem dilationOrbit_interchange_iff_adjoint_fixed (p : ℕ) (hp : 0 < p)
    (G : ℕ → ThresholdHilbert) (hG : ∀ N, G N ∈ CoefficientStabilization.closedSpace)
    (hzero : Tendsto (fun N => inner ℝ (G N) PrimePowerSchur.normalizedScreenedTwo) atTop (𝓝 0)) :
    screenedDilationInterchange p hp G ↔
      hilbertDilationAdjoint p hp PrimePowerSchur.normalizedScreenedTwo =
        PrimePowerSchur.normalizedScreenedTwo := by
  let u := PrimePowerSchur.normalizedScreenedTwo
  have hz (m : ℕ) (hm : 0 < m) :
      Tendsto (fun N => inner ℝ (hilbertDilation m hm (G N)) u) atTop (𝓝 0) := by
    apply hzero.congr
    intro N
    exact (PrimePowerSchur.inner_dilation_screenedTwo (hG N) m hm).symm
  have hid (m : ℕ) (hm : 0 < m) :
      inner ℝ (hilbertDilation m hm (hilbertOne - hilbertDilation p hp hilbertOne)) u =
        inner ℝ (u - hilbertDilationAdjoint p hp u) (hilbertDilation m hm hilbertOne) := by
    have hcomm : hilbertDilation m hm (hilbertDilation p hp hilbertOne) =
        hilbertDilation p hp (hilbertDilation m hm hilbertOne) := by
      simp only [hilbertDilation_comp, Nat.mul_comm m p]
    change inner ℝ (hilbertDilationContinuous m hm
      (hilbertOne - hilbertDilation p hp hilbertOne)) u = _
    rw [map_sub, hilbertDilationContinuous_apply, hilbertDilationContinuous_apply,
      inner_sub_left, hcomm, ← real_inner_comm (u - _) _, inner_sub_right]
    change _ = inner ℝ (hilbertDilation m hm hilbertOne) u -
      inner ℝ (hilbertDilation m hm hilbertOne) ((hilbertDilationContinuous p hp).adjoint u)
    rw [ContinuousLinearMap.adjoint_inner_right, hilbertDilationContinuous_apply]
  constructor
  · intro h
    apply Eq.symm
    apply sub_eq_zero.mp
    apply CoefficientStabilization.eq_zero_of_inner_dilation_one_eq_zero
    intro m hm
    rw [← hid m hm]
    exact tendsto_nhds_unique (h m hm) (hz m hm)
  · intro h m hm
    have hh : inner ℝ (hilbertDilation m hm
        (hilbertOne - hilbertDilation p hp hilbertOne)) u = 0 := by
      rw [hid, show hilbertDilationAdjoint p hp u = u from h, sub_self, inner_zero_left]
    change Tendsto _ atTop (𝓝 (inner ℝ (hilbertDilation m hm
      (hilbertOne - hilbertDilation p hp hilbertOne)) u))
    rw [hh]
    exact hz m hm

/-- For the actual parity sums, testing all dilates is exactly the dyadic
adjoint equation. -/
theorem paritySum_dilation_interchange_iff :
    screenedDilationInterchange 2 (by decide) paritySum ↔
      hilbertDilationAdjoint 2 (by decide) PrimePowerSchur.normalizedScreenedTwo =
        PrimePowerSchur.normalizedScreenedTwo := by
  apply dilationOrbit_interchange_iff_adjoint_fixed
  · intro N
    unfold paritySum
    apply CoefficientStabilization.closedSpace.add_mem
    · exact CoefficientStabilization.closedSpace.sub_mem
        (CoefficientStabilization.canonicalMobiusHilbert_mem_closedSpace N)
        (CoefficientStabilization.closedSpace_dilation
          (CoefficientStabilization.canonicalMobiusHilbert_mem_closedSpace N) 2 (by decide))
    · exact CoefficientStabilization.closedSpace.smul_mem _
        (CoefficientStabilization.closedSpace_dilation
          (PrimePowerSchur.packet_mem_closedSpace 2 (by decide)) (N+1) (by omega))
  · simpa only [real_inner_comm] using screened_pairing_tendsto_zero


/-- Once the entire dyadic parity orbit interchanges, one scalar upper bound
on the triadic adjoint norm supplies the remaining equation at three. -/
theorem paritySum_interchange_and_triadic_bound_iff_screened :
    (screenedDilationInterchange 2 (by decide) paritySum ∧
      ‖hilbertDilationAdjoint 3 (by decide) PrimePowerSchur.normalizedScreenedTwo‖^2 ≤
        ‖PrimePowerSchur.normalizedScreenedTwo‖^2) ↔
      PrimePowerSchur.normalizedScreenedTwo = hilbertOne := by
  rw [paritySum_dilation_interchange_iff]
  constructor
  · rintro ⟨h2, h3⟩
    apply PrimePowerSchur.one_mem_closedSpace_iff_normalizedScreenedTwo.mp
    apply PrimePowerSchur.CenteredMeanSnake.screenedLine_eq_one_line_iff_one_mem.mp
    apply PrimePowerSchur.screenedLine_eq_one_line_iff_two_three_adjoint_norms.mpr
    rw [h2, two_mul]
    exact add_le_add le_rfl h3
  · intro h
    rw [h, hilbertDilationAdjoint_one, hilbertDilationAdjoint_one]
    exact ⟨rfl, le_rfl⟩


/-- An actual right-half-strip zero forces a power-sized squared Hilbert
error at each fixed adjacent pair, through the full dilated exact head. -/
theorem adjacentContrast_mellin_power_lower (n N : ℕ) (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s = 0) :
    (2 * s.re - 1) * ‖(((n+1 : ℕ) : ℂ) ^ (1-s) - ((n+2 : ℕ) : ℂ) ^ (1-s)) / s‖ ^ 2 *
      (((n+1)*(N+1) : ℕ) : ℝ) ^ (2 * s.re - 1) ≤
        ‖tailBasisHilbert n - adjacentContrast n N‖ ^ 2 := by
  have hf : adjacentContrast n N ∈ CoefficientStabilization.closedSpace :=
    CoefficientStabilization.closedSpace.sub_mem
      (CoefficientStabilization.closedSpace_dilation
        (CoefficientStabilization.canonicalMobiusHilbert_mem_closedSpace N) _ (by omega))
      (CoefficientStabilization.closedSpace_dilation
        (CoefficientStabilization.canonicalMobiusHilbert_mem_closedSpace N) _ (by omega))
  rw [tailBasisHilbert_eq_dilation_one]
  apply CoefficientStabilization.thresholdContrast_exact_head_error_lower _ _ _ _ _
    (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)) hf _ s hs hs1 hz
  intro j _ hj
  rw [← tailBasisHilbert_eq_dilation_one]
  exact adjacentContrast_exact_scaled n N j hj

/-- A single fixed adjacent pair suffices: its complete squared errors need
only beat every positive power budget along some cutoffs. -/
theorem riemannHypothesis_of_adjacentContrast_subpower (n : ℕ)
    (h : ∀ a ε : ℝ, 0 < a → 0 < ε → ∃ N : ℕ,
      ‖tailBasisHilbert n - adjacentContrast n N‖^2 < ε * (((n+1)*(N+1) : ℕ) : ℝ)^a) :
    RiemannHypothesis := by
  apply RiemannResearch.RH.riemannHypothesis_iff_right_half_strip_zero_free.mpr
  intro s hs hlt hz
  have hs0 : s ≠ 0 := by intro he; norm_num [he] at hs
  have hs1 : s ≠ 1 := by intro he; norm_num [he] at hlt
  have hpow : 0 < 2*s.re-1 := by linarith
  have hsym := CoefficientStabilization.thresholdContrast_symbol_ne_zero
    (n+1) (n+2) (Nat.succ_pos _) (Nat.lt_succ_self _) s hs0 hlt
  have hcoef := mul_pos hpow (pow_pos (norm_pos_iff.mpr hsym) 2)
  obtain ⟨N, hN⟩ := h _ _ hpow hcoef
  exact (not_lt_of_ge (adjacentContrast_mellin_power_lower n N s hs hs1 hz)) hN

end MobiusParityInterchange
end RiemannResearch.RH.Pareto
