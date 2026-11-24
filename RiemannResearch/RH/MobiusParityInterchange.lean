import RiemannResearch.RH.CanonicalMobiusPNT
import RiemannResearch.RH.ScreenedMeanDilationTests
import RiemannResearch.RH.ParetoPrimePowerCovariance
import RiemannResearch.RH.ParetoSignedSchurRemainder
import RiemannResearch.RH.ScreenedParityPhysicalBounds
import RiemannResearch.RH.MobiusResidualFirstCoordinate
import RiemannResearch.RH.ThresholdHilbertL1
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

private theorem L1_smul (a : ℝ) (f : ThresholdHilbert) :
    hilbertL1Norm (a • f) = |a| * hilbertL1Norm f := by
  unfold hilbertL1Norm
  rw [← tsum_mul_left]
  apply tsum_congr
  intro k
  simp only [hilbertSequence_smul, Pi.smul_apply, smul_eq_mul, abs_mul]
  ring

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
    rw [L1_smul, L1_dilation]
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

end MobiusParityInterchange
end RiemannResearch.RH.Pareto
