import RiemannResearch.RH.PrimePowerRamanujanClosure
import RiemannResearch.RH.ThresholdHilbertDilation
import RiemannResearch.RH.MobiusResidualFirstCoordinate
import RiemannResearch.RH.ExactHeadResidualTail
import RiemannResearch.RH.ThresholdHilbertSpace
import RiemannResearch.RH.ParetoResidueDuality
import RiemannResearch.RH.MixedConductorRankOne
import RiemannResearch.RH.MobiusCoefficientStabilization
import RiemannResearch.RH.ThresholdRiemannHypothesis
import RiemannResearch.RH.PrimePowerRamanujanSchur
import RiemannResearch.RH.ScreenedParityPhysicalBounds
import RiemannResearch.RH.MixedConductorCovariance
import RiemannResearch.RH.PrimePowerRamanujanLimits
import RiemannResearch.RH.ParetoResidueMean
import RiemannResearch.RH.IntegratedRamanujanHilbert
import RiemannResearch.RH.ThresholdHilbertMean
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# The Pareto projection and a single prime-power test

For the Pareto weights `1 / (n * (n + 1))` on the positive integers, write
`V = closedSpace` for the closed real span of the residues and `M = mixedClosure`
for the closed span of packets with at least two distinct prime divisors.
The constant target is `hilbertOne`. The screened parity vector is
`u = (J₂ - P_M J₂) / log 2`.

The residue mean and Möbius inversion give `⟪J_q, 1⟫ = Λ(q)` in
`ParetoResidueMean`. The arithmetic rigidity theorem in `MixedConductorRankOne`
gives `(I - P_M) J_q = Λ(q) • u`. Thus the screened prime powers span the
line through `u` in `V`, and `⟪u, 1⟫ = 1`. The distinction between `u` and the
ambient constant is measured below by the covariance with a single packet.

Bagchi, *On Nyman, Beurling and Báez-Duarte's Hilbert space reformulation
of the Riemann hypothesis*, Theorem 1, https://arxiv.org/abs/math/0607733,
gives the discrete closure criterion. Báez-Duarte's natural-dilation theorem
is at https://arxiv.org/abs/math/0202141. For the additive rigidity input see
Kátai, *On additive functions*, equations (1.1) and (1.2),
https://doi.org/10.5486/PMD.1978.25.3-4.10.

Acknowledgment. I thank Michael Kruskal for his help with the Lean formalization.
-/

noncomputable section

namespace RiemannResearch.RH.Pareto.PrimePowerSchur
open CoefficientStabilization
open Filter
open scoped Topology

private theorem inner_centered_of_mean_one {x : ThresholdHilbert}
    (hx : inner ℝ x hilbertOne = 1) :
    inner ℝ x (x - hilbertOne) = ‖x - hilbertOne‖ ^ 2 := by
  rw [inner_sub_right, real_inner_self_eq_norm_sq, norm_sub_sq_real, hx, hilbertOne_norm_sq]
  ring

/-- On the legal space, pairing with the centered screened vector is the
mean multiplied by the full squared distance from the constant. -/
theorem legal_pairing_screenedTwo_sub_one {v : ThresholdHilbert} (hv : v ∈ closedSpace) :
    inner ℝ v (normalizedScreenedTwo - hilbertOne) =
      inner ℝ v hilbertOne * ‖normalizedScreenedTwo - hilbertOne‖ ^ 2 := by
  have hu := normalizedScreenedTwo_mem_screenedPrimeClosure
  rw [screenedPrimeClosure_eq_inf_orthogonal] at hu
  have hd : normalizedScreenedTwo - hilbertOne ∈ mixedClosureᗮ :=
    mixedClosure.orthogonal.sub_mem hu.2 one_mem_mixedClosure_orthogonal
  calc
    _ = inner ℝ (fullScreening v) (normalizedScreenedTwo - hilbertOne) :=
      (fullScreening_inner_right_of_orthogonal v _ hd).symm
    _ = _ := by rw [fullScreening_eq_mean_smul hv, real_inner_smul_left,
      inner_centered_of_mean_one normalizedScreenedTwo_mean]

/-- The covariance for every conductor, including all powers of each prime.
For a mixed conductor the factor on the right vanishes. -/
theorem packet_pairing_screenedTwo_sub_one (q : ℕ) (hq : 1 < q) :
    inner ℝ (ramanujanPacketHilbert q) (normalizedScreenedTwo - hilbertOne) =
      ArithmeticFunction.vonMangoldt q * ‖normalizedScreenedTwo - hilbertOne‖ ^ 2 := by
  rw [legal_pairing_screenedTwo_sub_one (packet_mem_closedSpace q hq), hilbert_inner_one,
    hilbertSequence_ramanujanPacketHilbert, paretoMean_ramanujanPacket]

/-- At a single prime power the covariance is nonpositive exactly when the
ambient constant belongs to the closed residue span. -/
theorem one_mem_iff_primePower_pairing_nonpos (q : ℕ) (hq : 1 < q) (hp : IsPrimePow q) :
    hilbertOne ∈ closedSpace ↔
      inner ℝ (ramanujanPacketHilbert q) (normalizedScreenedTwo - hilbertOne) ≤ 0 := by
  rw [one_mem_closedSpace_iff_normalizedScreenedTwo, packet_pairing_screenedTwo_sub_one q hq]
  constructor
  · intro hu
    simp [hu]
  · intro h
    have hΛ : 0 < ArithmeticFunction.vonMangoldt q :=
      ArithmeticFunction.vonMangoldt_pos_iff.mpr hp
    by_contra hne
    exact (not_lt_of_ge h) (mul_pos hΛ (sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne))))

/-- The single open parity inequality suffices for the Riemann hypothesis.
Here the raw packet at two is the indicator of odd sites. -/
theorem riemannHypothesis_of_parity_pairing_nonpos
    (h : inner ℝ (ramanujanPacketHilbert 2) (normalizedScreenedTwo - hilbertOne) ≤ 0) :
    RiemannHypothesis := by
  have hmem : hilbertOne ∈ closedSpace :=
    (one_mem_iff_primePower_pairing_nonpos 2 (by decide) Nat.prime_two.isPrimePow).mpr h
  exact riemannHypothesis_of_hilbertOne_mem_legalClosure {n : ℕ | 0 < n}
    (fun _ hn => hn) (closedSpace_le_legalClosure hmem)

/-! ## Appendix. Testing the inequality at finite mixed cutoffs -/

/-- At each finite cutoff the parity pairing is exactly the squared approximation
error multiplied by the odd-site mass. -/
theorem finite_parity_pairing_eq_variance (N : ℕ) :
    inner ℝ (ramanujanPacketHilbert 2) (fixedTwoTrial N - hilbertOne) =
      Real.log 2 * ‖fixedTwoTrial N - hilbertOne‖ ^ 2 := by
  let K := mixedSpace (Finset.Icc 2 N)
  let z := ramanujanPacketHilbert 2
  let u := fixedTwoTrial N
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hmean : inner ℝ u hilbertOne = 1 := by
    change inner ℝ ((Real.log 2)⁻¹ • screenedPacket (Finset.Icc 2 N) 2) hilbertOne = 1
    rw [real_inner_smul_left, screenedPacket_inner_one,
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    exact inv_mul_cancel₀ hlog
  have horth : u - hilbertOne ∈ Kᗮ :=
    K.orthogonal.sub_mem
      (K.orthogonal.smul_mem _ (K.sub_starProjection_mem_orthogonal z))
      (one_mem_mixed_orthogonal _)
  have hsplit : z = K.starProjection z + (Real.log 2) • u := by
    change z = K.starProjection z + (Real.log 2) • ((Real.log 2)⁻¹ • (z - K.starProjection z))
    rw [smul_smul, mul_inv_cancel₀ hlog, one_smul]
    abel
  change inner ℝ z (u - hilbertOne) = Real.log 2 * ‖u - hilbertOne‖ ^ 2
  calc
    _ = inner ℝ (K.starProjection z + (Real.log 2) • u) (u - hilbertOne) :=
      congrArg (fun x => inner ℝ x (u - hilbertOne)) hsplit
    _ = _ := by
      rw [inner_add_left, horth _ (K.starProjection_apply_mem z), zero_add,
        real_inner_smul_left, inner_centered_of_mean_one hmean]

/-- The signed error is strictly positive at every finite cutoff. All trial
packets vanish at a common positive multiple of their conductors. -/
theorem finite_parity_pairing_pos (N : ℕ) :
    0 < inner ℝ (ramanujanPacketHilbert 2) (fixedTwoTrial N - hilbertOne) := by
  have hne : fixedTwoTrial N ≠ hilbertOne := by
    intro he
    have hz := fixedTwoTrial_at_common_factorial N
    rw [he, hilbertOne_sequence] at hz
    have hpos : 0 < 2 * (N + 1).factorial := Nat.mul_pos (by decide) (Nat.factorial_pos _)
    simp [zeroAnchor, hpos.ne'] at hz
  rw [finite_parity_pairing_eq_variance]
  exact mul_pos (Real.log_pos (by norm_num))
    (sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne)))

/-- An equivalent statement of the open sign using only finite projections. -/
theorem one_mem_iff_finite_parity_pairing_tendsto_zero :
    hilbertOne ∈ closedSpace ↔
      Tendsto (fun N => inner ℝ (ramanujanPacketHilbert 2) (fixedTwoTrial N - hilbertOne))
        atTop (𝓝 0) := by
  have hlim : Tendsto
      (fun N => inner ℝ (ramanujanPacketHilbert 2) (fixedTwoTrial N - hilbertOne)) atTop
      (𝓝 (inner ℝ (ramanujanPacketHilbert 2) (normalizedScreenedTwo - hilbertOne))) :=
    tendsto_const_nhds.inner (fixedTwoTrial_tendsto.sub_const hilbertOne)
  constructor
  · intro hmem
    simpa [one_mem_closedSpace_iff_normalizedScreenedTwo.mp hmem] using hlim
  · intro hzero
    exact (one_mem_iff_primePower_pairing_nonpos 2 (by decide) Nat.prime_two.isPrimePow).mpr
      (tendsto_nhds_unique hlim hzero).le

/-! ## Second draft, November 22, 2026

The mixed projection of the centered parity indicator leaves exactly the
discrepancy in the paper. Each dilated parity block tests the same discrepancy
at a different physical scale. -/

/-- Centering the raw parity packet and then removing its mixed component
gives the centered screened vector. -/
theorem centered_parity_fullScreening :
    fullScreening ((Real.log 2)⁻¹ • ramanujanPacketHilbert 2 - hilbertOne) =
      normalizedScreenedTwo - hilbertOne := by
  rw [map_sub, map_smul, fullScreening_one, fullScreening_packet]
  rfl

/-- The raw centered indicator admits a mixed approximation with arbitrarily
small error exactly when the constant is in the closed residue span. -/
theorem centered_parity_mem_mixed_iff :
    (Real.log 2)⁻¹ • ramanujanPacketHilbert 2 - hilbertOne ∈ mixedClosure ↔
      hilbertOne ∈ closedSpace := by
  let g := (Real.log 2)⁻¹ • ramanujanPacketHilbert 2 - hilbertOne
  have hscreen : g - mixedClosure.starProjection g =
      normalizedScreenedTwo - hilbertOne := centered_parity_fullScreening
  rw [one_mem_closedSpace_iff_normalizedScreenedTwo, ← sub_eq_zero,
    ← hscreen, sub_eq_zero]
  constructor
  · intro hg
    exact (Submodule.starProjection_eq_self_iff.mpr hg).symm
  · intro hg
    exact Submodule.starProjection_eq_self_iff.mp hg.symm

/-- Dilation by a positive integer turns the parity packet into that integer
times the indicator of alternating blocks. Its signed pairing is constant
over every physical scale. -/
theorem dilated_parity_pairing_screenedTwo_sub_one (m : ℕ) (hm : 0 < m) :
    inner ℝ (hilbertDilation m hm (ramanujanPacketHilbert 2))
        (normalizedScreenedTwo - hilbertOne) =
      Real.log 2 * ‖normalizedScreenedTwo - hilbertOne‖ ^ 2 := by
  rw [legal_pairing_screenedTwo_sub_one
    (closedSpace_dilation (packet_mem_closedSpace 2 (by decide)) m hm),
    hilbert_inner_one, hilbertDilation_mean, hilbertSequence_ramanujanPacketHilbert,
    paretoMean_ramanujanPacket, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  norm_num

/-- The exact squared tail splits into the energy seen by the odd blocks and
the energy of the remaining tail. The tail shift starts at physical site N+1. -/
theorem screened_displacement_scaled_tail_identity (N : ℕ) :
    let d := normalizedScreenedTwo - hilbertOne
    let m := (N : ℝ) + 1
    let e := hilbertDilation (N + 1) (Nat.succ_pos N) (ramanujanPacketHilbert 2)
    m * ‖hilbertTailShift d N‖ ^ 2 =
      Real.log 2 * ‖d‖ ^ 4 +
        m * ‖hilbertTailShift d N - (‖d‖ ^ 2 / m) • hilbertTailShift e N‖ ^ 2 := by
  let d := normalizedScreenedTwo - hilbertOne
  let e := hilbertDilation (N + 1) (Nat.succ_pos N) (ramanujanPacketHilbert 2)
  have he (n : ℕ) (hn : n < N) : e n = 0 := by
    have hz : hilbertSequence e (n + 1) = 0 := by
      change hilbertSequence (hilbertDilation (N+1) _ _) (n+1) = 0
      rw [hilbertDilation_sequence]
      simp [dilation, Nat.div_eq_of_lt (show n + 1 < N + 1 by omega), hilbertSequence_zero]
    have hs := hilbertSequence_weighted_square e n
    rw [hz, zero_pow (by decide : 2 ≠ 0), mul_zero] at hs
    simpa [pow_two] using hs.symm
  have hpair : inner ℝ d e = Real.log 2 * ‖d‖ ^ 2 := by
    rw [real_inner_comm]
    exact dilated_parity_pairing_screenedTwo_sub_one (N + 1) (Nat.succ_pos N)
  have hen : ‖e‖ ^ 2 = ((N : ℝ) + 1) * Real.log 2 := by
    dsimp only [e]
    rw [hilbertDilation_norm_sq, ramanujanPacketHilbert_two_norm_sq, Nat.cast_add,
      Nat.cast_one]
  have htail := hilbertTailShift_inner d e N he
  have hnorm := hilbertTailShift_inner e e N he
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hen] at hnorm
  change ((N : ℝ) + 1) * ‖hilbertTailShift d N‖ ^ 2 =
    Real.log 2 * ‖d‖ ^ 4 + ((N : ℝ) + 1) *
      ‖hilbertTailShift d N - (‖d‖ ^ 2 / ((N : ℝ) + 1)) • hilbertTailShift e N‖ ^ 2
  rw [norm_sub_sq_real, real_inner_smul_right, htail, hpair, norm_smul,
    mul_pow, Real.norm_eq_abs, sq_abs, hnorm]
  have hm : (N : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hm]
  ring

/-- The odd blocks force a lower bound at every physical cutoff. -/
theorem screened_displacement_scaled_tail_lower (N : ℕ) :
    Real.log 2 * ‖normalizedScreenedTwo - hilbertOne‖ ^ 4 ≤
      ((N : ℝ) + 1) * ‖hilbertTailShift (normalizedScreenedTwo - hilbertOne) N‖ ^ 2 := by
  rw [screened_displacement_scaled_tail_identity N]
  exact le_add_of_nonneg_right (mul_nonneg (by positivity) (sq_nonneg _))

/-- Arbitrarily small scaled tail energies along cofinal physical cutoffs
characterize vanishing of the displacement. -/
theorem screenedTwo_eq_one_iff_cofinal_small_scaled_tail :
    normalizedScreenedTwo = hilbertOne ↔
      ∀ ε : ℝ, 0 < ε → ∃ᶠ N : ℕ in atTop,
        ((N : ℝ) + 1) * ‖hilbertTailShift (normalizedScreenedTwo - hilbertOne) N‖ ^ 2 < ε := by
  constructor
  · intro hu ε hε
    apply Filter.Eventually.frequently
    apply Filter.Eventually.of_forall
    intro N
    have hz : hilbertTailShift (0 : ThresholdHilbert) N = 0 := by
      ext n
      rfl
    simpa only [hu, sub_self, hz, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero] using hε
  · intro h
    by_contra hne
    have he : 0 < Real.log 2 * ‖normalizedScreenedTwo - hilbertOne‖ ^ 4 :=
      mul_pos (Real.log_pos (by norm_num)) (pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne)) _)
    obtain ⟨N, hN⟩ := (h _ he).exists
    exact (not_lt_of_ge (screened_displacement_scaled_tail_lower N)) hN

/-- A mixed fit formed by subtracting one large dilation pays the growth
factor sqrt(m)-1 in the complete Pareto norm. The centered parity target
only subtracts a fixed amount from this lower bound on its error. -/
theorem centered_parity_single_dilation_error_lower (m : ℕ) (hm : 0 < m)
    (y : ThresholdHilbert) :
    let g := (Real.log 2)⁻¹ • ramanujanPacketHilbert 2 - hilbertOne
    (Real.sqrt m - 1) * ‖y‖ - ‖g‖ ≤ ‖g - (y - hilbertDilation m hm y)‖ := by
  let g := (Real.log 2)⁻¹ • ramanujanPacketHilbert 2 - hilbertOne
  have hy := norm_sub_norm_le (hilbertDilation m hm y) y
  rw [hilbertDilation_norm, norm_sub_rev (hilbertDilation m hm y) y] at hy
  have hg := norm_sub_norm_le (y - hilbertDilation m hm y) g
  rw [norm_sub_rev (y - hilbertDilation m hm y) g] at hg
  change (Real.sqrt m - 1) * ‖y‖ - ‖g‖ ≤ ‖g - (y - hilbertDilation m hm y)‖
  rw [sub_mul, one_mul]
  exact (sub_le_sub_right hy _).trans hg

end RiemannResearch.RH.Pareto.PrimePowerSchur
