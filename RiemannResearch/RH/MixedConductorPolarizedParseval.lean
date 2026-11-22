import RiemannResearch.RH.MixedConductorGlobalParseval
import RiemannResearch.RH.CenteredMeanSnake
import RiemannResearch.RH.ResidueSmallGram

/-!
# Polarized Parseval tests for the centered boundary

The covariance of two legal vectors differs from their mixed inner product by the
product of their means times the squared norm of the snake boundary. Thus a single
off-diagonal scalar or its signed layer sum can test vanishing. At conductor two
the scalar contains the exact factor `Real.log 2`.

The (2,3) Gram entries use the exact digamma evaluations in ResidueSmallGram.
The mean-zero logarithmic combination has an explicit unconditional layer-energy limit.
The polarization argument uses the real inner-product identity in mathlib. The
arithmetic input is the repository's rank-one screening theorem. For background
on integer dilations, see L. Báez-Duarte, *A strengthening of the Nyman–Beurling
criterion for the Riemann hypothesis*, Rendiconti Lincei 14 (2003), 5–11.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis

open CoefficientStabilization

/-- Polarization of the weighted legal norm decomposition. -/
theorem legal_inner_split_screened (v w : closedSpace) :
    inner ℝ v w = inner ℝ (legalMixedRetraction v) (legalMixedRetraction w) +
      legalPacketMean v * legalPacketMean w * ‖normalizedScreenedTwo‖ ^ 2 := by
  have h := legal_norm_sq_split (v + w)
  have hv := legal_norm_sq_split v
  have hw := legal_norm_sq_split w
  simp only [map_add, norm_add_sq_real, sq_abs] at h hv hw
  nlinarith only [h, hv, hw]

/-- The defect in mixed covariance is a rank-one bilinear form with a known coefficient. -/
theorem legal_covariance_gap_eq_boundary (v w : closedSpace) :
    inner ℝ v w - legalPacketMean v * legalPacketMean w -
      inner ℝ (legalMixedRetraction v) (legalMixedRetraction w) =
      legalPacketMean v * legalPacketMean w * ‖CenteredMeanSnake.boundary‖ ^ 2 := by
  rw [legal_inner_split_screened, CenteredMeanSnake.boundary_norm_sq]
  ring

/-- A single pair of legal vectors of nonzero mean detects vanishing of the boundary. -/
theorem boundary_eq_zero_iff_legal_covariance (v w : closedSpace)
    (hmean : legalPacketMean v * legalPacketMean w ≠ 0) :
    CenteredMeanSnake.boundary = 0 ↔
      inner ℝ (legalMixedRetraction v) (legalMixedRetraction w) =
        inner ℝ v w - legalPacketMean v * legalPacketMean w := by
  have h := legal_covariance_gap_eq_boundary v w
  constructor
  · intro hb
    rw [hb, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero] at h
    exact (sub_eq_zero.mp h).symm
  · intro he
    rw [← he, sub_self] at h
    have hz := (mul_eq_zero.mp h.symm).resolve_left hmean
    simpa using hz

/-- Only the first vector needs to be reconstructed to compute the signed layer sum. -/
theorem tendsto_polarized_layer_sum (x y : mixedClosure) :
    Tendsto (fun n => ∑ k ∈ Finset.range n,
      inner ℝ ((supportLayer k).starProjection x) y)
      atTop (𝓝 (inner ℝ x y)) := by
  have h : Tendsto (fun n : ℕ => inner ℝ
      (∑ k ∈ Finset.range n, (supportLayer k).starProjection x)
      y) atTop
      (𝓝 (inner ℝ x y)) :=
    (tendsto_sum_supportLayer_projection x).inner
      (tendsto_const_nhds (x := y))
  simpa only [sum_inner] using h

/-- The endpoint of one signed scalar layer reconstruction tests membership of the constant. -/
theorem one_mem_iff_tendsto_polarized_layer_sum (v w : closedSpace)
    (hmean : legalPacketMean v * legalPacketMean w ≠ 0) :
    hilbertOne ∈ closedSpace ↔ Tendsto (fun n => ∑ k ∈ Finset.range n,
      inner ℝ ((supportLayer k).starProjection (legalMixedRetraction v)) (legalMixedRetraction w))
      atTop (𝓝 (inner ℝ v w - legalPacketMean v * legalPacketMean w)) := by
  rw [← CenteredMeanSnake.boundary_eq_zero_iff_one_mem,
    boundary_eq_zero_iff_legal_covariance v w hmean]
  constructor
  · intro he
    rw [← he]
    exact tendsto_polarized_layer_sum (legalMixedRetraction v) (legalMixedRetraction w)
  · exact tendsto_nhds_unique
      (tendsto_polarized_layer_sum (legalMixedRetraction v) (legalMixedRetraction w))

/-- The screened scalar can be read against any packet using the von Mangoldt weight. -/
theorem packet_inner_screened_eq_boundary (q : ℕ) (hq : 1 < q) :
    inner ℝ (ramanujanPacketHilbert q) normalizedScreenedTwo =
      ArithmeticFunction.vonMangoldt q * (1 + ‖CenteredMeanSnake.boundary‖ ^ 2) := by
  have hu := normalizedScreenedTwo_mem_screenedPrimeClosure
  rw [screenedPrimeClosure_eq_inf_orthogonal] at hu
  rw [← fullScreening_inner_right_of_orthogonal _ _ hu.2,
    fullScreening_packet_eq_mangoldt_smul q hq, real_inner_smul_left, real_inner_self_eq_norm_sq,
    CenteredMeanSnake.boundary_norm_sq]
  ring

/-- The excess of the parity pairing is exactly log two times the squared boundary norm. -/
theorem parity_pairing_sub_log_eq_boundary :
    inner ℝ (ramanujanPacketHilbert 2) normalizedScreenedTwo - Real.log 2 =
      Real.log 2 * ‖CenteredMeanSnake.boundary‖ ^ 2 := by
  rw [packet_inner_screened_eq_boundary 2 (by decide),
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two, Nat.cast_ofNat]
  ring

/-- One non-strict inequality at conductor two suffices to decide vanishing. -/
theorem boundary_eq_zero_iff_parity_pairing_le_log :
    CenteredMeanSnake.boundary = 0 ↔
      inner ℝ (ramanujanPacketHilbert 2) normalizedScreenedTwo ≤ Real.log 2 := by
  have h := parity_pairing_sub_log_eq_boundary
  constructor
  · intro hb
    rw [hb, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero] at h
    exact (sub_eq_zero.mp h).le
  · intro he
    by_contra hb
    have hp := mul_pos (Real.log_pos (by norm_num : (1 : ℝ) < 2))
      (sq_pos_of_pos (norm_pos_iff.mpr hb))
    linarith only [h, hp, he]

/-- Exact RH implication from a single parity moment of the screened vector. -/
theorem riemannHypothesis_of_parity_pairing_le_log
    (h : inner ℝ (ramanujanPacketHilbert 2) normalizedScreenedTwo ≤ Real.log 2) :
    RiemannHypothesis :=
  CenteredMeanSnake.riemannHypothesis_of_boundary_eq_zero
    (boundary_eq_zero_iff_parity_pairing_le_log.mpr h)

/-- The unnormalized parity and conductor-three packets have an explicit full Gram entry. -/
theorem two_three_packet_inner :
    inner ℝ (ramanujanPacketHilbert 2) (ramanujanPacketHilbert 3) =
      Real.log 2 + Real.log 3 / 2 - Real.pi / (3 * Real.sqrt 3) := by
  calc
    _ = 6 * inner ℝ (residueAtom 0) (residueAtom 1) := by
      rw [hilbert_inner_weighted, hilbertSequence_ramanujanPacketHilbert,
        hilbertSequence_ramanujanPacketHilbert, ramanujanPacket_prime_eq_residue 2 Nat.prime_two,
        ramanujanPacket_prime_eq_residue 3 Nat.prime_three]
      change paretoInner (residue 2) (residue 3) =
        6 * inner ℝ (normalizedResidueHilbert 2 _) (normalizedResidueHilbert 3 _)
      rw [normalizedResidueHilbert_inner]
      push_cast
      ring
    _ = _ := by
      rw [residueAtom_inner_zero_one]
      field_simp [show Real.sqrt 3 ≠ 0 by positivity]
      ring

/-- The signed difference between the elementary covariance and the mixed cross entry
is exactly log two times log three times the squared boundary norm. -/
theorem two_three_projected_covariance_gap :
    Real.log 2 + Real.log 3 / 2 - Real.pi / (3 * Real.sqrt 3) - Real.log 2 * Real.log 3 -
      inner ℝ (mixedClosure.starProjection (ramanujanPacketHilbert 2))
        (mixedClosure.starProjection (ramanujanPacketHilbert 3)) =
      Real.log 2 * Real.log 3 * ‖CenteredMeanSnake.boundary‖ ^ 2 := by
  let v : closedSpace := ⟨ramanujanPacketHilbert 2, packet_mem_closedSpace 2 (by decide)⟩
  let w : closedSpace := ⟨ramanujanPacketHilbert 3, packet_mem_closedSpace 3 (by decide)⟩
  have hm (p : ℕ) (hp : p.Prime) :
      inner ℝ (ramanujanPacketHilbert p) hilbertOne = Real.log (p : ℝ) := by
    rw [hilbert_inner_one, hilbertSequence_ramanujanPacketHilbert, paretoMean_ramanujanPacket,
      ArithmeticFunction.vonMangoldt_apply_prime hp]
  have hv : legalPacketMean v = Real.log 2 := hm 2 Nat.prime_two
  have hw : legalPacketMean w = Real.log 3 := hm 3 Nat.prime_three
  have h := legal_covariance_gap_eq_boundary v w
  rw [hv, hw, legalMixedRetraction_eq_projection, legalMixedRetraction_eq_projection] at h
  change inner ℝ (ramanujanPacketHilbert 2) (ramanujanPacketHilbert 3) -
    Real.log 2 * Real.log 3 - inner ℝ (mixedClosure.starProjection (ramanujanPacketHilbert 2))
      (mixedClosure.starProjection (ramanujanPacketHilbert 3)) = _ at h
  rwa [two_three_packet_inner] at h

/-- A single reverse bound on the fully mixed (2,3) inner product implies RH. -/
theorem riemannHypothesis_of_two_three_projected_covariance
    (h : Real.log 2 + Real.log 3 / 2 - Real.pi / (3 * Real.sqrt 3) - Real.log 2 * Real.log 3 ≤
      inner ℝ (mixedClosure.starProjection (ramanujanPacketHilbert 2))
        (mixedClosure.starProjection (ramanujanPacketHilbert 3))) : RiemannHypothesis := by
  apply CenteredMeanSnake.riemannHypothesis_of_boundary_eq_zero
  by_contra hb
  have hp := mul_pos (mul_pos (Real.log_pos (by norm_num : (1 : ℝ) < 2))
    (Real.log_pos (by norm_num : (1 : ℝ) < 3))) (sq_pos_of_pos (norm_pos_iff.mpr hb))
  linarith only [two_three_projected_covariance_gap, hp, h]

/-- RH's vanishing test can use the signed scalar layer sum at just conductors two and three. -/
theorem boundary_eq_zero_iff_tendsto_two_three_cross :
    let x := mixedClosure.orthogonalProjectionOnto (ramanujanPacketHilbert 2)
    let y := mixedClosure.orthogonalProjectionOnto (ramanujanPacketHilbert 3)
    CenteredMeanSnake.boundary = 0 ↔ Tendsto (fun n => ∑ k ∈ Finset.range n,
      inner ℝ ((supportLayer k).starProjection x) y) atTop
      (𝓝 (Real.log 2 + Real.log 3 / 2 - Real.pi / (3 * Real.sqrt 3) - Real.log 2 * Real.log 3)) := by
  let x := mixedClosure.orthogonalProjectionOnto (ramanujanPacketHilbert 2)
  let y := mixedClosure.orthogonalProjectionOnto (ramanujanPacketHilbert 3)
  let B := Real.log 2 + Real.log 3 / 2 - Real.pi / (3 * Real.sqrt 3) - Real.log 2 * Real.log 3
  have hgap : B - inner ℝ x y = Real.log 2 * Real.log 3 * ‖CenteredMeanSnake.boundary‖ ^ 2 :=
    two_three_projected_covariance_gap
  have hlim := tendsto_polarized_layer_sum x y
  change CenteredMeanSnake.boundary = 0 ↔ Tendsto (fun n => ∑ k ∈ Finset.range n,
    inner ℝ ((supportLayer k).starProjection x) y) atTop (𝓝 B)
  constructor
  · intro hb
    rw [hb, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero] at hgap
    rw [sub_eq_zero.mp hgap]
    exact hlim
  · intro ht
    have he := tendsto_nhds_unique hlim ht
    rw [← he, sub_self] at hgap
    have hn : Real.log 2 * Real.log 3 ≠ 0 := by positivity
    simpa using (mul_eq_zero.mp hgap.symm).resolve_left hn

/-- Exact raw energy of the unnormalized conductor-three packet. -/
theorem three_packet_norm_sq :
    ‖ramanujanPacketHilbert 3‖ ^ 2 = 2 * Real.log 3 - Real.pi / (3 * Real.sqrt 3) := by
  have h := residueAtom_one_norm_sq
  rw [← real_inner_self_eq_norm_sq] at h
  change inner ℝ (normalizedResidueHilbert 3 _) (normalizedResidueHilbert 3 _) = _ at h
  rw [normalizedResidueHilbert_inner] at h
  rw [← real_inner_self_eq_norm_sq, hilbert_inner_weighted,
    hilbertSequence_ramanujanPacketHilbert, ramanujanPacket_prime_eq_residue 3 Nat.prime_three]
  push_cast at h
  field_simp [show Real.sqrt 3 ≠ 0 by positivity] at h ⊢
  nlinarith only [h]

/-- The logarithmic coefficients cancel the screened term in the two prime packets. -/
def balancedTwoThree : mixedClosure :=
  Real.log 3 • mixedClosure.orthogonalProjectionOnto (ramanujanPacketHilbert 2) -
    Real.log 2 • mixedClosure.orthogonalProjectionOnto (ramanujanPacketHilbert 3)

theorem balancedTwoThree_val :
    (balancedTwoThree : ThresholdHilbert) =
      Real.log 3 • ramanujanPacketHilbert 2 - Real.log 2 • ramanujanPacketHilbert 3 := by
  have h2 := fullScreening_packet_eq_mangoldt_smul 2 (by decide)
  have h3 := fullScreening_packet_eq_mangoldt_smul 3 (by decide)
  rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two, Nat.cast_ofNat] at h2
  rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three, Nat.cast_ofNat] at h3
  change ramanujanPacketHilbert 2 - mixedClosure.starProjection (ramanujanPacketHilbert 2) =
    Real.log 2 • normalizedScreenedTwo at h2
  change ramanujanPacketHilbert 3 - mixedClosure.starProjection (ramanujanPacketHilbert 3) =
    Real.log 3 • normalizedScreenedTwo at h3
  have p2 : mixedClosure.starProjection (ramanujanPacketHilbert 2) =
      ramanujanPacketHilbert 2 - Real.log 2 • normalizedScreenedTwo := by rw [← h2, sub_sub_cancel]
  have p3 : mixedClosure.starProjection (ramanujanPacketHilbert 3) =
      ramanujanPacketHilbert 3 - Real.log 3 • normalizedScreenedTwo := by rw [← h3, sub_sub_cancel]
  change Real.log 3 • mixedClosure.starProjection (ramanujanPacketHilbert 2) -
    Real.log 2 • mixedClosure.starProjection (ramanujanPacketHilbert 3) = _
  rw [p2, p3, smul_sub, smul_sub, smul_smul, smul_smul, mul_comm (Real.log 3) (Real.log 2)]
  abel

/-- The logarithmic terms from the diagonal and cross Gram entries cancel exactly. -/
theorem balancedTwoThree_norm_sq :
    ‖balancedTwoThree‖ ^ 2 =
      Real.pi / (3 * Real.sqrt 3) * Real.log 2 * (2 * Real.log 3 - Real.log 2) := by
  change ‖(balancedTwoThree : ThresholdHilbert)‖ ^ 2 = _
  rw [balancedTwoThree_val]
  simp only [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_smul_left, real_inner_smul_right, ramanujanPacketHilbert_two_norm_sq,
    three_packet_norm_sq, two_three_packet_inner]
  ring

/-- An unconditional Parseval limit with an elementary endpoint in the original Pareto norm. -/
theorem tendsto_balancedTwoThree_layer_energy :
    Tendsto (fun n => ∑ k ∈ Finset.range n, ‖(supportLayer k).starProjection balancedTwoThree‖ ^ 2)
      atTop (𝓝 (Real.pi / (3 * Real.sqrt 3) * Real.log 2 * (2 * Real.log 3 - Real.log 2))) := by
  simpa only [balancedTwoThree_norm_sq] using tendsto_sum_supportLayer_energy balancedTwoThree

/-- A closed scalar coordinate of the full projected normalized conductor-two packet. -/
theorem balancedTwoThree_mixed_inner :
    inner ℝ balancedTwoThree parityMixedProjection =
      Real.log 3 / 2 - Real.log 2 + Real.pi / (3 * Real.sqrt 3) := by
  let g := (Real.log 2)⁻¹ • ramanujanPacketHilbert 2
  have hm := (mixedClosure.mem_orthogonal _).mp (mixedClosure.sub_starProjection_mem_orthogonal g)
    (balancedTwoThree : ThresholdHilbert) balancedTwoThree.property
  rw [inner_sub_right, sub_eq_zero] at hm
  change inner ℝ (balancedTwoThree : ThresholdHilbert) (mixedClosure.starProjection g) = _
  rw [← hm, balancedTwoThree_val]
  dsimp only [g]
  simp only [inner_sub_left, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, ramanujanPacketHilbert_two_norm_sq]
  have hcross : inner ℝ (ramanujanPacketHilbert 3) (ramanujanPacketHilbert 2) =
      Real.log 2 + Real.log 3 / 2 - Real.pi / (3 * Real.sqrt 3) :=
    (real_inner_comm _ _).trans two_three_packet_inner
  rw [hcross]
  field_simp [(Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne',
    show Real.sqrt 3 ≠ 0 by positivity] <;> ring

/-- A completed square for the entire parity projection, with its exact one-dimensional
contribution and its full orthogonal remainder. -/
theorem parity_projection_split_along_two_three :
    let E := Real.pi / (3 * Real.sqrt 3) * Real.log 2 * (2 * Real.log 3 - Real.log 2)
    let K := Real.log 3 / 2 - Real.log 2 + Real.pi / (3 * Real.sqrt 3)
    ‖parityMixedProjection‖ ^ 2 =
      K ^ 2 / E + ‖parityMixedProjection - (K / E) • balancedTwoThree‖ ^ 2 := by
  let E := Real.pi / (3 * Real.sqrt 3) * Real.log 2 * (2 * Real.log 3 - Real.log 2)
  let K := Real.log 3 / 2 - Real.log 2 + Real.pi / (3 * Real.sqrt 3)
  have hE : ‖balancedTwoThree‖ ^ 2 = E := balancedTwoThree_norm_sq
  have hK : inner ℝ parityMixedProjection balancedTwoThree = K :=
    (real_inner_comm _ _).trans balancedTwoThree_mixed_inner
  have hlt : Real.log 2 < Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
  have h3 := Real.log_pos (by norm_num : (1 : ℝ) < 3)
  have hdiff : 0 < 2 * Real.log 3 - Real.log 2 := by linarith only [hlt, h3]
  have he : E ≠ 0 := by dsimp only [E]; positivity
  change ‖parityMixedProjection‖ ^ 2 =
    K ^ 2 / E + ‖parityMixedProjection - (K / E) • balancedTwoThree‖ ^ 2
  rw [norm_sub_sq_real, real_inner_smul_right, hK, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, hE]
  field_simp [he]
  ring

end RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis
