import RiemannResearch.RH.MixedConductorGramZeroFree

/-!
# Gram determinants of the mixed projections

The centered packet Gram matrix subtracts the ambient constant. The actual
mixed projection subtracts the screened line with its Pareto norm. The ratio
of their determinants measures exactly the difference between those two
operations. The last results evaluate the finite stages supported by 2 and 3.
-/

noncomputable section
open Filter
open scoped Topology BigOperators Matrix

namespace RiemannResearch.RH.Pareto.PrimePowerSchur.PacketGramBoundary

open CoefficientStabilization RamanujanCanonicalOptimizer MixedConductorBasis

/-- Finite Gram matrix after orthogonal projection onto the full mixed closure. -/
def mixedPacketGram (n : ℕ) : Matrix (Fin n) (Fin n) ℝ := fun i j =>
  inner ℝ (mixedClosure.starProjection (ramanujanPacketHilbert (i.val + 2)))
    (mixedClosure.starProjection (ramanujanPacketHilbert (j.val + 2)))

/-- The centered pencil has the ambient centered packets as its Gram vectors. -/
theorem centeredPacketGram_apply (n : ℕ) (i j : Fin n) :
    meanPencil n 1 i j =
      inner ℝ (ramanujanPacketHilbert (i.val + 2) - meanVector n i • hilbertOne)
        (ramanujanPacketHilbert (j.val + 2) - meanVector n j • hilbertOne) := by
  have hi := RamanujanCanonicalOptimizer.packet_inner_one (i.val + 2)
  have hj := (real_inner_comm (ramanujanPacketHilbert (j.val + 2)) hilbertOne).trans
    (RamanujanCanonicalOptimizer.packet_inner_one (j.val + 2))
  change inner ℝ (ramanujanPacketHilbert (i.val + 2)) (ramanujanPacketHilbert (j.val + 2)) -
    1 * (meanVector n i * meanVector n j) = _
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, hilbertOne_norm_sq, hi, hj, meanVector]
  ring

/-- Mixed projection subtracts the rank-one outer product with its full scalar weight. -/
theorem mixedPacketGram_eq_pencil (n : ℕ) :
    mixedPacketGram n = meanPencil n (1 + ‖CenteredMeanSnake.boundary‖ ^ 2) := by
  ext i j
  let v : closedSpace := ⟨ramanujanPacketHilbert (i.val + 2),
    packet_mem_closedSpace _ (by omega)⟩
  let w : closedSpace := ⟨ramanujanPacketHilbert (j.val + 2),
    packet_mem_closedSpace _ (by omega)⟩
  have hv : legalPacketMean v = meanVector n i := RamanujanCanonicalOptimizer.packet_inner_one _
  have hw : legalPacketMean w = meanVector n j := RamanujanCanonicalOptimizer.packet_inner_one _
  have h := legal_covariance_gap_eq_boundary v w
  rw [hv, hw, legalMixedRetraction_eq_projection, legalMixedRetraction_eq_projection] at h
  change inner ℝ (ramanujanPacketHilbert (i.val + 2)) (ramanujanPacketHilbert (j.val + 2)) -
    meanVector n i * meanVector n j - mixedPacketGram n i j = _ at h
  change mixedPacketGram n i j = inner ℝ (ramanujanPacketHilbert (i.val + 2))
    (ramanujanPacketHilbert (j.val + 2)) - (1 + ‖CenteredMeanSnake.boundary‖ ^ 2) *
      (meanVector n i * meanVector n j)
  linarith only [h]

/-- Exact determinant ratio for the two different projections at each finite stage. -/
theorem mixed_det_ratio (n : ℕ) :
    (mixedPacketGram n).det / (meanPencil n 1).det =
      1 - centeredInverseGramMass n * ‖CenteredMeanSnake.boundary‖ ^ 2 := by
  rw [mixedPacketGram_eq_pencil, det_meanPencil, det_meanPencil, one_mul,
    centeredInverseGramMass_eq_div]
  field_simp [(finitePacketGram_det_pos n).ne', (sub_pos.mpr (packetMass_bounds n).2).ne']
  ring

/-- Projected packets at a finite stage have strictly positive Gram determinant. -/
theorem mixedPacketGram_det_pos (n : ℕ) : 0 < (mixedPacketGram n).det := by
  have hpos : 0 < (mixedPacketGram n).det / (meanPencil n 1).det := by
    rw [mixed_det_ratio]
    exact sub_pos.mpr (centeredInverseGramMass_mul_boundary_lt_one n)
  exact (div_pos_iff_of_pos_right (centered_det_pos n)).mp hpos

/-- Adding columns can only decrease the determinant ratio. -/
theorem mixed_det_ratio_antitone :
    Antitone (fun n => (mixedPacketGram n).det / (meanPencil n 1).det) := by
  intro n m hnm
  simp only [mixed_det_ratio]
  exact sub_le_sub_left (mul_le_mul_of_nonneg_right (centeredInverseGramMass_monotone hnm)
    (sq_nonneg _)) _

/-- At any nonempty stage exact equality of the two determinants characterizes the boundary. -/
theorem mixed_det_eq_centered_iff (n : ℕ) (hn : 0 < n) :
    (mixedPacketGram n).det = (meanPencil n 1).det ↔ CenteredMeanSnake.boundary = 0 := by
  have hI : 0 < centeredInverseGramMass n := by
    rw [centeredInverseGramMass_eq_div]
    exact div_pos (packetMass_pos n hn) (sub_pos.mpr (packetMass_bounds n).2)
  have hden := (centered_det_pos n).ne'
  constructor
  · intro he
    have h := mixed_det_ratio n
    rw [he, div_self hden] at h
    have hm : centeredInverseGramMass n * ‖CenteredMeanSnake.boundary‖ ^ 2 = 0 := by
      linarith only [h]
    have hd := (mul_eq_zero.mp hm).resolve_left hI.ne'
    simpa using hd
  · intro hb
    have h := mixed_det_ratio n
    rw [hb] at h
    have he : (mixedPacketGram n).det / (meanPencil n 1).det = 1 := by simpa using h
    exact (div_eq_one_iff_eq hden).mp he

/-- A nonzero centered boundary forces the relative mixed determinant to collapse. -/
theorem mixed_det_ratio_tendsto_zero_of_boundary_ne (hb : CenteredMeanSnake.boundary ≠ 0) :
    Tendsto (fun n => (mixedPacketGram n).det / (meanPencil n 1).det) atTop (𝓝 0) := by
  have hd : ‖CenteredMeanSnake.boundary‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hb)
  have ht := (tendsto_const_nhds (x := (1 : ℝ))).sub
    ((centeredInverseGramMass_tendsto_of_ne hb).mul_const (‖CenteredMeanSnake.boundary‖ ^ 2))
  simpa only [mixed_det_ratio, inv_mul_cancel₀ hd, sub_self] using ht

/-- Any positive lower bound along arbitrarily late stages forces the boundary to vanish. -/
theorem boundary_eq_zero_iff_cofinal_mixed_det_lower :
    CenteredMeanSnake.boundary = 0 ↔ ∃ ε : ℝ, 0 < ε ∧ ∀ N : ℕ, ∃ n ≥ N,
      ε ≤ (mixedPacketGram n).det / (meanPencil n 1).det := by
  constructor
  · intro hb
    refine ⟨1, zero_lt_one, fun N => ⟨N, le_rfl, ?_⟩⟩
    simp [mixed_det_ratio, hb]
  · rintro ⟨ε, hε, h⟩
    by_contra hb
    obtain ⟨N, hN⟩ := eventually_atTop.1
      ((tendsto_order.mp (mixed_det_ratio_tendsto_zero_of_boundary_ne hb)).2 ε hε)
    obtain ⟨n, hn, hc⟩ := h N
    exact (not_lt_of_ge hc) (hN n hn)

/-- The complete single-packet information has an elementary exact value. -/
theorem centeredInverseGramMass_one :
    centeredInverseGramMass 1 = Real.log 2 / (1 - Real.log 2) := by
  have hh := det_meanPencil 1 1
  have hg : (finitePacketGram 1).det = Real.log 2 := by
    rw [Matrix.det_fin_one]
    change inner ℝ (ramanujanPacketHilbert 2) (ramanujanPacketHilbert 2) = _
    rw [real_inner_self_eq_norm_sq, ramanujanPacketHilbert_two_norm_sq]
  have hm : meanVector 1 0 = Real.log 2 :=
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two
  rw [hg, Matrix.det_fin_one, one_mul] at hh
  change inner ℝ (ramanujanPacketHilbert 2) (ramanujanPacketHilbert 2) -
    1 * (meanVector 1 0 * meanVector 1 0) = _ at hh
  rw [real_inner_self_eq_norm_sq, ramanujanPacketHilbert_two_norm_sq, hm] at hh
  have he : packetMass 1 = Real.log 2 := by
    apply mul_left_cancel₀ (Real.log_pos (by norm_num : (1:ℝ)<2)).ne'
    linarith only [hh]
  rw [centeredInverseGramMass_eq_div, he]

/-- The cofactor multiplying the pencil parameter is the energy of the mean-zero 2,3 packet. -/
theorem det_two_meanPencil (t : ℝ) :
    (meanPencil 2 t).det =
      Real.log 2 * (2 * Real.log 3 - Real.pi / (3 * Real.sqrt 3)) -
      (Real.log 2 + Real.log 3 / 2 - Real.pi / (3 * Real.sqrt 3)) ^ 2 -
      t * ‖balancedTwoThree‖ ^ 2 := by
  have h0 : meanVector 2 0 = Real.log 2 :=
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two
  have h1 : meanVector 2 1 = Real.log 3 :=
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three
  have g00 : finitePacketGram 2 0 0 = Real.log 2 :=
    (real_inner_self_eq_norm_sq _).trans ramanujanPacketHilbert_two_norm_sq
  have g11 : finitePacketGram 2 1 1 = 2 * Real.log 3 - Real.pi / (3 * Real.sqrt 3) :=
    (real_inner_self_eq_norm_sq _).trans three_packet_norm_sq
  have g01 : finitePacketGram 2 0 1 = Real.log 2 + Real.log 3 / 2 -
      Real.pi / (3 * Real.sqrt 3) := two_three_packet_inner
  have g10 : finitePacketGram 2 1 0 = finitePacketGram 2 0 1 := real_inner_comm _ _
  rw [Matrix.det_fin_two]
  change (finitePacketGram 2 0 0 - t * (meanVector 2 0 * meanVector 2 0)) *
      (finitePacketGram 2 1 1 - t * (meanVector 2 1 * meanVector 2 1)) -
    (finitePacketGram 2 0 1 - t * (meanVector 2 0 * meanVector 2 1)) *
      (finitePacketGram 2 1 0 - t * (meanVector 2 1 * meanVector 2 0)) = _
  rw [g10, g00, g11, g01, h0, h1, balancedTwoThree_norm_sq]
  ring

/-- Closed logarithmic formula for the centered inverse Gram form on conductors 2 and 3. -/
theorem centeredInverseGramMass_two :
    let a := Real.log 2
    let b := Real.log 3
    let c := Real.pi / (3 * Real.sqrt 3)
    let D := a * (2*b-c) - (a+b/2-c)^2
    let F := c*a*(2*b-a)
    centeredInverseGramMass 2 = F/(D-F) := by
  dsimp only
  have hg : (finitePacketGram 2).det =
      Real.log 2 * (2 * Real.log 3 - Real.pi / (3 * Real.sqrt 3)) -
        (Real.log 2 + Real.log 3 / 2 - Real.pi / (3 * Real.sqrt 3))^2 := by
    simpa [meanPencil] using det_two_meanPencil 0
  have he := det_two_meanPencil 1
  rw [one_mul, balancedTwoThree_norm_sq] at he
  have hinv := centeredInverseGramMass_eq 2
  rw [inv_eq_one_div] at hinv
  have hratio : (meanPencil 2 1).det * (1 + centeredInverseGramMass 2) =
      (finitePacketGram 2).det := by
    rw [det_meanPencil, one_mul, hinv]
    field_simp [(sub_pos.mpr (packetMass_bounds 2).2).ne']
    ring
  have hpos := centered_det_pos 2
  rw [he] at hpos hratio
  rw [hg] at hratio
  apply (eq_div_iff hpos.ne').mpr
  linarith only [hratio]

end RiemannResearch.RH.Pareto.PrimePowerSchur.PacketGramBoundary
