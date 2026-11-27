import RiemannResearch.CategoryTheory.ParetoCharacterScreenedEnergy

/-! # Strict shortfall for finite character sections

Source: user-provided common-period argument. On positive multiples of a common
period the two mixed residuals equal negative logarithmic multiples of the same
screened vector. Reflection on that event retains its contribution in the
Cauchy–Schwarz estimate. Completing a weighted square gives the mass-only bound.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.CategoryTheory.ParetoCharacterScreenedEnergy

open RiemannResearch.RH.Pareto RiemannResearch.RH.Pareto.PrimePowerSchur
open MixedConductorBasis

/-- Restriction to physical sites divisible by `L`. Coordinate `i` in ℓ²
represents the positive physical integer `i+1`. -/
def multiplesPart (L : ℕ) (x : ThresholdHilbert) : ThresholdHilbert :=
  ⟨fun i => if L ∣ i + 1 then x i else 0, by
    apply (memℓp_gen_iff (show 0 < (2 : ENNReal).toReal by norm_num)).2
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]
    apply Summable.of_nonneg_of_le (fun i => sq_nonneg _) _ (hilbert_coordinate_square_summable x)
    intro i
    split_ifs <;> simp [sq_nonneg]⟩

private theorem inner_multiplesPart (L : ℕ) (x y : ThresholdHilbert) :
    inner ℝ x (multiplesPart L y) = inner ℝ (multiplesPart L x) (multiplesPart L y) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro i
  by_cases h : L ∣ i + 1 <;> simp [multiplesPart, h]

private theorem reflect_norm (L : ℕ) (y : ThresholdHilbert) :
    ‖y - (2 : ℝ) • multiplesPart L y‖ = ‖y‖ := by
  have hs : ‖y - (2 : ℝ) • multiplesPart L y‖ ^ 2 = ‖y‖ ^ 2 := by
    rw [hilbert_norm_sq, hilbert_norm_sq]
    apply tsum_congr
    intro i
    change (y i - 2 * (if L ∣ i + 1 then y i else 0))^2 = _
    split_ifs <;> ring
  nlinarith only [hs, norm_nonneg (y - (2 : ℝ) • multiplesPart L y), norm_nonneg y]

/-- The two residuals' agreement on the multiples adds twice their restricted
inner product to the usual lower Cauchy–Schwarz estimate. -/
private theorem restricted_inner_le_defect (L : ℕ) (x y : ThresholdHilbert) :
    2 * inner ℝ (multiplesPart L x) (multiplesPart L y) ≤
      ‖x‖ * ‖y‖ + inner ℝ x y := by
  let z := y - (2 : ℝ) • multiplesPart L y
  have h := (neg_le_neg (abs_real_inner_le_norm x z)).trans (neg_abs_le _)
  dsimp only [z] at h
  rw [reflect_norm, inner_sub_right, real_inner_smul_right, inner_multiplesPart] at h
  linarith


/-- Physical expectation with weight three on the multiples and one elsewhere. -/
theorem multiples_weighted_energy_eq_tsum (L : ℕ) (u : ThresholdHilbert) :
    ‖u‖^2 + 2 * ‖multiplesPart L u‖^2 =
      ∑' i : ℕ, (if L ∣ i + 1 then (3 : ℝ) else 1) *
        (paretoWeight i * (hilbertSequence u (i+1))^2) := by
  have hu := hilbert_coordinate_square_summable u
  have hm := hilbert_coordinate_square_summable (multiplesPart L u)
  rw [hilbert_norm_sq u, hilbert_norm_sq (multiplesPart L u), ← hm.tsum_mul_left 2,
    ← hu.tsum_add (hm.mul_left 2)]
  apply tsum_congr
  intro i
  rw [← positiveWeight_succ, hilbertSequence_weighted_square]
  change (u i)^2 + 2 * (if L ∣ i + 1 then u i else 0)^2 = _
  split_ifs <;> ring

/-- Pareto probability of the positive multiples of `L`. -/
def multiplesMass (L : ℕ) : ℝ := ‖multiplesPart L hilbertOne‖ ^ 2

theorem multiplesMass_eq_tsum (L : ℕ) :
    multiplesMass L = ∑' i : ℕ, if L ∣ i + 1 then paretoWeight i else 0 := by
  rw [multiplesMass, hilbert_norm_sq]
  apply tsum_congr
  intro i
  have h := hilbertSequence_weighted_square hilbertOne i
  rw [hilbertOne_sequence, positiveWeight_succ] at h
  simp [zeroAnchor] at h
  by_cases hi : L ∣ i + 1 <;> simp [multiplesPart, hi, h]

private theorem multiplesMass_le_one (L : ℕ) : multiplesMass L ≤ 1 := by
  rw [← hilbertOne_norm_sq, multiplesMass, hilbert_norm_sq, hilbert_norm_sq]
  apply Summable.tsum_le_tsum _ (hilbert_coordinate_square_summable _)
    (hilbert_coordinate_square_summable _)
  intro i
  by_cases hi : L ∣ i + 1 <;> simp [multiplesPart, hi, sq_nonneg]

theorem multiplesMass_pos (L : ℕ) (hL : 0 < L) : 0 < multiplesMass L := by
  rw [multiplesMass_eq_tsum]
  let f (i : ℕ) : ℝ := if L ∣ i + 1 then paretoWeight i else 0
  have hn (i : ℕ) : 0 ≤ f i := by
    dsimp only [f]
    split_ifs <;> simp [le_of_lt (paretoWeight_pos i)]
  have hs : Summable f := Summable.of_nonneg_of_le hn
    (fun i => by dsimp only [f]; split_ifs <;> simp [le_of_lt (paretoWeight_pos i)])
    paretoWeight_hasSum.summable
  exact hs.tsum_pos hn (L - 1) (by simpa [f, Nat.sub_add_cancel hL] using paretoWeight_pos (L - 1))

/-- Weighted mean-one inequality for the weight three on the multiples and
one on their complement. -/
private theorem weighted_energy_lower (L : ℕ) (u : ThresholdHilbert)
    (hmean : inner ℝ u hilbertOne = 1) :
    2 * multiplesMass L / (3 - 2 * multiplesMass L) ≤
      ‖u‖ ^ 2 + 2 * ‖multiplesPart L u‖ ^ 2 - 1 := by
  let p := multiplesMass L
  have hp : 0 < 3 - 2 * p := by dsimp [p]; linarith [multiplesMass_le_one L]
  have hquad (c : ℝ) :
      0 ≤ ‖u‖ ^ 2 + 2 * ‖multiplesPart L u‖ ^ 2 - 6 * c + (9 - 6 * p) * c ^ 2 := by
    have h := add_nonneg (sq_nonneg ‖u - (3*c) • hilbertOne + (2*c) • multiplesPart L hilbertOne‖)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
        (sq_nonneg ‖multiplesPart L u - c • multiplesPart L hilbertOne‖))
    rw [norm_add_sq_real, norm_sub_sq_real, norm_sub_sq_real] at h
    simp only [inner_sub_left, real_inner_smul_right, real_inner_smul_left,
      norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hmean, hilbertOne_norm_sq] at h
    rw [inner_multiplesPart L u, inner_multiplesPart L hilbertOne, real_inner_self_eq_norm_sq] at h
    dsimp only [p, multiplesMass]
    linarith only [h]
  have h := hquad (3 - 2 * p)⁻¹
  have he : (9 - 6*p) * ((3-2*p)⁻¹)^2 = 3 * (3-2*p)⁻¹ := by
    rw [show 9 - 6*p = 3 * (3 - 2*p) by ring, sq]
    calc
      _ = (3 * ((3 - 2*p) * (3 - 2*p)⁻¹)) * (3 - 2*p)⁻¹ := by ring
      _ = _ := by rw [mul_inv_cancel₀ hp.ne', mul_one]
  rw [he] at h
  change 2*p/(3-2*p) ≤ _
  have hid : 2*p/(3-2*p) = 3 * (3-2*p)⁻¹ - 1 := by
    field_simp [hp.ne']
    ring
  linarith only [h, hid]

/-- The omitted part of the full mixed projection at one conductor. -/
def characterResidual (s : Finset Index) (a : ℕ) : mixedClosure :=
  mixedClosure.orthogonalProjectionOnto (ramanujanPacketHilbert a) - partialSection s a

/-- Left side minus right side of the finite two-prime certificate. -/
def characterCrossShortfall (s : Finset Index) : ℝ :=
  Real.log 2 + Real.log 3 / 2 - Real.pi / (3 * Real.sqrt 3) - Real.log 2 * Real.log 3 +
    ‖characterResidual s 2‖ * ‖characterResidual s 3‖ - crossPartial s 2 3

/-- The full boundary contribution plus the signed residual Cauchy–Schwarz defect. -/
theorem characterCrossShortfall_exact (s : Finset Index) :
    characterCrossShortfall s =
      Real.log 2 * Real.log 3 * (‖normalizedScreenedTwo‖ ^ 2 - 1) +
      (‖characterResidual s 2‖ * ‖characterResidual s 3‖ +
        inner ℝ (characterResidual s 2) (characterResidual s 3)) := by
  have hg := two_three_projected_covariance_gap
  rw [CenteredMeanSnake.boundary_norm_sq] at hg
  have hs := packetProjection_cross_eq_partial_add_remainder s
  dsimp only at hs
  change Real.log 2 + Real.log 3 / 2 - Real.pi / (3 * Real.sqrt 3) - Real.log 2 * Real.log 3 -
    inner ℝ (mixedClosure.orthogonalProjectionOnto (ramanujanPacketHilbert 2))
      (mixedClosure.orthogonalProjectionOnto (ramanujanPacketHilbert 3)) = _ at hg
  unfold characterCrossShortfall characterResidual
  linarith only [hs, hg]

private def zeroSite (i : ℕ) : Submodule ℝ mixedClosure where
  carrier := {x | (x : ThresholdHilbert) i = 0}
  zero_mem' := rfl
  add_mem' := by
    intro x y hx hy
    change (x : ThresholdHilbert) i + (y : ThresholdHilbert) i = 0
    exact congrArg₂ (· + ·) hx hy |>.trans (zero_add 0)
  smul_mem' := by
    intro c x hx
    change c * (x : ThresholdHilbert) i = 0
    exact mul_eq_zero.mpr (Or.inr hx)

private theorem packet_coord_zero_of_dvd (a i : ℕ) (h : a ∣ i + 1) :
    ramanujanPacketHilbert a i = 0 := by
  have hz : hilbertSequence (ramanujanPacketHilbert a) (i+1) = 0 := by
    rw [hilbertSequence_ramanujanPacketHilbert, ramanujanPacket]
    apply Finset.sum_eq_zero
    intro d hd
    have hdvd := (Nat.dvd_of_mem_divisors hd).trans h
    simp [RiemannResearch.RH.Pareto.residue, Nat.mod_eq_zero_of_dvd hdvd]
  rw [hilbertSequence_succ] at hz
  simpa only [zero_mul] using
    (div_eq_iff (Real.sqrt_pos.mpr (paretoWeight_pos i)).ne').mp hz

/-- A sufficient arithmetic period condition. Each selected Gram–Schmidt mode
uses raw packets through its own conductor, including earlier unselected labels. -/
def IsCharacterPeriod (s : Finset Index) (L : ℕ) : Prop :=
  2 ∣ L ∧ 3 ∣ L ∧ ∀ q ∈ s, ∀ j : Index, j ≤ q → j.val ∣ L

theorem exists_pos_characterPeriod (s : Finset Index) :
    ∃ L : ℕ, 0 < L ∧ IsCharacterPeriod s L := by
  let n := max 3 (s.sup Subtype.val)
  refine ⟨n.factorial, Nat.factorial_pos _, Nat.dvd_factorial (by decide) ?_,
    Nat.dvd_factorial (by decide) (le_max_left ..), ?_⟩
  · exact (by decide : 2 ≤ 3).trans (le_max_left ..)
  · intro q hq j hj
    exact Nat.dvd_factorial (by have := j.property.1; omega)
      ((show j.val ≤ q.val from hj).trans ((Finset.le_sup hq).trans (le_max_right ..)))

private theorem partialSection_zeroSite (s : Finset Index) (a L i : ℕ)
    (hL : IsCharacterPeriod s L) (hi : L ∣ i + 1) :
    partialSection s a ∈ zeroSite i := by
  classical
  unfold partialSection
  apply Submodule.sum_mem
  intro q hq
  apply Submodule.smul_mem
  have hb : basis q ∈ Submodule.span ℝ (basis '' Set.Iic q) :=
    Submodule.subset_span ⟨q, Set.mem_Iic.mpr (le_refl q), rfl⟩
  rw [basis_span_through] at hb
  apply (Submodule.span_le.mpr ?_ : Submodule.span ℝ (packet '' Set.Iic q) ≤ zeroSite i) hb
  rintro _ ⟨j, hj, rfl⟩
  exact packet_coord_zero_of_dvd j.val i ((hL.2.2 q hq j hj).trans hi)

private theorem multiplesPart_residual (s : Finset Index) (L a : ℕ)
    (hL : IsCharacterPeriod s L) (ha : a.Prime) (haL : a ∣ L) :
    multiplesPart L (characterResidual s a : ThresholdHilbert) =
      -(Real.log (a : ℝ)) • multiplesPart L normalizedScreenedTwo := by
  have h := fullScreening_packet_eq_mangoldt_smul a ha.one_lt
  rw [ArithmeticFunction.vonMangoldt_apply_prime ha] at h
  change ramanujanPacketHilbert a - mixedClosure.starProjection (ramanujanPacketHilbert a) =
    Real.log (a : ℝ) • normalizedScreenedTwo at h
  apply Subtype.ext
  funext i
  by_cases hi : L ∣ i + 1
  · have he := congrArg (fun v : ThresholdHilbert => v i) h
    change ramanujanPacketHilbert a i - (mixedClosure.starProjection (ramanujanPacketHilbert a)) i =
      Real.log (a : ℝ) * normalizedScreenedTwo i at he
    rw [packet_coord_zero_of_dvd a i (haL.trans hi)] at he
    have hs : (partialSection s a : ThresholdHilbert) i = 0 := partialSection_zeroSite s a L i hL hi
    change (if L ∣ i+1 then (mixedClosure.starProjection (ramanujanPacketHilbert a)) i -
      (partialSection s a : ThresholdHilbert) i else 0) =
      -Real.log (a : ℝ) * (if L ∣ i+1 then normalizedScreenedTwo i else 0)
    rw [if_pos hi, if_pos hi, hs]
    linarith
  · change (if L ∣ i+1 then _ else 0) = -Real.log (a : ℝ) * (if L ∣ i+1 then _ else 0)
    rw [if_neg hi, if_neg hi, mul_zero]

/-- First bound, retaining the actual screened energy on the multiples. -/
theorem characterCrossShortfall_ge_weighted_energy (s : Finset Index) (L : ℕ)
    (hL : IsCharacterPeriod s L) :
    Real.log 2 * Real.log 3 *
      (‖normalizedScreenedTwo‖ ^ 2 + 2 * ‖multiplesPart L normalizedScreenedTwo‖ ^ 2 - 1)
      ≤ characterCrossShortfall s := by
  have h := restricted_inner_le_defect L (characterResidual s 2 : ThresholdHilbert)
    (characterResidual s 3 : ThresholdHilbert)
  rw [multiplesPart_residual s L 2 hL Nat.prime_two hL.1,
    multiplesPart_residual s L 3 hL Nat.prime_three hL.2.1, real_inner_smul_left,
    real_inner_smul_right, real_inner_self_eq_norm_sq] at h
  change 2 * (-(Real.log (2 : ℕ)) *
    (-(Real.log (3 : ℕ)) * ‖multiplesPart L normalizedScreenedTwo‖ ^ 2)) ≤
    ‖characterResidual s 2‖ * ‖characterResidual s 3‖ +
      inner ℝ (characterResidual s 2) (characterResidual s 3) at h
  push_cast at h
  rw [characterCrossShortfall_exact]
  linarith only [h]

/-- Quantitative obstruction for any admissible common period. -/
theorem characterCrossShortfall_ge_multiplesMass (s : Finset Index) (L : ℕ)
    (hL : IsCharacterPeriod s L) :
    Real.log 2 * Real.log 3 * (2 * multiplesMass L / (3 - 2 * multiplesMass L)) ≤
      characterCrossShortfall s :=
  (mul_le_mul_of_nonneg_left (weighted_energy_lower L _ normalizedScreenedTwo_mean)
    (by positivity)).trans (characterCrossShortfall_ge_weighted_energy s L hL)

/-- Strict failure of the original certificate inequality for *every* finite
mode set, including empty sets and non-prefix selections. -/
theorem finite_character_cross_certificate_impossible (s : Finset Index) :
    crossPartial s 2 3 <
      Real.log 2 + Real.log 3 / 2 - Real.pi / (3 * Real.sqrt 3) - Real.log 2 * Real.log 3 +
      ‖mixedClosure.orthogonalProjectionOnto (ramanujanPacketHilbert 2) - partialSection s 2‖ *
      ‖mixedClosure.orthogonalProjectionOnto (ramanujanPacketHilbert 3) - partialSection s 3‖ := by
  obtain ⟨L, hpos, hL⟩ := exists_pos_characterPeriod s
  have hp := multiplesMass_pos L hpos
  have hd : 0 < 3 - 2 * multiplesMass L := by linarith [multiplesMass_le_one L]
  have h : 0 < characterCrossShortfall s :=
    (mul_pos (mul_pos (Real.log_pos (by norm_num)) (Real.log_pos (by norm_num)))
      (div_pos (by positivity) hd)).trans_le (characterCrossShortfall_ge_multiplesMass s L hL)
  exact sub_pos.mp h

/-- Finite omitted vectors tend to zero in Pareto norm along the directed
family of all finite subsets. -/
private theorem characterResidual_tendsto_zero (a : ℕ) (ha : 0 < a) :
    Tendsto (fun s => characterResidual s a) atTop (𝓝 0) := by
  let x := mixedClosure.orthogonalProjectionOnto (ramanujanPacketHilbert a)
  have hs : Tendsto (fun s : Finset Index => partialSection s a) atTop (𝓝 x) := by
    have hh : HasSum (fun q => characterRow q a • basis q) x := by
      simpa only [x, basis_inner_packetProjection _ a ha] using (hasSum_modes x)
    exact hh
  simpa only [characterResidual, x, sub_self] using
    (tendsto_const_nhds (x := x)).sub hs

/-- Only the excess over the full covariance gap is controlled by the
product of omitted norms. -/
theorem characterCrossShortfall_le_boundary_add_tails (s : Finset Index) :
    characterCrossShortfall s ≤
      Real.log 2 * Real.log 3 * (‖normalizedScreenedTwo‖ ^ 2 - 1) +
        2 * ‖characterResidual s 2‖ * ‖characterResidual s 3‖ := by
  have h := (le_abs_self _).trans
    (abs_real_inner_le_norm (characterResidual s 2) (characterResidual s 3))
  rw [characterCrossShortfall_exact]
  linarith only [h]

/-- Exact exhaustive limit, also valid after composition with any cofinal
tower tending to `atTop` in the finite-subset order. -/
theorem characterCrossShortfall_tendsto :
    Tendsto characterCrossShortfall atTop
      (𝓝 (Real.log 2 * Real.log 3 * (‖normalizedScreenedTwo‖ ^ 2 - 1))) := by
  have h₂ := characterResidual_tendsto_zero 2 (by decide)
  have h₃ := characterResidual_tendsto_zero 3 (by decide)
  simp_rw [funext characterCrossShortfall_exact]
  simpa only [norm_zero, mul_zero, inner_zero_right, add_zero] using
    tendsto_const_nhds.add ((h₂.norm.mul h₃.norm).add (h₂.inner h₃))

theorem characterCrossShortfall_tendsto_zero_iff_rh :
    Tendsto characterCrossShortfall atTop (𝓝 0) ↔ RiemannHypothesis := by
  rw [← ScreenedSectionDescent.inner_self_eq_one_iff_rh, real_inner_self_eq_norm_sq]
  have hp : Real.log 2 * Real.log 3 ≠ 0 := by positivity
  constructor
  · intro h
    have he := tendsto_nhds_unique characterCrossShortfall_tendsto h
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hp)
  · intro h
    simpa only [h, sub_self, mul_zero] using characterCrossShortfall_tendsto

#print axioms finite_character_cross_certificate_impossible
#print axioms characterCrossShortfall_ge_multiplesMass
#print axioms characterCrossShortfall_tendsto_zero_iff_rh

/-- A finite symbolic upper bound from the two diagonal character Grams. -/
def diagonalShortfallUpper (s : Finset Index) : ℝ :=
  (characterGram 2 2 - energyPartial s 2 - (Real.log 2)^2) +
  (characterGram 3 3 - energyPartial s 3 - (Real.log 3)^2)

private theorem prime_diagonal_budget (s : Finset Index) (a : ℕ) (ha : a.Prime) :
    characterGram a a - energyPartial s a - (Real.log (a : ℝ))^2 =
    ‖characterResidual s a‖^2 +
      (Real.log (a : ℝ))^2 * (‖normalizedScreenedTwo‖^2 - 1) := by
  have hg : characterGram a a = ‖ramanujanPacketHilbert a‖^2 := by
    rw [characterGram_eq _ _ ha.pos ha.pos,
      CenteredMeanSnake.DigammaSection.packetGramEntry_eq _ _ ha.pos ha.pos,
      ← real_inner_self_eq_norm_sq, hilbert_inner_weighted, hilbertSequence_ramanujanPacketHilbert]
  have h := fullScreening_packet_eq_mangoldt_smul a ha.one_lt
  rw [ArithmeticFunction.vonMangoldt_apply_prime ha] at h
  change ramanujanPacketHilbert a - mixedClosure.starProjection (ramanujanPacketHilbert a) = _ at h
  have hp := Submodule.norm_sq_eq_add_norm_sq_starProjection (ramanujanPacketHilbert a) mixedClosure
  rw [Submodule.starProjection_orthogonal_val, h, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs] at hp
  change ‖ramanujanPacketHilbert a‖ ^ 2 =
    ‖mixedClosure.orthogonalProjectionOnto (ramanujanPacketHilbert a)‖ ^ 2 + _ at hp
  rw [hg, characterResidual, packetProjection_residual_norm_sq s a ha.pos]
  linarith only [hp]

theorem diagonalShortfallUpper_exact (s : Finset Index) :
    diagonalShortfallUpper s = ‖characterResidual s 2‖^2 + ‖characterResidual s 3‖^2 +
      ((Real.log 2)^2 + (Real.log 3)^2) * (‖normalizedScreenedTwo‖^2 - 1) := by
  have h₂ := prime_diagonal_budget s 2 Nat.prime_two
  have h₃ := prime_diagonal_budget s 3 Nat.prime_three
  norm_num only [Nat.cast_ofNat] at h₂ h₃
  rw [diagonalShortfallUpper, h₂, h₃]
  ring

theorem characterCrossShortfall_le_diagonalUpper (s : Finset Index) :
    characterCrossShortfall s ≤ diagonalShortfallUpper s := by
  have hc : 0 ≤ ‖normalizedScreenedTwo‖^2 - 1 := by
    nlinarith only [one_le_norm_normalizedScreenedTwo]
  have hl : Real.log 2 * Real.log 3 ≤ (Real.log 2)^2 + (Real.log 3)^2 := by
    nlinarith only [sq_nonneg (Real.log 2 - Real.log 3), sq_nonneg (Real.log 2),
      sq_nonneg (Real.log 3)]
  rw [diagonalShortfallUpper_exact]
  linarith only [characterCrossShortfall_le_boundary_add_tails s,
    mul_le_mul_of_nonneg_right hl hc, sq_nonneg (‖characterResidual s 2‖ - ‖characterResidual s 3‖)]

theorem diagonalShortfallUpper_antitone : Antitone diagonalShortfallUpper := by
  intro s t hst
  have h (a : ℕ) : energyPartial s a ≤ energyPartial t a :=
    Finset.sum_le_sum_of_subset_of_nonneg hst (fun _ _ _ => sq_nonneg _)
  unfold diagonalShortfallUpper
  linarith only [h 2, h 3]

theorem diagonalShortfallUpper_tendsto :
    Tendsto diagonalShortfallUpper atTop
      (𝓝 (((Real.log 2)^2 + (Real.log 3)^2) * (‖normalizedScreenedTwo‖^2 - 1))) := by
  have h₂ := (characterResidual_tendsto_zero 2 (by decide)).norm.pow 2
  have h₃ := (characterResidual_tendsto_zero 3 (by decide)).norm.pow 2
  rw [funext diagonalShortfallUpper_exact]
  simpa only [norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add] using
    (h₂.add h₃).add (tendsto_const_nhds
      (x := ((Real.log 2)^2 + (Real.log 3)^2) * (‖normalizedScreenedTwo‖^2 - 1)))


/-- A finite symbolic majorant tends to zero along an exhaustive tower exactly
when the screened section has unit energy. -/
theorem diagonalShortfallUpper_tower_zero_iff_rh (s : ℕ → Finset Index)
    (hs : Tendsto s atTop atTop) :
    Tendsto (diagonalShortfallUpper ∘ s) atTop (𝓝 0) ↔ RiemannHypothesis := by
  have ht := diagonalShortfallUpper_tendsto.comp hs
  rw [← ScreenedSectionDescent.inner_self_eq_one_iff_rh, real_inner_self_eq_norm_sq]
  have hp : (Real.log 2)^2 + (Real.log 3)^2 ≠ 0 := by positivity
  constructor
  · intro hz
    exact sub_eq_zero.mp ((mul_eq_zero.mp (tendsto_nhds_unique ht hz)).resolve_left hp)
  · intro h
    simpa only [h, sub_self, mul_zero] using ht

#print axioms characterCrossShortfall_le_diagonalUpper
#print axioms diagonalShortfallUpper_tower_zero_iff_rh

end RiemannResearch.CategoryTheory.ParetoCharacterScreenedEnergy
