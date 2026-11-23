import RiemannResearch.RH.CenteredMeanStageSnake
import RiemannResearch.RH.MixedConductorGramSites
import RiemannResearch.RH.MixedConductorGramZeroFree
import RiemannResearch.RH.MixedConductorPolarizedParseval
import RiemannResearch.RH.ParetoParityPeriodSection
import RiemannResearch.RH.TwoSeedDigammaJumps

/-!
# The screened mean section from the digamma recurrence

The jump sum uses the recurrence psi(x + 1) = psi(x) + 1/x at the end of a
period (NIST DLMF 5.5.2). Applied to packet products it computes every Gram
entry. Normalizing the finite mean lift gives every physical coordinate of
the unit section. At any quotient stage the squared error splits exactly
into the transported snake boundary and the distance to that section.
-/

noncomputable section
open Filter
open scoped Topology BigOperators Matrix

namespace RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.DigammaSection
open CoefficientStabilization RamanujanCanonicalOptimizer PacketGramBoundary

/-- Signed digamma jumps of a packet product over its common period. -/
def packetGramEntry (q s : ℕ) : ℝ :=
  -(digammaJumpSum (Nat.lcm q s) (fun k => ramanujanPacket q k * ramanujanPacket s k)) /
    (Nat.lcm q s : ℝ)

theorem packetGramEntry_eq (q s : ℕ) (hq : 0 < q) (hs : 0 < s) :
    packetGramEntry q s = paretoInner (ramanujanPacket q) (ramanujanPacket s) := by
  let L := Nat.lcm q s
  let f := fun k => ramanujanPacket q k * ramanujanPacket s k
  have hper (k : ℕ) : f (k + L) = f k := by
    dsimp [f, L]
    rw [ramanujanPacket_period_of_dvd q _ (Nat.dvd_lcm_left q s),
      ramanujanPacket_period_of_dvd s _ (Nat.dvd_lcm_right q s)]
  have hb (k : ℕ) := mul_le_mul (ramanujanPacket_abs_le q k) (ramanujanPacket_abs_le s k)
    (abs_nonneg _) ((abs_nonneg _).trans (ramanujanPacket_abs_le q k))
  have h0 : ramanujanPacket q 0 = 0 := by
    rw [← hilbertSequence_ramanujanPacketHilbert]
    simp
  have he := periodic_paretoMean_eq_digamma_jumps L (Nat.lcm_pos hq hs) f
    (fun k => by simpa only [f, abs_mul] using hb k) hper
  change _ = paretoMean f
  simpa only [packetGramEntry, f, L, h0, zero_mul, zero_sub, neg_div] using he.symm

/-- The original two-prime digamma evaluation, with the complete mixed
pairing retained when solving for the norm of the upper section. -/
theorem two_three_section_norm :
    packetGramEntry 2 3 = Real.log 2 + Real.log 3 / 2 - Real.pi / (3 * Real.sqrt 3) ∧
    ‖normalizedScreenedTwo‖^2 =
      (packetGramEntry 2 3 - inner ℝ (mixedClosure.starProjection (ramanujanPacketHilbert 2))
        (mixedClosure.starProjection (ramanujanPacketHilbert 3))) / (Real.log 2 * Real.log 3) := by
  have he : packetGramEntry 2 3 =
      inner ℝ (ramanujanPacketHilbert 2) (ramanujanPacketHilbert 3) := by
    rw [packetGramEntry_eq 2 3 (by decide) (by decide), hilbert_inner_weighted,
      hilbertSequence_ramanujanPacketHilbert, hilbertSequence_ramanujanPacketHilbert]
  have h := MixedConductorBasis.two_three_projected_covariance_gap
  rw [boundary_norm_sq] at h
  rw [he, MixedConductorBasis.two_three_packet_inner]
  refine ⟨rfl, (eq_div_iff (by positivity)).mpr ?_⟩
  nlinarith only [h]

/-- The matrix uses only packet values, rational digamma nodes and integer periods. -/
def jumpGram (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => packetGramEntry (i.val + 2) (j.val + 2)

theorem jumpGram_eq (n : ℕ) : jumpGram n = finitePacketGram n := by
  ext i j
  rw [finitePacketGram_apply]
  exact packetGramEntry_eq _ _ (by omega) (by omega)

/-- An arithmetic formula for the finite mean-one section at a physical site. -/
def sectionCoordinate (n k : ℕ) : ℝ :=
  let c := (jumpGram n)⁻¹.mulVec (meanVector n)
  dotProduct (siteVector n k) c / dotProduct (meanVector n) c

theorem sectionCoordinate_eq (n k : ℕ) :
    sectionCoordinate (n + 1) k = hilbertSequence (packetUnitMean n) k := by
  have he : dotProduct (siteVector (n + 1) k)
      ((finitePacketGram (n + 1))⁻¹.mulVec (meanVector (n + 1))) =
      hilbertSequence (packetCandidate (n + 1)) k := by
    rw [← anchoredEvaluationCLM_apply]
    change _ = anchoredEvaluationCLM k (∑ i : Fin (n + 1), packetCoefficients (n + 1) i •
      ramanujanPacketHilbert (i.val + 2))
    rw [map_sum]
    simp only [map_smul, smul_eq_mul, anchoredEvaluationCLM_apply,
      hilbertSequence_ramanujanPacketHilbert, packetCoefficients_eq_inverseGram]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  have hm : dotProduct (meanVector (n + 1))
      ((finitePacketGram (n + 1))⁻¹.mulVec (meanVector (n + 1))) = packetMass (n + 1) :=
    (packetMass_eq_inverseGram _).symm
  rw [sectionCoordinate, jumpGram_eq]
  rw [he, hm, packetUnitMean]
  conv_rhs => rw [← anchoredEvaluationCLM_apply, map_smul]
  simp only [anchoredEvaluationCLM_apply, smul_eq_mul, div_eq_inv_mul]

/-- The normalized digamma solves recover u at every fixed site, including
the zero anchor. This places no assumption on the ambient boundary. -/
theorem sectionCoordinate_tendsto (k : ℕ) :
    Tendsto (fun n => sectionCoordinate (n + 1) k) atTop
      (𝓝 (hilbertSequence normalizedScreenedTwo k)) := by
  have h := ((anchoredEvaluationCLM k).continuous.tendsto _).comp packetUnitMean_tendsto
  simpa only [Function.comp_def, anchoredEvaluationCLM_apply, sectionCoordinate_eq,
    packetUnitMeanLimit_eq_screened] using h

/-- A single lower bound that occurs cofinally on longer finite prefixes. -/
def cofinalPrefixLowerBound : Prop :=
  ∃ C : ℝ, ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧
    ∀ k : ℕ, 0 < k → k ≤ K → C ≤ sectionCoordinate (N + 1) k

/-- If the screened section is nonconstant, every proposed lower bound is
permanently violated on some later finite prefix. -/
theorem eventual_prefix_failure_of_screened_ne_one
    (hne : normalizedScreenedTwo ≠ hilbertOne) (C : ℝ) (K₀ : ℕ) :
    ∃ K : ℕ, K₀ ≤ K ∧ ∀ N : ℕ, K ≤ N →
      ∃ k : ℕ, 0 < k ∧ k ≤ K ∧ sectionCoordinate (N + 1) k < C := by
  obtain ⟨k, hk, hbad⟩ :=
    (screenedTwo_unbounded_both_sides_of_ne_one hne (-C)).2
  have hbad' : hilbertSequence normalizedScreenedTwo k < C := by linarith
  have ht := sectionCoordinate_tendsto k
  have hev : ∀ᶠ N : ℕ in atTop, sectionCoordinate (N + 1) k < C :=
    ht.eventually (Iio_mem_nhds hbad')
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hev
  let K := max K₀ (max k N₀)
  refine ⟨K, le_max_left _ _, fun N hKN => ⟨k, hk, ?_, hN₀ N ?_⟩⟩
  · dsimp only [K]
    omega
  · dsimp only [K] at hKN
    omega

/-- The cofinal prefix condition is exactly the assertion that the screened
section is the ambient constant. -/
theorem cofinalPrefixLowerBound_iff_screened_eq_one :
    cofinalPrefixLowerBound ↔ normalizedScreenedTwo = hilbertOne := by
  constructor
  · rintro ⟨C, hC⟩
    by_contra hne
    obtain ⟨K, -, hfail⟩ := eventual_prefix_failure_of_screened_ne_one hne C 0
    obtain ⟨N, hKN, hall⟩ := hC K
    obtain ⟨k, hk, hkK, hbad⟩ := hfail N hKN
    exact (not_lt_of_ge (hall k hk hkK)) hbad
  · intro hu
    refine ⟨0, fun K => ?_⟩
    have hpoint (k : ℕ) (hk : k ∈ Finset.Icc 1 K) :
        ∀ᶠ N : ℕ in atTop, 0 ≤ sectionCoordinate (N + 1) k := by
      have hkpos : 0 < k := (Finset.mem_Icc.mp hk).1
      have ht := sectionCoordinate_tendsto k
      have hlim : hilbertSequence normalizedScreenedTwo k = 1 := by
        rw [hu, hilbertOne_sequence]
        simp [zeroAnchor, hkpos.ne']
      rw [hlim] at ht
      exact (ht.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono
        (fun _ h => h.le)
    have hall : ∀ᶠ N : ℕ in atTop,
        ∀ k ∈ Finset.Icc 1 K, 0 ≤ sectionCoordinate (N + 1) k := by
      rw [Finset.eventually_all]
      intro k hk
      exact hpoint k hk
    obtain ⟨N, hN⟩ := eventually_atTop.1 hall
    refine ⟨max K N, le_max_left _ _, fun k hk hkK => ?_⟩
    exact hN (max K N) (le_max_right _ _) k (Finset.mem_Icc.mpr ⟨hk, hkK⟩)

/-- A cofinal common lower bound for the finite digamma sections proves RH. -/
theorem riemannHypothesis_of_cofinalPrefixLowerBound
    (h : cofinalPrefixLowerBound) : RiemannHypothesis := by
  have hu := cofinalPrefixLowerBound_iff_screened_eq_one.mp h
  apply CenteredMeanSnake.riemannHypothesis_of_boundary_eq_zero
  rw [CenteredMeanSnake.boundary_eq_zero_iff_one_mem, ← hu]
  exact screenedPrimeClosure_le_closedSpace normalizedScreenedTwo_mem_screenedPrimeClosure

/-- The reciprocal arithmetic mass gives the squared norm of the same lift. -/
theorem reciprocal_jump_mass_tendsto :
    Tendsto (fun n => (dotProduct (meanVector (n + 1))
      ((jumpGram (n + 1))⁻¹.mulVec (meanVector (n + 1))))⁻¹) atTop
      (𝓝 (‖normalizedScreenedTwo‖^2)) := by
  have he (n : ℕ) : (dotProduct (meanVector (n + 1))
      ((jumpGram (n + 1))⁻¹.mulVec (meanVector (n + 1))))⁻¹ = ‖packetUnitMean n‖^2 := by
    rw [packetUnitMean_energy, jumpGram_eq]
    exact congrArg (fun x : ℝ => x⁻¹) (packetMass_eq_inverseGram _).symm
  simp_rw [he]
  simpa only [packetUnitMeanLimit_eq_screened] using packetUnitMean_tendsto.norm.pow 2

/-- A single finite sum over the jumps of the squared residual. The physical
constant has value one at the periodic wrap of this scalar calculation. -/
def residualJumpAverage (n : ℕ) : ℝ :=
  let L := Nat.lcmUpto (n + 2)
  digammaJumpSum L (fun k => (1 - sectionCoordinate (n + 1) k)^2) / (L : ℝ)

private theorem periodic_error_eq (v : ThresholdHilbert) :
    paretoError (hilbertSequence v) = ‖v - hilbertOne‖^2 := by
  rw [hilbert_norm_weighted_sq]
  unfold paretoError paretoInner
  apply tsum_congr
  intro k
  cases k with
  | zero => simp [positiveWeight]
  | succ k =>
    rw [← anchoredEvaluationCLM_apply, map_sub]
    simp only [anchoredEvaluationCLM_apply, hilbertOne_sequence, zeroAnchor, Nat.succ_ne_zero,
      if_false]
    ring

theorem residualJumpAverage_eq (n : ℕ) :
    1 - residualJumpAverage n = ‖packetUnitMean n - hilbertOne‖^2 := by
  let L := Nat.lcmUpto (n + 2)
  have hL : 0 < L := Nat.pos_of_ne_zero (Nat.lcmUpto_ne_zero _)
  have hb := finiteSpace_sequence_abs_le (n + 1) _ (packetUnitMean_legal n)
  have hp (k : ℕ) : hilbertSequence (packetUnitMean n) (k + L) =
      hilbertSequence (packetUnitMean n) k :=
    finiteSpace_lcmUpto_period (n + 1) (packetUnitMean_legal n) k
  have h := paretoError_eq_one_sub_digamma_jumps L hL _ hb hp (by simp)
  simpa only [residualJumpAverage, sectionCoordinate_eq, periodic_error_eq, L] using h.symm

/-- Chase a finite arithmetic section itself through the two quotient rows. -/
theorem connecting_on_finite_section (S : Submodule ℝ mixedClosure) (n : ℕ) :
    Stage.connecting S 1 = (Stage.mixedImage S).mkQ ((Stage.zeroDen S).mkQ
      ⟨center (packetUnitMean n), center_mem (packetUnitMean n)⟩) := by
  let v : closedSpace := ⟨packetUnitMean n,
    RamanujanMultipleCapacityLimits.finiteSpace_le_closedSpace _ (packetUnitMean_legal n)⟩
  have hm : legalPacketMean v = 1 := by
    change inner ℝ (packetUnitMean n) hilbertOne = 1
    exact (real_inner_comm ..).trans (packetUnitMean_signal n)
  simpa only [hm] using Stage.connecting_on_lift S v

/-- Any stage of the categorical ladder gives the same boundary class. The
remaining term in the digamma calculation is the squared finite-section error. -/
theorem stage_unit_digamma_identity (S : Submodule ℝ mixedClosure) (n : ℕ) :
    1 - residualJumpAverage n =
      ‖Stage.targetEquiv S (Stage.connecting S 1)‖^2 +
        ‖packetUnitMean n - normalizedScreenedTwo‖^2 := by
  have hv : packetUnitMean n ∈ closedSpace :=
    RamanujanMultipleCapacityLimits.finiteSpace_le_closedSpace _ (packetUnitMean_legal n)
  have he := packetUnitMeanLimit_variance_completion _ hv (packetUnitMean_signal n)
  rw [residualJumpAverage_eq, Stage.targetEquiv_connecting, boundary_apply, one_smul,
    norm_defect_class, ← boundary_norm, boundary_norm_sq_eq_energy]
  simpa only [packetUnitMeanLimit_eq_screened] using he

/-- The zero boundary test expressed solely by the finite arithmetic jump sums. -/
theorem residualJumpAverage_tendsto :
    Tendsto residualJumpAverage atTop (𝓝 (1 - ‖boundary‖^2)) := by
  have ht : Tendsto (fun n => ‖packetUnitMean n - normalizedScreenedTwo‖^2) atTop (𝓝 0) := by
    simpa [packetUnitMeanLimit_eq_screened] using
      (packetUnitMean_tendsto.sub_const normalizedScreenedTwo).norm.pow 2
  have he (n : ℕ) : residualJumpAverage n =
      (1 - ‖boundary‖^2) - ‖packetUnitMean n - normalizedScreenedTwo‖^2 := by
    have h := stage_unit_digamma_identity (⊥ : Submodule ℝ mixedClosure) n
    rw [Stage.targetEquiv_connecting, boundary_apply, one_smul, norm_defect_class,
      ← boundary_norm] at h
    linarith
  change Tendsto (fun n => residualJumpAverage n) _ _
  simp_rw [he]
  simpa only [sub_zero] using
    (tendsto_const_nhds (x := (1 - ‖boundary‖^2))).sub ht

/-- The normalized jump sum is exactly two minus the reciprocal finite
Gram mass. Its periodic wrap term contributes one of the two units. -/
theorem residualJumpAverage_eq_mass (n : ℕ) :
    residualJumpAverage n = 2 - (packetMass (n + 1))⁻¹ := by
  have h := residualJumpAverage_eq n
  have hm : inner ℝ (packetUnitMean n) hilbertOne = 1 :=
    (real_inner_comm ..).trans (packetUnitMean_signal n)
  rw [norm_sub_sq_real, packetUnitMean_energy, hm, hilbertOne_norm_sq] at h
  linarith

theorem stage_unit_vanishes_iff_jump_limit (S : Submodule ℝ mixedClosure) :
    Stage.connecting S 1 = 0 ↔ Tendsto residualJumpAverage atTop (𝓝 1) := by
  rw [Stage.connecting_one_eq_zero_iff, ← boundary_eq_zero_iff_one_mem]
  constructor
  · intro h
    simpa [h] using residualJumpAverage_tendsto
  · intro h
    have hz := tendsto_nhds_unique residualJumpAverage_tendsto h
    apply norm_eq_zero.mp
    nlinarith only [hz, norm_nonneg boundary]

/-- The orthogonal representative of a coset in the ambient legal quotient H/V. -/
def representative : ThresholdHilbert →L[ℝ] ThresholdHilbert :=
  ContinuousLinearMap.id ℝ ThresholdHilbert - closedSpace.starProjection

private theorem representative_mem (f : ThresholdHilbert) : representative f ∈ closedSpaceᗮ :=
  closedSpace.sub_starProjection_mem_orthogonal f

private theorem representative_norm_le (f v : ThresholdHilbert) (hv : v ∈ closedSpace) :
    ‖representative f‖^2 ≤ ‖f - v‖^2 := by
  let p := closedSpace.starProjection f
  have horth := (closedSpace.mem_orthogonal _).mp (representative_mem f) (p - v)
    (closedSpace.sub_mem (closedSpace.starProjection_apply_mem f) hv)
  have he : f - v = (p - v) + representative f := by change f - v = (p - v) + (f - p); abel
  rw [he, norm_add_sq_real, horth]
  linarith only [sq_nonneg ‖p - v‖]

/-- Centered representer of evaluation at a positive Pareto site. -/
def siteContrast (k : ℕ) (hk : 0 < k) : ThresholdHilbert :=
  (positiveWeight k)⁻¹ • hilbertAtom k hk - hilbertOne

private theorem siteContrast_pair (k : ℕ) (hk : 0 < k) (v : ThresholdHilbert) :
    inner ℝ v (siteContrast k hk) = hilbertSequence v k - inner ℝ v hilbertOne := by
  have hw : 0 < positiveWeight k := by unfold positiveWeight; positivity
  rw [siteContrast, inner_sub_right, real_inner_smul_right,
    show inner ℝ v (hilbertAtom k hk) = _ from
      (real_inner_comm ..).trans (hilbertAtom_inner k hk v),
    ← mul_assoc, inv_mul_cancel₀ hw.ne', one_mul]

private theorem residual_site_pair (k : ℕ) (hk : 0 < k) :
    inner ℝ (representative hilbertOne) (representative (siteContrast k hk)) =
      -(1 - limitEnergy) * (hilbertSequence normalizedScreenedTwo k - 1) := by
  let z := siteContrast k hk
  have horth := (closedSpace.mem_orthogonal _).mp (representative_mem hilbertOne)
    _ (closedSpace.starProjection_apply_mem z)
  have hz : inner ℝ hilbertOne z = 0 := by
    rw [siteContrast_pair, hilbertOne_sequence, zeroAnchor, if_neg hk.ne',
      real_inner_self_eq_norm_sq, hilbertOne_norm_sq, sub_self]
  change inner ℝ (representative hilbertOne) (z - closedSpace.starProjection z) = _
  rw [inner_sub_right, (real_inner_comm ..).trans horth, sub_zero]
  change inner ℝ (hilbertOne - limitProjection) z = _
  rw [inner_sub_left, hz, limitProjection_eq_scaled_screenedTwo, real_inner_smul_left,
    siteContrast_pair, normalizedScreenedTwo_mean]
  ring

/-- Every coordinate of u minus one is the signed difference of two squared
quotient norms, divided by four times the scale times the limiting mean mass. -/
theorem site_quotient_polarization (k : ℕ) (hk : 0 < k) (t : ℝ) :
    4 * t * (1 - limitEnergy) * (hilbertSequence normalizedScreenedTwo k - 1) =
      ‖representative (t • hilbertOne - siteContrast k hk)‖^2 -
        ‖representative (t • hilbertOne + siteContrast k hk)‖^2 := by
  rw [map_sub, map_add, map_smul, norm_sub_sq_real, norm_add_sq_real, real_inner_smul_left,
    residual_site_pair]
  ring

/-- Finite legal trials give both signs of a certified coordinate enclosure. -/
theorem site_between_trial_errors (k : ℕ) (hk : 0 < k) (t : ℝ) (plus minus : ThresholdHilbert)
    (hp : plus ∈ closedSpace) (hm : minus ∈ closedSpace) :
    -‖(t • hilbertOne + siteContrast k hk) - plus‖^2 ≤
      4 * t * (1 - limitEnergy) * (hilbertSequence normalizedScreenedTwo k - 1) ∧
      4 * t * (1 - limitEnergy) * (hilbertSequence normalizedScreenedTwo k - 1) ≤
        ‖(t • hilbertOne - siteContrast k hk) - minus‖^2 := by
  rw [site_quotient_polarization k hk t]
  constructor
  · linarith only [representative_norm_le (t • hilbertOne + siteContrast k hk) plus hp,
      sq_nonneg ‖representative (t • hilbertOne - siteContrast k hk)‖]
  · linarith only [representative_norm_le (t • hilbertOne - siteContrast k hk) minus hm,
      sq_nonneg ‖representative (t • hilbertOne + siteContrast k hk)‖]

/-- The first-site experiment uses two explicit physical profiles. -/
theorem first_site_profiles (j : ℕ) (hj : 0 < j) :
    hilbertSequence ((2 : ℝ) • hilbertOne + siteContrast 1 (by decide)) j =
      1 + (if j = 1 then 2 else 0) ∧
    hilbertSequence ((2 : ℝ) • hilbertOne - siteContrast 1 (by decide)) j =
      3 - (if j = 1 then 2 else 0) := by
  have h1 : anchoredEvaluationCLM j hilbertOne = 1 := by
    simp [anchoredEvaluationCLM_apply, hilbertOne_sequence, zeroAnchor, hj.ne']
  have ha : anchoredEvaluationCLM j (hilbertAtom 1 (by decide)) = if j = 1 then 1 else 0 := by
    rw [anchoredEvaluationCLM_apply, hilbertAtom_sequence]
  simp only [← anchoredEvaluationCLM_apply, siteContrast, map_add, map_sub, map_smul,
    h1, ha, smul_eq_mul]
  by_cases he : j = 1 <;> norm_num [positiveWeight, he]

/-- Any three legal trials with certified errors yield an interval for the
actual first coordinate, regardless of whether the boundary vanishes. -/
theorem first_site_interval (v p m : ThresholdHilbert) (hv : v ∈ closedSpace)
    (hp : p ∈ closedSpace) (hm : m ∈ closedSpace) (e a b : ℝ) (he : e < 1)
    (hv' : ‖hilbertOne - v‖^2 ≤ e)
    (hp' : ‖((2 : ℝ) • hilbertOne + siteContrast 1 (by decide)) - p‖^2 ≤ a)
    (hm' : ‖((2 : ℝ) • hilbertOne - siteContrast 1 (by decide)) - m‖^2 ≤ b) :
    1 - a / (8 * (1 - e)) ≤ hilbertSequence normalizedScreenedTwo 1 ∧
    hilbertSequence normalizedScreenedTwo 1 ≤ 1 + b / (8 * (1 - e)) := by
  have hE : limitEnergy ≤ e := (representative_norm_le hilbertOne v hv).trans hv'
  have hscale : 0 < 8 * (1 - e) := by linarith
  have h := site_between_trial_errors 1 (by decide) 2 p m hp hm
  have ha := (sq_nonneg _).trans hp'
  have hb := (sq_nonneg _).trans hm'
  let u1 := hilbertSequence normalizedScreenedTwo 1
  have hlow : -a ≤ 8 * (1 - limitEnergy) * (u1 - 1) := by
    change -a ≤ 8 * (1 - limitEnergy) * (hilbertSequence normalizedScreenedTwo 1 - 1)
    linarith only [h.1, hp']
  have hhigh : 8 * (1 - limitEnergy) * (u1 - 1) ≤ b := by
    change 8 * (1 - limitEnergy) * (hilbertSequence normalizedScreenedTwo 1 - 1) ≤ b
    linarith only [h.2, hm']
  change 1 - a / _ ≤ u1 ∧ u1 ≤ 1 + b / _
  constructor
  · suffices H : 1 - u1 ≤ a / (8 * (1 - e)) by linarith
    apply (le_div_iff₀ hscale).mpr
    by_cases hs : u1 ≤ 1
    · nlinarith only [hlow, mul_nonneg (sub_nonneg.mpr hE) (sub_nonneg.mpr hs)]
    · exact (mul_nonpos_of_nonpos_of_nonneg (by linarith only [hs]) hscale.le).trans ha
  · suffices H : u1 - 1 ≤ b / (8 * (1 - e)) by linarith
    apply (le_div_iff₀ hscale).mpr
    by_cases hs : 1 ≤ u1
    · nlinarith only [hhigh, mul_nonneg (sub_nonneg.mpr hE) (sub_nonneg.mpr hs)]
    · exact (mul_nonpos_of_nonpos_of_nonneg (by linarith only [hs]) hscale.le).trans hb

end RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.DigammaSection
