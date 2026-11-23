import RiemannResearch.RH.MixedConductorStrictDescent
import RiemannResearch.RH.NearbyDilationGram
import RiemannResearch.RH.PeriodicDilationAverages
import RiemannResearch.RH.PrimeReciprocalTail
import RiemannResearch.RH.TernaryMixedOrbitObstruction

/-!
# Prime multiples of mixed conductors in a fixed finite fit

The dilation term pairs to order 1/p against every fixed finite legal
vector when the dilated packet has Pareto mean zero. The undilated term
supplies a divergent series of squared correlations whenever it is
detected. Once the base conductor is fitted, that term vanishes.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake
open CoefficientStabilization CaptureGains

private theorem mixed_packet_mem_window {q B : ℕ} (hq : 1 < q) (hmix : ¬ IsPrimePow q)
    (hle : q ≤ B) : ramanujanPacketHilbert q ∈ mixedSpace (Finset.Icc 2 B) :=
  Submodule.subset_span ⟨⟨q, Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨by omega, hle⟩, hmix⟩⟩, rfl⟩

theorem mixed_packet_pair_fitted {q B : ℕ} (hq : 1 < q) (hmix : ¬ IsPrimePow q)
    (hle : q ≤ B) : inner ℝ (ramanujanPacketHilbert q) (fixedTwoTrial B) = 0 := by
  let S := mixedSpace (Finset.Icc 2 B)
  have ho : fixedTwoTrial B ∈ Sᗮ :=
    S.orthogonal.smul_mem _ (S.sub_starProjection_mem_orthogonal _)
  exact (S.mem_orthogonal _).mp ho _ (mixed_packet_mem_window hq hmix hle)

/-- Every finite fit detects some mixed packet strictly beyond its own cutoff. -/
theorem exists_mixed_packet_pair_ne_zero (B : ℕ) :
    ∃ q : ℕ, B < q ∧ 1 < q ∧ ¬ IsPrimePow q ∧
      inner ℝ (ramanujanPacketHilbert q) (fixedTwoTrial B) ≠ 0 := by
  by_contra! h
  let v := fixedTwoTrial B
  let F := innerSL ℝ v
  have hzero (q : ℕ) (hq : 1 < q) (hmix : ¬ IsPrimePow q) :
      inner ℝ (ramanujanPacketHilbert q) v = 0 := by
    rcases le_or_gt q B with hle | hlt
    · exact mixed_packet_pair_fitted hq hmix hle
    · exact h q hlt hq hmix
  have hker : mixedClosure ≤ F.ker := by
    apply Submodule.topologicalClosure_minimal
    · apply iSup_le
      intro N
      apply Submodule.span_le.mpr
      rintro _ ⟨q, rfl⟩
      obtain ⟨hi, hm⟩ := Finset.mem_filter.mp q.property
      change inner ℝ v (ramanujanPacketHilbert q.val) = 0
      exact (real_inner_comm ..).trans (hzero q.val (Finset.mem_Icc.mp hi).1 hm)
    · exact F.isClosed_ker
  have hd := fixedTwoTrial_sub_screenedTwo_mem_mixedClosure B
  have hv : inner ℝ v (v - normalizedScreenedTwo) = 0 := hker hd
  have hu : normalizedScreenedTwo ∈ mixedClosureᗮ :=
    mixedClosure.orthogonal.smul_mem _ (fullScreening_mem_orthogonal _)
  have hx := (mixedClosure.mem_orthogonal _).mp hu _ hd
  have hx' : inner ℝ normalizedScreenedTwo (v - normalizedScreenedTwo) = 0 :=
    (real_inner_comm ..).trans hx
  have hz : inner ℝ (v - normalizedScreenedTwo) (v - normalizedScreenedTwo) = 0 := by
    rw [inner_sub_left, hv, hx', sub_self]
  exact fixedTwoTrial_ne_screened B (sub_eq_zero.mp (inner_self_eq_zero.mp hz))

/-- The coefficient responsible for a fixed prime-family divergence is
bounded uniformly over all mixed directions by the distance to the screened section. -/
theorem normalized_mixed_pair_le_tail (B : ℕ) {y : ThresholdHilbert} (hy : y ∈ mixedClosure) :
    |inner ℝ y (fixedTwoTrial B)| / ‖y‖ ≤ ‖fixedTwoTrial B - normalizedScreenedTwo‖ := by
  have hu : normalizedScreenedTwo ∈ mixedClosureᗮ :=
    mixedClosure.orthogonal.smul_mem _ (fullScreening_mem_orthogonal _)
  have h := abs_real_inner_le_norm y (fixedTwoTrial B - normalizedScreenedTwo)
  rw [inner_sub_right, (mixedClosure.mem_orthogonal _).mp hu y hy, sub_zero] at h
  by_cases hz : y = 0
  · simp [hz]
  · exact (div_le_iff₀ (norm_pos_iff.mpr hz)).mpr (by rwa [mul_comm])

/-- Even an arbitrary moving choice of mixed test packet has vanishing
absolute normalized pairing against the updated mean-one fits. -/
theorem moving_normalized_mixed_pair_tendsto_zero (y : ℕ → ThresholdHilbert)
    (hy : ∀ B, y B ∈ mixedClosure) :
    Filter.Tendsto (fun B => |inner ℝ (y B) (fixedTwoTrial B)| / ‖y B‖)
      Filter.atTop (nhds 0) := by
  apply squeeze_zero (fun B => div_nonneg (abs_nonneg _) (norm_nonneg _))
    (fun B => normalized_mixed_pair_le_tail B (hy B))
  simpa using (fixedTwoTrial_tendsto.sub_const normalizedScreenedTwo).norm

/-- The prime multiplication recurrence on the original Hilbert packets. -/
theorem packet_prime_mul_sub_dilation {p q : ℕ} (hp : p.Prime) (hq : 1 < q) (hlt : q < p) :
    ramanujanPacketHilbert (p*q) =
      hilbertDilation p hp.pos (ramanujanPacketHilbert q) - ramanujanPacketHilbert q := by
  apply hilbertSequence_injective
  funext k
  rw [← anchoredEvaluationCLM_apply, ← anchoredEvaluationCLM_apply, map_sub]
  simp only [anchoredEvaluationCLM_apply, hilbertDilation_sequence,
    hilbertSequence_ramanujanPacketHilbert]
  exact ramanujanPacket_mul_prime_of_not_dvd p q k hp hq
    (fun hd => (not_le.mpr hlt) (Nat.le_of_dvd (by omega) hd))

/-- One constant controls all mean-zero inputs against the fixed finite fit. -/
theorem finite_fit_dilated_pair_bound (n : ℕ) {v : ThresholdHilbert} (hv : v ∈ finiteSpace n) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (f : ThresholdHilbert), inner ℝ f hilbertOne = 0 →
      ∀ (m : ℕ) (hm : 0 < m),
      |inner ℝ (hilbertDilation m hm f) v| ≤ K * ‖f‖ / (m : ℝ) := by
  obtain ⟨μ, K, hK, hb⟩ := PeriodicDilation.finiteSpace_adjoint_bound n hv
  refine ⟨K, hK, fun f hf m hm => ?_⟩
  have he : inner ℝ (hilbertDilation m hm f) v =
      inner ℝ f (hilbertDilationAdjoint m hm v - μ • hilbertOne) := by
    rw [inner_sub_right, real_inner_smul_right, hf, mul_zero, sub_zero]
    exact (ContinuousLinearMap.adjoint_inner_right (hilbertDilationContinuous m hm) f v).symm
  rw [he]
  calc
    _ ≤ ‖f‖ * _ := abs_real_inner_le_norm _ _
    _ ≤ ‖f‖ * (K / (m : ℝ)) := mul_le_mul_of_nonneg_left (hb m hm) (norm_nonneg _)
    _ = _ := by ring

private theorem mixed_mean_zero {q : ℕ} (hq : 1 < q) (hmix : ¬ IsPrimePow q) :
    inner ℝ (ramanujanPacketHilbert q) hilbertOne = 0 :=
  ((mixedSpace (Finset.Icc 2 q)).mem_orthogonal _).mp (one_mem_mixed_orthogonal _)
    _ (mixed_packet_mem_window hq hmix le_rfl)

/-- When the base conductor is fitted the prime-multiple correlation is purely
the dilation term, so its constant term disappears exactly. -/
theorem fitted_prime_multiple_bound (B : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (p q : ℕ), p.Prime → 1 < q → ¬ IsPrimePow q →
      q ≤ B → q < p →
      |inner ℝ (ramanujanPacketHilbert (p*q)) (fixedTwoTrial B)| ≤
        K * ‖ramanujanPacketHilbert q‖ / (p : ℝ) := by
  obtain ⟨K, hK, hb⟩ := finite_fit_dilated_pair_bound _ (fixedTwoTrial_mem_finiteSpace B)
  refine ⟨K, hK, fun p q hp hq hmix hfit hlt => ?_⟩
  rw [packet_prime_mul_sub_dilation hp hq hlt, inner_sub_left,
    mixed_packet_pair_fitted hq hmix hfit, sub_zero]
  exact hb _ (mixed_mean_zero hq hmix) p hp.pos

private theorem prime_multiple_norm_le {p q : ℕ} (hp : p.Prime) (hq : 1 < q) (hlt : q < p) :
    ‖ramanujanPacketHilbert (p*q)‖ ^ 2 ≤ 4 * p * ‖ramanujanPacketHilbert q‖ ^ 2 := by
  let f := ramanujanPacketHilbert q
  let x := hilbertDilation p hp.pos f
  have he : ‖x‖ ^ 2 = (p : ℝ) * ‖f‖ ^ 2 := hilbertDilation_norm_sq _ _ _
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  rw [packet_prime_mul_sub_dilation hp hq hlt]
  have hs := (sq_le_sq₀ (norm_nonneg (x-f)) (add_nonneg (norm_nonneg x) (norm_nonneg f))).mpr
    (norm_sub_le x f)
  change ‖x-f‖ ^ 2 ≤ 4 * (p : ℝ) * ‖f‖ ^ 2
  nlinarith only [hs, he, sq_nonneg (‖x‖ - ‖f‖), mul_nonneg (sub_nonneg.mpr hp1) (sq_nonneg ‖f‖)]

private theorem prime_multiple_norm_lower {p q : ℕ} (hp : p.Prime) (hp4 : 4 ≤ p)
    (hq : 1 < q) (hlt : q < p) :
    (p : ℝ) * ‖ramanujanPacketHilbert q‖^2 ≤ 4 * ‖ramanujanPacketHilbert (p * q)‖^2 := by
  let f := ramanujanPacketHilbert q
  let x := hilbertDilation p hp.pos f
  let y := ramanujanPacketHilbert (p * q)
  have hxy : x = y + f := by dsimp [y, x, f]; rw [packet_prime_mul_sub_dilation hp hq hlt]; abel
  have hx : ‖x‖^2 = (p : ℝ) * ‖f‖^2 := hilbertDilation_norm_sq _ _ _
  have htri : ‖x‖ ≤ ‖y‖ + ‖f‖ := hxy ▸ norm_add_le y f
  have hs := (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr htri
  have hpR : (4 : ℝ) ≤ p := by exact_mod_cast hp4
  change (p : ℝ) * ‖f‖^2 ≤ 4 * ‖y‖^2
  nlinarith only [hs, hx, sq_nonneg (‖y‖ - ‖f‖), mul_nonneg (sub_nonneg.mpr hpR) (sq_nonneg ‖f‖)]

/-- Once q is fitted, the squared correlation divided by the packet norm
squared has a cubic upper bound, uniform in every fitted mixed q. -/
theorem fitted_prime_score_cubic_bound (B : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (p q : ℕ), p.Prime → 4 ≤ p → 1 < q → ¬ IsPrimePow q →
      q ≤ B → q < p →
      (inner ℝ (ramanujanPacketHilbert (p * q)) (fixedTwoTrial B))^2 /
        ‖ramanujanPacketHilbert (p * q)‖^2 ≤ 4 * K^2 / (p : ℝ)^3 := by
  obtain ⟨K, hK, hb⟩ := fitted_prime_multiple_bound B
  refine ⟨K, hK, fun p q hp hp4 hq hm hB hlt => ?_⟩
  let f := ramanujanPacketHilbert q
  let y := ramanujanPacketHilbert (p * q)
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  change (inner ℝ y (fixedTwoTrial B))^2 / ‖y‖^2 ≤ 4 * K^2 / (p : ℝ)^3
  by_cases hz : y = 0
  · simpa [hz] using (show 0 ≤ 4 * K^2 / (p : ℝ)^3 by positivity)
  have hs := (sq_le_sq₀ (abs_nonneg _) (show 0 ≤ K * ‖f‖ / (p : ℝ) by positivity)).mpr
    (hb p q hp hq hm hB hlt)
  rw [sq_abs] at hs
  have hprod : (p : ℝ)^3 * (inner ℝ y (fixedTwoTrial B))^2 ≤ 4 * K^2 * ‖y‖^2 := calc
    _ ≤ (p : ℝ)^3 * (K * ‖f‖ / (p : ℝ))^2 := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = K^2 * ((p : ℝ) * ‖f‖^2) := by field_simp [hpR.ne']
    _ ≤ K^2 * (4 * ‖y‖^2) := mul_le_mul_of_nonneg_left
      (prime_multiple_norm_lower hp hp4 hq hlt) (sq_nonneg _)
    _ = _ := by ring
  apply (div_le_div_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hz)) (by positivity)).mpr
  linarith only [hprod]

/-- At any fixed later stage containing q, the very same prime family now
has a summable series of squared correlations. -/
theorem fitted_prime_scores_summable (B q N : ℕ) (hq : 1 < q) (hm : ¬ IsPrimePow q)
    (hB : q ≤ B) (hqN : q < N) (hN : 4 ≤ N) :
    Summable (fun p : {p : ℕ // p.Prime ∧ N ≤ p} =>
      (inner ℝ (ramanujanPacketHilbert (p.val * q)) (fixedTwoTrial B))^2 /
        ‖ramanujanPacketHilbert (p.val * q)‖^2) := by
  obtain ⟨K, _, hb⟩ := fitted_prime_score_cubic_bound B
  have hs : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ)^3) :=
    Real.summable_one_div_nat_pow.mpr (by decide : 1 < 3)
  have hr := (hs.comp_injective
    (Subtype.val_injective (p := fun p : ℕ => p.Prime ∧ N ≤ p))).mul_left (4 * K^2)
  apply Summable.of_nonneg_of_le (fun p => div_nonneg (sq_nonneg _) (sq_nonneg _)) _ hr
  intro p
  change _ ≤ 4 * K^2 * (1 / (p.val : ℝ)^3)
  rw [mul_one_div]
  exact hb p.val q p.property.1 (hN.trans p.property.2) hq hm hB (hqN.trans_le p.property.2)

/-- A base packet detected by a fixed legal vector produces a divergent series
of normalized squared correlations along distinct prime multiples. -/
theorem not_summable_prime_multiple_scores (n : ℕ) {v : ThresholdHilbert} (hv : v ∈ finiteSpace n)
    {q : ℕ} (hq : 1 < q) (hmix : ¬ IsPrimePow q)
    (hc : inner ℝ (ramanujanPacketHilbert q) v ≠ 0) :
    ∃ N : ℕ, q < N ∧ ¬ Summable (fun p : {p : ℕ // p.Prime ∧ N ≤ p} =>
      (inner ℝ (ramanujanPacketHilbert (p.val*q)) v)^2 / ‖ramanujanPacketHilbert (p.val*q)‖^2) := by
  let f := ramanujanPacketHilbert q
  let c := |inner ℝ f v|
  have hc0 : 0 < c := abs_pos.mpr hc
  have hf : f ≠ 0 := fun h => hc (by change inner ℝ f v = 0; simp [h])
  have hf2 : 0 < ‖f‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hf)
  obtain ⟨K, hK, hb⟩ := finite_fit_dilated_pair_bound n hv
  obtain ⟨A, hA⟩ := exists_nat_gt (2*K*‖f‖/c)
  let N := max (q+1) A
  refine ⟨N, lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left ..), ?_⟩
  let a := (c/2)^2/(4*‖f‖^2)
  have ha : 0 < a := by dsimp [a]; positivity
  intro hsum
  apply not_summable_prime_reciprocal_tail N
  apply Summable.of_nonneg_of_le (fun p => by positivity) _ (hsum.mul_left a⁻¹)
  intro z
  let p := z.val
  have hp : p.Prime := z.property.1
  have hlt : q < p := lt_of_lt_of_le (Nat.lt_succ_self q) ((le_max_left _ A).trans z.property.2)
  have hpR : 0 < (p:ℝ) := by exact_mod_cast hp.pos
  have hcA := (div_lt_iff₀ hc0).mp hA
  have hap : (A:ℝ) ≤ p := by exact_mod_cast ((le_max_right (q+1) A).trans z.property.2)
  have hd : |inner ℝ (hilbertDilation p hp.pos f) v| ≤ c/2 := by
    apply (hb f (mixed_mean_zero hq hmix) p hp.pos).trans
    apply (div_le_iff₀ hpR).mpr
    nlinarith only [hcA, mul_nonneg (sub_nonneg.mpr hap) hc0.le]
  let y := ramanujanPacketHilbert (p*q)
  have hcorr : c/2 ≤ |inner ℝ y v| := by
    have he : inner ℝ f v = inner ℝ (hilbertDilation p hp.pos f) v - inner ℝ y v := by
      dsimp [y, f]
      rw [packet_prime_mul_sub_dilation hp hq hlt, inner_sub_left]
      ring
    have htri := abs_sub_le (inner ℝ (hilbertDilation p hp.pos f) v) 0 (inner ℝ y v)
    simp only [sub_zero, zero_sub, abs_neg, ← he] at htri
    change |inner ℝ f v| / 2 ≤ _
    dsimp only [c] at hd
    linarith
  have hys : 0 < ‖y‖^2 := by
    apply sq_pos_of_pos (norm_pos_iff.mpr _)
    intro h
    simp [h] at hcorr
    linarith
  have hcorr2 := (sq_le_sq₀ (by positivity : 0 ≤ c/2) (abs_nonneg _)).mpr hcorr
  rw [sq_abs] at hcorr2
  have hyn : ‖y‖^2 ≤ 4 * (p:ℝ) * ‖f‖^2 := prime_multiple_norm_le hp hq hlt
  change 1 / (p:ℝ) ≤ a⁻¹ * ((inner ℝ y v)^2 / ‖y‖^2)
  rw [← div_eq_inv_mul]
  apply (le_div_iff₀ ha).mpr
  apply (le_div_iff₀ hys).mpr
  calc
    _ = a / (p:ℝ) * ‖y‖^2 := by ring
    _ ≤ a / (p:ℝ) * (4 * p * ‖f‖^2) := mul_le_mul_of_nonneg_left hyn (by positivity)
    _ = (c/2)^2 := by dsimp [a]; field_simp [hpR.ne', hf2.ne']
    _ ≤ _ := hcorr2

/-- At each finite cutoff there is a single mixed base conductor whose
prime multiples have divergent correlation shares against that fixed fit. -/
theorem fixed_fit_prime_shares_not_summable (B : ℕ) :
    ∃ q N : ℕ, B < q ∧ 1 < q ∧ ¬ IsPrimePow q ∧ q < N ∧
      ¬ Summable (fun p : {p : ℕ // p.Prime ∧ N ≤ p} =>
        correlationShare B (ramanujanPacketHilbert (p.val * q))) := by
  obtain ⟨q, hB, hq, hm, hc⟩ := exists_mixed_packet_pair_ne_zero B
  obtain ⟨N, hN, hd⟩ := not_summable_prime_multiple_scores _ (fixedTwoTrial_mem_finiteSpace B)
    hq hm hc
  refine ⟨q, N, hB, hq, hm, hN, fun h => hd ?_⟩
  apply (h.mul_left (deficit B / (Real.log 2)^2)).congr
  intro p
  have hpq : 1 < p.val * q := hq.trans_le (Nat.le_mul_of_pos_left q p.property.1.pos)
  have hmix : ¬ IsPrimePow (p.val * q) :=
    fun hpow => hm (hpow.dvd (dvd_mul_left q p.val) (by omega))
  have hy := mixed_packet_mem_window hpq hmix le_rfl
  unfold correlationShare
  rw [finite_mixed_test_pairing B _ _ hy]
  field_simp [(deficit_pos B).ne', (Real.log_pos (by norm_num : (1:ℝ) < 2)).ne']

/-- Along successive updated fits, every normalized test direction has a
summable series of absolute energy gains. The proof charges each direction
to its own one-step orthogonal projection increment. -/
theorem updated_absolute_scores_summable (y : ℕ → ThresholdHilbert)
    (hy : ∀ k, y k ∈ mixedSpace (Finset.Icc 2 (k + 1))) :
    Summable (fun k => (inner ℝ (y k) (finiteScreening k centeredParity))^2 / ‖y k‖^2) := by
  have hsum (N : ℕ) : ∑ k ∈ Finset.range N, gain k (k + 1) = deficit 0 - deficit N := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      linarith only [deficit_step (Nat.le_succ N)]
  have hg : Summable (fun k => gain k (k + 1)) := by
    apply summable_of_sum_range_le (fun k => sq_nonneg _) (c := deficit 0)
    intro N
    change (∑ k ∈ Finset.range N, gain k (k + 1)) ≤ deficit 0
    rw [hsum]
    linarith only [deficit_pos N]
  apply Summable.of_nonneg_of_le (fun k => div_nonneg (sq_nonneg _) (sq_nonneg _)) _ hg
  intro k
  by_cases h : y k = 0
  · simp [h, gain]
  · exact (div_le_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr h))).mpr
      (correlation_sq_le_gain_mul_norm_sq k (k + 1) _ (hy k))

/-- A compensated pair of adjacent dilations tests the actual block gain.
The denominator is the explicit harmonic jump sum plus the uniform Gram remainder. -/
theorem adjacent_dilation_block_gain (B m q : ℕ) (hm : 0 < m)
    (hq : 1 < q) (hmix : ¬ IsPrimePow q) (C : ℝ) (hC : ∀ k, |ramanujanPacket q k| ≤ C) :
    let f := ramanujanPacketHilbert q
    let y := hilbertDilation (m + 1) (Nat.succ_pos _) f - hilbertDilation m hm f
    (inner ℝ y (finiteScreening B centeredParity))^2 ≤
      gain B (max B (q * (m + 1))) *
        (nearbyDilationHarmonicMain (ramanujanPacket q) (ramanujanPacket q) m + 15 * C * C) := by
  let f := ramanujanPacketHilbert q
  let y := hilbertDilation (m + 1) (Nat.succ_pos _) f - hilbertDilation m hm f
  let N := max B (q * (m + 1))
  have hmem (s : ℕ) (hs : 0 < s) (hsm : s ≤ m + 1) :
      hilbertDilation s hs f ∈ mixedSpace (Finset.Icc 2 N) := by
    apply mixedSpace_mono _ (dilated_mixed_packet_mem_window s q hs hq hmix)
    intro d hd
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hd
    exact Finset.mem_Icc.mpr ⟨hlo, hhi.trans ((Nat.mul_le_mul_left q hsm).trans (le_max_right ..))⟩
  have hy : y ∈ mixedSpace (Finset.Icc 2 N) :=
    (mixedSpace _).sub_mem (hmem _ (Nat.succ_pos _) le_rfl) (hmem m hm (Nat.le_succ m))
  have hseq : hilbertSequence y = nearbyDilationPacket (ramanujanPacket q) m := by
    rw [nearbyDilationPacket_eq_dilation]
    simp only [y, f, hilbertSequence_sub, hilbertDilation_sequence,
      hilbertSequence_ramanujanPacketHilbert]
  have hzero : ramanujanPacket q 0 = 0 := by
    rw [← hilbertSequence_ramanujanPacketHilbert]
    simp
  have hnorm : ‖y‖^2 ≤ nearbyDilationHarmonicMain (ramanujanPacket q) (ramanujanPacket q) m +
      15 * C * C := by
    rw [← real_inner_self_eq_norm_sq, hilbert_inner_weighted, hseq]
    linarith only [(abs_le.mp (nearbyDilationGram_harmonic_error_bound hC hC hzero hzero m hm)).2]
  exact (correlation_sq_le_gain_mul_norm_sq B N y hy).trans
    (mul_le_mul_of_nonneg_left hnorm (sq_nonneg _))

private theorem six_pair_ne_zero :
    inner ℝ (ramanujanPacketHilbert 6) (ramanujanPacketHilbert 2) ≠ 0 := by
  rw [real_inner_comm, packet_two_six_inner_and_norm.1]
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have hp : 0 < Real.sqrt 3 := by positivity
  have hlt : (3/4 : ℝ) < Real.pi/(2 * Real.sqrt 3) := by
    apply (lt_div_iff₀ (by positivity)).mpr
    nlinarith only [Real.pi_gt_three, hs, sq_nonneg (Real.sqrt 3 - 2)]
  linarith only [hlt, Real.log_two_lt_d9]

/-- The actual conductor-six orbit exhibits divergent fixed squared
correlations and a strictly positive distance from centered parity. -/
theorem six_orbit_divergence_and_error :
    ∃ N : ℕ, 6 < N ∧
      (¬ Summable (fun p : {p : ℕ // p.Prime ∧ N ≤ p} =>
        (inner ℝ (ramanujanPacketHilbert (p.val * 6)) (ramanujanPacketHilbert 2))^2 /
        ‖ramanujanPacketHilbert (p.val * 6)‖^2)) ∧
      (∀ p : ℕ, p.Prime → 6 < p → ramanujanPacketHilbert (p * 6) ∈ TernaryOrbit.sixOrbit) ∧
      ∀ x ∈ TernaryOrbit.sixOrbit, (49 / 1000 : ℝ) < ‖centeredParity - x‖^2 := by
  have hv : ramanujanPacketHilbert 2 ∈ finiteSpace 1 := by
    change ramanujanPacketHilbert 2 ∈
      Submodule.span ℝ (Set.range (fun i : Fin 1 => residueAtom i.val))
    rw [← finitePacket_span_eq]
    exact Submodule.subset_span ⟨(0 : Fin 1), rfl⟩
  have hm : ¬ IsPrimePow 6 := by decide +kernel
  obtain ⟨N, hN, hd⟩ := not_summable_prime_multiple_scores _ hv (by decide : 1 < 6) hm
    six_pair_ne_zero
  refine ⟨N, hN, hd, ?_, fun x hx => TernaryOrbit.sixOrbit_error_gt hx⟩
  have horb (m : ℕ) (hm : 0 < m) :
      hilbertDilation m hm (ramanujanPacketHilbert 6) ∈ TernaryOrbit.sixOrbit := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
    exact Submodule.le_topologicalClosure _
      (Submodule.subset_span ⟨k, rfl⟩)
  intro p hp hlt
  rw [packet_prime_mul_sub_dilation hp (by decide) hlt]
  apply TernaryOrbit.sixOrbit.sub_mem (horb p hp.pos)
  simpa only [hilbertDilation_one] using horb 1 (by decide)

end RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake
