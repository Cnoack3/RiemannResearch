import RiemannResearch.RH.ScreenedParityPhysicalBounds

/-! # Finite mixed projection bounds for the limiting screened parity packet -/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.Pareto.PrimePowerSchur
open CoefficientStabilization

/-- The remaining displacement after a finite mixed projection lies in the full
mixed space and is perpendicular to the centered limiting packet. -/
theorem fixedTwoTrial_gap_inner_centered (L : ℕ) :
    inner ℝ (fixedTwoTrial L - normalizedScreenedTwo)
      (normalizedScreenedTwo - hilbertOne) = 0 := by
  let K := mixedSpace (Finset.Icc 2 L)
  let J := ramanujanPacketHilbert 2
  have hgap : fixedTwoTrial L - normalizedScreenedTwo ∈ mixedClosure := by
    change (Real.log 2)⁻¹ • (J - K.starProjection J) -
      (Real.log 2)⁻¹ • (J - mixedClosure.starProjection J) ∈ _
    rw [← smul_sub, show (J - K.starProjection J) - (J - mixedClosure.starProjection J) =
        mixedClosure.starProjection J - K.starProjection J by abel]
    exact mixedClosure.smul_mem _ (mixedClosure.sub_mem
      (mixedClosure.starProjection_apply_mem J)
      (mixedSpace_window_le_closure L (K.starProjection_apply_mem J)))
  have hu : normalizedScreenedTwo ∈ mixedClosureᗮ :=
    mixedClosure.orthogonal.smul_mem _ (fullScreening_mem_orthogonal J)
  exact (mixedClosure.mem_orthogonal _).mp
    (mixedClosure.orthogonal.sub_mem hu one_mem_mixedClosure_orthogonal) _ hgap

/-- The centered limiting packet lies on the sphere with diameter the segment
from zero to the centered finite packet. This is its doubled-radius form. -/
theorem fixedTwoTrial_diameter_norm (L : ℕ) :
    ‖(normalizedScreenedTwo - hilbertOne) - (fixedTwoTrial L - normalizedScreenedTwo)‖ =
      ‖fixedTwoTrial L - hilbertOne‖ := by
  let a := normalizedScreenedTwo - hilbertOne
  let b := fixedTwoTrial L - normalizedScreenedTwo
  have hi : inner ℝ a b = 0 := (real_inner_comm _ _).trans (fixedTwoTrial_gap_inner_centered L)
  have h : ‖a - b‖ ^ 2 = ‖a + b‖ ^ 2 := by
    rw [norm_sub_sq_real, norm_add_sq_real, hi]
    ring
  have ha : a + b = fixedTwoTrial L - hilbertOne := by dsimp [a, b]; abel
  rw [← ha]
  change ‖a - b‖ = ‖a + b‖
  nlinarith [norm_nonneg (a-b), norm_nonneg (a+b)]

/-- Every continuous linear functional gives an interval for the actual limiting
value whose center and width depend only on the finite packet. -/
theorem fixedTwoTrial_functional_diameter_bound (L : ℕ) (F : ThresholdHilbert →L[ℝ] ℝ) :
    |2 * F normalizedScreenedTwo - F hilbertOne - F (fixedTwoTrial L)| ≤
      ‖F‖ * ‖fixedTwoTrial L - hilbertOne‖ := by
  have h := F.le_opNorm ((normalizedScreenedTwo - hilbertOne) -
    (fixedTwoTrial L - normalizedScreenedTwo))
  rw [fixedTwoTrial_diameter_norm, Real.norm_eq_abs] at h
  simpa only [map_sub, show ∀ a b c : ℝ, (a - b) - (c - a) = 2*a-b-c by
    intro a b c; ring] using h

/-- Subtracting any finite mixed vector and any constant direction from the
Riesz representative reduces the radius without changing the expression being
bounded. Taking the best such correction gives the finite Gram certificate. -/
theorem fixedTwoTrial_reduced_pairing_bound (L : ℕ) (v m : ThresholdHilbert)
    (hm : m ∈ mixedSpace (Finset.Icc 2 L)) (c : ℝ) :
    |2 * inner ℝ v normalizedScreenedTwo - inner ℝ v hilbertOne -
      inner ℝ v (fixedTwoTrial L)| ≤
      ‖v - m - c • hilbertOne‖ * ‖fixedTwoTrial L - hilbertOne‖ := by
  let K := mixedSpace (Finset.Icc 2 L)
  let J := ramanujanPacketHilbert 2
  let d := (normalizedScreenedTwo - hilbertOne) - (fixedTwoTrial L - normalizedScreenedTwo)
  have hu : normalizedScreenedTwo ∈ mixedClosureᗮ :=
    mixedClosure.orthogonal.smul_mem _ (fullScreening_mem_orthogonal J)
  have hL : fixedTwoTrial L ∈ Kᗮ :=
    K.orthogonal.smul_mem _ (Submodule.sub_starProjection_mem_orthogonal J)
  have hum := (mixedClosure.mem_orthogonal _).mp hu m (mixedSpace_window_le_closure L hm)
  have hLm := (K.mem_orthogonal _).mp hL m hm
  have h1m := (mixedClosure.mem_orthogonal _).mp one_mem_mixedClosure_orthogonal m
    (mixedSpace_window_le_closure L hm)
  have hmd : inner ℝ m d = 0 := by
    simp only [d, inner_sub_right, hum, hLm, h1m, sub_zero]
  have hmeanL : inner ℝ (fixedTwoTrial L) hilbertOne = 1 := by
    rw [fixedTwoTrial, real_inner_smul_left, screenedPacket_inner_one,
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    norm_num only [Nat.cast_ofNat]
    exact inv_mul_cancel₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have h1d : inner ℝ hilbertOne d = 0 := by
    rw [real_inner_comm]
    simp only [d, inner_sub_left, normalizedScreenedTwo_mean, hmeanL,
      real_inner_self_eq_norm_sq, hilbertOne_norm_sq, sub_self]
  have h := abs_real_inner_le_norm (v - m - c • hilbertOne) d
  rw [inner_sub_left, inner_sub_left, real_inner_smul_left, hmd, h1d, mul_zero,
    sub_zero, sub_zero, show ‖d‖ = _ from fixedTwoTrial_diameter_norm L] at h
  simpa only [d, inner_sub_right, show ∀ a b c : ℝ, (a-b)-(c-a)=2*a-b-c by
    intro a b c; ring] using h

/-- Summing evaluations preserves the joint information of the window. The
operator norm is that of the sum of evaluations. -/
theorem fixedTwoTrial_sites_lower (L : ℕ) (S : Finset ℕ)
    (hpos : ∀ n ∈ S, 0 < n) :
    (S.card : ℝ) + (∑ n ∈ S, hilbertSequence (fixedTwoTrial L) n) -
      ‖∑ n ∈ S, anchoredEvaluationCLM n‖ * ‖fixedTwoTrial L - hilbertOne‖ ≤
    2 * ∑ n ∈ S, hilbertSequence normalizedScreenedTwo n := by
  let F : ThresholdHilbert →L[ℝ] ℝ := ∑ n ∈ S, anchoredEvaluationCLM n
  have hev (v : ThresholdHilbert) : F v = ∑ n ∈ S, hilbertSequence v n := by
    simp [F, anchoredEvaluationCLM_apply]
  have hone : F hilbertOne = (S.card : ℝ) := by
    rw [hev]
    have hseq (n : ℕ) (hn : n ∈ S) : hilbertSequence hilbertOne n = 1 := by
      simp [hilbertOne_sequence, zeroAnchor, (hpos n hn).ne']
    rw [Finset.sum_congr rfl hseq]
    simp
  have h := (abs_le.mp (fixedTwoTrial_functional_diameter_bound L F)).1
  rw [hone, hev, hev] at h
  change (S.card : ℝ) + _ - ‖F‖ * _ ≤ _
  linarith

/-- The Riesz vector for the sum of physical evaluations at sites n+1 for n∈S. -/
def finiteSiteRiesz (S : Finset ℕ) : ThresholdHilbert :=
  ∑ n ∈ S, (paretoWeight n)⁻¹ • paretoPointHilbert n

theorem finiteSiteRiesz_inner (S : Finset ℕ) (v : ThresholdHilbert) :
    inner ℝ (finiteSiteRiesz S) v = ∑ n ∈ S, hilbertSequence v (n+1) := by
  rw [finiteSiteRiesz, sum_inner]
  apply Finset.sum_congr rfl
  intro n hn
  rw [real_inner_smul_left]
  change physicalEvaluationCLM n v = _
  exact physicalEvaluationCLM_apply n v

theorem finiteSiteRiesz_inner_one (S : Finset ℕ) :
    inner ℝ (finiteSiteRiesz S) hilbertOne = (S.card : ℝ) := by
  rw [finiteSiteRiesz_inner]
  calc
    _ = ∑ _n ∈ S, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [hilbertOne_sequence]
      simp [zeroAnchor]
    _ = _ := by simp

theorem finiteSiteRiesz_norm_sq (S : Finset ℕ) :
    ‖finiteSiteRiesz S‖ ^ 2 = ∑ n ∈ S, (paretoWeight n)⁻¹ := by
  rw [← real_inner_self_eq_norm_sq, finiteSiteRiesz_inner]
  apply Finset.sum_congr rfl
  intro n hn
  rw [← anchoredEvaluationCLM_apply, finiteSiteRiesz, map_sum]
  have site (x : ℕ) :
      anchoredEvaluationCLM (n+1) ((paretoWeight x)⁻¹ • paretoPointHilbert x) =
        (paretoWeight x)⁻¹ * (if n+1 = x+1 then 1 else 0) := by
    simp only [map_smul, anchoredEvaluationCLM_apply, hilbertSequence_paretoPoint,
      paretoPointSequence, smul_eq_mul]
  rw [Finset.sum_eq_single n]
  · rw [site]
    simp
  · intro j _ hj
    rw [site]
    simp [Ne.symm hj]
  · intro h
    exact (h hn).elim

/-- The finite projection and the mean remove two exact terms from the squared
norm of the aggregate evaluation functional. -/
theorem finiteSiteRiesz_centered_projection_norm_sq (L : ℕ) (S : Finset ℕ) :
    let v := finiteSiteRiesz S
    let p := (mixedSpace (Finset.Icc 2 L)).starProjection v
    ‖v-p-(S.card : ℝ) • hilbertOne‖ ^ 2 =
      (∑ n ∈ S, (paretoWeight n)⁻¹) - ‖p‖ ^ 2 - (S.card : ℝ) ^ 2 := by
  let K := mixedSpace (Finset.Icc 2 L)
  let v := finiteSiteRiesz S
  let p := K.starProjection v
  change ‖v-p-(S.card : ℝ) • hilbertOne‖ ^ 2 =
    _ - ‖p‖ ^ 2 - (S.card : ℝ) ^ 2
  have hp : p ∈ K := K.starProjection_apply_mem v
  have horth : v-p ∈ Kᗮ := Submodule.sub_starProjection_mem_orthogonal v
  have hpv := (K.mem_orthogonal _).mp horth p hp
  rw [inner_sub_right, real_inner_self_eq_norm_sq, sub_eq_zero, real_inner_comm] at hpv
  have hp1 : inner ℝ p hilbertOne = 0 :=
    (mixedClosure.mem_orthogonal _).mp one_mem_mixedClosure_orthogonal p
      (mixedSpace_window_le_closure L hp)
  have hv1 : inner ℝ v hilbertOne = (S.card : ℝ) := finiteSiteRiesz_inner_one S
  rw [norm_sub_sq_real, norm_sub_sq_real, hpv, finiteSiteRiesz_norm_sq,
    real_inner_smul_right, inner_sub_left, hv1, hp1, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs, hilbertOne_norm_sq]
  ring

/-- A joint physical lower bound using the exact finite projection cost and
the explicitly known mean of the site functional. -/
theorem fixedTwoTrial_sites_gram_lower (L : ℕ) (S : Finset ℕ) :
    let p := (mixedSpace (Finset.Icc 2 L)).starProjection (finiteSiteRiesz S)
    (S.card : ℝ) + (∑ n ∈ S, hilbertSequence (fixedTwoTrial L) (n+1)) -
      Real.sqrt ((∑ n ∈ S, (paretoWeight n)⁻¹) - ‖p‖^2 - (S.card : ℝ)^2) *
        ‖fixedTwoTrial L - hilbertOne‖ ≤
      2 * ∑ n ∈ S, hilbertSequence normalizedScreenedTwo (n+1) := by
  let K := mixedSpace (Finset.Icc 2 L)
  let v := finiteSiteRiesz S
  let p := K.starProjection v
  have h := (abs_le.mp
    (fixedTwoTrial_reduced_pairing_bound L v p (K.starProjection_apply_mem v) (S.card : ℝ))).1
  have hv1 : inner ℝ v hilbertOne = (S.card : ℝ) := finiteSiteRiesz_inner_one S
  rw [hv1, finiteSiteRiesz_inner, finiteSiteRiesz_inner] at h
  have hsq := finiteSiteRiesz_centered_projection_norm_sq L S
  change ‖v-p-(S.card : ℝ) • hilbertOne‖^2 =
    (∑ n ∈ S, (paretoWeight n)⁻¹) - ‖p‖^2 - (S.card : ℝ)^2 at hsq
  change (S.card : ℝ) + _ - Real.sqrt (_ - ‖p‖^2 - (S.card : ℝ)^2) * _ ≤ _
  rw [← hsq, Real.sqrt_sq (norm_nonneg _)]
  linarith

/-- A finite Gram bound on each subset of `m+1` sites certifies the exception
count for the limiting packet. Indices in `window` label the physical sites
`n+1`, as in the finite site Riesz representative. -/
theorem fixedTwoTrial_deep_site_count_le (L m : ℕ) (window : Finset ℕ) (F : ℝ)
    (hcert : ∀ S ⊆ window, S.card = m + 1 →
      let p := (mixedSpace (Finset.Icc 2 L)).starProjection (finiteSiteRiesz S);
      (-2 : ℝ) * F * (S.card : ℝ) ≤
        (S.card : ℝ) + (∑ n ∈ S, hilbertSequence (fixedTwoTrial L) (n + 1)) -
        Real.sqrt ((∑ n ∈ S, (paretoWeight n)⁻¹) - ‖p‖ ^ 2 - (S.card : ℝ) ^ 2) *
          ‖fixedTwoTrial L - hilbertOne‖) :
    (window.filter (fun n => hilbertSequence normalizedScreenedTwo (n + 1) < -F)).card ≤ m := by
  classical
  by_contra h
  let bad := window.filter (fun n => hilbertSequence normalizedScreenedTwo (n + 1) < -F)
  have hcard : m + 1 ≤ bad.card := Nat.succ_le_of_lt (lt_of_not_ge h)
  obtain ⟨S, hSb, hS⟩ := Finset.exists_subset_card_eq hcard
  have hSw : S ⊆ window := fun n hn => (Finset.mem_filter.mp (hSb hn)).1
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  have hsum : (∑ n ∈ S, hilbertSequence normalizedScreenedTwo (n + 1)) <
      ∑ _n ∈ S, (-F) :=
    Finset.sum_lt_sum_of_nonempty hne (fun n hn => (Finset.mem_filter.mp (hSb hn)).2)
  rw [Finset.sum_const, nsmul_eq_mul] at hsum
  have hlow := (hcert S hSw hS).trans (fixedTwoTrial_sites_gram_lower L S)
  linarith only [hsum, hlow]

end RiemannResearch.RH.Pareto.PrimePowerSchur
