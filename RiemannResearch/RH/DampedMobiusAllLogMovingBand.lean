import RiemannResearch.Analysis.IncreasingAbelSplit
import RiemannResearch.Analysis.SqrtLogCutoff
import RiemannResearch.RH.DampedMobiusHalfHilbertAllLogRates
import RiemannResearch.RH.DampedMobiusUniformHalfRange

/-!
# Every fixed logarithmic coefficient in the moving subhalf band

Every fixed coefficient c >= 0 is allowed in
  (1/2 - epsilon) log(M+1) <= c log(6+log(M+1)).
The proof splits centered Abel prefix errors at exp(sqrt(log(M+1))).
The all-logarithmic endpoint theorem supplies a tail exponent k > 2c.
All arithmetic providers are unconditional. Constants may depend on c.
No fixed subhalf infinite-energy assertion is made.
-/

noncomputable section
open Filter Set
open scoped Topology BigOperators

namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis

/-- There is no largest fixed coefficient in the supported
log-logarithmic-over-logarithmic subhalf band. -/
theorem dampedMobius_all_log_subhalf_band_tendsto
    (ε : ℕ → ℝ) (hε : ∀ j, ε j ≤ (1 / 2 : ℝ))
    (M : ℕ → ℕ) (hM : Tendsto M atTop atTop)
    (c : ℝ) (hc : 0 ≤ c)
    (hband : ∀ᶠ j in atTop,
      ((1 / 2 : ℝ) - ε j) * Real.log ((M j + 1 : ℕ) : ℝ) ≤
        c * Real.log (6 + Real.log ((M j + 1 : ℕ) : ℝ))) :
    Tendsto (fun j => arithmeticFloorHilbertPartial (dampedMobiusWeight (ε j)) (M j))
      atTop (𝓝 (dampedMobiusHalfRangeLimit (1 / 2) le_rfl)) := by
  let δ : ℕ → ℝ := fun j => (1 / 2 : ℝ) - ε j
  have hδ (j : ℕ) : 0 ≤ δ j := sub_nonneg.mpr (hε j)
  let a : ℝ := 2 * c + 2
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have hca : c < a / 2 := by dsimp [a]; linarith
  obtain ⟨hJlim, hJMweak, hhead, hamp⟩ :=
    sqrtLogCutoff_band_facts M hM δ hδ c a hc hca hband
  have hJMstrict := sqrtLogCutoff_succ_le_eventually M hM
  obtain ⟨C, hC, herror⟩ := dampedMobius_half_cutoffs_all_log_rate a
  obtain ⟨B, hB, hglobalBound⟩ := dampedMobius_half_cutoffs_all_log_rate 0
  let u := fun m => -arithmeticResidueTerm (dampedMobiusWeight (1 / 2)) m
  let f := dampedMobiusHalfRangeLimit (1 / 2) le_rfl
  let w := fun j n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (δ j)
  let J := fun j => sqrtLogCutoff (M j)
  let P := fun j => M j - 1
  let R := fun n : ℕ => C * (6 + Real.log ((n + 1 : ℕ) : ℝ)) ^ (-a)
  have hR (n : ℕ) : 0 ≤ R n := by dsimp [R]; positivity
  have hglobal (n : ℕ) : ‖signedVectorPrefix u (n + 1) - f‖ ≤ B := by
    have he := hglobalBound (n + 1)
    simpa only [neg_zero, Real.rpow_zero, mul_one, u, f,
      signedVectorPrefix, Finset.sum_neg_distrib, arithmeticFloorHilbertPartial] using he
  have htail (K n : ℕ) (hKn : K ≤ n) :
      ‖signedVectorPrefix u (n + 1) - f‖ ≤ R K := by
    have he : ‖signedVectorPrefix u (n + 1) - f‖ ≤
        C * (6 + Real.log ((n + 1 + 1 : ℕ) : ℝ)) ^ (-a) := by
      simpa only [u, f, signedVectorPrefix, Finset.sum_neg_distrib,
        arithmeticFloorHilbertPartial] using herror (n + 1)
    apply he.trans
    apply mul_le_mul_of_nonneg_left _ hC
    apply Real.rpow_le_rpow_of_nonpos
    · have hh := Real.log_nonneg
        (show (1 : ℝ) ≤ ((K + 1 : ℕ) : ℝ) by exact_mod_cast (by omega : 1 ≤ K + 1))
      linarith
    · have hh := Real.log_le_log
        (by positivity : (0 : ℝ) < ((K + 1 : ℕ) : ℝ))
        (show ((K + 1 : ℕ) : ℝ) ≤ ((n + 1 + 1 : ℕ) : ℝ) by exact_mod_cast (by omega : K + 1 ≤ n + 1 + 1))
      linarith
    · exact neg_nonpos.mpr ha
  have hw (j : ℕ) : Monotone (w j) := by
    intro n m hnm
    exact Real.rpow_le_rpow (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hnm 1) (hδ j)
  have hwn (j n : ℕ) : 0 ≤ w j n := by dsimp [w]; positivity
  have hwzero (j : ℕ) : w j 0 = 1 := by simp [w]
  have hJP : ∀ᶠ j in atTop, J j ≤ P j := by
    filter_upwards [hJMstrict] with j hj
    dsimp [J, P]
    omega
  have hhead' : Tendsto (fun j => w j (J j)) atTop (𝓝 1) := hhead
  have hampC : Tendsto (fun j => w j (M j) * R (J j)) atTop (𝓝 0) := by
    have hh := hamp.const_mul C
    simpa only [w, R, J, mul_zero, mul_left_comm, mul_assoc] using hh
  have hampP : Tendsto (fun j => w j (P j) * R (J j)) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun j => mul_nonneg (hwn j _) (hR _)))
      (Eventually.of_forall (fun j => ?_)) hampC
    exact mul_le_mul_of_nonneg_right (hw j (Nat.sub_le _ _)) (hR _)
  have hv := signedVector_increasing_weights_split_tendsto u f B R hR hglobal htail
    w hw hwn hwzero P J hJP hhead' hampP
  apply hv.congr'
  filter_upwards [hM.eventually (eventually_ge_atTop (1 : ℕ))] with j hj
  have hP : P j + 1 = M j := by dsimp [P]; omega
  rw [hP, dampedMobiusPartial_from_half]
  simp only [w, u, δ, show -(ε j - 1 / 2) = (1 / 2 : ℝ) - ε j by ring]

/-- Uniformity over the entire moving band follows from its sequential
form, with conductor and damping independently quantified. -/
theorem dampedMobius_all_log_subhalf_band_uniform (c : ℝ) (hc : 0 ≤ c) :
    ∀ η : ℝ, 0 < η → ∃ J : ℕ, ∀ M : ℕ, J ≤ M → ∀ ε : ℝ,
      ε ≤ (1 / 2 : ℝ) →
      ((1 / 2 : ℝ) - ε) * Real.log ((M + 1 : ℕ) : ℝ) ≤
        c * Real.log (6 + Real.log ((M + 1 : ℕ) : ℝ)) →
      ‖arithmeticFloorHilbertPartial (dampedMobiusWeight ε) M -
        dampedMobiusHalfRangeLimit (1 / 2) le_rfl‖ ≤ η := by
  intro η hη
  by_contra h
  push Not at h
  choose M hMJ ε hε hband hbad using h
  have hM : Tendsto M atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop b] with j hj
    exact hj.trans (hMJ j)
  have hv := dampedMobius_all_log_subhalf_band_tendsto ε hε M hM c hc
    (Eventually.of_forall hband)
  obtain ⟨J, hJ⟩ := Metric.tendsto_atTop.mp hv η hη
  have hgood : ‖arithmeticFloorHilbertPartial (dampedMobiusWeight (ε J)) (M J) -
      dampedMobiusHalfRangeLimit (1 / 2) le_rfl‖ < η := by
    simpa only [dist_eq_norm] using hJ J le_rfl
  linarith [hbad J]

/-- The complete signed Gram energy converges throughout every fixed
coefficient band. This remains a statement about finite conductor vectors. -/
theorem dampedMobius_all_log_subhalf_band_energy_tendsto
    (ε : ℕ → ℝ) (hε : ∀ j, ε j ≤ (1 / 2 : ℝ))
    (M : ℕ → ℕ) (hM : Tendsto M atTop atTop)
    (c : ℝ) (hc : 0 ≤ c)
    (hband : ∀ᶠ j in atTop,
      ((1 / 2 : ℝ) - ε j) * Real.log ((M j + 1 : ℕ) : ℝ) ≤
        c * Real.log (6 + Real.log ((M j + 1 : ℕ) : ℝ))) :
    Tendsto (fun j =>
      ‖arithmeticFloorHilbertPartial (dampedMobiusWeight (ε j)) (M j)‖ ^ 2) atTop
      (𝓝 (∑' n : ℕ, positiveWeight n *
        (dampedMobiusPrefix (1 / 2) n - (n : ℝ) *
          (1 / riemannZeta (1 + ((1 / 2 : ℝ) : ℂ))).re) ^ 2)) := by
  have h := (dampedMobius_all_log_subhalf_band_tendsto ε hε M hM c hc hband).norm.pow 2
  simpa only [hilbert_norm_weighted_sq,
    (dampedMobiusHalfRangeLimit_spec (1 / 2) le_rfl).1] using h

/-- Uniform convergence of the full finite signed energy in the same band. -/
theorem dampedMobius_all_log_subhalf_band_energy_uniform (c : ℝ) (hc : 0 ≤ c) :
    ∀ η : ℝ, 0 < η → ∃ J : ℕ, ∀ M : ℕ, J ≤ M → ∀ ε : ℝ,
      ε ≤ (1 / 2 : ℝ) →
      ((1 / 2 : ℝ) - ε) * Real.log ((M + 1 : ℕ) : ℝ) ≤
        c * Real.log (6 + Real.log ((M + 1 : ℕ) : ℝ)) →
      |‖arithmeticFloorHilbertPartial (dampedMobiusWeight ε) M‖ ^ 2 -
        ‖dampedMobiusHalfRangeLimit (1 / 2) le_rfl‖ ^ 2| ≤ η := by
  intro η hη
  by_contra h
  push Not at h
  choose M hMJ ε hε hband hbad using h
  have hM : Tendsto M atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop b] with j hj
    exact hj.trans (hMJ j)
  have hv := (dampedMobius_all_log_subhalf_band_tendsto ε hε M hM c hc
    (Eventually.of_forall hband)).norm.pow 2
  obtain ⟨J, hJ⟩ := Metric.tendsto_atTop.mp hv η hη
  have hgood : |‖arithmeticFloorHilbertPartial (dampedMobiusWeight (ε J)) (M J)‖ ^ 2 -
      ‖dampedMobiusHalfRangeLimit (1 / 2) le_rfl‖ ^ 2| < η := by
    simpa only [dist_eq_norm, Real.norm_eq_abs] using hJ J le_rfl
  linarith [hbad J]

end RiemannResearch.RH.Pareto
