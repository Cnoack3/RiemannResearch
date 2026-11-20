import RiemannResearch.Analysis.ActualZeroDisplacementMoments
import RiemannResearch.Analysis.FiniteSizeBiasedExponential

/-!
# Size-biased exponential estimates for actual zero displacements

The finite cutoff law assigns equal mass to each occurrence, including analytic
multiplicity. Its scaled displacement is the physical displacement times log T.
The height-normalized input below is the observable in the first-order tilted
Selberg estimate.
-/

noncomputable section
open Filter Zeta23
open scoped BigOperators Topology

namespace RiemannResearch.Analysis.ActualZeroOrdinate

/-- The expectation of X exp(aX) under the actual copy law. -/
def microscopicSizeBiasedTilt (T a : ℝ) : ℝ :=
  (∑ j : Copies T, (copyDisplacement T j * Real.log T) *
    Real.exp (a * (copyDisplacement T j * Real.log T))) / (Ncount 0 T : ℝ)

private theorem actual_mark_mass (T : ℝ) (k : ℕ) (hN : 0 < (Ncount 0 T : ℝ)) :
    (∑ j : Copies T, (copyDisplacement T j * Real.log T) ^ k) =
      (Ncount 0 T : ℝ) * (displacementMoment T k * Real.log T ^ k) := by
  have h : (∑ j : Copies T, (copyDisplacement T j * Real.log T) ^ k) /
      (Ncount 0 T : ℝ) = displacementMoment T k * Real.log T ^ k := by
    simp only [mul_pow, ← Finset.sum_mul, displacementMoment]
    ring
  exact ((div_eq_iff hN.ne').mp h).trans (mul_comm _ _)

/-- The true second moment enters the exponential with denominator the true mean. -/
theorem actual_sizeBiased_exp {T a : ℝ} (hT : 1 ≤ T) (hN : 0 < (Ncount 0 T : ℝ))
    (hm : 0 < displacementMoment T 1 * Real.log T) :
    (displacementMoment T 1 * Real.log T) * Real.exp
      (a * ((displacementMoment T 2 * Real.log T ^ 2) /
        (displacementMoment T 1 * Real.log T))) ≤ microscopicSizeBiasedTilt T a := by
  have h := FiniteSizeBiasedExponential.normalized_sizeBiased_exp Finset.univ
    (fun _ : Copies T => (1 : ℝ)) (fun j => copyDisplacement T j * Real.log T) a
    (Z := (Ncount 0 T : ℝ)) (m := displacementMoment T 1 * Real.log T)
    (q := displacementMoment T 2 * Real.log T ^ 2) hN hm
    (by intro j _; exact mul_nonneg zero_le_one
          (mul_nonneg (abs_nonneg _) (Real.log_nonneg hT)))
    (by simpa only [one_mul, pow_one] using actual_mark_mass T 1 hN)
    (by simpa only [one_mul] using actual_mark_mass T 2 hN)
  simpa only [one_mul, microscopicSizeBiasedTilt] using h

/-- Convert the height-normalized first-order tilt to the copy-law normalization. -/
theorem microscopicSizeBiasedTilt_le_of_height {T a K : ℝ} (hT : 1 ≤ T)
    (h : (∑ j : Copies T, copyDisplacement T j *
      Real.exp ((a * Real.log T) * copyDisplacement T j)) / T ≤ K) :
    microscopicSizeBiasedTilt T a ≤ K * T * Real.log T / (Ncount 0 T : ℝ) := by
  have he : (∑ j : Copies T, (copyDisplacement T j * Real.log T) *
      Real.exp (a * (copyDisplacement T j * Real.log T))) =
      (∑ j : Copies T, copyDisplacement T j *
        Real.exp ((a * Real.log T) * copyDisplacement T j)) * Real.log T := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [show a * (copyDisplacement T j * Real.log T) =
      (a * Real.log T) * copyDisplacement T j by ring]
    ring
  unfold microscopicSizeBiasedTilt
  rw [he]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right ((div_le_iff₀ (zero_lt_one.trans_le hT)).mp h)
      (Real.log_nonneg hT)) (Nat.cast_nonneg _)

/-- A height-normalized Selberg tilted bound controls the scaled actual second
moment with a logarithmic factor in the reciprocal scaled first moment. -/
theorem actual_secondMoment_le_log_of_heightTilt {T a K : ℝ} (hT : 1 ≤ T)
    (hN : 0 < (Ncount 0 T : ℝ)) (ha : 0 < a)
    (hm : 0 < displacementMoment T 1 * Real.log T)
    (h : (∑ j : Copies T, copyDisplacement T j *
      Real.exp ((a * Real.log T) * copyDisplacement T j)) / T ≤ K) :
    displacementMoment T 2 * Real.log T ^ 2 ≤
      ((displacementMoment T 1 * Real.log T) / a) *
        Real.log ((K * T * Real.log T / (Ncount 0 T : ℝ)) /
          (displacementMoment T 1 * Real.log T)) :=
  FiniteSizeBiasedExponential.secondMoment_le_log_of_tilt ha hm
    ((actual_sizeBiased_exp hT hN hm).trans (microscopicSizeBiasedTilt_le_of_height hT h))

/-- The two-sided Selberg tail of slope b bounds the microscopic size-biased
tilt at every strictly lower positive slope a. -/
theorem microscopicSizeBiasedTilt_le_of_selberg {T C b a : ℝ}
    (hT : 1 < T) (hC : 0 ≤ C) (ha : 0 < a) (hab : a < b)
    (hD : SelbergDensityBound T C b) :
    microscopicSizeBiasedTilt T a ≤
      (2*C*b/(b-a)^2) * T * Real.log T / (Ncount 0 T : ℝ) := by
  have hL := Real.log_pos hT
  have hbase := tiltedMoment_div_height_of_selberg 0 hT hC
    (mul_nonneg ha.le hL.le) (mul_lt_mul_of_pos_right hab hL) hD
  apply microscopicSizeBiasedTilt_le_of_height hT.le
  simp only [Nat.zero_add, pow_one, Nat.factorial_one, Nat.cast_one, one_mul] at hbase
  apply hbase.trans_eq
  rw [← sub_mul, mul_pow]
  field_simp [hL.ne', (sub_pos.mpr hab).ne'] <;> ring

/-- One finite tilt cap holds eventually whenever the inclusive zero-density
envelope holds at any strictly larger slope. The logarithmic feedback is
simultaneous in the true first and second moments at each cutoff. -/
theorem exists_actual_sizeBiased_cap_of_uniformSelberg {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hD : UniformSelbergDensity b) :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ T : ℝ in Filter.atTop,
      microscopicSizeBiasedTilt T a ≤ M ∧
      (0 < displacementMoment T 1 * Real.log T →
        displacementMoment T 2 * Real.log T ^ 2 ≤
          ((displacementMoment T 1 * Real.log T) / a) *
            Real.log (M / (displacementMoment T 1 * Real.log T))) := by
  obtain ⟨C,T₀,hC,hT₀,h⟩ := hD
  obtain ⟨c,hc,hcount⟩ := exists_count_normalization
  let K := 2*C*b/(b-a)^2
  have hb := ha.trans hab
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K/c+1, by positivity, ?_⟩
  filter_upwards [hcount, Filter.eventually_ge_atTop T₀] with T hn ht
  have hT := hT₀.trans_le ht
  have hTpos := zero_lt_one.trans hT
  have hL := Real.log_pos hT
  have hN : 0 < (Ncount 0 T : ℝ) := lt_of_lt_of_le (by positivity) hn
  have hr : K*T*Real.log T/(Ncount 0 T : ℝ) ≤ K/c := by
    apply (div_le_iff₀ hN).mpr
    calc
      _ = (K/c)*(c*T*Real.log T) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hn (div_nonneg hK hc.le)
  have htilt : microscopicSizeBiasedTilt T a ≤ K/c+1 :=
    ((microscopicSizeBiasedTilt_le_of_selberg hT hC ha hab (h T ht)).trans hr).trans
      (by linarith)
  exact ⟨htilt, fun hm => FiniteSizeBiasedExponential.secondMoment_le_log_of_tilt ha hm
    ((actual_sizeBiased_exp hT.le hN hm).trans htilt)⟩

/-- Every fixed microscopic tilt in the published open interval is available
with its own cap. No uniformity in a is required. -/
theorem exists_actual_sizeBiased_cap_of_conreyBaluyot
    (hD : ConreyBaluyotDensityHypothesis) {a : ℝ} (ha : 0 < a) (ha' : a < 8/7) :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ T : ℝ in Filter.atTop,
      microscopicSizeBiasedTilt T a ≤ M ∧
      (0 < displacementMoment T 1 * Real.log T →
        displacementMoment T 2 * Real.log T ^ 2 ≤
          ((displacementMoment T 1 * Real.log T) / a) *
            Real.log (M / (displacementMoment T 1 * Real.log T))) := by
  obtain ⟨b, hab, hb⟩ := exists_between ha'
  exact exists_actual_sizeBiased_cap_of_uniformSelberg ha hab (hD b (ha.trans hab) hb)

/-- A family of one-log density slopes below A bounds the second-to-first
moment ratio by every fixed coefficient above 1/A along the chosen heights.
The analytic mean-convergence and positivity hypotheses stay explicit. -/
theorem actual_secondMoment_ratio_le_of_density_slopes {A c : ℝ} (hA : 0 < A)
    (hD : ∀ b : ℝ, 0 < b → b < A → UniformSelbergDensity b) (hc : 1 / A < c)
    {ι : Type*} {l : Filter ι} {T : ι → ℝ} (hT : Tendsto T l atTop)
    (hm : Tendsto (fun i => displacementMoment (T i) 1 * Real.log (T i)) l (𝓝 0))
    (hp : ∀ᶠ i in l, 0 < displacementMoment (T i) 1 * Real.log (T i)) :
    ∀ᶠ i in l, (displacementMoment (T i) 2 * Real.log (T i) ^ 2) /
      ((displacementMoment (T i) 1 * Real.log (T i)) *
        Real.log (1 / (displacementMoment (T i) 1 * Real.log (T i)))) ≤ c := by
  apply FiniteSizeBiasedExponential.eventually_secondMoment_ratio_le_of_open_tilts hA hc hm hp
  intro a ha haA
  obtain ⟨b, hab, hb⟩ := exists_between haA
  obtain ⟨M, hM, hcap⟩ := exists_actual_sizeBiased_cap_of_uniformSelberg ha hab
    (hD b (ha.trans hab) hb)
  refine ⟨M, hM, ?_⟩
  filter_upwards [hT.eventually hcap, hp, hT.eventually eventually_count_pos,
    hT.eventually (eventually_gt_atTop (1 : ℝ))] with i hcap' hpos hN ht
  exact (actual_sizeBiased_exp ht.le (by exact_mod_cast hN) hpos).trans hcap'.1

/-- The quantitative microscopic-concentration implication for actual zeros.
For a vanishing positive microscopic mean, the scaled second moment is eventually
at most c times m log(1/m), for every c strictly greater than 7/8. -/
theorem actual_secondMoment_ratio_le_of_conreyBaluyot
    (hD : ConreyBaluyotDensityHypothesis) {c : ℝ} (hc : 7/8 < c)
    (hm : Tendsto (fun T => displacementMoment T 1 * Real.log T) atTop (𝓝 0))
    (hmpos : ∀ᶠ T : ℝ in atTop, 0 < displacementMoment T 1 * Real.log T) :
    ∀ᶠ T : ℝ in atTop,
      (displacementMoment T 2 * Real.log T ^ 2) /
        ((displacementMoment T 1 * Real.log T) *
          Real.log (1/(displacementMoment T 1 * Real.log T))) ≤ c := by
  exact actual_secondMoment_ratio_le_of_density_slopes (A := 8 / 7) (by norm_num)
    hD (by norm_num; exact hc) tendsto_id hm hmpos

end RiemannResearch.Analysis.ActualZeroOrdinate
