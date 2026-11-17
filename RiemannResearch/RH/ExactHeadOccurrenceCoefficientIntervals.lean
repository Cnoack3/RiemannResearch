import RiemannResearch.RH.ExactHeadOccurrenceStability
import RiemannResearch.RH.ExactHeadOccurrenceWeightConvergence
import RiemannResearch.Analysis.FiniteWeightedVariancePerturbation
import RiemannResearch.Analysis.RationalInterval
import Mathlib.Data.Rat.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Automatic complete-weight intervals for occurrence coefficients

Source: exact weighted-mean perturbation, complete Pareto weight intervals and
the canonical difference-of-means formula. Each active coefficient has a
rational enclosure at every positive depth, with exact inverse-square width.
No approximate optimizer or asymptotic provider is a hypothesis.
-/
noncomputable section
open scoped BigOperators
open Filter
namespace RiemannResearch.RH.Pareto.ExactHeadOccurrenceProjection
open RiemannResearch
open RiemannResearch.Analysis.FiniteWeightedVariance
open ExactHeadAtomOptimizer

def rationalBlockMean (P a b K : ℕ) : ℚ :=
  (∑ r ∈ Finset.Ico a b, (elementaryProgressionInterval P r K).lo * rationalTarget P r) /
    (∑ r ∈ Finset.Ico a b, (elementaryProgressionInterval P r K).lo)

def rationalBlockBaseMass (P a b : ℕ) : ℚ :=
  ∑ r ∈ Finset.Ico a b, (elementaryProgressionInterval P r 0).lo

def rationalBlockMeanRadius (P a b K : ℕ) : ℚ :=
  (rationalTarget P (b-1) - rationalTarget P a) * ((Finset.Ico a b).card : ℚ) /
    (rationalBlockBaseMass P a b * (((P : ℚ)*K)^2))

def rationalBlockMeanInterval (P a b K : ℕ) : RatInterval :=
  ⟨rationalBlockMean P a b K - rationalBlockMeanRadius P a b K,
    rationalBlockMean P a b K + rationalBlockMeanRadius P a b K⟩

theorem rationalBlockMean_cast (P a b K : ℕ) :
    (rationalBlockMean P a b K : ℝ) =
      mean (Finset.Ico a b) (fun r => ((elementaryProgressionInterval P r K).lo : ℝ))
        (target P) := by
  simp only [rationalBlockMean, mean, mass, Rat.cast_div, Rat.cast_sum,
    Rat.cast_mul, rationalTarget_cast]

/-- A fully rational a priori radius certifies the actual complete-weight block mean. -/
theorem rationalBlockMeanInterval_contains (P a b K : ℕ)
    (ha : 1 ≤ a) (hab : a < b) (hb : b ≤ P) (hK : 0 < K) :
    (rationalBlockMeanInterval P a b K).Contains
      (mean (Finset.Ico a b) (progressionWeight P) (target P)) := by
  have hP : 0 < P := by omega
  let s := Finset.Ico a b
  let lower := fun r => ((elementaryProgressionInterval P r K).lo : ℝ)
  let R := target P (b-1) - target P a
  let e : ℝ := 1 / (((P : ℝ)*K)^2)
  have hrpos : ∀ r ∈ s, 0 < r := by
    intro r hr
    have := Finset.mem_Ico.mp hr
    omega
  have hlpos : ∀ r ∈ s, 0 < lower r := by
    intro r hr
    change (0 : ℝ) < ((elementaryProgressionInterval P r K).lo : ℝ)
    exact_mod_cast elementaryProgressionInterval_lower_pos P r K hP (hrpos r hr)
  have hsne : s.Nonempty := ⟨a, Finset.mem_Ico.mpr ⟨le_rfl,hab⟩⟩
  have hL : 0 < mass s lower := Finset.sum_pos hlpos hsne
  have hM : 0 < mass s (progressionWeight P) := occurrence_block_mass_pos P a b ha hab hb
  have hM0q : 0 < rationalBlockBaseMass P a b := by
    exact Finset.sum_pos (fun r hr =>
      elementaryProgressionInterval_lower_pos P r 0 hP (hrpos r hr)) hsne
  have hM0 : (0 : ℝ) < (rationalBlockBaseMass P a b : ℝ) := by exact_mod_cast hM0q
  have hM0le : (rationalBlockBaseMass P a b : ℝ) ≤ mass s (progressionWeight P) := by
    simp only [rationalBlockBaseMass, Rat.cast_sum]
    exact Finset.sum_le_sum (fun r hr =>
      (elementaryProgressionInterval_contains P r 0 hP (hrpos r hr)).1)
  have hlo : ∀ r ∈ s, target P a ≤ target P r :=
    fun r hr => occurrence_target_mono P (Finset.mem_Ico.mp hr).1
  have hhi : ∀ r ∈ s, target P r ≤ target P (b-1) := by
    intro r hr
    exact occurrence_target_mono P (by have := Finset.mem_Ico.mp hr; omega)
  have hR : 0 ≤ R := sub_nonneg.mpr (occurrence_target_mono P (by omega))
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hmass : mass s (fun r => progressionWeight P r - lower r) ≤ (s.card : ℝ)*e := by
    calc
      _ ≤ ∑ r ∈ s, e := Finset.sum_le_sum (fun r hr =>
        (progressionWeight_endpoint_errors P r K hP (hrpos r hr) hK).2.1)
      _ = _ := by simp
  have hm := mean_weight_error_le s lower (progressionWeight P) (target P)
    (fun r hr => (hlpos r hr).le) hL
    (fun r hr => (elementaryProgressionInterval_contains P r K hP (hrpos r hr)).1)
    (target P a) (target P (b-1)) hlo hhi
  have hrad : (rationalBlockMeanRadius P a b K : ℝ) =
      R * ((s.card : ℝ)*e) / (rationalBlockBaseMass P a b : ℝ) := by
    simp only [rationalBlockMeanRadius, Rat.cast_div, Rat.cast_mul, Rat.cast_sub,
      Rat.cast_natCast, Rat.cast_pow, rationalTarget_cast]
    dsimp [R, e, s]
    simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
    ring
  have herr : |mean s (progressionWeight P) (target P) -
      (rationalBlockMean P a b K : ℝ)| ≤ (rationalBlockMeanRadius P a b K : ℝ) := by
    rw [rationalBlockMean_cast, hrad]
    calc
      _ ≤ R * mass s (fun r => progressionWeight P r - lower r) /
          mass s (progressionWeight P) := hm
      _ ≤ R * ((s.card : ℝ)*e) / mass s (progressionWeight P) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hmass hR) hM.le
      _ ≤ _ := by
        simp only [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left ((inv_le_inv₀ hM hM0).mpr hM0le)
          (mul_nonneg hR (mul_nonneg (Nat.cast_nonneg _) he))
  obtain ⟨hl,hu⟩ := abs_le.mp herr
  change ((rationalBlockMean P a b K - rationalBlockMeanRadius P a b K : ℚ) : ℝ) ≤
      mean s (progressionWeight P) (target P) ∧
    mean s (progressionWeight P) (target P) ≤
      ((rationalBlockMean P a b K + rationalBlockMeanRadius P a b K : ℚ) : ℝ)
  push_cast
  constructor <;> linarith

theorem rationalBlockMeanRadius_factorization (P a b K : ℕ) :
    rationalBlockMeanRadius P a b K =
      rationalBlockMeanRadius P a b 1 / (K : ℚ)^2 := by
  simp only [rationalBlockMeanRadius, Nat.cast_one, mul_one, div_eq_mul_inv,
    mul_pow, mul_inv_rev]
  ring

def rationalOccurrenceCoefficientInterval (P x K i : ℕ) : RatInterval :=
  let current := rationalBlockMeanInterval P (occurrenceBoundary P x i)
    (occurrenceBoundary P x (i+1)) K
  if i = 0 then current else
    RatInterval.sub current (rationalBlockMeanInterval P (occurrenceBoundary P x (i-1))
      (occurrenceBoundary P x i) K)

/-- Every actual active coefficient has an automatic rational enclosure at every positive depth. -/
theorem rationalOccurrenceCoefficientInterval_contains (P x K i : ℕ)
    (hP : 0 < P) (hK : 0 < K) (hi : i < (freePositions P x).card) :
    (rationalOccurrenceCoefficientInterval P x K i).Contains
      (occurrenceCoefficients P x (occurrenceBoundary P x i)) := by
  have hm (j : ℕ) (hj : j < (freePositions P x).card) :
      (rationalBlockMeanInterval P (occurrenceBoundary P x j)
        (occurrenceBoundary P x (j+1)) K).Contains (occurrenceBlockMean P x j) :=
    rationalBlockMeanInterval_contains P _ _ K (occurrenceBoundary_pos P x j hP)
      (occurrenceBoundary_strict P x j hj) (occurrenceBoundary_le_period P x (j+1)) hK
  rw [occurrenceCoefficients_boundary P x i hP hi]
  unfold rationalOccurrenceCoefficientInterval
  dsimp only
  by_cases hi0 : i = 0
  · simp only [if_pos hi0, sub_zero]
    exact hm i hi
  · simp only [if_neg hi0]
    have hp := hm (i-1) (by omega)
    have he : i-1+1 = i := by omega
    rw [he] at hp
    exact RatInterval.contains_sub (hm i hi) hp

/-- The entire coefficient interval width has an exact inverse-square scaling law. -/
theorem rationalOccurrenceCoefficientInterval_width (P x K i : ℕ) :
    (rationalOccurrenceCoefficientInterval P x K i).hi -
      (rationalOccurrenceCoefficientInterval P x K i).lo =
      ((rationalOccurrenceCoefficientInterval P x 1 i).hi -
        (rationalOccurrenceCoefficientInterval P x 1 i).lo) / (K : ℚ)^2 := by
  by_cases hi : i = 0
  · simp only [rationalOccurrenceCoefficientInterval, if_pos hi, rationalBlockMeanInterval]
    simp only [rationalBlockMeanRadius_factorization P
      (occurrenceBoundary P x i) (occurrenceBoundary P x (i+1)) K]
    ring
  · simp only [rationalOccurrenceCoefficientInterval, if_neg hi, rationalBlockMeanInterval,
      RatInterval.sub, RatInterval.add, RatInterval.neg]
    simp only [rationalBlockMeanRadius_factorization P
      (occurrenceBoundary P x i) (occurrenceBoundary P x (i+1)) K,
      rationalBlockMeanRadius_factorization P
        (occurrenceBoundary P x (i-1)) (occurrenceBoundary P x i) K]
    ring

theorem rationalOccurrenceCoefficientInterval_width_tendsto_zero (P x i : ℕ) :
    Tendsto (fun K =>
      ((rationalOccurrenceCoefficientInterval P x K i).hi : ℝ) -
        ((rationalOccurrenceCoefficientInterval P x K i).lo : ℝ)) atTop (nhds 0) := by
  have he (K : ℕ) :
      ((rationalOccurrenceCoefficientInterval P x K i).hi : ℝ) -
        ((rationalOccurrenceCoefficientInterval P x K i).lo : ℝ) =
      (((rationalOccurrenceCoefficientInterval P x 1 i).hi -
        (rationalOccurrenceCoefficientInterval P x 1 i).lo : ℚ) : ℝ) / (K : ℝ)^2 := by
    have h := congrArg (fun q : ℚ => (q : ℝ))
      (rationalOccurrenceCoefficientInterval_width P x K i)
    simpa only [Rat.cast_sub, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast] using h
  simp_rw [he]
  have hinv : Tendsto (fun K : ℕ => (K : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  simpa only [div_eq_mul_inv, inv_pow, zero_pow (by decide : 2 ≠ 0), mul_zero] using
    (hinv.pow 2).const_mul
      (((rationalOccurrenceCoefficientInterval P x 1 i).hi -
        (rationalOccurrenceCoefficientInterval P x 1 i).lo : ℚ) : ℝ)


/-- The automatic lower endpoints converge to the actual active coefficient. -/
theorem rationalOccurrenceCoefficientInterval_lower_tendsto (P x i : ℕ)
    (hP : 0 < P) (hi : i < (freePositions P x).card) :
    Tendsto (fun K => ((rationalOccurrenceCoefficientInterval P x K i).lo : ℝ))
      atTop (nhds (occurrenceCoefficients P x (occurrenceBoundary P x i))) := by
  have hd : Tendsto (fun K => occurrenceCoefficients P x (occurrenceBoundary P x i) -
      ((rationalOccurrenceCoefficientInterval P x K i).lo : ℝ)) atTop (nhds 0) := by
    apply squeeze_zero' _ _ (rationalOccurrenceCoefficientInterval_width_tendsto_zero P x i)
    · filter_upwards [eventually_ge_atTop 1] with K hK
      exact sub_nonneg.mpr (rationalOccurrenceCoefficientInterval_contains P x K i hP hK hi).1
    · filter_upwards [eventually_ge_atTop 1] with K hK
      exact sub_le_sub_right (rationalOccurrenceCoefficientInterval_contains P x K i hP hK hi).2 _
  simpa only [sub_sub_cancel, sub_zero] using
    (tendsto_const_nhds : Tendsto
      (fun _ : ℕ => occurrenceCoefficients P x (occurrenceBoundary P x i)) atTop
      (nhds (occurrenceCoefficients P x (occurrenceBoundary P x i)))).sub hd

/-- The automatic upper endpoints converge to the same actual active coefficient. -/
theorem rationalOccurrenceCoefficientInterval_upper_tendsto (P x i : ℕ)
    (hP : 0 < P) (hi : i < (freePositions P x).card) :
    Tendsto (fun K => ((rationalOccurrenceCoefficientInterval P x K i).hi : ℝ))
      atTop (nhds (occurrenceCoefficients P x (occurrenceBoundary P x i))) := by
  have hd : Tendsto (fun K => ((rationalOccurrenceCoefficientInterval P x K i).hi : ℝ) -
      occurrenceCoefficients P x (occurrenceBoundary P x i)) atTop (nhds 0) := by
    apply squeeze_zero' _ _ (rationalOccurrenceCoefficientInterval_width_tendsto_zero P x i)
    · filter_upwards [eventually_ge_atTop 1] with K hK
      exact sub_nonneg.mpr (rationalOccurrenceCoefficientInterval_contains P x K i hP hK hi).2
    · filter_upwards [eventually_ge_atTop 1] with K hK
      exact sub_le_sub_left (rationalOccurrenceCoefficientInterval_contains P x K i hP hK hi).1 _
  simpa only [sub_add_cancel, zero_add] using
    hd.add (tendsto_const_nhds : Tendsto
      (fun _ : ℕ => occurrenceCoefficients P x (occurrenceBoundary P x i)) atTop
      (nhds (occurrenceCoefficients P x (occurrenceBoundary P x i))))

/-- Every strict coefficient ordering is eventually certified by disjoint rational intervals. -/
theorem rationalOccurrenceCoefficientInterval_eventually_separated (P x i j : ℕ)
    (hP : 0 < P) (hi : i < (freePositions P x).card) (hj : j < (freePositions P x).card)
    (hlt : occurrenceCoefficients P x (occurrenceBoundary P x i) <
      occurrenceCoefficients P x (occurrenceBoundary P x j)) :
    ∀ᶠ K in atTop, (rationalOccurrenceCoefficientInterval P x K i).hi <
      (rationalOccurrenceCoefficientInterval P x K j).lo := by
  let mid := (occurrenceCoefficients P x (occurrenceBoundary P x i) +
    occurrenceCoefficients P x (occurrenceBoundary P x j)) / 2
  have hu := (tendsto_order.mp
    (rationalOccurrenceCoefficientInterval_upper_tendsto P x i hP hi)).2 mid
      (by dsimp [mid]; linarith)
  have hl := (tendsto_order.mp
    (rationalOccurrenceCoefficientInterval_lower_tendsto P x j hP hj)).1 mid
      (by dsimp [mid]; linarith)
  filter_upwards [hu,hl] with K hU hL
  exact (Rat.cast_lt (K := ℝ)).mp (hU.trans hL)

/-- Positive active coefficients are exactly those with a positive rational lower certificate. -/
theorem occurrenceCoefficient_pos_iff_rational_certificate (P x i : ℕ)
    (hP : 0 < P) (hi : i < (freePositions P x).card) :
    0 < occurrenceCoefficients P x (occurrenceBoundary P x i) ↔
      ∃ K : ℕ, 1 ≤ K ∧ 0 < (rationalOccurrenceCoefficientInterval P x K i).lo := by
  constructor
  · intro hc
    have he := (tendsto_order.mp
      (rationalOccurrenceCoefficientInterval_lower_tendsto P x i hP hi)).1 0 hc
    obtain ⟨K,hK,hpos⟩ := ((eventually_ge_atTop 1).and he).exists
    exact ⟨K,hK,(Rat.cast_pos (K := ℝ)).mp hpos⟩
  · rintro ⟨K,hK,hpos⟩
    exact ((Rat.cast_pos (K := ℝ)).2 hpos).trans_le
      (rationalOccurrenceCoefficientInterval_contains P x K i hP hK hi).1

/-- Every strict increase under a fixed-period cutoff change has a finite rational certificate. -/
theorem occurrenceEnergy_lt_iff_rational_certificate (P x y : ℕ)
    (hP : 0 < P) (hxy : x ≤ y) :
    occurrenceEnergy P x < occurrenceEnergy P y ↔
      ∃ K : ℕ, 1 ≤ K ∧ ∃ i < (freePositions P x).card,
        occurrenceBoundary P x i ∉ freePositions P y ∧
          0 < (rationalOccurrenceCoefficientInterval P x K i).lo := by
  rw [occurrenceEnergy_lt_iff_removed_nonzero P x y hP hxy]
  constructor
  · rintro ⟨n,hn,hny,hne⟩
    have hpos : 0 < occurrenceCoefficients P x n := by
      rcases lt_or_eq_of_le (occurrenceCoefficients_nonneg P x hP n hn) with hp | he
      · exact hp
      · exact (hne he.symm).elim
    obtain ⟨i,hi,rfl⟩ := exists_occurrenceBoundary P x n hn
    obtain ⟨K,hK,hposK⟩ :=
      (occurrenceCoefficient_pos_iff_rational_certificate P x i hP hi).mp hpos
    exact ⟨K,hK,i,hi,hny,hposK⟩
  · rintro ⟨K,hK,i,hi,hny,hposK⟩
    have hpos := (occurrenceCoefficient_pos_iff_rational_certificate P x i hP hi).mpr
      ⟨K,hK,hposK⟩
    exact ⟨occurrenceBoundary P x i, occurrenceBoundary_mem P x i hi, hny, ne_of_gt hpos⟩

end RiemannResearch.RH.Pareto.ExactHeadOccurrenceProjection
