import RiemannResearch.Analysis.GLSSArgumentVarianceCalibration
import RiemannResearch.Analysis.TwoPrimeCompactCollision

/-! # Absolute Gaussian recovery of collisions of actual zero ordinates

The allowance is independent of the Gaussian precision. Every original occurrence is
included. The even integer being recovered is the excess of ordered same-height pairs
over the occurrence diagonal. Source for the absolute error calibration: the user's
argument. Goldston–Lee–Schettler–Suriajaya, https://arxiv.org/abs/2503.15449,
supply the horizontal multiplicity terminology and the density comparison.
-/

noncomputable section
open Filter Zeta23
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.ActualZeroOrdinate
open ActualZeroCollisionCertificate OrdinateCollisionCertificate

/-- Precision allowance that leaves one quarter of a pair in the unnormalized error. -/
def gaussianCollisionAllowance (T : ℝ) : ℝ := Real.log (12 * (Ncount 0 T : ℝ))

/-- Reconstructed all-pair Gaussian power minus its occurrence diagonal in count units. -/
def absoluteGaussianExcess (a T : ℝ) : ℝ :=
  (Ncount 0 T : ℝ) * (reconstructedGaussianPowerWithAllowance a T (gaussianCollisionAllowance T) - 1)

/-- The unnormalized positive contribution of pairs at different heights. -/
def unequalGaussianTotal (a T : ℝ) : ℝ :=
  (Ncount 0 T : ℝ) * unequalOrdinateGaussianMoment a T

/-- Signed difference in unfolded physical units. -/
def gaussianSeparation (T : ℝ) (i j : Copies T) : ℝ :=
  Real.log T / (2 * Real.pi) * (copyOrdinate T i - copyOrdinate T j)

/-- Every pair of different labels with equal ordinate belongs to the collision atom. -/
def unequalGaussianTerm (a T : ℝ) (i j : Copies T) : ℝ := by
  classical
  exact if copyOrdinate T i = copyOrdinate T j then 0
    else Real.exp (-a * (gaussianSeparation T i j)^2)

theorem unequalGaussianTerm_nonneg (a T : ℝ) (i j : Copies T) :
    0 ≤ unequalGaussianTerm a T i j := by
  classical
  unfold unequalGaussianTerm
  split <;> positivity

theorem unequalGaussianTotal_eq_sum (a T : ℝ) (hN : 0 < Ncount 0 T) :
    unequalGaussianTotal a T = ∑ i : Copies T, ∑ j : Copies T, unequalGaussianTerm a T i j := by
  classical
  have hn : (Ncount 0 T : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  change (Ncount 0 T : ℝ) * ((∑ i : Copies T, ∑ j ∈ Finset.univ.erase i,
    unequalGaussianTerm a T i j) / (Ncount 0 T : ℝ)) = _
  calc
    _ = ∑ i : Copies T, ∑ j ∈ Finset.univ.erase i, unequalGaussianTerm a T i j := by
      field_simp [hn]
    _ = _ := Finset.sum_congr rfl fun i _ =>
      Finset.sum_erase Finset.univ (by simp [unequalGaussianTerm])

theorem unequalGaussianTotal_nonneg (a T : ℝ) : 0 ≤ unequalGaussianTotal a T := by
  by_cases hN : 0 < Ncount 0 T
  · rw [unequalGaussianTotal_eq_sum _ _ hN]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => unequalGaussianTerm_nonneg _ _ i j
  · have hz : Ncount 0 T = 0 := by omega
    simp [unequalGaussianTotal, hz]

theorem gaussianCollisionAllowance_nonneg {T : ℝ} (hN : 0 < Ncount 0 T) :
    0 ≤ gaussianCollisionAllowance T := by
  have hn : (1 : ℝ) ≤ Ncount 0 T := by exact_mod_cast hN
  exact Real.log_nonneg (by linarith only [hn])

theorem gaussianCollisionAllowance_error {T : ℝ} (hN : 0 < Ncount 0 T) :
    3 * (Ncount 0 T : ℝ) * Real.exp (-gaussianCollisionAllowance T) = 1 / 4 := by
  have hn : (0 : ℝ) < Ncount 0 T := by exact_mod_cast hN
  rw [gaussianCollisionAllowance, Real.exp_neg, Real.exp_log (by positivity)]
  field_simp [hn.ne']
  <;> ring

/-- Both terms of the horizontal collision split survive at integer-count precision. -/
theorem absolute_gaussian_split_error {a T b : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hN : 0 < Ncount 0 T) :
    |(actualCollision T : ℝ) - (Ncount 0 T : ℝ) + unequalGaussianTotal a T -
        (Ncount 0 T : ℝ) * (reconstructedGaussianPowerWithAllowance a T b - 1)| ≤
      3 * (Ncount 0 T : ℝ) * Real.exp (-b) := by
  have hn : (Ncount 0 T : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hcol : (actualCollision T : ℝ) = (Ncount 0 T : ℝ) + (occurrenceExcess (copyOrdinate T) : ℝ) := by
    simp only [actualCollision, occurrenceCollision_eq_card_add_excess, card_copies, Nat.cast_add]
  have he := gaussianFactorialMoment_reconstruction_with_allowance ha hb hN
  calc
    _ = |(Ncount 0 T : ℝ) * (gaussianFactorialMoment a T -
        (reconstructedGaussianPowerWithAllowance a T b - 1))| := by
      rw [gaussianFactorialMoment_split, hcol, unequalGaussianTotal]
      congr 1
      field_simp [hn]
      <;> ring
    _ = (Ncount 0 T : ℝ) * |gaussianFactorialMoment a T -
        (reconstructedGaussianPowerWithAllowance a T b - 1)| := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    _ ≤ _ := (mul_le_mul_of_nonneg_left he (Nat.cast_nonneg _)).trans_eq (by ring)

/-- A quarter-pair bound uniformly for every positive Gaussian precision. -/
theorem absolute_gaussian_quarter_error {T a : ℝ} (hN : 0 < Ncount 0 T) (ha : 0 < a) :
    |(actualCollision T : ℝ) - (Ncount 0 T : ℝ) + unequalGaussianTotal a T -
      absoluteGaussianExcess a T| ≤ 1 / 4 :=
  (absolute_gaussian_split_error ha (gaussianCollisionAllowance_nonneg hN) hN).trans_eq
    (gaussianCollisionAllowance_error hN)

theorem collision_eq_count_of_absolute_gaussian_upper {a T : ℝ}
    (hN : 0 < Ncount 0 T) (ha : 0 < a) (hupper : absoluteGaussianExcess a T < 1) :
    actualCollision T = Ncount 0 T := by
  have hu := unequalGaussianTotal_nonneg a T
  have herr := (abs_le.mp (absolute_gaussian_quarter_error hN ha)).2
  have hlt : (actualCollision T : ℝ) < (Ncount 0 T : ℝ) + 2 := by linarith only [herr, hu, hupper]
  have hnat : actualCollision T < Ncount 0 T + 2 := by exact_mod_cast hlt
  have hsum := actualCollision_eq_count_add_excess T
  obtain ⟨m, hm⟩ := actualCollision_sub_count_even T
  omega

/-- Existence of a passing positive integer precision is exact at a fixed nonempty height. -/
theorem absolute_gaussian_finite_iff {T : ℝ} (hT : 1 < T) (hN : 0 < Ncount 0 T) :
    (∃ k : ℕ, absoluteGaussianExcess ((k : ℝ)+1) T < 1) ↔ actualCollision T = Ncount 0 T := by
  constructor
  · rintro ⟨k, hk⟩
    exact collision_eq_count_of_absolute_gaussian_upper hN (by positivity) hk
  · intro hc
    have hlim : Tendsto (fun k : ℕ => unequalGaussianTotal ((k : ℝ)+1) T) atTop (𝓝 0) := by
      simpa only [unequalGaussianTotal, mul_zero] using
        (MontgomeryPositiveGap.unequalGaussian_tendsto_zero_at_fixed_height hT).const_mul
          (Ncount 0 T : ℝ)
    obtain ⟨k, hk⟩ := (hlim.eventually_lt_const (by norm_num : (0 : ℝ) < 1/2)).exists
    have he := (abs_le.mp (absolute_gaussian_quarter_error hN (show 0 < (k : ℝ)+1 by positivity))).1
    rw [hc] at he
    exact ⟨k, by linarith only [he, hk]⟩

/-- A cofinal absolute upper bound is equivalent to RH and analytic simplicity everywhere. -/
theorem cofinal_absolute_gaussian_iff_global :
    (∃ᶠ T : ℝ in atTop, ∃ k : ℕ, absoluteGaussianExcess ((k : ℝ)+1) T < 1) ↔
      RiemannHypothesis ∧ ∀ ρ : ℂ, IsNontrivialZero ρ → zeroMult ρ = 1 := by
  constructor
  · intro h
    apply MontgomeryFormFactor.frequently_collision_lt_count_add_two_iff_global.mp
    apply (h.and_eventually ((eventually_gt_atTop (1 : ℝ)).and eventually_count_pos)).mono
    rintro T ⟨htest, ht, hn⟩
    rw [(absolute_gaussian_finite_iff ht hn).mp htest]
    omega
  · intro h
    have hall := MontgomeryFormFactor.all_cutoffs_critical_simple_iff_global.mpr h
    apply Filter.Eventually.frequently
    filter_upwards [eventually_gt_atTop (1 : ℝ), eventually_count_pos] with T ht hn
    exact (absolute_gaussian_finite_iff ht hn).mpr ((actualCollision_eq_count_iff T).mpr (hall T))

/-- A physical separation lower bound controls the complete off-collision sum. The condition
is vacuous when no two occupied ordinates differ. -/
theorem unequalGaussianTotal_le_of_separation {a T δ : ℝ} (hN : 0 < Ncount 0 T)
    (ha : 0 ≤ a) (hδ : 0 ≤ δ)
    (hsep : ∀ i j : Copies T, copyOrdinate T i ≠ copyOrdinate T j → δ ≤ |gaussianSeparation T i j|) :
    unequalGaussianTotal a T ≤ (Ncount 0 T : ℝ)^2 * Real.exp (-a*δ^2) := by
  classical
  rw [unequalGaussianTotal_eq_sum _ _ hN]
  have hp (i j : Copies T) : unequalGaussianTerm a T i j ≤ Real.exp (-a*δ^2) := by
    by_cases he : copyOrdinate T i = copyOrdinate T j
    · simpa only [unequalGaussianTerm, if_pos he] using (Real.exp_pos (-a*δ^2)).le
    rw [unequalGaussianTerm, if_neg he]
    apply Real.exp_le_exp.mpr
    have hsq := pow_le_pow_left₀ hδ (hsep i j he) 2
    rw [sq_abs] at hsq
    exact mul_le_mul_of_nonpos_left hsq (neg_nonpos.mpr ha)
  calc
    _ ≤ ∑ _i : Copies T, ∑ _j : Copies T, Real.exp (-a*δ^2) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hp i j
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, card_copies, nsmul_eq_mul]
      ring

/-- At the stated separation precision the unequal-height mass costs at most one quarter. -/
theorem unequalGaussianTotal_le_quarter {a T δ : ℝ} (hN : 0 < Ncount 0 T) (ha : 0 ≤ a)
    (hδ : 0 < δ) (hprec : Real.log (4 * (Ncount 0 T : ℝ)^2) / δ^2 ≤ a)
    (hsep : ∀ i j : Copies T, copyOrdinate T i ≠ copyOrdinate T j → δ ≤ |gaussianSeparation T i j|) :
    unequalGaussianTotal a T ≤ 1 / 4 := by
  have hn : (0 : ℝ) < Ncount 0 T := by exact_mod_cast hN
  have hc := (div_le_iff₀ (sq_pos_of_pos hδ)).mp hprec
  have hb : Real.exp (-a*δ^2) ≤ (4*(Ncount 0 T : ℝ)^2)⁻¹ := by
    calc
      _ ≤ Real.exp (-Real.log (4*(Ncount 0 T : ℝ)^2)) :=
        Real.exp_le_exp.mpr (by linarith only [hc])
      _ = _ := by rw [Real.exp_neg, Real.exp_log (by positivity)]
  apply (unequalGaussianTotal_le_of_separation hN ha hδ.le hsep).trans
  apply (mul_le_mul_of_nonneg_left hb (sq_nonneg (Ncount 0 T : ℝ))).trans_eq
  field_simp [hn.ne']
  <;> ring

/-- The reconstructed excess is at most half a unit from the collision integer. -/
theorem absolute_gaussian_half_error {a T : ℝ} (hN : 0 < Ncount 0 T) (ha : 0 < a)
    (hu : unequalGaussianTotal a T ≤ 1 / 4) :
    |absoluteGaussianExcess a T - ((actualCollision T : ℝ) - (Ncount 0 T : ℝ))| ≤ 1 / 2 := by
  obtain ⟨hl, hr⟩ := abs_le.mp (absolute_gaussian_quarter_error hN ha)
  have hp := unequalGaussianTotal_nonneg a T
  exact abs_le.mpr ⟨by linarith only [hr, hp], by linarith only [hl, hu]⟩

/-- Half-unit accuracy identifies the even collision excess for any real statistic. -/
theorem decode_collision_of_half_error {T S : ℝ}
    (h : |S - ((actualCollision T : ℝ) - (Ncount 0 T : ℝ))| ≤ 1/2) :
    2 * ⌊(S+1)/2⌋₊ = actualCollision T - Ncount 0 T := by
  obtain ⟨hl,hr⟩ := abs_le.mp h
  have hs := actualCollision_eq_count_add_excess T
  have hle : Ncount 0 T ≤ actualCollision T := by omega
  obtain ⟨k, hk⟩ := actualCollision_sub_count_even T
  have he : (actualCollision T : ℝ) - (Ncount 0 T : ℝ) = (k : ℝ) + k := by
    rw [← Nat.cast_sub hle, hk, Nat.cast_add]
  have hn : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
  have hfloor : ⌊(S + 1)/2⌋₊ = k :=
    (Nat.floor_eq_iff (by linarith only [hl, he, hn])).mpr
      ⟨by linarith only [hl, he], by linarith only [hr, he]⟩
  rw [hfloor, hk, two_mul]

/-- Nearest-even decoding is unambiguous, including at the half-unit boundary. -/
theorem absolute_gaussian_recovers_collision {a T δ : ℝ} (hN : 0 < Ncount 0 T) (ha : 0 < a)
    (hδ : 0 < δ) (hprec : Real.log (4 * (Ncount 0 T : ℝ)^2) / δ^2 ≤ a)
    (hsep : ∀ i j : Copies T, copyOrdinate T i ≠ copyOrdinate T j → δ ≤ |gaussianSeparation T i j|) :
    2 * ⌊(absoluteGaussianExcess a T + 1)/2⌋₊ = actualCollision T - Ncount 0 T :=
  decode_collision_of_half_error
    (absolute_gaussian_half_error hN ha (unequalGaussianTotal_le_quarter hN ha.le hδ hprec hsep))

/-- Both finite certificates detect the same integer event with the original labels. -/
theorem absolute_gaussian_iff_two_prime_fejer {T : ℝ} (hT : 1 < T) (hN : 0 < Ncount 0 T) :
    (∃ k : ℕ, absoluteGaussianExcess ((k : ℝ)+1) T < 1) ↔
      ∃ M : ℕ, TwoPrimeCompactCollision.compactEnergy (copyOrdinate T) M < (Ncount 0 T : ℝ)+2 := by
  rw [absolute_gaussian_finite_iff hT hN]
  constructor
  · intro hc
    have he : (occurrenceCollision (copyOrdinate T) : ℝ) = (Ncount 0 T : ℝ) := by
      exact_mod_cast hc
    apply ((TwoPrimeCompactCollision.compactEnergy_tendsto (copyOrdinate T)).eventually_lt_const
      (show (occurrenceCollision (copyOrdinate T) : ℝ) < (Ncount 0 T : ℝ)+2 by linarith only [he])).exists
  · rintro ⟨M, hm⟩
    have he := (TwoPrimeCompactCollision.actualCollision_le_compactEnergy T M).trans_lt hm
    have hn : actualCollision T < Ncount 0 T + 2 := by exact_mod_cast he
    have hsum := actualCollision_eq_count_add_excess T
    obtain ⟨k, hk⟩ := actualCollision_sub_count_even T
    omega

/--
info: 'RiemannResearch.Analysis.ActualZeroOrdinate.absolute_gaussian_recovers_collision' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms absolute_gaussian_recovers_collision

/--
info: 'RiemannResearch.Analysis.ActualZeroOrdinate.cofinal_absolute_gaussian_iff_global' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms cofinal_absolute_gaussian_iff_global

end RiemannResearch.Analysis.ActualZeroOrdinate
