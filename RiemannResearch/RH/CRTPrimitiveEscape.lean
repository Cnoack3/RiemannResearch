import RiemannResearch.RH.CRTGCDGram
import RiemannResearch.RH.ParetoResidueMoments
import RiemannResearch.RH.ParetoNoiseSignal
import RiemannResearch.RH.ParetoPrimitiveEnergy

/-!
# Exact obstruction to uniform CRT primitive transfer

Source: direct specialization of the user's CRT program to the binary residue,
using the existing exact Pareto dilation and residue moments.
Every energy is the complete infinite Pareto sum. The two-conductor family
has zero reciprocal charge; its Pareto mean is log 2. A three-conductor family
also has zero Pareto mean. These examples refute a uniform inverse-difference
estimate, not RH or convergence of the actual optimal projections.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.CRTPrimitiveEscape
open RiemannResearch.RH.Pareto
open RiemannResearch.RH.Pareto.CRTSparseEnergy

def binaryPrimitive (m : ℕ) : ℕ → ℝ := dilation m (residue 2)

def binaryJump (m k : ℕ) : ℝ := binaryPrimitive m k - binaryPrimitive m (k-1)

def alternatingProfile (k : ℕ) : ℝ := 1 - if 2 ∣ k then 2 else 0

theorem binaryPrimitive_legal (m k : ℕ) :
    binaryPrimitive m k = residue (2*m) k - residue m k := by
  simpa only [binaryPrimitive, Nat.mul_comm m 2] using residue_mul_floor m 2 k

theorem binaryPrimitive_mean (m : ℕ) (hm : 0 < m) :
    paretoMean (binaryPrimitive m) = Real.log 2 := by
  change paretoMean (dilation m (residue 2)) = _
  rw [paretoMean_dilation (fun k => residue_abs_le 2 k (by norm_num))
    (by simp [residue]) m hm, paretoMean_residue_two]

theorem binaryPrimitive_energy (m : ℕ) (hm : 0 < m) :
    paretoInner (binaryPrimitive m) (binaryPrimitive m) = (m : ℝ)*Real.log 2 := by
  change paretoInner (dilation m (residue 2)) (dilation m (residue 2)) = _
  rw [paretoInner_dilation (fun k => residue_abs_le 2 k (by norm_num))
    (fun k => residue_abs_le 2 k (by norm_num))
    (by simp [residue]) m hm, paretoInner_residue_two]

theorem binaryJump_eq (m k : ℕ) (hk : 0 < k) :
    binaryJump m k =
      (if m ∣ k then (m : ℝ) else 0) -
        (if m*2 ∣ k then ((m*2 : ℕ) : ℝ) else 0) := by
  unfold binaryJump
  rw [binaryPrimitive_legal, binaryPrimitive_legal]
  have he : (residue (2*m) k - residue m k) -
      (residue (2*m) (k-1) - residue m (k-1)) =
      (residue (2*m) k - residue (2*m) (k-1)) -
      (residue m k - residue m (k-1)) := by ring
  rw [he, residue_difference _ _ hk, residue_difference _ _ hk]
  simp only [Nat.mul_comm m 2]
  ring

theorem binaryJump_zero (m : ℕ) : binaryJump m 0 = 0 := by
  simp [binaryJump]

theorem binaryJump_multiple (m r : ℕ) (hm : 0 < m) (hr : 0 < r) :
    binaryJump m (m*r) = (m : ℝ)*alternatingProfile r := by
  rw [binaryJump_eq m (m*r) (Nat.mul_pos hm hr)]
  have hmd : m ∣ m*r := ⟨r, rfl⟩
  simp only [if_pos hmd, Nat.mul_dvd_mul_iff_left hm]
  by_cases hd : 2 ∣ r <;> simp [alternatingProfile, hd] <;> push_cast <;> ring

theorem binaryJump_support (m k : ℕ) (hk : ¬ m ∣ k) : binaryJump m k = 0 := by
  have hk0 : 0 < k := by
    by_contra h
    have hz : k = 0 := Nat.eq_zero_of_not_pos h
    exact hk (by simp [hz])
  have h2 : ¬ m*2 ∣ k := fun h => hk (dvd_trans (dvd_mul_right m 2) h)
  simp only [binaryJump_eq m k hk0, if_neg hk, if_neg h2, sub_self]

theorem alternatingProfile_sq (k : ℕ) : (alternatingProfile k)^2 = 1 := by
  unfold alternatingProfile
  split_ifs <;> norm_num

theorem alternatingProfile_abs (k : ℕ) : |alternatingProfile k| ≤ 1 := by
  unfold alternatingProfile
  split_ifs <;> norm_num

theorem alternatingProfile_summable :
    Summable (fun k : ℕ => (alternatingProfile (k+1)/((k : ℝ)+1))^2) :=
  bounded_profile_summable _ 1 (by norm_num) alternatingProfile_abs

theorem alternatingProfile_reference : referenceEnergy alternatingProfile = zetaTwoSeries := by
  unfold referenceEnergy
  simp_rw [div_pow, alternatingProfile_sq]
  have h := zetaTwoSeries_summable.sum_add_tsum_nat_add 1
  simpa [zetaTwoSeries, Finset.sum_range_one] using h

theorem binaryJump_energy (m : ℕ) (hm : 0 < m) :
    (∑' k : ℕ, positiveWeight k * (binaryJump m k)^2) =
      sparseEnergy m alternatingProfile := by
  exact full_physical_energy_eq_sparseEnergy m hm alternatingProfile (binaryJump m)
    (binaryJump_zero m) (fun k => binaryJump_multiple m (k+1) hm (by omega))
    (binaryJump_support m)

/-- Full derivative energy plus the complete positive CRT remainder. -/
theorem binaryJump_energy_add_remainder (m : ℕ) (hm : 0 < m) :
    (∑' k : ℕ, positiveWeight k * (binaryJump m k)^2) +
      positiveRemainder m alternatingProfile = zetaTwoSeries := by
  rw [binaryJump_energy m hm]
  simpa only [alternatingProfile_reference] using
    sparseEnergy_add_remainder m hm alternatingProfile alternatingProfile_summable

theorem binaryJump_energy_bounds (m : ℕ) (hm : 0 < m) :
    ((m : ℝ)/((m : ℝ)+1))*zetaTwoSeries ≤
      (∑' k : ℕ, positiveWeight k * (binaryJump m k)^2) ∧
      (∑' k : ℕ, positiveWeight k * (binaryJump m k)^2) ≤ zetaTwoSeries := by
  rw [binaryJump_energy m hm]
  simpa only [alternatingProfile_reference] using
    sparseEnergy_relative_bounds m hm alternatingProfile alternatingProfile_summable

/-- No conductor-independent upper bound on primitive energy can hold,
even for this exact two-residue family with zero reciprocal charge. -/
theorem no_uniform_primitive_bound :
    ¬ ∃ C : ℝ, ∀ m : ℕ, 2 ≤ m →
      paretoInner (binaryPrimitive m) (binaryPrimitive m) ≤
        C * (∑' k : ℕ, positiveWeight k * (binaryJump m k)^2) := by
  rintro ⟨C, hC⟩
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨m, hm⟩ := exists_nat_gt (max 2 (max C 0 * zetaTwoSeries / Real.log 2))
  have hm2 : 2 ≤ m := by
    have : (2 : ℝ) < m := lt_of_le_of_lt (le_max_left _ _) hm
    exact_mod_cast (le_of_lt this)
  have hmp : 0 < m := by omega
  have hbig : max C 0 * zetaTwoSeries < (m : ℝ)*Real.log 2 := by
    have hd : max C 0 * zetaTwoSeries / Real.log 2 < m :=
      lt_of_le_of_lt (le_max_right _ _) hm
    exact (div_lt_iff₀ hlog).mp hd
  have he0 : 0 ≤ ∑' k : ℕ, positiveWeight k * (binaryJump m k)^2 :=
    tsum_nonneg (fun k => mul_nonneg (positiveWeight_nonneg k) (sq_nonneg _))
  have hupper := (binaryJump_energy_bounds m hmp).2
  have hbound := hC m hm2
  rw [binaryPrimitive_energy m hmp] at hbound
  have hbound' : C * (∑' k : ℕ, positiveWeight k * (binaryJump m k)^2) ≤
      max C 0 * zetaTwoSeries :=
    (mul_le_mul_of_nonneg_right (le_max_left C 0) he0).trans
      (mul_le_mul_of_nonneg_left hupper (le_max_right C 0))
  linarith


theorem binaryPrimitive_scale_error (m : ℕ) (hm : 0 < m) (a : ℝ) :
    paretoError (fun k => a * binaryPrimitive m k) =
      1 - Real.log 2 / (m : ℝ) +
        ((m : ℝ)*Real.log 2) * (a - 1 / (m : ℝ))^2 := by
  have hb : ∀ k, |binaryPrimitive m k| ≤ (m : ℝ)*2 :=
    dilation_abs_le (fun k => residue_abs_le 2 k (by norm_num)) m
  rw [paretoError_scale hb, paretoVariance_eq hb,
    binaryPrimitive_mean m hm, binaryPrimitive_energy m hm]
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  field_simp
  <;> ring

theorem binaryPrimitive_optimal_error (m : ℕ) (hm : 0 < m) :
    paretoError (fun k => (1 / (m : ℝ)) * binaryPrimitive m k) =
      1 - Real.log 2 / (m : ℝ) := by
  rw [binaryPrimitive_scale_error m hm]
  simp

theorem binaryPrimitive_optimal_error_le (m : ℕ) (hm : 0 < m) (a : ℝ) :
    1 - Real.log 2 / (m : ℝ) ≤
      paretoError (fun k => a * binaryPrimitive m k) := by
  rw [binaryPrimitive_scale_error m hm]
  exact le_add_of_nonneg_right
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num)))
      (sq_nonneg _))


def centeredSeed (k : ℕ) : ℝ := residue 2 k - dilation 2 (residue 2) k

def centeredPrimitive (m : ℕ) : ℕ → ℝ := dilation m centeredSeed

def centeredJump (m k : ℕ) : ℝ :=
  centeredPrimitive m k - centeredPrimitive m (k-1)

theorem centeredSeed_bounded : ∀ k, |centeredSeed k| ≤ (6 : ℝ) := by
  have h := bounded_sub (fun k => residue_abs_le 2 k (by norm_num))
    (dilation_abs_le (fun k => residue_abs_le 2 k (by norm_num)) 2)
  norm_num at h
  exact h

theorem centeredSeed_energy : paretoInner centeredSeed centeredSeed = Real.pi/2 := by
  have hr : ∀ k, |residue 2 k| ≤ (2 : ℝ) := fun k => residue_abs_le 2 k (by norm_num)
  have hd := dilation_abs_le hr 2
  have hm := paretoInner_residual_polynomial hr hd 1
  have hp := paretoInner_residual_polynomial hr hd (-1)
  have he : (fun k => residue 2 k - (-1) * dilation 2 (residue 2) k) = residue 4 := by
    funext k
    rw [residue_mul_floor]
    norm_num
  rw [he, paretoInner_residue_four, paretoInner_residue_two,
    paretoInner_dilation hr hr (by simp [residue]) 2 (by norm_num),
    paretoInner_residue_two] at hp
  simp only [one_mul] at hm
  change paretoInner centeredSeed centeredSeed = _ at hm
  rw [paretoInner_residue_two,
    paretoInner_dilation hr hr (by simp [residue]) 2 (by norm_num),
    paretoInner_residue_two] at hm
  norm_num at hp hm
  linarith

theorem centeredSeed_mean : paretoMean centeredSeed = 0 := by
  have hr : ∀ k, |residue 2 k| ≤ (2 : ℝ) := fun k => residue_abs_le 2 k (by norm_num)
  unfold centeredSeed
  rw [paretoMean_sub hr (dilation_abs_le hr 2),
    paretoMean_dilation hr (by simp [residue]) 2 (by norm_num)]
  ring

theorem centeredPrimitive_energy (m : ℕ) (hm : 0 < m) :
    paretoInner (centeredPrimitive m) (centeredPrimitive m) = (m : ℝ)*Real.pi/2 := by
  unfold centeredPrimitive
  rw [paretoInner_dilation centeredSeed_bounded centeredSeed_bounded
    (by simp [centeredSeed, dilation, residue]) m hm, centeredSeed_energy]
  ring

theorem centeredPrimitive_mean (m : ℕ) (hm : 0 < m) :
    paretoMean (centeredPrimitive m) = 0 := by
  unfold centeredPrimitive
  rw [paretoMean_dilation centeredSeed_bounded
    (by simp [centeredSeed, dilation, residue]) m hm, centeredSeed_mean]

theorem centeredPrimitive_eq_binary (m k : ℕ) :
    centeredPrimitive m k = binaryPrimitive m k - binaryPrimitive (2*m) k := by
  simp only [centeredPrimitive, centeredSeed, binaryPrimitive, dilation,
    mul_sub, Nat.div_div_eq_div_mul, Nat.cast_mul, Nat.cast_ofNat]
  rw [Nat.mul_comm m 2]
  ring

theorem centeredPrimitive_legal (m k : ℕ) :
    centeredPrimitive m k =
      2*residue (2*m) k - residue m k - residue (4*m) k := by
  rw [centeredPrimitive_eq_binary, binaryPrimitive_legal, binaryPrimitive_legal]
  have hm4 : 2*(2*m) = 4*m := by omega
  rw [hm4]
  ring

theorem centeredJump_eq_binary (m k : ℕ) :
    centeredJump m k = binaryJump m k - binaryJump (2*m) k := by
  simp only [centeredJump, centeredPrimitive_eq_binary, binaryJump]
  ring

theorem binaryJump_square_summable (m : ℕ) (hm : 0 < m) :
    Summable (fun k => positiveWeight k * (binaryJump m k)^2) := by
  have hp := dilation_abs_le (fun k => residue_abs_le 2 k (by norm_num)) m
  have hb : ∀ k, |binaryJump m k| ≤ (m : ℝ)*2 + (m : ℝ)*2 :=
    bounded_sub hp (fun k => hp (k-1))
  simpa only [pow_two] using weighted_summable_of_bounded (bounded_product hb hb)

theorem centeredJump_square_summable (m : ℕ) (hm : 0 < m) :
    Summable (fun k => positiveWeight k * (centeredJump m k)^2) := by
  have hp := dilation_abs_le centeredSeed_bounded m
  have hb : ∀ k, |centeredJump m k| ≤ (m : ℝ)*6 + (m : ℝ)*6 :=
    bounded_sub hp (fun k => hp (k-1))
  simpa only [pow_two] using weighted_summable_of_bounded (bounded_product hb hb)

theorem centeredJump_energy_le (m : ℕ) (hm : 0 < m) :
    (∑' k, positiveWeight k * (centeredJump m k)^2) ≤ 4*zetaTwoSeries := by
  have h2m : 0 < 2*m := by omega
  have hpoint (k : ℕ) : positiveWeight k * (centeredJump m k)^2 ≤
      2*(positiveWeight k * (binaryJump m k)^2) +
        2*(positiveWeight k * (binaryJump (2*m) k)^2) := by
    rw [centeredJump_eq_binary]
    have hsq := sq_nonneg (binaryJump m k + binaryJump (2*m) k)
    have hw := positiveWeight_nonneg k
    nlinarith [mul_nonneg hw hsq]
  have hsum := (centeredJump_square_summable m hm).tsum_le_tsum hpoint
    (((binaryJump_square_summable m hm).mul_left 2).add
      ((binaryJump_square_summable (2*m) h2m).mul_left 2))
  rw [(((binaryJump_square_summable m hm).mul_left 2).tsum_add
    ((binaryJump_square_summable (2*m) h2m).mul_left 2)), tsum_mul_left, tsum_mul_left] at hsum
  have h1 := (binaryJump_energy_bounds m hm).2
  have h2 := (binaryJump_energy_bounds (2*m) h2m).2
  linarith

theorem no_uniform_centered_primitive_bound :
    ¬ ∃ C : ℝ, ∀ m : ℕ, 2 ≤ m →
      paretoInner (centeredPrimitive m) (centeredPrimitive m) ≤
        C * (∑' k : ℕ, positiveWeight k * (centeredJump m k)^2) := by
  rintro ⟨C, hC⟩
  have hpi : 0 < Real.pi/2 := by positivity
  obtain ⟨m, hm⟩ := exists_nat_gt (max 2 (max C 0 * (4*zetaTwoSeries) / (Real.pi/2)))
  have hm2 : 2 ≤ m := by
    have : (2 : ℝ) < m := lt_of_le_of_lt (le_max_left _ _) hm
    exact_mod_cast (le_of_lt this)
  have hmp : 0 < m := by omega
  have hbig : max C 0 * (4*zetaTwoSeries) < (m : ℝ)*(Real.pi/2) := by
    have hd : max C 0 * (4*zetaTwoSeries) / (Real.pi/2) < m :=
      lt_of_le_of_lt (le_max_right _ _) hm
    exact (div_lt_iff₀ hpi).mp hd
  have he0 : 0 ≤ ∑' k : ℕ, positiveWeight k * (centeredJump m k)^2 :=
    tsum_nonneg (fun k => mul_nonneg (positiveWeight_nonneg k) (sq_nonneg _))
  have hupper := centeredJump_energy_le m hmp
  have hbound := hC m hm2
  rw [centeredPrimitive_energy m hmp] at hbound
  have hbound' : C * (∑' k : ℕ, positiveWeight k * (centeredJump m k)^2) ≤
      max C 0 * (4*zetaTwoSeries) :=
    (mul_le_mul_of_nonneg_right (le_max_left C 0) he0).trans
      (mul_le_mul_of_nonneg_left hupper (le_max_right C 0))
  nlinarith


theorem binaryPrimitive_scaled_energy (m : ℕ) (hm : 0 < m) (a : ℝ) :
    paretoInner (fun k => a*binaryPrimitive m k) (fun k => a*binaryPrimitive m k) =
      a^2 * ((m : ℝ)*Real.log 2) := by
  have hb : ∀ k, |binaryPrimitive m k| ≤ (m : ℝ)*2 :=
    dilation_abs_le (fun k => residue_abs_le 2 k (by norm_num)) m
  rw [paretoInner_const_mul_left hb (bounded_const_mul hb a),
    paretoInner_const_mul_right hb hb, binaryPrimitive_energy m hm]
  ring

theorem binaryJump_scaled_energy (m : ℕ) (a : ℝ) :
    (∑' k : ℕ, positiveWeight k *
      (a*binaryPrimitive m k - a*binaryPrimitive m (k-1))^2) =
      a^2 * (∑' k : ℕ, positiveWeight k * (binaryJump m k)^2) := by
  calc
    _ = ∑' k : ℕ, a^2 * (positiveWeight k * (binaryJump m k)^2) := by
      apply tsum_congr
      intro k
      unfold binaryJump
      ring
    _ = _ := tsum_mul_left

theorem normalized_binaryPrimitive_energy (m : ℕ) (hm : 0 < m) :
    paretoInner (fun k => (1/Real.sqrt (m : ℝ))*binaryPrimitive m k)
      (fun k => (1/Real.sqrt (m : ℝ))*binaryPrimitive m k) = Real.log 2 := by
  rw [binaryPrimitive_scaled_energy m hm, div_pow, one_pow,
    Real.sq_sqrt (Nat.cast_nonneg m)]
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  field_simp

theorem normalized_binaryJump_energy_le (m : ℕ) (hm : 0 < m) :
    (∑' k : ℕ, positiveWeight k *
      ((1/Real.sqrt (m : ℝ))*binaryPrimitive m k -
        (1/Real.sqrt (m : ℝ))*binaryPrimitive m (k-1))^2) ≤
      zetaTwoSeries / (m : ℝ) := by
  rw [binaryJump_scaled_energy, div_pow, one_pow,
    Real.sq_sqrt (Nat.cast_nonneg m)]
  have h := mul_le_mul_of_nonneg_left (binaryJump_energy_bounds m hm).2
    (show 0 ≤ 1/(m : ℝ) by positivity)
  simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using h

theorem binaryPrimitive_zero_of_lt (m k : ℕ) (hk : k < m) :
    binaryPrimitive m k = 0 := by
  simp [binaryPrimitive, dilation, residue, Nat.div_eq_of_lt hk]

theorem normalized_binary_approximate_kernel (ε : ℝ) (hε : 0 < ε) :
    ∃ m : ℕ, 2 ≤ m ∧
      paretoInner (fun k => (1/Real.sqrt (m : ℝ))*binaryPrimitive m k)
        (fun k => (1/Real.sqrt (m : ℝ))*binaryPrimitive m k) = Real.log 2 ∧
      (∑' k : ℕ, positiveWeight k *
        ((1/Real.sqrt (m : ℝ))*binaryPrimitive m k -
          (1/Real.sqrt (m : ℝ))*binaryPrimitive m (k-1))^2) < ε := by
  obtain ⟨m, hm⟩ := exists_nat_gt (max 2 (zetaTwoSeries / ε))
  have hm2 : 2 ≤ m := by
    have : (2 : ℝ) < m := lt_of_le_of_lt (le_max_left _ _) hm
    exact_mod_cast (le_of_lt this)
  have hmp : 0 < m := by omega
  refine ⟨m, hm2, normalized_binaryPrimitive_energy m hmp, ?_⟩
  apply lt_of_le_of_lt (normalized_binaryJump_energy_le m hmp)
  apply (div_lt_iff₀ (show (0 : ℝ) < m by positivity)).mpr
  have hd : zetaTwoSeries / ε < m := lt_of_le_of_lt (le_max_right _ _) hm
  have hh := (div_lt_iff₀ hε).mp hd
  nlinarith

end RiemannResearch.RH.Pareto.CRTPrimitiveEscape


namespace RiemannResearch.RH.Pareto.CRTPrimitiveEscape
open RiemannResearch.RH.Pareto.CRTSparseEnergy
open RiemannResearch.RH.Pareto.PrimitiveEnergy

/-- Exact growth of the two full primitive remainders, with the positive
sparse CRT remainder still present. -/
theorem binaryPrimitive_full_remainder (m : ℕ) (hm : 0 < m) :
    4 * (m : ℝ) * Real.log 2 + positiveRemainder m alternatingProfile =
      zetaTwoSeries + energy (symmetricPrimitive (binaryPrimitive m)) +
        2 * shiftDefect (binaryPrimitive m) := by
  have hb : ∀ k, |binaryPrimitive m k| ≤ (m : ℝ)*2 :=
    dilation_abs_le (fun k => residue_abs_le 2 k (by norm_num)) m
  have h := full_primitive_energy_identity hb
  have he : energy (binaryPrimitive m) = (m : ℝ)*Real.log 2 :=
    binaryPrimitive_energy m hm
  have hd : energy (difference (binaryPrimitive m)) =
      ∑' k : ℕ, positiveWeight k * (binaryJump m k)^2 := by
    change (∑' k : ℕ, positiveWeight k *
      ((binaryPrimitive m k - binaryPrimitive m (k-1)) *
        (binaryPrimitive m k - binaryPrimitive m (k-1)))) = _
    simp only [binaryJump, pow_two]
  rw [he, hd] at h
  have hr := binaryJump_energy_add_remainder m hm
  linarith

end RiemannResearch.RH.Pareto.CRTPrimitiveEscape
