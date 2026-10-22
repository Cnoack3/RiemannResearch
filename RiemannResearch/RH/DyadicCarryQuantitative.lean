import RiemannResearch.RH.DyadicCarryCRT
import RiemannResearch.RH.DilationWaveletOffScale
import RiemannResearch.RH.NearbyDilationGram

/-!
# Quantitative transport from whole carry blocks to the constant

Source: the user-provided odd-carry continuation, 2026-09-20. The elementary
head/tail estimate below quantifies the previously established convergence.
It bounds the cost of converting a legal carry-block approximant to a legal
constant approximant; it does not construct either missing approximant.
-/

noncomputable section
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto
open RiemannResearch.RH.ArithmeticCumulative

theorem dyadicSampledResidue_coordinate_bounds (k n : ℕ) :
    0 ≤ hilbertSequence (dyadicSampledResidue k) n ∧
      hilbertSequence (dyadicSampledResidue k) n ≤ 1 := by
  rw [dyadicSampledResidue_sequence]
  unfold residueFraction
  constructor
  · positivity
  · apply le_of_lt
    apply (div_lt_one (by positivity :
      (0 : ℝ) < ((2 ^ k + 1 : ℕ) : ℝ))).mpr
    exact_mod_cast Nat.mod_lt (2 ^ k * n) (by positivity : 0 < 2 ^ k + 1)

/-- The actual infinite weighted error is at most twice the reciprocal modulus. -/
theorem dyadicSampledResidue_error_sq_le (k : ℕ) :
    ‖dyadicSampledResidue k - hilbertOne‖ ^ 2 ≤
      2 / ((2 ^ k + 1 : ℕ) : ℝ) := by
  let d : ℕ := 2 ^ k + 1
  have hd : 0 < d := by dsimp [d]; positivity
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  let e := hilbertSequence (dyadicSampledResidue k - hilbertOne)
  have he (n : ℕ) : e n =
      hilbertSequence (dyadicSampledResidue k) n - hilbertSequence hilbertOne n := by
    exact congrFun (hilbertSequenceLinear.map_sub _ _) n
  have hs : Summable (fun n => positiveWeight n * e n ^ 2) :=
    hilbertSequence_square_summable _
  have hhead (n : ℕ) (hn : n ∈ Finset.range d) :
      positiveWeight n * e n ^ 2 ≤ 1 / (d : ℝ) ^ 2 := by
    by_cases hn0 : n = 0
    · subst n
      simp only [he, hilbertSequence_zero, sub_self, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
      positivity
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hen : e n = -(n : ℝ) / d := by
      rw [he, dyadicSampledResidue_sequence,
        reverseResidue_head _ _ hnpos (Finset.mem_range.mp hn), hilbertOne_sequence]
      simp [zeroAnchor, hn0, d]
      ring
    rw [hen]
    have hi : (n : ℝ) / ((n : ℝ) + 1) ≤ 1 :=
      (div_le_one (by positivity)).mpr (by linarith)
    calc
      _ = ((n : ℝ) / ((n : ℝ) + 1)) / (d : ℝ) ^ 2 := by
        unfold positiveWeight
        field_simp
      _ ≤ 1 / (d : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hi (sq_nonneg _)
  have htail (n : ℕ) : positiveWeight (n + d) * e (n + d) ^ 2 ≤
      positiveWeight (n + d) := by
    have hn0 : n + d ≠ 0 := by omega
    have hb := dyadicSampledResidue_coordinate_bounds k (n + d)
    have he1 : e (n + d) =
        hilbertSequence (dyadicSampledResidue k) (n + d) - 1 := by
      rw [he, hilbertOne_sequence]
      simp [zeroAnchor]
    have hh : e (n + d) ^ 2 ≤ 1 := by
      rw [he1]
      nlinarith [mul_nonneg hb.1 (sub_nonneg.mpr hb.2)]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hh (positiveWeight_nonneg _)
  rw [hilbert_norm_weighted_sq, ← hs.sum_add_tsum_nat_add d]
  change (∑ n ∈ Finset.range d, positiveWeight n * e n ^ 2) +
      (∑' n, positiveWeight (n + d) * e (n + d) ^ 2) ≤ 2 / (d : ℝ)
  have hfin : (∑ n ∈ Finset.range d, positiveWeight n * e n ^ 2) ≤
      1 / (d : ℝ) := by
    calc
      _ ≤ ∑ _n ∈ Finset.range d, 1 / (d : ℝ) ^ 2 := Finset.sum_le_sum hhead
      _ = 1 / (d : ℝ) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp
  have hinf : (∑' n, positiveWeight (n + d) * e (n + d) ^ 2) ≤
      1 / (d : ℝ) := by
    calc
      _ ≤ ∑' n, positiveWeight (n + d) :=
        Summable.tsum_le_tsum htail ((summable_nat_add_iff d).mpr hs)
          ((summable_nat_add_iff d).mpr positiveWeight_summable)
      _ = _ := positiveWeight_tail_tsum d hd
  calc
    _ ≤ 1 / (d : ℝ) + 1 / (d : ℝ) := add_le_add hfin hinf
    _ = _ := by ring

theorem dyadicSampledResidue_error_le (k : ℕ) :
    ‖dyadicSampledResidue k - hilbertOne‖ ≤
      Real.sqrt (2 / ((2 ^ k + 1 : ℕ) : ℝ)) := by
  exact (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr
    (dyadicSampledResidue_error_sq_le k)

/-- After subtracting the legal residue, the error is supported on multiples. -/
def dyadicMultipleIndicator (k : ℕ) : ThresholdHilbert :=
  hilbertOne -
    (normalizedResidueHilbert (2 ^ k + 1) (by positivity) + dyadicSampledResidue k)

@[simp] theorem dyadicMultipleIndicator_sequence (k n : ℕ) :
    hilbertSequence (dyadicMultipleIndicator k) n =
      if n = 0 then 0 else if (2 ^ k + 1) ∣ n then 1 else 0 := by
  have he : hilbertSequence (dyadicMultipleIndicator k) =
      hilbertSequence hilbertOne -
        (hilbertSequence (normalizedResidueHilbert (2 ^ k + 1) (by positivity)) +
          hilbertSequence (dyadicSampledResidue k)) := by
    exact (hilbertSequenceLinear.map_sub _ _).trans
      (congrArg (fun f => hilbertSequence hilbertOne - f)
        (hilbertSequenceLinear.map_add _ _))
  rw [he, Pi.sub_apply, Pi.add_apply, normalizedResidueHilbert_sequence,
    dyadicSampledResidue_sequence, add_comm, residueFraction_reverse_all,
    sub_add_cancel, hilbertOne_sequence]
  by_cases hn : n = 0
  · subst n; simp [zeroAnchor]
  · simp only [zeroAnchor, hn, if_false]
    split_ifs <;> norm_num

/-- Exact sparse energy: only positive multiples of the modulus contribute. -/
theorem dyadicMultipleIndicator_norm_sq (k : ℕ) :
    ‖dyadicMultipleIndicator k‖ ^ 2 =
      ∑' a : ℕ, positiveWeight ((2 ^ k + 1) * (a + 1)) := by
  let d : ℕ := 2 ^ k + 1
  have hd : 0 < d := by dsimp [d]; positivity
  rw [hilbert_norm_weighted_sq]
  apply tsum_eq_tsum_of_ne_zero_bij
    (fun a : Function.support (fun a : ℕ => positiveWeight (d * (a + 1))) =>
      d * (a.val + 1))
  · intro a b hab
    apply Subtype.ext
    have h := Nat.eq_of_mul_eq_mul_left hd hab
    omega
  · intro n hn
    have hnz : n ≠ 0 := by
      intro h; subst n
      simpa only [Function.mem_support, hilbertSequence_zero, zero_pow (by omega : 2 ≠ 0),
        mul_zero, ne_eq, not_true_eq_false] using hn
    have hdiv : d ∣ n := by
      by_contra h
      have hz : hilbertSequence (dyadicMultipleIndicator k) n = 0 := by
        simp [dyadicMultipleIndicator_sequence, hnz, show ¬ (2 ^ k + 1) ∣ n from h]
      simpa only [Function.mem_support, hz, zero_pow (by omega : 2 ≠ 0),
        mul_zero, ne_eq, not_true_eq_false] using hn
    obtain ⟨a, rfl⟩ := hdiv
    have ha : 0 < a := by
      by_contra h
      have hz : a = 0 := Nat.eq_zero_of_not_pos h
      simp [hz] at hnz
    refine ⟨⟨a - 1, ?_⟩, ?_⟩
    · change positiveWeight (d * (a - 1 + 1)) ≠ 0
      unfold positiveWeight
      positivity
    · simp [Nat.sub_add_cancel ha]
  · intro a
    have hn : d * (a.val + 1) ≠ 0 := by positivity
    have hv : (2 ^ k + 1) ∣ d * (a.val + 1) := dvd_mul_right _ _
    simp only [dyadicMultipleIndicator_sequence, hn, if_false, hv, if_true,
      one_pow, mul_one]

theorem dyadicMultipleIndicator_norm_sq_le (k : ℕ) :
    ‖dyadicMultipleIndicator k‖ ^ 2 ≤ 2 / ((2 ^ k + 1 : ℕ) : ℝ) ^ 2 := by
  let d : ℕ := 2 ^ k + 1
  have hd : 0 < d := by dsimp [d]; positivity
  have hs := (summable_nat_add_iff 1).mpr positiveWeight_summable
  have hg := hs.mul_left (2 / (d : ℝ) ^ 2)
  have hb (a : ℕ) : positiveWeight (d * (a + 1)) ≤
      (2 / (d : ℝ) ^ 2) * positiveWeight (a + 1) :=
    positiveWeight_mul_bound d (a + 1) hd
  have hf : Summable (fun a : ℕ => positiveWeight (d * (a + 1))) :=
    Summable.of_nonneg_of_le (fun _ => positiveWeight_nonneg _) hb hg
  rw [dyadicMultipleIndicator_norm_sq]
  calc
    _ ≤ ∑' a : ℕ, (2 / (d : ℝ) ^ 2) * positiveWeight (a + 1) :=
      hf.tsum_le_tsum hb hg
    _ = 2 / (d : ℝ) ^ 2 := by
      rw [tsum_mul_left, positiveWeight_tail_tsum 1 (by omega)]
      norm_num

namespace CoefficientStabilization

/-- The full projected discrepancy is exactly the sparse-multiple discrepancy. -/
theorem dyadicCarryBlock_projection_sparse (k : ℕ) :
    (dyadicCarryBlock k (2 ^ k + 1) (by positivity) -
      closedSpace.starProjection (dyadicCarryBlock k (2 ^ k + 1) (by positivity))) +
      (hilbertOne - closedSpace.starProjection hilbertOne) =
      dyadicMultipleIndicator k - closedSpace.starProjection (dyadicMultipleIndicator k) := by
  rw [dyadicCarryBlock_projection_residual]
  have hg := Submodule.starProjection_eq_self_iff.mpr
    (normalizedResidue_mem_closedSpace (2 ^ k + 1) (by positivity))
  dsimp [dyadicMultipleIndicator]
  rw [map_sub, map_add, hg]
  abel

/-- Quantitative convergence of the optimum, without asserting its limit is zero. -/
theorem dyadicCarryGap_error_le (k : ℕ) :
    |dyadicCarryGap k - ‖hilbertOne - closedSpace.starProjection hilbertOne‖| ≤
      Real.sqrt (2 / ((2 ^ k + 1 : ℕ) : ℝ) ^ 2) := by
  have h := abs_norm_sub_norm_le
    (dyadicCarryBlock k (2 ^ k + 1) (by positivity) -
      closedSpace.starProjection (dyadicCarryBlock k (2 ^ k + 1) (by positivity)))
    (-(hilbertOne - closedSpace.starProjection hilbertOne))
  rw [norm_neg, sub_neg_eq_add, dyadicCarryBlock_projection_sparse] at h
  change |dyadicCarryGap k - ‖hilbertOne - closedSpace.starProjection hilbertOne‖| ≤ _ at h
  have hp : ‖dyadicMultipleIndicator k - closedSpace.starProjection (dyadicMultipleIndicator k)‖ ≤
      ‖dyadicMultipleIndicator k‖ := by
    rw [← Submodule.starProjection_orthogonal_val]
    exact closedSpaceᗮ.norm_starProjection_apply_le _
  exact h.trans (hp.trans ((Real.le_sqrt (norm_nonneg _) (by positivity)).mpr
    (dyadicMultipleIndicator_norm_sq_le k)))

/-- Affine conversion keeps the legal-space constraint exactly. -/
theorem dyadicCarryBlock_transport_mem (k : ℕ) (v : ThresholdHilbert)
    (hv : v ∈ closedSpace) :
    ((2 ^ k + 1 : ℕ) : ℝ) • normalizedResidueHilbert (2 ^ k + 1) (by positivity) - v ∈
      closedSpace :=
  closedSpace.sub_mem
    (closedSpace.smul_mem _ (normalizedResidue_mem_closedSpace _ _)) hv

/-- Quantitative transfer for every candidate, without dropping mixed terms. -/
theorem dyadicCarryBlock_transport_error (k : ℕ) (v : ThresholdHilbert) :
    |‖hilbertOne -
        (((2 ^ k + 1 : ℕ) : ℝ) • normalizedResidueHilbert (2 ^ k + 1) (by positivity) - v)‖ -
      ‖dyadicCarryBlock k (2 ^ k + 1) (by positivity) - v‖| ≤
      Real.sqrt (2 / ((2 ^ k + 1 : ℕ) : ℝ) ^ 2) := by
  have h := abs_norm_sub_norm_le
    (hilbertOne -
      (((2 ^ k + 1 : ℕ) : ℝ) • normalizedResidueHilbert (2 ^ k + 1) (by positivity) - v))
    (-(dyadicCarryBlock k (2 ^ k + 1) (by positivity) - v))
  have he : hilbertOne -
        (((2 ^ k + 1 : ℕ) : ℝ) • normalizedResidueHilbert (2 ^ k + 1) (by positivity) - v) -
      (-(dyadicCarryBlock k (2 ^ k + 1) (by positivity) - v)) =
      dyadicMultipleIndicator k := by
    dsimp [dyadicCarryBlock, dyadicMultipleIndicator, dyadicSampledResidue]
    push_cast
    simp only [add_smul, one_smul]
    abel
  rw [norm_neg, he] at h
  exact h.trans ((Real.le_sqrt (norm_nonneg _) (by positivity)).mpr
    (dyadicMultipleIndicator_norm_sq_le k))

end CoefficientStabilization
end RiemannResearch.RH.Pareto
