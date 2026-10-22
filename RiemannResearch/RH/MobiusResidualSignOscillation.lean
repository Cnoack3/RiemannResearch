import RiemannResearch.RH.MobiusResidualEscape
import RiemannResearch.RH.ThresholdHilbertAdjoint
import RiemannResearch.RH.ParetoReciprocalDifference

/-!
# Order of Mobius coordinates and residual sign oscillation

Source: independent continuation of the project's finite Mobius inversion,
physical sublinearity, and residual reconstruction escape, 24 September 2026.
No mathematical novelty is claimed.

For any vector whose Mobius charges are nonnegative at all moduli >= 2,
the ordered reconstructions lie pointwise between that vector and zero,
and have norm at most its norm. Subtracting a finite reconstruction extends
the argument to eventual sign conditions.

For the ACTUAL limiting orthogonal residual, eventual one-sided charges
would imply RH. Contrapositively, failure of RH forces positive and negative
limiting Mobius corrections arbitrarily far out. The eventual-sign premise
is an OPEN arithmetic condition; this module does not prove it.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto
open RiemannResearch.RH.ArithmeticCumulative
namespace CoefficientStabilization

theorem coefficientCLM_coordinatePartialSum (f : ThresholdHilbert)
    (N m : ℕ) (hm : 1 < m) :
    coefficientCLM m (coordinatePartialSum f N) =
      if m ≤ N + 1 then coefficientCLM m f else 0 := by
  classical
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, m = j + 2 := ⟨m - 2, by omega⟩
  by_cases hj : j < N
  · rw [if_pos (show j + 2 ≤ N + 1 by omega)]
    exact coefficient_finite_sum N
      (fun i : Fin N => coefficientCLM (i.val + 2) f) ⟨j, hj⟩
  · rw [if_neg (show ¬ j + 2 ≤ N + 1 by omega)]
    simp only [coordinatePartialSum, map_sum, map_smul,
      coefficientCLM_biorthogonal]
    apply Finset.sum_eq_zero
    intro i _
    have hji : j ≠ i.val := by
      intro he
      apply hj
      rw [he]
      exact i.isLt
    simp [hji]

theorem mobiusDifferenceCLM_coordinatePartialSum (f : ThresholdHilbert)
    (N m : ℕ) (hm : 1 < m) :
    mobiusDifferenceCLM m (coordinatePartialSum f N) =
      if m ≤ N + 1 then mobiusDifferenceCLM m f else 0 := by
  have hc := coefficientCLM_coordinatePartialSum f N m hm
  change -(mobiusDifferenceCLM m (coordinatePartialSum f N)) =
    (if m ≤ N + 1 then -(mobiusDifferenceCLM m f) else 0) at hc
  by_cases h : m ≤ N + 1
  · rw [if_pos h] at hc ⊢
    linarith
  · rw [if_neg h] at hc ⊢
    exact neg_eq_zero.mp hc

theorem mobiusDifferenceCLM_sub_coordinatePartialSum
    (f : ThresholdHilbert) (N m : ℕ) (hm : 1 < m) :
    mobiusDifferenceCLM m (f - coordinatePartialSum f N) =
      if m ≤ N + 1 then 0 else mobiusDifferenceCLM m f := by
  rw [map_sub, mobiusDifferenceCLM_coordinatePartialSum f N m hm]
  split_ifs <;> simp

theorem mobiusDifferenceCLM_sub_coordinatePartialSum_nonneg
    (f : ThresholdHilbert) (N : ℕ)
    (hf : ∀ m : ℕ, N + 1 < m → 0 ≤ mobiusDifferenceCLM m f) :
    ∀ m : ℕ, 1 < m →
      0 ≤ mobiusDifferenceCLM m (f - coordinatePartialSum f N) := by
  intro m hm
  rw [mobiusDifferenceCLM_sub_coordinatePartialSum f N m hm]
  split_ifs with h
  · exact le_rfl
  · exact hf m (by omega)

theorem coordinatePartialSum_sub (f g : ThresholdHilbert) (N : ℕ) :
    coordinatePartialSum (f - g) N =
      coordinatePartialSum f N - coordinatePartialSum g N := by
  simp only [coordinatePartialSum, map_sub, sub_smul,
    Finset.sum_sub_distrib]

theorem coordinatePartialSum_neg (f : ThresholdHilbert) (N : ℕ) :
    coordinatePartialSum (-f) N = -coordinatePartialSum f N := by
  simp only [coordinatePartialSum, map_neg, neg_smul,
    Finset.sum_neg_distrib]

theorem coordinatePartialSum_nested (f : ThresholdHilbert)
    (D N : ℕ) (hDN : D ≤ N) :
    coordinatePartialSum (coordinatePartialSum f D) N =
      coordinatePartialSum f D := by
  apply sub_eq_zero.mp
  apply eq_zero_of_mobius_coordinates_zero
  intro m hm
  have hc : coefficientCLM m
      (coordinatePartialSum (coordinatePartialSum f D) N -
        coordinatePartialSum f D) = 0 := by
    rw [map_sub, coefficientCLM_coordinatePartialSum
      (coordinatePartialSum f D) N m hm]
    by_cases hmN : m ≤ N + 1
    · rw [if_pos hmN, sub_self]
    · rw [if_neg hmN, coefficientCLM_coordinatePartialSum f D m hm,
        if_neg (show ¬ m ≤ D + 1 by omega)]
      simp
  change -(mobiusDifferenceCLM m
    (coordinatePartialSum (coordinatePartialSum f D) N -
      coordinatePartialSum f D)) = 0 at hc
  exact neg_eq_zero.mp hc

end CoefficientStabilization

theorem firstCoordinate_nonpos_of_mobius_nonneg (f : ThresholdHilbert)
    (hf : ∀ m : ℕ, 1 < m → 0 ≤ mobiusDifferenceCLM m f) :
    hilbertSequence f 1 ≤ 0 := by
  have hstep (n : ℕ) :
      hilbertSequence f 1 ≤ hilbertSequence f (n + 1) - hilbertSequence f n := by
    have hi := sum_mobiusDifference (hilbertSequence f) (n + 1) (by omega)
    simp only [Nat.add_sub_cancel] at hi
    rw [← hi]
    calc
      _ = ∑ d ∈ (n + 1).divisors,
          if d = 1 then hilbertSequence f 1 else 0 := by simp [Nat.mem_divisors]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro d hd
        by_cases h1 : d = 1
        · subst d
          simp [mobiusDifference]
        · rw [if_neg h1]
          have hp := Nat.pos_of_mem_divisors hd
          simpa only [mobiusDifferenceCLM_apply] using hf d (by omega)
  have hlower (n : ℕ) :
      (n : ℝ) * hilbertSequence f 1 ≤ hilbertSequence f n := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hh := hstep n
      push_cast
      nlinarith
  apply ge_of_tendsto (hilbert_physical_sublinear f)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  apply (le_div_iff₀ hnpos).mpr
  nlinarith [hlower n]

namespace CoefficientStabilization

theorem coordinatePartialSum_nonpos_of_mobius_nonneg
    (f : ThresholdHilbert)
    (hf : ∀ m : ℕ, 1 < m → 0 ≤ mobiusDifferenceCLM m f)
    (N k : ℕ) :
    hilbertSequence (coordinatePartialSum f N) k ≤ 0 := by
  rw [← anchoredEvaluationCLM_apply]
  simp only [coordinatePartialSum, map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_nonpos
  intro i _
  apply mul_nonpos_of_nonpos_of_nonneg
  · change -mobiusDifferenceCLM (i.val + 2) f ≤ 0
    exact neg_nonpos.mpr (hf _ (by omega))
  · rw [anchoredEvaluationCLM_apply, residueAtom, normalizedResidueHilbert_sequence]
    unfold residueFraction
    positivity

end CoefficientStabilization
open CoefficientStabilization

theorem sequence_nonpos_of_mobius_nonneg (f : ThresholdHilbert)
    (hf : ∀ m : ℕ, 1 < m → 0 ≤ mobiusDifferenceCLM m f) (k : ℕ) :
    hilbertSequence f k ≤ 0 := by
  have ht := mobiusDifferenceCLM_sub_coordinatePartialSum_nonneg f k
    (fun m hm => hf m (by omega))
  have hfirst := firstCoordinate_nonpos_of_mobius_nonneg
    (f - coordinatePartialSum f k) ht
  have hp := coordinatePartialSum_prefix_linear f k k (by omega)
  simp only [hilbertSequence_sub, Pi.sub_apply] at hfirst hp
  have hm := mul_nonneg (Nat.cast_nonneg k)
    (show 0 ≤ hilbertSequence (coordinatePartialSum f k) 1 -
      hilbertSequence f 1 by linarith)
  have hn := coordinatePartialSum_nonpos_of_mobius_nonneg f hf k k
  nlinarith

namespace CoefficientStabilization

theorem coordinatePartialSum_order_of_mobius_nonneg (f : ThresholdHilbert)
    (hf : ∀ m : ℕ, 1 < m → 0 ≤ mobiusDifferenceCLM m f)
    (N k : ℕ) :
    hilbertSequence f k ≤ hilbertSequence (coordinatePartialSum f N) k ∧
      hilbertSequence (coordinatePartialSum f N) k ≤ 0 := by
  have ht := mobiusDifferenceCLM_sub_coordinatePartialSum_nonneg f N
    (fun m hm => hf m (by omega))
  have h := sequence_nonpos_of_mobius_nonneg (f - coordinatePartialSum f N) ht k
  simp only [hilbertSequence_sub, Pi.sub_apply] at h
  exact ⟨by linarith, coordinatePartialSum_nonpos_of_mobius_nonneg f hf N k⟩

theorem coordinatePartialSum_norm_le_of_mobius_nonneg (f : ThresholdHilbert)
    (hf : ∀ m : ℕ, 1 < m → 0 ≤ mobiusDifferenceCLM m f)
    (N : ℕ) : ‖coordinatePartialSum f N‖ ≤ ‖f‖ := by
  have hsq : ‖coordinatePartialSum f N‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    rw [hilbert_norm_weighted_sq, hilbert_norm_weighted_sq]
    apply (hilbertSequence_square_summable (coordinatePartialSum f N)).tsum_le_tsum
      _ (hilbertSequence_square_summable f)
    intro k
    apply mul_le_mul_of_nonneg_left _ (by unfold positiveWeight; positivity)
    have h := coordinatePartialSum_order_of_mobius_nonneg f hf N k
    nlinarith [h.1, h.2]
  nlinarith [norm_nonneg (coordinatePartialSum f N), norm_nonneg f]

theorem coordinatePartialSum_norm_le_of_mobius_one_sign (f : ThresholdHilbert)
    (hf : (∀ m : ℕ, 1 < m → 0 ≤ mobiusDifferenceCLM m f) ∨
      (∀ m : ℕ, 1 < m → mobiusDifferenceCLM m f ≤ 0))
    (N : ℕ) : ‖coordinatePartialSum f N‖ ≤ ‖f‖ := by
  rcases hf with hp | hn
  · exact coordinatePartialSum_norm_le_of_mobius_nonneg f hp N
  · have hp : ∀ m : ℕ, 1 < m → 0 ≤ mobiusDifferenceCLM m (-f) := by
      intro m hm
      rw [map_neg]
      exact neg_nonneg.mpr (hn m hm)
    simpa only [coordinatePartialSum_neg, norm_neg] using
      coordinatePartialSum_norm_le_of_mobius_nonneg (-f) hp N

theorem riemannHypothesis_of_eventually_one_sign_mobiusDifference
    (hsign : (∀ᶠ m : ℕ in atTop, 0 ≤ mobiusDifferenceCLM m limitResidual) ∨
      (∀ᶠ m : ℕ in atTop, mobiusDifferenceCLM m limitResidual ≤ 0)) :
    RiemannHypothesis := by
  have he : ∃ M : ℕ,
      (∀ m, M ≤ m → 0 ≤ mobiusDifferenceCLM m limitResidual) ∨
      (∀ m, M ≤ m → mobiusDifferenceCLM m limitResidual ≤ 0) := by
    rcases hsign with hp | hn
    · obtain ⟨M, hM⟩ := eventually_atTop.1 hp
      exact ⟨M, Or.inl hM⟩
    · obtain ⟨M, hM⟩ := eventually_atTop.1 hn
      exact ⟨M, Or.inr hM⟩
  obtain ⟨M, hM⟩ := he
  let f := limitResidual - coordinatePartialSum limitResidual M
  have hf : (∀ m : ℕ, 1 < m → 0 ≤ mobiusDifferenceCLM m f) ∨
      (∀ m : ℕ, 1 < m → mobiusDifferenceCLM m f ≤ 0) := by
    rcases hM with hp | hn
    · exact Or.inl (mobiusDifferenceCLM_sub_coordinatePartialSum_nonneg
        limitResidual M (fun m hm => hp m (by omega)))
    · right
      intro m hm
      dsimp [f]
      rw [mobiusDifferenceCLM_sub_coordinatePartialSum _ M m hm]
      split_ifs with h
      · exact le_rfl
      · exact hn m (by omega)
  apply riemannHypothesis_of_cofinally_bounded_defect_reconstruction
  refine ⟨‖f‖ + ‖coordinatePartialSum limitResidual M‖, ?_⟩
  intro N
  refine ⟨max N M, le_max_left _ _, ?_⟩
  have hp : coordinatePartialSum limitResidual (max N M) =
      coordinatePartialSum f (max N M) + coordinatePartialSum limitResidual M := by
    dsimp [f]
    rw [coordinatePartialSum_sub, coordinatePartialSum_nested _ M (max N M)
      (le_max_right _ _)]
    abel
  rw [hp]
  calc
    _ ≤ ‖coordinatePartialSum f (max N M)‖ +
        ‖coordinatePartialSum limitResidual M‖ := norm_add_le _ _
    _ ≤ ‖f‖ + ‖coordinatePartialSum limitResidual M‖ := by
      have hh := coordinatePartialSum_norm_le_of_mobius_one_sign f hf (max N M)
      linarith

theorem not_RH_mobiusDifference_sign_oscillation
    (hRH : ¬ RiemannHypothesis) (M : ℕ) :
    (∃ m : ℕ, M < m ∧ 1 < m ∧ 0 < mobiusDifferenceCLM m limitResidual) ∧
      (∃ m : ℕ, M < m ∧ 1 < m ∧ mobiusDifferenceCLM m limitResidual < 0) := by
  constructor
  · by_contra! hn
    apply hRH
    apply riemannHypothesis_of_eventually_one_sign_mobiusDifference
    right
    filter_upwards [eventually_gt_atTop (max M 1)] with m hm
    exact hn m (by omega) (by omega)
  · by_contra! hn
    apply hRH
    apply riemannHypothesis_of_eventually_one_sign_mobiusDifference
    left
    filter_upwards [eventually_gt_atTop (max M 1)] with m hm
    exact hn m (by omega) (by omega)

end CoefficientStabilization
end RiemannResearch.RH.Pareto
