import RiemannResearch.RH.DyadicCriticalApproximation

/-!
# Physical weighted coordinates of every dyadic half-adjoint iterate

Source: user-provided DyadicResidueKernelVerification20260910(1).md,
September 10, 2026. These exact block identities supply the physical
coordinates needed for the all-scale arithmetic kernel estimate.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
open RiemannResearch.Analysis.AbelCoboundary
noncomputable section

theorem dyadicHalfAdjoint_orbit_weighted_coordinate
    (f : ThresholdHilbert) (j k : ℕ) (hk : 0 < k) :
    positiveWeight k * hilbertSequence (orbit dyadicHalfAdjoint f j) k =
      ∑ n ∈ Finset.Ico (2^j*k) (2^j*(k+1)),
        positiveWeight n * hilbertSequence f n := by
  have he := dyadicAdjointOrbit_inner j f (hilbertAtom k hk)
  rw [hilbertAtom_inner, hilbertDilation_hilbertAtom_inner] at he
  rw [dyadicHalfAdjoint_orbit_eq, hilbertSequence_smul]
  change positiveWeight k * ((1/2 : ℝ)^j *
    hilbertSequence (orbit (hilbertDilationAdjoint 2 (by norm_num)) f j) k) = _
  have hp : (1/2 : ℝ)^j * ((2^j : ℕ) : ℝ) = 1 := by
    push_cast
    rw [← mul_pow]
    norm_num
  calc
    _ = (1/2 : ℝ)^j * (positiveWeight k *
      hilbertSequence (orbit (hilbertDilationAdjoint 2 (by norm_num)) f j) k) := by ring
    _ = _ := by rw [he, ← mul_assoc, hp, one_mul]

theorem dyadicHalfAdjoint_orbit_coordinate
    (f : ThresholdHilbert) (j k : ℕ) (hk : 0 < k) :
    hilbertSequence (orbit dyadicHalfAdjoint f j) k =
      (∑ n ∈ Finset.Ico (2^j*k) (2^j*(k+1)),
        positiveWeight n * hilbertSequence f n) / positiveWeight k := by
  have hw : positiveWeight k ≠ 0 := by unfold positiveWeight; positivity
  apply (eq_div_iff hw).mpr
  simpa only [mul_comm] using dyadicHalfAdjoint_orbit_weighted_coordinate f j k hk

theorem dyadicHalfAdjoint_orbit_coordinate_bounds
    (f : ThresholdHilbert) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ k, 0 ≤ hilbertSequence f k ∧ hilbertSequence f k ≤ C)
    (j k : ℕ) :
    0 ≤ hilbertSequence (orbit dyadicHalfAdjoint f j) k ∧
      hilbertSequence (orbit dyadicHalfAdjoint f j) k ≤ C / (2 : ℝ)^j := by
  by_cases hk : k = 0
  · subst k
    simpa only [hilbertSequence_zero] using
      (show (0 : ℝ) ≤ 0 ∧ 0 ≤ C / (2 : ℝ)^j from ⟨le_rfl, by positivity⟩)
  have hkp : 0 < k := Nat.pos_of_ne_zero hk
  have hw : 0 < positiveWeight k := by unfold positiveWeight; positivity
  have he := dyadicHalfAdjoint_orbit_weighted_coordinate f j k hkp
  have hn : 0 ≤ ∑ n ∈ Finset.Ico (2^j*k) (2^j*(k+1)),
      positiveWeight n * hilbertSequence f n :=
    Finset.sum_nonneg (fun n _ => mul_nonneg (positiveWeight_nonneg n) (hf n).1)
  have hu : (∑ n ∈ Finset.Ico (2^j*k) (2^j*(k+1)),
      positiveWeight n * hilbertSequence f n) ≤
      positiveWeight k * (C / (2 : ℝ)^j) := by
    calc
      _ ≤ ∑ n ∈ Finset.Ico (2^j*k) (2^j*(k+1)), positiveWeight n * C :=
        Finset.sum_le_sum (fun n _ => mul_le_mul_of_nonneg_left (hf n).2
          (positiveWeight_nonneg n))
      _ = _ := by
        rw [← Finset.sum_mul, positiveWeight_block _ _ (by positivity) hkp]
        push_cast
        ring
  constructor
  · exact (mul_nonneg_iff_of_pos_left hw).mp (he.symm ▸ hn)
  · nlinarith [he.trans_le hu]

theorem dyadicHalfAdjoint_orbit_coordinate_of_constant
    (f : ThresholdHilbert) (j k : ℕ) (hk : 0 < k) (c : ℝ)
    (hf : ∀ n ∈ Finset.Ico (2^j*k) (2^j*(k+1)), hilbertSequence f n = c) :
    hilbertSequence (orbit dyadicHalfAdjoint f j) k = c / (2 : ℝ)^j := by
  have hw : positiveWeight k ≠ 0 := by unfold positiveWeight; positivity
  apply mul_left_cancel₀ hw
  calc
    _ = ∑ n ∈ Finset.Ico (2^j*k) (2^j*(k+1)),
        positiveWeight n * hilbertSequence f n :=
      dyadicHalfAdjoint_orbit_weighted_coordinate f j k hk
    _ = (∑ n ∈ Finset.Ico (2^j*k) (2^j*(k+1)), positiveWeight n) * c := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun n hn => by rw [hf n hn])
    _ = _ := by
      rw [positiveWeight_block _ _ (by positivity) hk]
      push_cast
      ring

end
end RiemannResearch.RH.Pareto
