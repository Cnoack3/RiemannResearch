import RiemannResearch.RH.ThresholdHilbertMean
import Mathlib.Tactic.Linarith
/-!
# Exact adjoint blocks and all-integer fixed-vector rigidity

Source: independently developed from the actual weighted operators formalized
for Christian Noack's RH_Two_Seed_Threshold.tex (8 September 2026).
The paper supplies the motivating adjoint and rigidity questions; proofs below
use the existing exact weighted Hilbert construction.

We construct physical tail indicators and point atoms inside H, derive the
actual finite weighted-block adjoint law, and recover each physical coordinate
from two consecutive adjoint pairings. All positive integer adjoints have
precisely the constant fixed vectors. This is NOT the two-seed rigidity theorem,
does not identify the annihilator of a legal seed space, and proves no RH
criterion or legal approximation convergence.
-/
namespace RiemannResearch.RH.Pareto
open scoped BigOperators
noncomputable section
@[simp] theorem hilbertSequence_sub (f g : ThresholdHilbert) :
    hilbertSequence (f-g) = hilbertSequence f - hilbertSequence g :=
  hilbertSequenceLinear.map_sub f g

def hilbertTail (m : ℕ) (hm : 0 < m) : ThresholdHilbert :=
  (1 / (m : ℝ)) • hilbertDilation m hm hilbertOne

theorem hilbertTail_sequence (m : ℕ) (hm : 0 < m) :
    hilbertSequence (hilbertTail m hm) = fun n => if m ≤ n then 1 else 0 := by
  rw [hilbertTail, hilbertSequence_smul, hilbertDilation_sequence, hilbertOne_sequence]
  funext n
  change 1 / (m : ℝ) * ((m : ℝ) * (if n / m = 0 then 0 else 1)) =
    if m ≤ n then 1 else 0
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  by_cases h : m ≤ n
  · have hn : n / m ≠ 0 := Nat.ne_of_gt (Nat.div_pos_iff.mpr ⟨hm, h⟩)
    simp [h, hn, hm0]
  · have hn : n / m = 0 := Nat.div_eq_of_lt (Nat.lt_of_not_ge h)
    simp [h, hn]

def hilbertAtom (k : ℕ) (hk : 0 < k) : ThresholdHilbert :=
  hilbertTail k hk - hilbertTail (k+1) (by omega)

theorem hilbertAtom_sequence (k : ℕ) (hk : 0 < k) :
    hilbertSequence (hilbertAtom k hk) = fun n => if n = k then 1 else 0 := by
  rw [hilbertAtom, hilbertSequence_sub, hilbertTail_sequence, hilbertTail_sequence]
  funext n
  simp only [Pi.sub_apply]
  split_ifs <;> norm_num <;> omega

theorem hilbertAtom_inner (k : ℕ) (hk : 0 < k) (f : ThresholdHilbert) :
    inner ℝ (hilbertAtom k hk) f = positiveWeight k * hilbertSequence f k := by
  rw [hilbert_inner_weighted, hilbertAtom_sequence]
  unfold paretoInner
  rw [tsum_eq_single k (fun n hn => by simp [hn])]
  simp

theorem hilbertDilation_hilbertAtom_inner (m k : ℕ) (hm : 0 < m) (hk : 0 < k)
    (f : ThresholdHilbert) :
    inner ℝ (hilbertDilation m hm (hilbertAtom k hk)) f =
      (m : ℝ) * ∑ n ∈ Finset.Ico (m*k) (m*(k+1)),
        positiveWeight n * hilbertSequence f n := by
  rw [hilbert_inner_weighted, hilbertDilation_sequence, hilbertAtom_sequence]
  unfold paretoInner dilation
  rw [tsum_eq_sum (s := Finset.Ico (m*k) (m*(k+1))) (fun n hn => by
    have hnk : n / m ≠ k := by
      intro h
      have hd := (Nat.div_eq_iff hm).mp h
      apply hn
      simp only [Finset.mem_Ico, Nat.mul_add, Nat.mul_one]
      rw [Nat.mul_comm m k]
      omega
    simp [hnk])]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hd : n / m = k := by
    apply Nat.div_eq_of_lt_le
    · simpa [Nat.mul_comm] using (Finset.mem_Ico.mp hn).1
    · simpa [Nat.mul_comm] using (Finset.mem_Ico.mp hn).2
  simp [hd]
  ring

theorem hilbertDilationAdjoint_coordinate (m k : ℕ) (hm : 0 < m) (hk : 0 < k)
    (f : ThresholdHilbert) :
    hilbertSequence (hilbertDilationAdjoint m hm f) k =
      (m : ℝ) / positiveWeight k *
        ∑ n ∈ Finset.Ico (m*k) (m*(k+1)),
          positiveWeight n * hilbertSequence f n := by
  have he := ContinuousLinearMap.adjoint_inner_right
    (hilbertDilationContinuous m hm) (hilbertAtom k hk) f
  change inner ℝ (hilbertAtom k hk) (hilbertDilationAdjoint m hm f) =
    inner ℝ (hilbertDilation m hm (hilbertAtom k hk)) f at he
  rw [hilbertAtom_inner, hilbertDilation_hilbertAtom_inner] at he
  have hw : positiveWeight k ≠ 0 := by unfold positiveWeight; positivity
  apply (mul_left_cancel₀ hw)
  rw [he]
  field_simp

theorem hilbert_coordinate_recovery (f : ThresholdHilbert) (k : ℕ) (hk : 0 < k) :
    hilbertSequence f k =
      ((k : ℝ)+1) * inner ℝ hilbertOne (hilbertDilationAdjoint k hk f) -
      (k : ℝ) * inner ℝ hilbertOne (hilbertDilationAdjoint (k+1) (by omega) f) := by
  have he := hilbertAtom_inner k hk f
  unfold hilbertAtom hilbertTail at he
  rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left] at he
  have ht (m : ℕ) (hm : 0 < m) :
      inner ℝ (hilbertDilation m hm hilbertOne) f =
        inner ℝ hilbertOne (hilbertDilationAdjoint m hm f) :=
    (ContinuousLinearMap.adjoint_inner_right (hilbertDilationContinuous m hm)
      hilbertOne f).symm
  rw [ht, ht] at he
  unfold positiveWeight at he
  push_cast at he
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  have hk1 : (k : ℝ)+1 ≠ 0 := by positivity
  field_simp at he
  nlinarith

theorem hilbertDilationAdjoint_all_fixed_iff (f : ThresholdHilbert) :
    (∀ (m : ℕ) (hm : 0 < m), hilbertDilationAdjoint m hm f = f) ↔
      ∃ c : ℝ, f = c • hilbertOne := by
  constructor
  · intro h
    refine ⟨inner ℝ hilbertOne f, ?_⟩
    apply hilbertSequence_injective
    funext k
    by_cases hk : k = 0
    · subst k
      simp
    · have hkp : 0 < k := Nat.pos_of_ne_zero hk
      rw [hilbert_coordinate_recovery f k hkp, h k hkp, h (k+1) (by omega)]
      simp only [hilbertSequence_smul, Pi.smul_apply, smul_eq_mul, hilbertOne_sequence]
      simp only [zeroAnchor, if_neg hk]
      ring
  · rintro ⟨c, rfl⟩ m hm
    rw [map_smul, hilbertDilationAdjoint_one]


/-- The complete signed coordinate defect, before taking any inequality. -/
theorem hilbert_coordinate_defect (f : ThresholdHilbert) (k : ℕ) (hk : 0 < k) :
    hilbertSequence f k - inner ℝ hilbertOne f =
      ((k : ℝ)+1) * inner ℝ hilbertOne (hilbertDilationAdjoint k hk f - f) -
      (k : ℝ) * inner ℝ hilbertOne
        (hilbertDilationAdjoint (k+1) (by omega) f - f) := by
  rw [inner_sub_right, inner_sub_right, hilbert_coordinate_recovery f k hk]
  ring

private theorem target_norm : ‖hilbertOne‖ = 1 := by
  nlinarith [hilbertOne_norm_sq, norm_nonneg hilbertOne]

theorem hilbert_coordinate_defect_bound (f : ThresholdHilbert) (k : ℕ) (hk : 0 < k) :
    |hilbertSequence f k - inner ℝ hilbertOne f| ≤
      ((k : ℝ)+1) * ‖hilbertDilationAdjoint k hk f - f‖ +
      (k : ℝ) * ‖hilbertDilationAdjoint (k+1) (by omega) f - f‖ := by
  rw [hilbert_coordinate_defect f k hk]
  calc
    _ ≤ |((k : ℝ)+1) * inner ℝ hilbertOne (hilbertDilationAdjoint k hk f-f)| +
        |(k : ℝ) * inner ℝ hilbertOne (hilbertDilationAdjoint (k+1) (by omega) f-f)| :=
      abs_sub _ _
    _ ≤ _ := by
      simp only [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (k : ℝ)+1),
        abs_of_nonneg (show (0 : ℝ) ≤ (k : ℝ) from Nat.cast_nonneg k)]
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa [target_norm] using
          abs_real_inner_le_norm hilbertOne (hilbertDilationAdjoint k hk f-f)
      · apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg k)
        simpa [target_norm] using
          abs_real_inner_le_norm hilbertOne (hilbertDilationAdjoint (k+1) (by omega) f-f)

end
end RiemannResearch.RH.Pareto
