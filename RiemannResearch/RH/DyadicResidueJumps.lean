import RiemannResearch.RH.DyadicFiniteCriticalNorm
import Mathlib.Tactic.Ring

/-!
# Exact arithmetic jumps of residue dilations

Source: user-provided dyadic regularization continuation, September 10, 2026.
These declarations specialize the existing exact residue difference identity
to actual arithmetic Hilbert vectors. They preserve the negative triple jump.
No norm estimate, summability, or RH assumption enters the arithmetic identities.
-/

namespace RiemannResearch.RH.Pareto
noncomputable section

/-- Every dilation residue jump is an exact difference of divisibility channels. -/
theorem dilation_residue_difference (m a k : ℕ) (hk : 0 < k) :
    dilation m (residue a) k - dilation m (residue a) (k-1) =
      (if m ∣ k then (m : ℝ) else 0) -
        (if m*a ∣ k then ((m*a : ℕ) : ℝ) else 0) := by
  calc
    _ = (residue (m*a) k - residue (m*a) (k-1)) -
        (residue m k - residue m (k-1)) := by
      rw [residue_mul_floor, residue_mul_floor]
      ring
    _ = _ := by
      rw [residue_difference _ _ hk, residue_difference _ _ hk]
      ring

/-- Actual arithmetic Hilbert vectors have precisely the same signed jumps. -/
theorem hilbertDilation_residue_difference
    (m a k : ℕ) (hm : 0 < m) (ha : 0 < a) (hk : 0 < k) :
    hilbertSequence (hilbertDilation m hm (hilbertResidue a ha)) k -
      hilbertSequence (hilbertDilation m hm (hilbertResidue a ha)) (k-1) =
        (if m ∣ k then (m : ℝ) else 0) -
          (if m*a ∣ k then ((m*a : ℕ) : ℝ) else 0) := by
  rw [hilbertDilation_sequence, hilbertResidue_sequence]
  exact dilation_residue_difference m a k hk

/-- No jump occurs away from an actual multiple of the dilation index. -/
theorem hilbertDilation_residue_difference_eq_zero
    (m a k : ℕ) (hm : 0 < m) (ha : 0 < a) (hk : 0 < k)
    (hnd : ¬ m ∣ k) :
    hilbertSequence (hilbertDilation m hm (hilbertResidue a ha)) k -
      hilbertSequence (hilbertDilation m hm (hilbertResidue a ha)) (k-1) = 0 := by
  have hnda : ¬ m*a ∣ k := by
    intro h
    exact hnd (dvd_trans (show m ∣ m*a from ⟨a, rfl⟩) h)
  rw [hilbertDilation_residue_difference m a k hm ha hk]
  simp only [if_neg hnd, if_neg hnda, sub_self]

/-- At an actual multiple, the original residue jump survives with scale m. -/
theorem hilbertDilation_residue_difference_multiple
    (m a r : ℕ) (hm : 0 < m) (ha : 0 < a) (hr : 0 < r) :
    hilbertSequence (hilbertDilation m hm (hilbertResidue a ha)) (m*r) -
      hilbertSequence (hilbertDilation m hm (hilbertResidue a ha)) (m*r-1) =
        (m : ℝ) * (residue a r - residue a (r-1)) := by
  rw [hilbertDilation_residue_difference m a (m*r) hm ha (Nat.mul_pos hm hr),
    residue_difference a r hr]
  have hmd : m ∣ m*r := ⟨r, rfl⟩
  simp only [if_pos hmd, Nat.mul_dvd_mul_iff_left hm]
  by_cases hd : a ∣ r <;> simp [hd] <;> push_cast <;> ring

/-- The signed triadic jump is +m except at triple multiples, where it is -2m. -/
theorem hilbertDilation_residue_three_difference_multiple
    (m r : ℕ) (hm : 0 < m) (hr : 0 < r) :
    hilbertSequence (hilbertDilation m hm (hilbertResidue 3 (by norm_num))) (m*r) -
      hilbertSequence (hilbertDilation m hm (hilbertResidue 3 (by norm_num)))
        (m*r-1) = if 3 ∣ r then -2*(m : ℝ) else (m : ℝ) := by
  rw [hilbertDilation_residue_difference_multiple m 3 r hm (by norm_num) hr,
    residue_difference 3 r hr]
  by_cases hd : 3 ∣ r <;> simp [hd] <;> ring

/-- All nonzero triadic jumps lie in the exact three-value alphabet. -/
theorem hilbertDilation_residue_three_difference_values
    (m k : ℕ) (hm : 0 < m) (hk : 0 < k) :
    let d := hilbertSequence
        (hilbertDilation m hm (hilbertResidue 3 (by norm_num))) k -
      hilbertSequence (hilbertDilation m hm (hilbertResidue 3 (by norm_num))) (k-1)
    d = 0 ∨ d = (m : ℝ) ∨ d = -2*(m : ℝ) := by
  dsimp only
  rw [hilbertDilation_residue_difference m 3 k hm (by norm_num) hk]
  by_cases hmd : m ∣ k
  · by_cases hmt : m*3 ∣ k
    · right; right
      simp [hmd, hmt]
      ring
    · right; left
      simp [hmd, hmt]
  · have hmt : ¬ m*3 ∣ k := by
      intro h
      exact hmd (dvd_trans (show m ∣ m*3 from ⟨3, rfl⟩) h)
    left
    simp [hmd, hmt]

/-- Exact annihilation of every even dilation by the dyadic kernel projection. -/
theorem dyadicKernelDefect_even_dilation (m : ℕ) (hm : 0 < m)
    (f : ThresholdHilbert) :
    dyadicKernelDefect (hilbertDilation (2*m) (by positivity) f) = 0 := by
  rw [dyadicKernelDefect_apply,
    ← hilbertDilation_comp 2 m (by norm_num) hm,
    hilbertBlockProjection_dilation, sub_self]

end
end RiemannResearch.RH.Pareto
