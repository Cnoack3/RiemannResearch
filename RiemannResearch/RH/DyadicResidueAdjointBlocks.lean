import RiemannResearch.RH.DyadicAdjointCoordinates
import RiemannResearch.RH.DyadicSparseBlockEnergy

/-!
# Uniform all-scale dyadic kernel bound for actual triadic residue dilations

Source: user-provided DyadicResidueKernelVerification20260910(1).md,
September 10, 2026, and its weighted-block proof plan. The proof below uses
one active multiple per disjoint pair of blocks, improving the proposed 6 to 4.
The exact physical weighted coordinates are used before their differences
are estimated. No arithmetic convergence, Gram bound, or RH is assumed.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
open RiemannResearch.Analysis.AbelCoboundary
noncomputable section

theorem hilbertDilation_triadicResidue_coordinate_bounds
    (m : ℕ) (hm : 0 < m) (k : ℕ) :
    0 ≤ hilbertSequence (hilbertDilation m hm (hilbertResidue 3 (by norm_num))) k ∧
      hilbertSequence (hilbertDilation m hm (hilbertResidue 3 (by norm_num))) k ≤
        2 * (m : ℝ) := by
  rw [hilbertDilation_sequence, hilbertResidue_sequence]
  change 0 ≤ (m : ℝ) * (((k/m)%3 : ℕ) : ℝ) ∧
    (m : ℝ) * (((k/m)%3 : ℕ) : ℝ) ≤ 2*(m : ℝ)
  have hmod : (k/m)%3 ≤ 2 := by omega
  have hc : (((k/m)%3 : ℕ) : ℝ) ≤ 2 := by exact_mod_cast hmod
  constructor
  · positivity
  · nlinarith [show (0 : ℝ) ≤ m by positivity]

theorem dyadicHalfAdjoint_triadicResidue_coordinate_bounds
    (m : ℕ) (hm : 0 < m) (j k : ℕ) :
    0 ≤ hilbertSequence
      (orbit dyadicHalfAdjoint (hilbertDilation m hm (hilbertResidue 3 (by norm_num))) j) k ∧
    hilbertSequence
      (orbit dyadicHalfAdjoint (hilbertDilation m hm (hilbertResidue 3 (by norm_num))) j) k ≤
      2*(m : ℝ)/(2 : ℝ)^j :=
  dyadicHalfAdjoint_orbit_coordinate_bounds _ (2*(m : ℝ)) (by positivity)
    (hilbertDilation_triadicResidue_coordinate_bounds m hm) j k

theorem dyadicHalfAdjoint_triadicResidue_difference_eq_zero
    (m : ℕ) (hm : 0 < m) (j n : ℕ)
    (hno : 2*2^j*(n+1) ≤ (2*2^j*n/m+1)*m) :
    hilbertSequence
      (orbit dyadicHalfAdjoint (hilbertDilation m hm (hilbertResidue 3 (by norm_num))) j)
        (2*n+1) -
    hilbertSequence
      (orbit dyadicHalfAdjoint (hilbertDilation m hm (hilbertResidue 3 (by norm_num))) j)
        (2*n) = 0 := by
  let f := hilbertDilation m hm (hilbertResidue 3 (by norm_num))
  by_cases hn : n = 0
  · subst n
    have hm2 : 2*2^j ≤ m := by simpa using hno
    have hc : hilbertSequence (orbit dyadicHalfAdjoint f j) 1 = 0 := by
      have he := dyadicHalfAdjoint_orbit_coordinate_of_constant f j 1 (by norm_num) 0
        (by
          intro k hk
          have hk2 : k < m := lt_of_lt_of_le (by
            have h := (Finset.mem_Ico.mp hk).2
            nlinarith) hm2
          dsimp [f]
          rw [hilbertDilation_sequence, hilbertResidue_sequence]
          simp [dilation, residue, Nat.div_eq_of_lt hk2])
      simpa using he
    change hilbertSequence (orbit dyadicHalfAdjoint f j) (2*0+1) -
      hilbertSequence (orbit dyadicHalfAdjoint f j) (2*0) = 0
    simpa only [Nat.mul_zero, Nat.zero_add, hilbertSequence_zero, sub_zero] using hc
  have hnp : 0 < n := Nat.pos_of_ne_zero hn
  let c : ℝ := (m : ℝ) * (((2*2^j*n/m)%3 : ℕ) : ℝ)
  have hconst (k : ℕ) (hkl : 2*2^j*n ≤ k) (hku : k < 2*2^j*(n+1)) :
      hilbertSequence f k = c := by
    have hd : k/m = 2*2^j*n/m := by
      apply Nat.div_eq_of_lt_le
      · exact (Nat.div_mul_le_self _ _).trans hkl
      · exact hku.trans_le hno
    dsimp only [f, c]
    rw [hilbertDilation_sequence, hilbertResidue_sequence]
    change (m : ℝ) * (((k/m)%3 : ℕ) : ℝ) = _
    rw [hd]
  have hleft := dyadicHalfAdjoint_orbit_coordinate_of_constant f j (2*n)
    (by positivity) c (by
      intro k hk
      have h := Finset.mem_Ico.mp hk
      apply hconst k <;> nlinarith)
  have hright := dyadicHalfAdjoint_orbit_coordinate_of_constant f j (2*n+1)
    (by positivity) c (by
      intro k hk
      have h := Finset.mem_Ico.mp hk
      apply hconst k <;> nlinarith)
  change hilbertSequence (orbit dyadicHalfAdjoint f j) (2*n+1) -
    hilbertSequence (orbit dyadicHalfAdjoint f j) (2*n) = 0
  rw [hleft, hright, sub_self]

/-- Unconditional uniform estimate for every actual arithmetic kernel block. -/
theorem dyadicKernelDefect_halfAdjoint_triadicResidue_norm_sq_le
    (m : ℕ) (hm : 0 < m) (j : ℕ) :
    ‖dyadicKernelDefect
      (orbit dyadicHalfAdjoint (hilbertDilation m hm (hilbertResidue 3 (by norm_num))) j)‖^2 ≤
      16 := by
  apply dyadicKernelDefect_norm_sq_le_sixteen_of_sparse_block_coordinates
    _ (2^j) m (by positivity) hm
  · intro k
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      dyadicHalfAdjoint_triadicResidue_coordinate_bounds m hm j k
  · exact dyadicHalfAdjoint_triadicResidue_difference_eq_zero m hm j

/-- The all-scale block bound improves the proposed constant six to four. -/
theorem dyadicKernelDefect_halfAdjoint_triadicResidue_norm_le
    (m : ℕ) (hm : 0 < m) (j : ℕ) :
    ‖dyadicKernelDefect
      (orbit dyadicHalfAdjoint (hilbertDilation m hm (hilbertResidue 3 (by norm_num))) j)‖ ≤
      4 := by
  have h := dyadicKernelDefect_halfAdjoint_triadicResidue_norm_sq_le m hm j
  nlinarith [norm_nonneg (dyadicKernelDefect
    (orbit dyadicHalfAdjoint (hilbertDilation m hm (hilbertResidue 3 (by norm_num))) j))]

end
end RiemannResearch.RH.Pareto
