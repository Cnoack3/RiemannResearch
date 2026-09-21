import RiemannResearch.RH.FiniteResidueHeadSurjectivity

/-!
# Exact cardinal residues and their doubled-coordinate obstruction

Source: user-provided `RH_Fredholm_Two_Scale_Route_to_qN_2026-09-21.md`,
Sections 5 and 8 (the diagonal determinant research target). The identities
below are elementary finite-residue calculations documented in
`RH_Lean_Window_Positivity_and_Energy_Audit_2026-09-21.md`.

These concrete finite-dictionary identities assume no RH, density, uniform
interpolation bound, or spectral saturation. The ordinary determinant
obstruction that they support is not a theorem in this module.
-/

noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.RH.Pareto
open Probability.ConditionalIID

/-- A concrete legal cardinal vector for a coordinate in the upper half
of a head of length `M`, supported on three residue moduli. -/
def diagonalCardinalResidue (M j : ℕ) : ℕ → ℝ :=
  (1 / ((j + 1 : ℕ) : ℝ)) • residue (j + 1) -
    (1 / (j : ℝ)) • residue j +
    (1 / ((j : ℝ) * ((j + 1 : ℕ) : ℝ))) • residue (M + 1)

theorem diagonalCardinalResidue_apply (M j n : ℕ) :
    diagonalCardinalResidue M j n =
      residue (j + 1) n / ((j + 1 : ℕ) : ℝ) -
      residue j n / (j : ℝ) +
      residue (M + 1) n / ((j : ℝ) * ((j + 1 : ℕ) : ℝ)) := by
  simp [diagonalCardinalResidue, div_eq_mul_inv, mul_comm]

theorem diagonalCardinalResidue_mem {M j : ℕ}
    (hj : 0 < j) (hjM : j ≤ M) :
    diagonalCardinalResidue M j ∈ finiteResidueSubspace (M + 1) := by
  exact (finiteResidueSubspace _).add_mem
    ((finiteResidueSubspace _).sub_mem
      ((finiteResidueSubspace _).smul_mem _
        (residue_mem_finiteResidueSubspace (by omega) (by omega)))
      ((finiteResidueSubspace _).smul_mem _
        (residue_mem_finiteResidueSubspace hj (by omega))))
    ((finiteResidueSubspace _).smul_mem _
      (residue_mem_finiteResidueSubspace (by omega) le_rfl))

theorem diagonalCardinalResidue_full_legal {M j : ℕ}
    (hj : 0 < j) (hjM : j ≤ M) :
    diagonalCardinalResidue M j ∈ legalSeedSpan (Set.Ici 1) :=
  finiteResidueSubspace_le_full_legal (M + 1)
    (diagonalCardinalResidue_mem hj hjM)

private theorem residue_eq_sub_mul_quotient (d n : ℕ) :
    residue d n = (n : ℝ) - (d : ℝ) * ((n / d : ℕ) : ℝ) := by
  have h := congrArg (fun a : ℕ => (a : ℝ)) (Nat.mod_add_div n d)
  norm_num only [Nat.cast_add, Nat.cast_mul] at h
  change ((n % d : ℕ) : ℝ) = _
  linarith

/-- Exact cancellation of the linear parts of the three raw residues. -/
theorem diagonalCardinalResidue_floor {M j n : ℕ} (hj : 0 < j) :
    diagonalCardinalResidue M j n =
      ((n / j : ℕ) : ℝ) - ((n / (j + 1) : ℕ) : ℝ) -
      ((M + 1 : ℕ) : ℝ) / ((j : ℝ) * ((j + 1 : ℕ) : ℝ)) *
        ((n / (M + 1) : ℕ) : ℝ) := by
  rw [diagonalCardinalResidue_apply]
  simp only [residue_eq_sub_mul_quotient, Nat.cast_add, Nat.cast_one]
  have hj0 : (j : ℝ) ≠ 0 := by positivity
  have hj1 : (j : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hj0, hj1]
  <;> ring

/-- Every head coordinate is exact; `M < 2*j` is the upper-half condition. -/
theorem diagonalCardinalResidue_head {M j n : ℕ}
    (hj : 0 < j) (hjM : j ≤ M) (hhalf : M < 2 * j) (hn : n ≤ M) :
    diagonalCardinalResidue M j n = if n = j then 1 else 0 := by
  rw [diagonalCardinalResidue_floor hj]
  have hqM : n / (M + 1) = 0 := Nat.div_eq_of_lt (by omega)
  rw [hqM]
  rcases lt_trichotomy n j with hnj | heq | hjn
  · have hqj : n / j = 0 := Nat.div_eq_of_lt hnj
    have hqj1 : n / (j + 1) = 0 := Nat.div_eq_of_lt (by omega)
    simp [hqj, hqj1, hnj.ne]
  · subst n
    have hqj : j / j = 1 := Nat.div_self (by omega)
    have hqj1 : j / (j + 1) = 0 := Nat.div_eq_of_lt (by omega)
    simp [hqj, hqj1]
  · have hqj : n / j = 1 :=
      Nat.div_eq_of_lt_le (by omega) (by omega)
    have hqj1 : n / (j + 1) = 1 :=
      Nat.div_eq_of_lt_le (by omega) (by omega)
    simp [hqj, hqj1, ne_of_gt hjn]

/-- On a top-third block the doubled-coordinate matrix is exactly
identity minus a rank-one matrix. All index assumptions are linear. -/
theorem diagonalCardinalResidue_double {M i j : ℕ}
    (hj : 0 < j) (hiM : i ≤ M) (hjM : j ≤ M)
    (htail : M + 1 ≤ 2 * i) (hthird : 2 * M < 3 * j) :
    diagonalCardinalResidue M j (2 * i) =
      (if i = j then 1 else 0) -
      ((M + 1 : ℕ) : ℝ) / ((j : ℝ) * ((j + 1 : ℕ) : ℝ)) := by
  rw [diagonalCardinalResidue_floor hj]
  have hqM : (2 * i) / (M + 1) = 1 :=
    Nat.div_eq_of_lt_le (by omega) (by omega)
  rw [hqM]
  rcases lt_trichotomy i j with hij | heq | hji
  · have hqj : (2 * i) / j = 1 :=
      Nat.div_eq_of_lt_le (by omega) (by omega)
    have hqj1 : (2 * i) / (j + 1) = 1 :=
      Nat.div_eq_of_lt_le (by omega) (by omega)
    simp [hqj, hqj1, hij.ne]
  · subst i
    have hqj : (2 * j) / j = 2 :=
      Nat.div_eq_of_lt_le (by omega) (by omega)
    have hqj1 : (2 * j) / (j + 1) = 1 :=
      Nat.div_eq_of_lt_le (by omega) (by omega)
    norm_num [hqj, hqj1]
  · have hqj : (2 * i) / j = 2 :=
      Nat.div_eq_of_lt_le (by omega) (by omega)
    have hqj1 : (2 * i) / (j + 1) = 2 :=
      Nat.div_eq_of_lt_le (by omega) (by omega)
    simp [hqj, hqj1, ne_of_gt hji]

end RiemannResearch.RH.Pareto
