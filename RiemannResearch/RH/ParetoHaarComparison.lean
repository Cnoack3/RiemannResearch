import RiemannResearch.RH.ParetoPeriodicRegrouping
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Necessary loss when comparing the actual Pareto quotient with uniform Haar

Source: the user-provided generalized CRT conversation of 16 September 2026.
The finite weights below are the actual infinite progression sums, not an
independent prime-coordinate model. The coordinate at index zero corresponds
to the positive residue representative one.

We certify the exact optimal energy comparison constant L times the mass of
residue one; this lies between L / 2 and L / 2 + 1 / 2. Thus the corresponding
norm loss is at least sqrt (L / 2). No bound independent of the conductor is
possible on the entire residue space. This statement does not rule out a
comparison on a restricted legal space or a particular residual.
-/

open scoped BigOperators

namespace RiemannResearch.RH.Pareto

noncomputable section

/-- Actual Pareto energy on the quotient with positive representatives 1,...,L. -/
def quotientParetoEnergy (L : ℕ) (f : Fin L → ℝ) : ℝ :=
  ∑ r, progressionWeight L (r.val + 1) * (f r) ^ 2

/-- Uniform probability energy on the same finite quotient. -/
def quotientHaarEnergy (L : ℕ) (f : Fin L → ℝ) : ℝ :=
  (∑ r, (f r) ^ 2) / (L : ℝ)

/-- The indicator of the positive residue representative one. -/
def firstResidueAtom (N : ℕ) (r : Fin (N + 1)) : ℝ :=
  if r = 0 then 1 else 0

theorem quotientParetoEnergy_firstResidueAtom (N : ℕ) :
    quotientParetoEnergy (N + 1) (firstResidueAtom N) =
      progressionWeight (N + 1) 1 := by
  classical
  simp [quotientParetoEnergy, firstResidueAtom]

theorem quotientHaarEnergy_firstResidueAtom (N : ℕ) :
    quotientHaarEnergy (N + 1) (firstResidueAtom N) =
      1 / ((N + 1 : ℕ) : ℝ) := by
  classical
  simp [quotientHaarEnergy, firstResidueAtom]

/-- The atom at integer one alone contributes probability one half. -/
theorem half_le_progressionWeight_one (L : ℕ) (hL : 0 < L) :
    (1 / 2 : ℝ) ≤ progressionWeight L 1 := by
  have h := positiveWeight_le_progressionWeight L 1 hL
  norm_num [positiveWeight] at h
  exact h

theorem quotientParetoEnergy_nonneg (L : ℕ) (f : Fin L → ℝ) :
    0 ≤ quotientParetoEnergy L f := by
  apply Finset.sum_nonneg
  intro r _
  exact mul_nonneg (progressionWeight_nonneg L (r.val + 1)) (sq_nonneg (f r))

theorem quotientHaarEnergy_nonneg (L : ℕ) (f : Fin L → ℝ) :
    0 ≤ quotientHaarEnergy L f := by
  unfold quotientHaarEnergy
  positivity

/-- Any uniform energy comparison on a whole finite quotient must lose at least
L / 2. The conclusion applies to the actual infinite Pareto progression masses. -/
theorem quotient_energy_comparison_loss (N : ℕ) (C : ℝ)
    (hC : ∀ f : Fin (N + 1) → ℝ,
      quotientParetoEnergy (N + 1) f ≤ C * quotientHaarEnergy (N + 1) f) :
    ((N + 1 : ℕ) : ℝ) / 2 ≤ C := by
  have h := hC (firstResidueAtom N)
  rw [quotientParetoEnergy_firstResidueAtom, quotientHaarEnergy_firstResidueAtom] at h
  have hL : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have hmul : progressionWeight (N + 1) 1 * ((N + 1 : ℕ) : ℝ) ≤ C := by
    apply (le_div_iff₀ hL).mp
    simpa only [mul_one_div] using h
  have hhalf := half_le_progressionWeight_one (N + 1) (by omega)
  have hhalf_mul := mul_le_mul_of_nonneg_right hhalf hL.le
  nlinarith

/-- No constant compares the Pareto and Haar energies uniformly
on unrestricted finite residue spaces. -/
theorem no_uniform_quotient_energy_comparison :
    ¬ ∃ C : ℝ, ∀ N : ℕ, ∀ f : Fin (N + 1) → ℝ,
      quotientParetoEnergy (N + 1) f ≤ C * quotientHaarEnergy (N + 1) f := by
  rintro ⟨C, hC⟩
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * C)
  have h := quotient_energy_comparison_loss N C (hC N)
  norm_num only [Nat.cast_add, Nat.cast_one] at h
  linarith

/-- A probability weight on any one residue is at most one. -/
theorem progressionWeight_le_one_on_quotient (L : ℕ) (hL : 0 < L) (r : Fin L) :
    progressionWeight L (r.val + 1) ≤ 1 := by
  calc
    progressionWeight L (r.val + 1) ≤
        ∑ s : Fin L, progressionWeight L (s.val + 1) := by
      exact Finset.single_le_sum (fun s _ => progressionWeight_nonneg L (s.val + 1))
        (Finset.mem_univ r)
    _ = 1 := progressionWeight_normalization L hL

/-- A simple global upper comparison shows that the necessary energy loss
has linear order in the conductor. -/
theorem quotientParetoEnergy_le_conductor_mul_haar (L : ℕ) (hL : 0 < L)
    (f : Fin L → ℝ) :
    quotientParetoEnergy L f ≤ (L : ℝ) * quotientHaarEnergy L f := by
  have hLreal : (L : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hL)
  calc
    quotientParetoEnergy L f ≤ ∑ r : Fin L, (f r) ^ 2 := by
      apply Finset.sum_le_sum
      intro r _
      exact mul_le_of_le_one_left (sq_nonneg (f r))
        (progressionWeight_le_one_on_quotient L hL r)
    _ = (L : ℝ) * quotientHaarEnergy L f := by
      unfold quotientHaarEnergy
      field_simp [hLreal]

/-- Pareto point masses decrease on the positive integers. -/
theorem positiveWeight_le_of_pos_le {i j : ℕ} (hi : 0 < i) (hij : i ≤ j) :
    positiveWeight j ≤ positiveWeight i := by
  have hiR : (0 : ℝ) < i := by exact_mod_cast hi
  have hijR : (i : ℝ) ≤ j := by exact_mod_cast hij
  unfold positiveWeight
  apply one_div_le_one_div_of_le (by positivity)
  exact mul_le_mul hijR (by linarith) (by positivity) (by positivity)

/-- Residue one has the largest actual progression mass among positive
representatives. This comparison retains the whole infinite progression. -/
theorem progressionWeight_le_first (L r : ℕ) (hL : 0 < L) (hr : 0 < r) :
    progressionWeight L r ≤ progressionWeight L 1 := by
  apply Summable.tsum_le_tsum
  · intro j
    exact positiveWeight_le_of_pos_le (by omega) (by omega)
  · exact progressionWeight_summable L r hL
  · exact progressionWeight_summable L 1 hL

/-- Exact best energy comparison on the entire finite residue quotient.
The indicator of residue one attains this coefficient. -/
theorem quotient_energy_comparison_iff (N : ℕ) (C : ℝ) :
    (∀ f : Fin (N + 1) → ℝ,
      quotientParetoEnergy (N + 1) f ≤ C * quotientHaarEnergy (N + 1) f) ↔
      ((N + 1 : ℕ) : ℝ) * progressionWeight (N + 1) 1 ≤ C := by
  have hL : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  constructor
  · intro hC
    have h := hC (firstResidueAtom N)
    rw [quotientParetoEnergy_firstResidueAtom, quotientHaarEnergy_firstResidueAtom] at h
    have hmul : progressionWeight (N + 1) 1 * ((N + 1 : ℕ) : ℝ) ≤ C := by
      apply (le_div_iff₀ hL).mp
      simpa only [mul_one_div] using h
    simpa only [mul_comm] using hmul
  · intro hC f
    calc
      quotientParetoEnergy (N + 1) f ≤
          progressionWeight (N + 1) 1 * ∑ r, (f r) ^ 2 := by
        unfold quotientParetoEnergy
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro r _
        exact mul_le_mul_of_nonneg_right
          (progressionWeight_le_first (N + 1) (r.val + 1) (by omega) (by omega))
          (sq_nonneg (f r))
      _ = (((N + 1 : ℕ) : ℝ) * progressionWeight (N + 1) 1) *
          quotientHaarEnergy (N + 1) f := by
        unfold quotientHaarEnergy
        field_simp [ne_of_gt hL]
      _ ≤ C * quotientHaarEnergy (N + 1) f :=
        mul_le_mul_of_nonneg_right hC (quotientHaarEnergy_nonneg (N + 1) f)

/-- The exact best energy loss differs from L / 2 by at most one half. -/
theorem quotient_energy_optimal_constant_bounds (L : ℕ) (hL : 0 < L) :
    (L : ℝ) / 2 ≤ (L : ℝ) * progressionWeight L 1 ∧
      (L : ℝ) * progressionWeight L 1 ≤ (L : ℝ) / 2 + 1 / 2 := by
  have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
  constructor
  · have h := mul_le_mul_of_nonneg_left (half_le_progressionWeight_one L hL) hLreal.le
    nlinarith
  · have hsplit := progressionWeight_split L 1 hL
    norm_num [positiveWeight] at hsplit
    have hsplitmul := congrArg (fun x : ℝ => (L : ℝ) * x) hsplit
    have htail : progressionWeight L (1 + L) ≤ 1 / ((L : ℝ) * 2) := by
      convert progressionWeight_tail_upper L 1 hL using 1 <;> norm_num
    have hmul := (le_div_iff₀ (show (0 : ℝ) < (L : ℝ) * 2 by positivity)).mp htail
    nlinarith

end
end RiemannResearch.RH.Pareto
