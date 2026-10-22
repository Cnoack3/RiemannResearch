/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ParetoPeriodicRegrouping
import RiemannResearch.RH.ParetoResidueMoments
import RiemannResearch.RH.ParetoNoiseSignal

/-!
# Exact progression-weight calculus

Source: the user discussion of the Pareto/CRT weights, 11 September 2026.
These results concern the actual `progressionWeight`, with positive residue
representatives. The zero residue class is represented by the modulus.
All infinite sums below are genuinely summable; signed mixed entries survive.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

/-- Partial fractions with the complete scaling factor `1 / Q`. -/
theorem positiveWeight_progression_reciprocal (Q r j : ℕ)
    (hQ : 0 < Q) (hr : 0 < r) :
    positiveWeight (r + Q * j) =
      (1 / (Q : ℝ)) *
        (1 / ((j : ℝ) + (r : ℝ) / Q) -
          1 / ((j : ℝ) + ((r : ℝ) + 1) / Q)) := by
  have hq : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have h0 : (r : ℝ) + Q * j ≠ 0 := by positivity
  have h1 : (r : ℝ) + Q * j + 1 ≠ 0 := by positivity
  have ha : (j : ℝ) + (r : ℝ) / Q ≠ 0 := by positivity
  have hb : (j : ℝ) + ((r : ℝ) + 1) / Q ≠ 0 := by positivity
  simp only [positiveWeight, Nat.cast_add, Nat.cast_mul]
  field_simp
  <;> ring

/-- The reciprocal differences converge absolutely; the divergent reciprocal
series are never split into separate infinite sums. -/
theorem progression_reciprocal_summable (Q r : ℕ)
    (hQ : 0 < Q) (hr : 0 < r) :
    Summable (fun j : ℕ =>
      1 / ((j : ℝ) + (r : ℝ) / Q) -
        1 / ((j : ℝ) + ((r : ℝ) + 1) / Q)) := by
  have hs := (progressionWeight_summable Q r hQ).mul_left (Q : ℝ)
  apply hs.congr
  intro j
  rw [positiveWeight_progression_reciprocal Q r j hQ hr]
  have hq : (Q : ℝ) ≠ 0 := by positivity
  field_simp

/-- Exact convergent reciprocal-difference representation of the CRT weight. -/
theorem progressionWeight_reciprocal_series (Q r : ℕ)
    (hQ : 0 < Q) (hr : 0 < r) :
    progressionWeight Q r = (1 / (Q : ℝ)) *
      ∑' j : ℕ, (1 / ((j : ℝ) + (r : ℝ) / Q) -
        1 / ((j : ℝ) + ((r : ℝ) + 1) / Q)) := by
  unfold progressionWeight
  simp_rw [positiveWeight_progression_reciprocal Q r _ hQ hr]
  exact (progression_reciprocal_summable Q r hQ hr).tsum_mul_left _

/-- Exchange the finite residue sum and the infinite progression sum, for
arbitrary signed residue coefficients as well as nonnegative squared errors. -/
theorem progressionWeight_sum_exchange (Q : ℕ) (hQ : 0 < Q)
    (c : Fin Q → ℝ) :
    (∑ r : Fin Q, progressionWeight Q (r.val + 1) * c r) =
      ∑' j : ℕ, ∑ r : Fin Q, positiveWeight (r.val + 1 + Q * j) * c r := by
  have hs (r : Fin Q) :=
    (progressionWeight_summable Q (r.val + 1) hQ).mul_right (c r)
  calc
    _ = ∑ r : Fin Q, ∑' j : ℕ,
        positiveWeight (r.val + 1 + Q * j) * c r := by
      apply Finset.sum_congr rfl
      intro r _
      exact ((progressionWeight_summable Q (r.val + 1) hQ).tsum_mul_right _).symm
    _ = _ := by
      exact (Summable.tsum_finsetSum (s := Finset.univ) (fun r _ => hs r)).symm

/-- The exchanged expression is the complete Pareto squared approximation
error of a bounded periodic function, not a truncated CRT energy. -/
theorem periodic_paretoError_blocks (Q : ℕ) (hQ : 0 < Q)
    (f : ℕ → ℝ) {C : ℝ} (hf : ∀ n, |f n| ≤ C)
    (hp : ∀ n, f (n + Q) = f n) :
    paretoError f = ∑' j : ℕ, ∑ r : Fin Q,
      positiveWeight (r.val + 1 + Q * j) * (1 - f (r.val + 1)) ^ 2 := by
  have he : ∀ n, |1 - f n| ≤ 1 + C := by
    intro n
    calc
      _ ≤ |(1 : ℝ)| + |f n| := abs_sub _ _
      _ ≤ 1 + C := by simpa using add_le_add_left (hf n) 1
  rw [paretoError, periodic_paretoInner Q hQ _ he (by intro n; rw [hp])]
  exact progressionWeight_sum_exchange Q hQ _

/-- The actual positive Pareto mass strictly decreases with its index. -/
theorem positiveWeight_strictAntiOn :
    StrictAntiOn positiveWeight (Set.Ioi (0 : ℕ)) := by
  intro r hr s hs hrs
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hrs' : (r : ℝ) < s := by exact_mod_cast hrs
  have hs' : (0 : ℝ) < s := lt_trans hr' hrs'
  unfold positiveWeight
  apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith

/-- Larger positive representatives carry strictly less progression mass. -/
theorem progressionWeight_strictAntiOn (Q : ℕ) (hQ : 0 < Q) :
    StrictAntiOn (progressionWeight Q) (Set.Ioi (0 : ℕ)) := by
  intro r hr s hs hrs
  have hlt (j : ℕ) : positiveWeight (s + Q * j) < positiveWeight (r + Q * j) :=
    positiveWeight_strictAntiOn (by simp only [Set.mem_Ioi] at *; omega)
      (by simp only [Set.mem_Ioi] at *; omega) (by omega)
  exact Summable.tsum_lt_tsum (fun j => (hlt j).le) (hlt 0)
    (progressionWeight_summable Q s hQ) (progressionWeight_summable Q r hQ)

theorem progressionWeight_one_one : progressionWeight 1 1 = 1 := by
  have h := progressionWeight_normalization 1 (by omega)
  simpa [Fin.sum_univ_succ] using h

theorem progressionWeight_two_one : progressionWeight 2 1 = Real.log 2 := by
  have h := periodic_paretoMean 2 (by omega) (residue 2)
    (fun n => residue_abs_le 2 n (by omega))
    (by intro n; simp [residue, Nat.add_mod])
  norm_num [Fin.sum_univ_succ, residue] at h
  exact h.symm.trans paretoMean_residue_two

theorem progressionWeight_two_two : progressionWeight 2 2 = 1 - Real.log 2 := by
  have h := progressionWeight_normalization 2 (by omega)
  norm_num [Fin.sum_univ_succ, progressionWeight_two_one] at h
  linarith

end
end RiemannResearch.RH.Pareto
