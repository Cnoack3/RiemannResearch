import RiemannResearch.RH.ParetoResidueGramStrict

/-!
# Exact constrained minimization for the actual full-tail residue Gram form

Source: advanced covariance repair report, Section 7.6. The finite Lagrange
certificate below applies directly to the genuine residue functions and the
complete infinite Pareto inner product. Its conclusion is an exact Pythagorean
identity with a strictly positive error for any distinct coefficient vector.
No uniform estimate, matrix convergence, or RH statement is assumed or proved.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

/-- Synthesis by distinct, nontrivial actual residues. -/
def residueSynthesis (s : Finset ℕ) (z : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ s, z i * residue (i + 2) k

theorem residueSynthesis_bounded (s : Finset ℕ) (z : ℕ → ℝ) :
    ∀ k, |residueSynthesis s z k| ≤ ∑ i ∈ s, |z i| * ((i + 2 : ℕ) : ℝ) :=
  bounded_finsetCombination s z (fun i k => residue_abs_le (i + 2) k (by omega))

theorem residueSynthesis_sub (s : Finset ℕ) (z x : ℕ → ℝ) :
    residueSynthesis s (fun i => z i - x i) =
      fun k => residueSynthesis s z k - residueSynthesis s x k := by
  funext k
  simp only [residueSynthesis, sub_mul, Finset.sum_sub_distrib]

/-- The actual residual objective, with every mixed term and infinite tail. -/
def residueResidualObjective (s : Finset ℕ) (r : ℕ → ℝ) (z : ℕ → ℝ) : ℝ :=
  paretoInner (fun k => r k - residueSynthesis s z k)
    (fun k => r k - residueSynthesis s z k)

/-- Exact error decomposition from orthogonality of the true residual. -/
theorem residueResidualObjective_split (s : Finset ℕ) {r : ℕ → ℝ} {C : ℝ}
    (hr : ∀ k, |r k| ≤ C) (z x : ℕ → ℝ)
    (ho : paretoInner (fun k => r k - residueSynthesis s x k)
      (residueSynthesis s (fun i => z i - x i)) = 0) :
    residueResidualObjective s r z = residueResidualObjective s r x +
      residueGramQuadratic s (fun i => z i - x i) := by
  have hid : (fun k => r k - residueSynthesis s z k) =
      (fun k => (r k - residueSynthesis s x k) -
        1 * residueSynthesis s (fun i => z i - x i) k) := by
    rw [residueSynthesis_sub]
    funext k
    ring
  unfold residueResidualObjective
  rw [hid, paretoInner_residual_polynomial
    (bounded_sub hr (residueSynthesis_bounded s x))
    (residueSynthesis_bounded s (fun i => z i - x i)), ho]
  rw [residueGramQuadratic_eq_inner]
  change _ = _ + paretoInner (residueSynthesis s (fun i => z i - x i))
    (residueSynthesis s (fun i => z i - x i))
  ring

/-- Every genuine Gram row is the corresponding residual pairing. -/
theorem residue_residual_pairing (s : Finset ℕ) {r : ℕ → ℝ} {C : ℝ}
    (hr : ∀ k, |r k| ≤ C) (x : ℕ → ℝ) (i : ℕ) :
    paretoInner (residue (i + 2)) (fun k => r k - residueSynthesis s x k) =
      paretoInner (residue (i + 2)) r -
        ∑ j ∈ s, x j * paretoInner (residue (i + 2)) (residue (j + 2)) := by
  have hi := fun k => residue_abs_le (i + 2) k (by omega)
  rw [paretoInner_sub_right hi hr (residueSynthesis_bounded s x)]
  unfold residueSynthesis
  rw [paretoInner_finsetSum_right s hi
    (fun j => bounded_const_mul (fun k => residue_abs_le (j + 2) k (by omega)) (x j))]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  exact paretoInner_const_mul_right hi
    (fun k => residue_abs_le (j + 2) k (by omega)) (x j)

/-- Linear constraints annihilate the Lagrange multiplier pairing exactly. -/
theorem residue_constraint_orthogonality (s rows : Finset ℕ)
    (K : ℕ → ℕ → ℝ) (lambda u : ℕ → ℝ)
    {v : ℕ → ℝ} {C : ℝ} (hv : ∀ k, |v k| ≤ C)
    (hstationary : ∀ i ∈ s,
      paretoInner (residue (i + 2)) v = ∑ a ∈ rows, lambda a * K a i)
    (hhomogeneous : ∀ a ∈ rows, ∑ i ∈ s, K a i * u i = 0) :
    paretoInner v (residueSynthesis s u) = 0 := by
  rw [paretoInner_comm]
  unfold residueSynthesis
  rw [paretoInner_finsetSum_left s
    (fun i => bounded_const_mul (fun k => residue_abs_le (i + 2) k (by omega)) (u i)) hv]
  calc
    _ = ∑ i ∈ s, u i * ∑ a ∈ rows, lambda a * K a i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [paretoInner_const_mul_left
        (fun k => residue_abs_le (i + 2) k (by omega)) hv, hstationary i hi]
    _ = ∑ a ∈ rows, lambda a * ∑ i ∈ s, K a i * u i := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro a ha
      rw [hhomogeneous a ha, mul_zero]

/-- The exact constrained minimum identity. The stationarity certificate is
written using the actual complete residue Gram matrix, not an abstract form. -/
theorem residue_constrained_minimum_identity (s rows : Finset ℕ)
    (K : ℕ → ℕ → ℝ) (lambda z x : ℕ → ℝ)
    {r : ℕ → ℝ} {C : ℝ} (hr : ∀ k, |r k| ≤ C)
    (hfeasible : ∀ a ∈ rows,
      (∑ i ∈ s, K a i * z i) = ∑ i ∈ s, K a i * x i)
    (hstationary : ∀ i ∈ s,
      paretoInner (residue (i + 2)) r -
          (∑ j ∈ s, x j * paretoInner (residue (i + 2)) (residue (j + 2))) =
        ∑ a ∈ rows, lambda a * K a i) :
    residueResidualObjective s r z = residueResidualObjective s r x +
      residueGramQuadratic s (fun i => z i - x i) := by
  apply residueResidualObjective_split s hr z x
  apply residue_constraint_orthogonality s rows K lambda (fun i => z i - x i)
    (bounded_sub hr (residueSynthesis_bounded s x))
  · intro i hi
    rw [residue_residual_pairing s hr x i]
    exact hstationary i hi
  · intro a ha
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr (hfeasible a ha)

/-- Any different feasible coefficient vector has strictly larger full error. -/
theorem residue_constrained_minimum_strict (s rows : Finset ℕ)
    (K : ℕ → ℕ → ℝ) (lambda z x : ℕ → ℝ)
    {r : ℕ → ℝ} {C : ℝ} (hr : ∀ k, |r k| ≤ C)
    (hfeasible : ∀ a ∈ rows,
      (∑ i ∈ s, K a i * z i) = ∑ i ∈ s, K a i * x i)
    (hstationary : ∀ i ∈ s,
      paretoInner (residue (i + 2)) r -
          (∑ j ∈ s, x j * paretoInner (residue (i + 2)) (residue (j + 2))) =
        ∑ a ∈ rows, lambda a * K a i)
    (hne : ∃ i ∈ s, z i ≠ x i) :
    residueResidualObjective s r x < residueResidualObjective s r z := by
  rw [residue_constrained_minimum_identity s rows K lambda z x hr hfeasible hstationary]
  apply lt_add_of_pos_right
  apply residueGramQuadratic_pos
  obtain ⟨i, hi, hne⟩ := hne
  exact ⟨i, hi, sub_ne_zero.mpr hne⟩

end
end RiemannResearch.RH.Pareto
