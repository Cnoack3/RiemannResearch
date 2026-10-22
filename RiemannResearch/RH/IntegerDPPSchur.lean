import RiemannResearch.RH.IntegerDPPHazards

/-!
# The actual signed tail-Gram Schur increment

Source: user-provided
`RH_DPP_Proof_Attempt_and_Explicit_Zero_Hole_Obstruction_2026-09-20.md`,
Section 2. This module uses the actual residue-tail Gram matrices and their
verified inverses. No divergence hypothesis is assumed except explicitly
in the conditional RH endpoints.
-/

noncomputable section
open Filter
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.IntegerDPP
open CoefficientStabilization
open CoefficientStabilization.TailCapacity
open RiemannResearch.Analysis.FiniteGramCapacity
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.FiniteHilbertConstraints

/-- Only a reindexing of the actual next residue-tail dictionary. -/
def appendTail (n : ℕ) : Fin n ⊕ Unit → ThresholdHilbert :=
  Sum.elim (fun i : Fin n => tailAtom i.val) (fun _ : Unit => tailAtom n)

def appendSource (n : ℕ) : Fin n ⊕ Unit → ℝ :=
  Sum.elim (reciprocalSource n) (fun _ : Unit => 1 / ((n+2 : ℕ) : ℝ))

theorem appendTail_independent (n : ℕ) : LinearIndependent ℝ (appendTail n) := by
  let j : Fin n ⊕ Unit → Fin (n+1) :=
    Sum.elim Fin.castSucc (fun _ : Unit => Fin.last n)
  have hj : Function.Injective j := by
    intro a b hab
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        apply congrArg Sum.inl
        apply Fin.ext
        exact congrArg (fun x : Fin (n+1) => x.val) hab
      | inr b =>
        have he := congrArg Fin.val hab
        change a.val = n at he
        have ha := a.isLt
        omega
    | inr a =>
      cases b with
      | inl b =>
        have he := congrArg Fin.val hab
        change n = b.val at he
        have hb := b.isLt
        omega
      | inr b =>
        cases a
        cases b
        rfl
  have he : (fun i => tailAtom (j i).val) = appendTail n := by
    funext i
    cases i <;> rfl
  simpa only [Function.comp_def, he] using
    (finiteTailAtom_independent (n+1)).comp j hj

/-- The singleton Schur direction retains all signed old-block correlations. -/
def tailInnovation (n : ℕ) : ThresholdHilbert :=
  screened (finiteTailAtom_independent n) (fun _ : Unit => tailAtom n) ()

def schurSigma (n : ℕ) : ℝ := ‖tailInnovation n‖ ^ 2

def schurEta (n : ℕ) : ℝ :=
  1 / ((n+2 : ℕ) : ℝ) - inner ℝ (tailAtom n) (tailMinimum n)

theorem tailInnovation_ne_zero (n : ℕ) : tailInnovation n ≠ 0 := by
  exact LinearIndependent.ne_zero ()
    (screened_linearIndependent (finiteTailAtom_independent n)
      (fun _ : Unit => tailAtom n) (appendTail_independent n))

theorem schurSigma_pos (n : ℕ) : 0 < schurSigma n := by
  exact sq_pos_of_pos (norm_pos_iff.mpr (tailInnovation_ne_zero n))

/-- Entrywise full Schur complement, not a diagonal approximation. -/
theorem schurSigma_eq (n : ℕ) :
    schurSigma n = inner ℝ (tailAtom n) (tailAtom n) -
      ∑ i : Fin n, inverseCoeff (finiteTailAtom_independent n) (tailAtom n) i *
        cross (fun j : Fin n => tailAtom j.val) (tailAtom n) i := by
  simpa only [schurSigma, tailInnovation, real_inner_self_eq_norm_sq] using
    screened_gram_entry (finiteTailAtom_independent n)
      (fun _ : Unit => tailAtom n) () ()

/-- The signed source difference is kept intact. -/
theorem schurEta_eq (n : ℕ) :
    schurEta n = 1 / ((n+2 : ℕ) : ℝ) -
      ∑ i : Fin n, inverseSource (finiteTailAtom_independent n) (reciprocalSource n) i *
        cross (fun j : Fin n => tailAtom j.val) (tailAtom n) i := by
  exact screenedSource_eq (finiteTailAtom_independent n)
    (fun _ : Unit => tailAtom n) (reciprocalSource n)
    (fun _ : Unit => 1 / ((n+2 : ℕ) : ℝ)) ()

private theorem capacity_unit {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {v : Unit → H} (hv : LinearIndependent ℝ v) (b : Unit → ℝ) :
    capacity hv b = (b ()) ^ 2 / ‖v ()‖ ^ 2 := by
  have hσ : ‖v ()‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr (LinearIndependent.ne_zero () hv))
  have hn := inverseSource_normal hv b ()
  simp only [RiemannResearch.Analysis.FiniteHilbertGram.gram_apply,
    Fintype.sum_unique, real_inner_self_eq_norm_sq] at hn
  simp only [capacity, Fintype.sum_unique]
  apply (eq_div_iff hσ).mpr
  calc
    inverseSource hv b () * b () * ‖v ()‖ ^ 2 =
        (‖v ()‖ ^ 2 * inverseSource hv b ()) * b () := by ring
    _ = (b ()) ^ 2 := by rw [hn]; ring

/-- Equality under the concrete old-plus-new reindexing, via both variational
    minima. The inverse matrices are not identified by a separate assumption. -/
theorem append_capacity_eq (n : ℕ) :
    capacity (appendTail_independent n) (appendSource n) = tailCapacity (n+1) := by
  rw [capacity_eq_norm_sq, ← tailMinimum_norm_sq]
  apply le_antisymm
  · apply minimumVector_minimizes
    intro i
    cases i with
    | inl i =>
      simpa only [appendTail, appendSource, Sum.elim_inl, reciprocalSource,
        Fin.val_castSucc] using tailMinimum_observation (n+1) i.castSucc
    | inr i =>
      simpa only [appendTail, appendSource, Sum.elim_inr, reciprocalSource,
        Fin.val_last] using tailMinimum_observation (n+1) (Fin.last n)
  · apply minimumVector_minimizes (finiteTailAtom_independent (n+1))
      (reciprocalSource (n+1))
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [appendTail, appendSource, Sum.elim_inr, reciprocalSource,
        Fin.val_last] using
        minimumVector_observation (appendTail_independent n) (appendSource n) (Sum.inr ())
    · simpa only [appendTail, appendSource, Sum.elim_inl, reciprocalSource,
        Fin.val_castSucc] using
        minimumVector_observation (appendTail_independent n) (appendSource n) (Sum.inl j)

/-- The exact scalar gain from the actual signed tail Gram matrix. -/
theorem capacity_schur_step (n : ℕ) :
    tailCapacity (n+1) = tailCapacity n + (schurEta n) ^ 2 / schurSigma n := by
  let hs := screened_linearIndependent (finiteTailAtom_independent n)
    (fun _ : Unit => tailAtom n) (appendTail_independent n)
  have h := capacity_screened_add (finiteTailAtom_independent n)
    (fun _ : Unit => tailAtom n) hs (appendTail_independent n)
    (reciprocalSource n) (fun _ : Unit => 1 / ((n+2 : ℕ) : ℝ))
  change capacity (appendTail_independent n) (appendSource n) = _ at h
  rw [append_capacity_eq, capacity_unit] at h
  exact h

theorem capacity_schur_increment (n : ℕ) :
    tailCapacity (n+1) - tailCapacity n = (schurEta n) ^ 2 / schurSigma n := by
  rw [capacity_schur_step]
  ring

/-- Conditional entrance formula in exact arithmetic Schur coordinates. -/
theorem hazard_eq_schur (n : ℕ) :
    hazard n = (schurEta n) ^ 2 /
      ((tailCapacity n + 2) * schurSigma n + (schurEta n) ^ 2) := by
  have hσ := ne_of_gt (schurSigma_pos n)
  have hden : (tailCapacity n + 2) * schurSigma n + (schurEta n) ^ 2 ≠ 0 := by
    have hc : 0 < tailCapacity n + 2 := by linarith [tailCapacity_nonneg n]
    nlinarith [mul_pos hc (schurSigma_pos n), sq_nonneg (schurEta n)]
  rw [hazard_eq_capacity_increment, capacity_schur_increment, capacity_schur_step]
  field_simp [hσ, hden]
  ring

/-- Every increment, including stage zero, appears in the signed Schur telescope. -/
theorem capacity_eq_sum_schur (n : ℕ) :
    tailCapacity n = ∑ j ∈ Finset.range n, (schurEta j) ^ 2 / schurSigma j := by
  have h := capacity_telescope tailCapacity
    (fun j => (schurEta j) ^ 2 / schurSigma j) capacity_schur_step n
  have hc : tailCapacity 0 = 0 := by simp [tailCapacity, capacity]
  simpa only [hc, zero_add] using h

theorem riemannHypothesis_of_schur_sum_tendsto
    (h : Tendsto (fun N => ∑ j ∈ Finset.range N,
      (schurEta j) ^ 2 / schurSigma j) Filter.atTop Filter.atTop) : RiemannHypothesis := by
  apply riemannHypothesis_of_tailCapacity_tendsto
  change Tendsto tailCapacity atTop atTop
  simpa only [← capacity_eq_sum_schur] using h

end RiemannResearch.RH.Pareto.IntegerDPP
