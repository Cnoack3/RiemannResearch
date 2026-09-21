import RiemannResearch.RH.ParetoCoprimeDefectVariational

/-!
# Exact elimination of even moduli in the odd-moment problem

Source: continuation of the user-provided Pareto capacity handoff,
2026-09-21. The proof uses the existing finite Hilbert Gram identities.
Even moduli are optimized out, with their full Schur correction retained.
The resulting small-energy condition remains an Open arithmetic premise.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.FiniteHilbertConstraints
open RiemannResearch.Analysis.FiniteGramCapacity

abbrev EvenTailIndex (n : ℕ) := {i : Fin n // 2 ∣ i.val + 2}
abbrev OddTailIndex (n : ℕ) := {i : Fin n // ¬ 2 ∣ i.val + 2}

def evenTailAtom (n : ℕ) (i : EvenTailIndex n) : ThresholdHilbert := tailAtom i.val.val
def oddTailAtom (n : ℕ) (i : OddTailIndex n) : ThresholdHilbert := tailAtom i.val.val

theorem evenTailAtom_independent (n : ℕ) : LinearIndependent ℝ (evenTailAtom n) :=
  (finiteTailAtom_independent n).comp Subtype.val Subtype.val_injective

private theorem parityTailAtom_independent (n : ℕ) :
    LinearIndependent ℝ (Sum.elim (evenTailAtom n) (oddTailAtom n)) := by
  let f : EvenTailIndex n ⊕ OddTailIndex n → Fin n := Sum.elim Subtype.val Subtype.val
  have hf : Function.Injective f := by
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (Subtype.ext h)
      | inr b =>
        change a.val = b.val at h
        exact (b.property (h ▸ a.property)).elim
    | inr a =>
      cases b with
      | inl b =>
        change a.val = b.val at h
        exact (a.property (h.symm ▸ b.property)).elim
      | inr b => exact congrArg Sum.inr (Subtype.ext h)
  convert (finiteTailAtom_independent n).comp f hf using 1
  funext i
  cases i <;> rfl

/-- Odd rows after projection off every even row in the same dictionary. -/
def screenedOddTailAtom (n : ℕ) : OddTailIndex n → ThresholdHilbert :=
  screened (evenTailAtom_independent n) (oddTailAtom n)

theorem screenedOddTailAtom_independent (n : ℕ) :
    LinearIndependent ℝ (screenedOddTailAtom n) :=
  screened_linearIndependent (evenTailAtom_independent n) (oddTailAtom n)
    (parityTailAtom_independent n)

theorem even_screenedOdd_orthogonal (n : ℕ) (i : EvenTailIndex n) (j : OddTailIndex n) :
    inner ℝ (evenTailAtom n i) (screenedOddTailAtom n j) = 0 :=
  inner_old_screened (evenTailAtom_independent n) (oddTailAtom n) i j

/-- Entrywise full Schur complement, including every even-odd mixed term. -/
theorem screenedOddTailAtom_gram (n : ℕ) (i j : OddTailIndex n) :
    inner ℝ (screenedOddTailAtom n i) (screenedOddTailAtom n j) =
      inner ℝ (oddTailAtom n i) (oddTailAtom n j) -
        ∑ k, inverseCoeff (evenTailAtom_independent n) (oddTailAtom n i) k *
          inner ℝ (evenTailAtom n k) (oddTailAtom n j) :=
  screened_gram_entry (evenTailAtom_independent n) (oddTailAtom n) i j

def parityTailCoefficients (n : ℕ) (a : EvenTailIndex n → ℝ)
    (b : OddTailIndex n → ℝ) (i : Fin n) : ℝ :=
  if h : 2 ∣ i.val + 2 then a ⟨i,h⟩ else b ⟨i,h⟩

theorem parityTailCoefficients_synthesis (n : ℕ) (a : EvenTailIndex n → ℝ)
    (b : OddTailIndex n → ℝ) :
    Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val)
      (parityTailCoefficients n a b) =
      Fintype.linearCombination ℝ (evenTailAtom n) a +
      Fintype.linearCombination ℝ (oddTailAtom n) b := by
  simp only [Fintype.linearCombination_apply]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun i : Fin n => 2 ∣ i.val+2)]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _
  · simp [parityTailCoefficients, i.property, evenTailAtom]
  · simp [parityTailCoefficients, i.property, oddTailAtom]

theorem parityTailCoefficients_moment (n : ℕ) (a : EvenTailIndex n → ℝ)
    (b : OddTailIndex n → ℝ) :
    (∑ i : Fin n, if 2 ∣ i.val+2 then 0 else
      parityTailCoefficients n a b i / ((i.val+2 : ℕ) : ℝ)^2) =
      ∑ j : OddTailIndex n, b j / ((j.val.val+2 : ℕ) : ℝ)^2 := by
  rw [← Fintype.sum_subtype_add_sum_subtype (fun i : Fin n => 2 ∣ i.val+2)]
  have he : (∑ i : EvenTailIndex n, if 2 ∣ i.val.val+2 then (0 : ℝ) else
      parityTailCoefficients n a b i.val / ((i.val.val+2 : ℕ) : ℝ)^2) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact if_pos i.property
  rw [he, zero_add]
  apply Finset.sum_congr rfl
  intro i _
  simp [parityTailCoefficients, i.property]

/-- The unique optimal even coefficients for fixed odd coefficients. -/
def optimalEvenTailCoefficients (n : ℕ) (b : OddTailIndex n → ℝ) : EvenTailIndex n → ℝ :=
  -inverseCoeff (evenTailAtom_independent n)
    (Fintype.linearCombination ℝ (oddTailAtom n) b)

theorem screenedOdd_synthesis (n : ℕ) (b : OddTailIndex n → ℝ) :
    Fintype.linearCombination ℝ (screenedOddTailAtom n) b =
      Fintype.linearCombination ℝ (oddTailAtom n) b -
        Fintype.linearCombination ℝ (evenTailAtom n)
          (inverseCoeff (evenTailAtom_independent n)
            (Fintype.linearCombination ℝ (oddTailAtom n) b)) := by
  have hi : inverseCoeff (evenTailAtom_independent n)
      (Fintype.linearCombination ℝ (oddTailAtom n) b) =
      ∑ j, b j • inverseCoeff (evenTailAtom_independent n) (oddTailAtom n j) := by
    unfold inverseCoeff cross
    simp only [Fintype.linearCombination_apply, inner_sum, inner_smul_right]
    rw [show (fun i => ∑ j, b j * inner ℝ (evenTailAtom n i) (oddTailAtom n j)) =
      ∑ j, b j • (fun i => inner ℝ (evenTailAtom n i) (oddTailAtom n j)) by
        funext i; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]]
    simp only [map_sum, map_smul]
  rw [hi]
  simp only [Fintype.linearCombination_apply, screenedOddTailAtom, screened,
    smul_sub, Finset.sum_sub_distrib, map_sum, map_smul]

theorem optimalEvenTail_synthesis (n : ℕ) (b : OddTailIndex n → ℝ) :
    Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val)
      (parityTailCoefficients n (optimalEvenTailCoefficients n b) b) =
      Fintype.linearCombination ℝ (screenedOddTailAtom n) b := by
  rw [parityTailCoefficients_synthesis, optimalEvenTailCoefficients, map_neg,
    screenedOdd_synthesis]
  abel

/-- Exact completion for arbitrary signed even coefficients. -/
theorem parityTail_energy_completion (n : ℕ) (a : EvenTailIndex n → ℝ)
    (b : OddTailIndex n → ℝ) :
    ‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val)
      (parityTailCoefficients n a b)‖^2 =
      ‖Fintype.linearCombination ℝ (screenedOddTailAtom n) b‖^2 +
      ‖Fintype.linearCombination ℝ (evenTailAtom n)
        (a - optimalEvenTailCoefficients n b)‖^2 := by
  have h := residual_completion (evenTailAtom_independent n)
    (Fintype.linearCombination ℝ (oddTailAtom n) b) (-a)
  rw [map_neg, sub_neg_eq_add, ← screenedOdd_synthesis] at h
  rw [show (-a - inverseCoeff (evenTailAtom_independent n)
      (Fintype.linearCombination ℝ (oddTailAtom n) b)) =
      -(a - optimalEvenTailCoefficients n b) by
        unfold optimalEvenTailCoefficients; abel, map_neg, norm_neg] at h
  rw [parityTailCoefficients_synthesis, add_comm]
  exact h

theorem parityTail_optimal_iff (n : ℕ) (a : EvenTailIndex n → ℝ)
    (b : OddTailIndex n → ℝ) :
    ‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val)
      (parityTailCoefficients n a b)‖^2 =
      ‖Fintype.linearCombination ℝ (screenedOddTailAtom n) b‖^2 ↔
      a = optimalEvenTailCoefficients n b := by
  rw [parityTail_energy_completion]
  constructor
  · intro h
    have hn : Fintype.linearCombination ℝ (evenTailAtom n)
        (a - optimalEvenTailCoefficients n b) = 0 := by
      apply norm_eq_zero.mp
      nlinarith [norm_nonneg (Fintype.linearCombination ℝ (evenTailAtom n)
        (a - optimalEvenTailCoefficients n b))]
    apply sub_eq_zero.mp
    apply (evenTailAtom_independent n).fintypeLinearCombination_injective
    simpa only [map_zero] using hn
  · rintro rfl
    simp

theorem oddMoment_small_tail_iff_screened :
    (∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (c : Fin n → ℝ),
      (∑ i, if 2 ∣ i.val+2 then 0 else c i / ((i.val+2 : ℕ) : ℝ)^2) = 1 ∧
      ‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) c‖^2 < ε) ↔
    (∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (b : OddTailIndex n → ℝ),
      (∑ j, b j / ((j.val.val+2 : ℕ) : ℝ)^2) = 1 ∧
      ‖Fintype.linearCombination ℝ (screenedOddTailAtom n) b‖^2 < ε) := by
  constructor
  · intro h ε hε
    obtain ⟨n,c,hc,he⟩ := h ε hε
    let a : EvenTailIndex n → ℝ := fun i => c i.val
    let b : OddTailIndex n → ℝ := fun i => c i.val
    have hp : parityTailCoefficients n a b = c := by
      funext i; dsimp [parityTailCoefficients, a, b]; split <;> rfl
    refine ⟨n,b,?_,?_⟩
    · rw [← parityTailCoefficients_moment n a b, hp]
      exact hc
    · have hx := parityTail_energy_completion n a b
      rw [hp] at hx
      nlinarith [sq_nonneg ‖Fintype.linearCombination ℝ (evenTailAtom n)
        (a - optimalEvenTailCoefficients n b)‖]
  · intro h ε hε
    obtain ⟨n,b,hb,he⟩ := h ε hε
    refine ⟨n,parityTailCoefficients n (optimalEvenTailCoefficients n b) b,?_,?_⟩
    · rwa [parityTailCoefficients_moment]
    · rwa [optimalEvenTail_synthesis]

/-- CONDITIONAL RESEARCH REDUCTION: the screened odd energy premise is Open. -/
theorem riemannHypothesis_of_screenedOdd_small_tail
    (h : ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (b : OddTailIndex n → ℝ),
      (∑ j, b j / ((j.val.val+2 : ℕ) : ℝ)^2) = 1 ∧
      ‖Fintype.linearCombination ℝ (screenedOddTailAtom n) b‖^2 < ε) :
    RiemannHypothesis :=
  riemannHypothesis_of_oddMoment_small_tail (oddMoment_small_tail_iff_screened.mpr h)

theorem coprimeDefectMinimum_even_observation (n : ℕ) (i : EvenTailIndex n) :
    inner ℝ (evenTailAtom n i) (coprimeDefectMinimum n) = 0 := by
  have h := coprimeDefectMinimum_observation n i.val
  simpa only [coprimeDefectSource, coprimeObservationDefect_two,
    if_pos i.property, evenTailAtom] using h

theorem coprimeDefectMinimum_screenedOdd_observation (n : ℕ) (j : OddTailIndex n) :
    inner ℝ (screenedOddTailAtom n j) (coprimeDefectMinimum n) =
      coprimeDefectSource n j.val := by
  unfold screenedOddTailAtom screened
  rw [inner_sub_left, inner_synthesis_left]
  simp only [coprimeDefectMinimum_even_observation, mul_zero,
    Finset.sum_const_zero, sub_zero]
  exact coprimeDefectMinimum_observation n j.val

/-- The full defect representer is exactly the odd Schur representer. -/
theorem coprimeDefectMinimum_eq_screenedOdd (n : ℕ) :
    coprimeDefectMinimum n = minimumVector (screenedOddTailAtom_independent n)
      (fun j : OddTailIndex n => coprimeDefectSource n j.val) := by
  let x := minimumVector (screenedOddTailAtom_independent n)
    (fun j : OddTailIndex n => coprimeDefectSource n j.val)
  have he (i : EvenTailIndex n) : inner ℝ (evenTailAtom n i) x = 0 :=
    inner_old_screened_minimumVector (evenTailAtom_independent n) (oddTailAtom n)
      (screenedOddTailAtom_independent n) _ i
  have ho (j : OddTailIndex n) : inner ℝ (oddTailAtom n j) x =
      coprimeDefectSource n j.val := by
    have h := minimumVector_observation (screenedOddTailAtom_independent n)
      (fun j : OddTailIndex n => coprimeDefectSource n j.val) j
    change inner ℝ (oddTailAtom n j -
      Fintype.linearCombination ℝ (evenTailAtom n)
        (inverseCoeff (evenTailAtom_independent n) (oddTailAtom n j))) x = _ at h
    rw [inner_sub_left, inner_synthesis_left] at h
    simpa only [he, mul_zero, Finset.sum_const_zero, sub_zero] using h
  have hx (i : Fin n) : inner ℝ (tailAtom i.val) x = coprimeDefectSource n i := by
    by_cases hi : 2 ∣ i.val+2
    · have h := he ⟨i,hi⟩
      simpa only [evenTailAtom, coprimeDefectSource,
        coprimeObservationDefect_two, if_pos hi] using h
    · exact ho ⟨i,hi⟩
  have h₁ := minimumVector_minimizes (finiteTailAtom_independent n)
    (coprimeDefectSource n) x hx
  have h₂ := minimumVector_minimizes (screenedOddTailAtom_independent n)
    (fun j : OddTailIndex n => coprimeDefectSource n j.val)
    (coprimeDefectMinimum n) (coprimeDefectMinimum_screenedOdd_observation n)
  exact ((feasible_norm_sq_eq_iff (finiteTailAtom_independent n)
    (coprimeDefectSource n) x hx).mp (le_antisymm h₂ h₁)).symm

/-- Exact capacity reduction; the unscreened odd principal Gram is not used. -/
theorem coprimeDefectCapacity_eq_screenedOdd (n : ℕ) :
    coprimeDefectCapacity n = capacity (screenedOddTailAtom_independent n)
      (fun j : OddTailIndex n => coprimeDefectSource n j.val) := by
  rw [← coprimeDefectMinimum_norm_sq, coprimeDefectMinimum_eq_screenedOdd,
    capacity_eq_norm_sq]

end RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
