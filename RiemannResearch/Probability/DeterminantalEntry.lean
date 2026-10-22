import RiemannResearch.Probability.DeterminantalProcess
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Entry probabilities in an already given nested DPP coupling

Source: the user-provided `RH_DPP_Proof_Attempt_and_Explicit_Zero_Hole_Obstruction`
handoff, Section 2. The exact entrance identity is a probability identity on a
common sample space. This module assumes the pointwise nested coupling and does
not claim to construct a coupling from ordered kernels. The two-point formulas
are direct instances of the determinantal correlation definition.
-/

noncomputable section
open MeasureTheory Matrix
open scoped BigOperators Classical ENNReal

namespace RiemannResearch.Probability.DPP

variable {α Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X Y : Ω → Set α} {K L : α → α → ℝ}

/-- In a given nested coupling, entry at the next stage is exactly the vacancy
mass lost between the two stages. No independence is assumed. -/
theorem IsDPP.entry_mass (hX : IsDPP μ X K) (hY : IsDPP μ Y L)
    (hXY : ∀ ω, X ω ⊆ Y ω) (i : α) :
    μ.real {ω | i ∈ Y ω ∧ i ∉ X ω} =
      μ.real {ω | i ∉ X ω} - μ.real {ω | i ∉ Y ω} := by
  have hsub : {ω | i ∈ X ω} ⊆ {ω | i ∈ Y ω} :=
    fun ω hω => hXY ω hω
  change μ.real ({ω | i ∈ Y ω} \ {ω | i ∈ X ω}) = _
  rw [measureReal_sdiff hsub (hX.measurable_occupancy i),
    hY.occupation i, hX.occupation i, hX.vacancy i, hY.vacancy i]
  ring

/-- Conditional entry probability given current absence, expressed as the
ratio of the entry event to the conditioning event. The positivity hypothesis
ensures that this conditioning event has positive probability. -/
theorem IsDPP.entry_ratio (hX : IsDPP μ X K) (hY : IsDPP μ Y L)
    (hXY : ∀ ω, X ω ⊆ Y ω) (i : α)
    (hq : 0 < μ.real {ω | i ∉ X ω}) :
    μ.real {ω | i ∈ Y ω ∧ i ∉ X ω} / μ.real {ω | i ∉ X ω} =
      1 - μ.real {ω | i ∉ Y ω} / μ.real {ω | i ∉ X ω} := by
  rw [hX.entry_mass hY hXY i, sub_div, div_self (ne_of_gt hq)]

/-- The exact conditional entrance probability is in the interval `[0,1]`. -/
theorem IsDPP.entry_ratio_bounds (hX : IsDPP μ X K) (hY : IsDPP μ Y L)
    (hXY : ∀ ω, X ω ⊆ Y ω) (i : α)
    (hq : 0 < μ.real {ω | i ∉ X ω}) :
    0 ≤ μ.real {ω | i ∈ Y ω ∧ i ∉ X ω} / μ.real {ω | i ∉ X ω} ∧
      μ.real {ω | i ∈ Y ω ∧ i ∉ X ω} / μ.real {ω | i ∉ X ω} ≤ 1 := by
  constructor
  · exact div_nonneg measureReal_nonneg hq.le
  · rw [hX.entry_ratio hY hXY i hq]
    have hnonneg : 0 ≤ μ.real {ω | i ∉ Y ω} / μ.real {ω | i ∉ X ω} :=
      div_nonneg measureReal_nonneg hq.le
    linarith

/-- The same conditional entry identity stated entirely in kernel diagonals. -/
theorem IsDPP.entry_ratio_kernel (hX : IsDPP μ X K) (hY : IsDPP μ Y L)
    (hXY : ∀ ω, X ω ⊆ Y ω) (i : α)
    (hq : 0 < 1 - K i i) :
    μ.real {ω | i ∈ Y ω ∧ i ∉ X ω} / (1 - K i i) =
      1 - (1 - L i i) / (1 - K i i) := by
  have hq' : 0 < μ.real {ω | i ∉ X ω} := by rwa [hX.vacancy i]
  simpa only [hX.vacancy i, hY.vacancy i] using hX.entry_ratio hY hXY i hq'

/-- The generic two-stage formula applies at every step of a given nested
sequence of DPPs on one probability space. -/
theorem nested_entry_ratio
    (Z : ℕ → Ω → Set α) (Q : ℕ → α → α → ℝ)
    (hZ : ∀ n, IsDPP μ (Z n) (Q n))
    (hmono : ∀ n ω, Z n ω ⊆ Z (n + 1) ω)
    (n : ℕ) (i : α) (hq : 0 < μ.real {ω | i ∉ Z n ω}) :
    μ.real {ω | i ∈ Z (n + 1) ω ∧ i ∉ Z n ω} /
        μ.real {ω | i ∉ Z n ω} =
      1 - μ.real {ω | i ∉ Z (n + 1) ω} / μ.real {ω | i ∉ Z n ω} :=
  (hZ n).entry_ratio (hZ (n + 1)) (hmono n) i hq

/-- The exact two-point inclusion law at distinct sites. -/
theorem IsDPP.two_point (h : IsDPP μ X K) {i j : α} (hij : i ≠ j) :
    μ.real {ω | i ∈ X ω ∧ j ∈ X ω} =
      K i i * K j j - K i j * K j i := by
  let e : Fin 2 ↪ α :=
    ⟨fun k => if k = 0 then i else j, by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all⟩
  have he0 : e 0 = i := rfl
  have he1 : e 1 = j := rfl
  have hevent : {ω | ∀ k : Fin 2, e k ∈ X ω} =
      {ω | i ∈ X ω ∧ j ∈ X ω} := by
    ext ω
    constructor
    · intro hh
      exact ⟨by simpa only [he0] using hh 0, by simpa only [he1] using hh 1⟩
    · rintro ⟨hi, hj⟩ k
      fin_cases k
      · change e (0 : Fin 2) ∈ X ω
        rw [he0]
        exact hi
      · change e (1 : Fin 2) ∈ X ω
        rw [he1]
        exact hj
  have hc := h.correlation 2 e
  rw [hevent, Matrix.det_fin_two] at hc
  simpa only [Matrix.of_apply, he0, he1] using hc

/-- The covariance of the two occupancy indicators is the signed kernel
product `-K(i,j)K(j,i)`. -/
theorem IsDPP.occupancy_covariance (h : IsDPP μ X K) {i j : α} (hij : i ≠ j) :
    μ.real {ω | i ∈ X ω ∧ j ∈ X ω} -
        μ.real {ω | i ∈ X ω} * μ.real {ω | j ∈ X ω} = - K i j * K j i := by
  rw [h.two_point hij, h.occupation i, h.occupation j]
  ring

/-- Symmetry makes the pair covariance nonpositive. This states pairwise
negative correlation, and does not claim the stronger negative-association
property for arbitrary increasing events. -/
theorem IsDPP.two_point_le_product (h : IsDPP μ X K) {i j : α}
    (hij : i ≠ j) (hsymm : K i j = K j i) :
    μ.real {ω | i ∈ X ω ∧ j ∈ X ω} ≤
      μ.real {ω | i ∈ X ω} * μ.real {ω | j ∈ X ω} := by
  rw [h.two_point hij, h.occupation i, h.occupation j, hsymm]
  nlinarith [sq_nonneg (K j i)]

end RiemannResearch.Probability.DPP
