import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The continuity obstruction for logarithmic integer step functions

Source: user-provided Hilbert--Pólya discussion, September 20, 2026.
This module formalizes the jump argument, including the fact that changing a
function on a null set cannot remove its jumps. It does not assume a Fourier
transform or a Sobolev embedding theorem. `FourierFirstMomentContinuity` and
`MellinLogFrequencyDomain` separately supply and assemble the analytic bridge
to the domain of frequency multiplication.

The integer sequence uses the physical indexing convention: entry `1` is
the first site, and entry `0` is ignored by the logarithmic step function.
-/

noncomputable section

open Set MeasureTheory
open scoped Topology

namespace RiemannResearch.Analysis.MellinLogStep

section ContinuousCells

variable {E : Type*} [TopologicalSpace E] [T2Space E] [Zero E]

/-- Continuity propagates the zero value across all adjacent constant cells.
No exhaustion hypothesis on the cell endpoints is needed. -/
theorem coefficients_zero_of_continuous_cells
    (a : ℕ → ℝ) (ha : ∀ n, a n < a (n + 1))
    (c : ℕ → E) (h : ℝ → E) (hh : Continuous h)
    (hleft : EqOn h (fun _ => 0) (Iio (a 0)))
    (hcells : ∀ n, EqOn h (fun _ => c n) (Ioo (a n) (a (n + 1)))) :
    ∀ n, c n = 0 := by
  have hclosed (n : ℕ) :
      EqOn h (fun _ => c n) (Icc (a n) (a (n + 1))) := by
    have he := (hcells n).closure hh continuous_const
    simpa only [closure_Ioo (ne_of_lt (ha n))] using he
  have hstart : h (a 0) = 0 := by
    have hm : a 0 ∈ closure (Iio (a 0)) := by
      rw [closure_Iio]
      exact (le_refl (a 0) : a 0 ≤ a 0)
    exact (hleft.closure hh continuous_const) hm
  intro n
  induction n with
  | zero =>
      exact (hclosed 0 ⟨le_rfl, (ha 0).le⟩).symm.trans hstart
  | succ n ih =>
      have hprev : h (a (n + 1)) = c n :=
        hclosed n ⟨(ha n).le, le_rfl⟩
      have hnext : h (a (n + 1)) = c (n + 1) :=
        hclosed (n + 1) ⟨le_rfl, (ha (n + 1)).le⟩
      exact hnext.symm.trans (hprev.trans ih)

omit [Zero E] in
/-- An a.e. equality to a cellwise constant function determines a continuous
representative at every interior point of the cell. -/
theorem eqOn_const_of_continuous_ae_eq
    {h k : ℝ → E} (hh : Continuous h) (heq : h =ᵐ[volume] k)
    {U : Set ℝ} (hU : IsOpen U) {c : E}
    (hcell : EqOn k (fun _ => c) U) : EqOn h (fun _ => c) U := by
  apply Measure.eqOn_open_of_ae_eq (μ := volume) _ hU
    hh.continuousOn continuous_const.continuousOn
  filter_upwards [ae_restrict_of_ae heq, ae_restrict_mem hU.measurableSet]
    with x hx hxU
  exact hx.trans (hcell hxU)

end ContinuousCells

section LogarithmicCells

variable {E : Type*} [Zero E]

/-- The logarithmic lift of an integer step function, extended by zero to
negative logarithmic coordinates. -/
def logarithmicStep (f : ℕ → E) (u : ℝ) : E :=
  if 0 ≤ u then f ⌊Real.exp u⌋₊ else 0

@[simp] theorem logarithmicStep_zero : logarithmicStep (0 : ℕ → E) = 0 := by
  funext u
  simp [logarithmicStep]

/-- The left boundary of the cell for physical integer `n + 1`. -/
def logBoundary (n : ℕ) : ℝ := Real.log ((n + 1 : ℕ) : ℝ)

@[simp] theorem logBoundary_zero : logBoundary 0 = 0 := by
  simp [logBoundary]

theorem logBoundary_lt_succ (n : ℕ) : logBoundary n < logBoundary (n + 1) := by
  apply Real.log_lt_log
  · positivity
  · exact Nat.cast_lt.mpr (Nat.lt_succ_self (n + 1))

theorem logBoundary_nonneg (n : ℕ) : 0 ≤ logBoundary n := by
  apply Real.log_nonneg
  rw [Nat.cast_add, Nat.cast_one]
  exact le_add_of_nonneg_left (Nat.cast_nonneg n)

theorem logarithmicStep_eq_zero_of_neg (f : ℕ → E) {u : ℝ} (hu : u < 0) :
    logarithmicStep f u = 0 := by
  simp [logarithmicStep, not_le_of_gt hu]

theorem logarithmicStep_eq_on_cell (f : ℕ → E) (n : ℕ) :
    EqOn (logarithmicStep f) (fun _ => f (n + 1))
      (Ioo (logBoundary n) (logBoundary (n + 1))) := by
  intro u hu
  have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hpos' : (0 : ℝ) < ((n + 1 + 1 : ℕ) : ℝ) := by positivity
  have hlo : ((n + 1 : ℕ) : ℝ) ≤ Real.exp u := by
    have he := Real.exp_le_exp.mpr hu.1.le
    simpa only [logBoundary, Real.exp_log hpos] using he
  have hhi : Real.exp u < ((n + 1 : ℕ) : ℝ) + 1 := by
    have he := Real.exp_lt_exp.mpr hu.2
    change Real.exp u < Real.exp (Real.log ((n + 1 + 1 : ℕ) : ℝ)) at he
    rw [Real.exp_log hpos'] at he
    simpa only [Nat.cast_add, Nat.cast_one] using he
  have hfloor : ⌊Real.exp u⌋₊ = n + 1 :=
    Nat.floor_eq_on_Ico (n + 1) (Real.exp u) ⟨hlo, hhi⟩
  have hu0 : 0 ≤ u := (logBoundary_nonneg n).trans hu.1.le
  simp [logarithmicStep, hu0, hfloor]

end LogarithmicCells

section ContinuousRepresentatives

variable {E : Type*} [TopologicalSpace E] [T2Space E] [Zero E]

/-- A logarithmic step function can have a continuous representative only
when all its physical integer values vanish.  A null-set change at the jump
points does not evade the conclusion. -/
theorem positive_values_zero_of_continuous_ae_eq_step
    (f : ℕ → E) (h : ℝ → E) (hh : Continuous h)
    (heq : h =ᵐ[volume] logarithmicStep f) : ∀ n, f (n + 1) = 0 := by
  apply coefficients_zero_of_continuous_cells logBoundary logBoundary_lt_succ
    (fun n => f (n + 1)) h hh
  · apply eqOn_const_of_continuous_ae_eq hh heq isOpen_Iio
    intro u hu
    exact logarithmicStep_eq_zero_of_neg f (by simpa using hu)
  · intro n
    exact eqOn_const_of_continuous_ae_eq hh heq isOpen_Ioo
      (logarithmicStep_eq_on_cell f n)

end ContinuousRepresentatives

section WeightedProfile

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The inverse-Fourier profile appearing in the critical-line Mellin
realization of the Pareto-weighted sequence space. -/
def mellinLogProfile (f : ℕ → E) (u : ℝ) : E :=
  Real.exp (-u / 2) • logarithmicStep f u

@[simp] theorem mellinLogProfile_zero : mellinLogProfile (0 : ℕ → E) = 0 := by
  funext u
  simp [mellinLogProfile]

theorem deweight_mellinLogProfile (f : ℕ → E) (u : ℝ) :
    Real.exp (u / 2) • mellinLogProfile f u = logarithmicStep f u := by
  rw [mellinLogProfile, smul_smul, ← Real.exp_add]
  rw [show u / 2 + -u / 2 = 0 by ring, Real.exp_zero, one_smul]

/-- The exponential envelope cannot remove any jump, even after a null-set
change. This is the concrete obstruction used by the Hilbert--Pólya domain
argument; Fourier--Sobolev regularity is a separate bridge. -/
theorem positive_values_zero_of_continuous_ae_eq_profile
    (f : ℕ → E) (h : ℝ → E) (hh : Continuous h)
    (heq : h =ᵐ[volume] mellinLogProfile f) : ∀ n, f (n + 1) = 0 := by
  let q : ℝ → E := fun u => Real.exp (u / 2) • h u
  have hq : Continuous q :=
    (Real.continuous_exp.comp (continuous_id.div_const 2)).smul hh
  have heqq : q =ᵐ[volume] logarithmicStep f := by
    filter_upwards [heq] with u hu
    dsimp only [q]
    rw [hu, deweight_mellinLogProfile]
  exact positive_values_zero_of_continuous_ae_eq_step f q hq heqq

theorem eq_zero_of_continuous_ae_eq_profile
    (f : ℕ → E) (hf0 : f 0 = 0) (h : ℝ → E) (hh : Continuous h)
    (heq : h =ᵐ[volume] mellinLogProfile f) : f = 0 := by
  funext n
  cases n with
  | zero => exact hf0
  | succ n => exact positive_values_zero_of_continuous_ae_eq_profile f h hh heq n

theorem exists_continuous_ae_eq_profile_iff
    (f : ℕ → E) (hf0 : f 0 = 0) :
    (∃ h : ℝ → E, Continuous h ∧ h =ᵐ[volume] mellinLogProfile f) ↔ f = 0 := by
  constructor
  · rintro ⟨h, hh, heq⟩
    exact eq_zero_of_continuous_ae_eq_profile f hf0 h hh heq
  · intro hf
    subst f
    refine ⟨fun _ => 0, continuous_const, ?_⟩
    simp only [mellinLogProfile_zero]
    exact Filter.EventuallyEq.rfl

theorem continuous_profile_iff (f : ℕ → E) (hf0 : f 0 = 0) :
    Continuous (mellinLogProfile f) ↔ f = 0 := by
  constructor
  · intro hh
    exact eq_zero_of_continuous_ae_eq_profile f hf0 (mellinLogProfile f) hh
      Filter.EventuallyEq.rfl
  · intro hf
    subst f
    rw [mellinLogProfile_zero]
    exact continuous_const

end WeightedProfile

end RiemannResearch.Analysis.MellinLogStep
