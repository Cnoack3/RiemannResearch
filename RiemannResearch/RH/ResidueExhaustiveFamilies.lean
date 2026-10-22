import RiemannResearch.RH.IntegerDPPClosure
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Explicit exhaustive legal residue families

Source: user request of 2026-09-21 for exhaustive legal families approaching I.
The convergence proof uses the existing exhaustive projection theorem.
The identity on the ambient space remains equivalent to legal density;
no density assumption or RH converse is silently discharged.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.ExhaustiveFamilies
open RiemannResearch.Analysis.ExhaustiveWalk

/-- Project onto g_2,...,g_(c(n)+1), with the complete Pareto norm. -/
def cutoffProjection (c : ℕ → ℕ) (n : ℕ) : ThresholdHilbert →L[ℝ] ThresholdHilbert :=
  (finiteSpace (c n)).starProjection

def ordinaryCutoff (n : ℕ) : ℕ := n
def dyadicCutoff (n : ℕ) : ℕ := 2 ^ n
def factorialCutoff (n : ℕ) : ℕ := (n + 1).factorial

theorem ordinaryCutoff_ge (n : ℕ) : n ≤ ordinaryCutoff n := le_rfl

theorem dyadicCutoff_ge (n : ℕ) : n ≤ dyadicCutoff n := by
  exact (Nat.lt_two_pow_self (n := n)).le

theorem factorialCutoff_ge (n : ℕ) : n ≤ factorialCutoff n := by
  exact (Nat.le_succ n).trans (Nat.self_le_factorial (n + 1))

/-- A simple explicit sufficient condition for an exhaustive schedule. -/
theorem cutoff_tendsto (c : ℕ → ℕ) (hc : ∀ n, n ≤ c n) :
    Tendsto c atTop atTop :=
  tendsto_atTop_mono hc tendsto_id

/-- Every residue generator occurs at a finite stage of these schedules. -/
theorem generator_mem (c : ℕ → ℕ) (hc : ∀ n, n ≤ c n) (i : ℕ) :
    residueAtom i ∈ finiteSpace (c (i + 1)) := by
  apply Submodule.subset_span
  exact ⟨⟨i, lt_of_lt_of_le (Nat.lt_succ_self i) (hc (i + 1))⟩, rfl⟩

/-- Exhaustion concerns the entire algebraic legal span, not only a head. -/
theorem iSup_finiteSpace (c : ℕ → ℕ) (hc : ∀ n, n ≤ c n) :
    (⨆ n, finiteSpace (c n)) = Submodule.span ℝ (Set.range residueAtom) := by
  apply le_antisymm
  · exact iSup_le (fun n => walkSpan_le residueAtom id (c n))
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact (le_iSup (fun n => finiteSpace (c n)) (i + 1)) (generator_mem c hc i)

theorem cutoffProjection_legal (c : ℕ → ℕ) (n : ℕ) (f : ThresholdHilbert) :
    cutoffProjection c n f ∈ Submodule.span ℝ (Set.range residueAtom) :=
  walkSpan_le residueAtom id (c n) ((finiteSpace (c n)).starProjection_apply_mem f)

theorem cutoffProjection_tendsto (c : ℕ → ℕ) (hc : ∀ n, n ≤ c n)
    (f : ThresholdHilbert) :
    Tendsto (fun n => cutoffProjection c n f) atTop (𝓝 (closedSpace.starProjection f)) :=
  (walkProjection_tendsto residueAtom id Function.surjective_id f).comp
    (cutoff_tendsto c hc)

theorem ordinary_tendsto (f : ThresholdHilbert) :
    Tendsto (fun n => cutoffProjection ordinaryCutoff n f) atTop
      (𝓝 (closedSpace.starProjection f)) :=
  cutoffProjection_tendsto ordinaryCutoff ordinaryCutoff_ge f

theorem dyadic_tendsto (f : ThresholdHilbert) :
    Tendsto (fun n => cutoffProjection dyadicCutoff n f) atTop
      (𝓝 (closedSpace.starProjection f)) :=
  cutoffProjection_tendsto dyadicCutoff dyadicCutoff_ge f

theorem factorial_tendsto (f : ThresholdHilbert) :
    Tendsto (fun n => cutoffProjection factorialCutoff n f) atTop
      (𝓝 (closedSpace.starProjection f)) :=
  cutoffProjection_tendsto factorialCutoff factorialCutoff_ge f

/-- Unconditional identity approximation on the closed legal subspace. -/
theorem tendsto_self_of_mem (c : ℕ → ℕ) (hc : ∀ n, n ≤ c n)
    (f : ThresholdHilbert) (hf : f ∈ closedSpace) :
    Tendsto (fun n => cutoffProjection c n f) atTop (𝓝 f) := by
  simpa only [Submodule.starProjection_eq_self_iff.mpr hf] using
    cutoffProjection_tendsto c hc f

/-- Ambient identity approximation is precisely the missing density condition. -/
theorem tendsto_identity_iff_top (c : ℕ → ℕ) (hc : ∀ n, n ≤ c n) :
    (∀ f : ThresholdHilbert,
      Tendsto (fun n => cutoffProjection c n f) atTop (𝓝 f)) ↔ closedSpace = ⊤ := by
  constructor
  · intro h
    apply top_unique
    intro f _
    have he : closedSpace.starProjection f = f :=
      tendsto_nhds_unique (cutoffProjection_tendsto c hc f) (h f)
    exact Submodule.starProjection_eq_self_iff.mp he
  · intro h f
    exact tendsto_self_of_mem c hc f (by rw [h]; trivial)

/-- For this dictionary, approximating just the constant is already enough. -/
theorem tendsto_identity_iff_one (c : ℕ → ℕ) (hc : ∀ n, n ≤ c n) :
    (∀ f : ThresholdHilbert,
      Tendsto (fun n => cutoffProjection c n f) atTop (𝓝 f)) ↔
    Tendsto (fun n => cutoffProjection c n hilbertOne) atTop (𝓝 hilbertOne) := by
  constructor
  · exact fun h => h hilbertOne
  · intro h
    apply (tendsto_identity_iff_top c hc).mpr
    apply closedSpace_eq_top_iff_one_mem.mpr
    exact Submodule.starProjection_eq_self_iff.mp
      (tendsto_nhds_unique (cutoffProjection_tendsto c hc hilbertOne) h)

/-- Exact error split, retaining all tail energy. -/
theorem error_eq_defect_add (c : ℕ → ℕ) (n : ℕ) (f : ThresholdHilbert) :
    ‖f - cutoffProjection c n f‖ ^ 2 =
      ‖f - closedSpace.starProjection f‖ ^ 2 +
      ‖closedSpace.starProjection f - cutoffProjection c n f‖ ^ 2 :=
  walkError_eq_limitingError_add residueAtom id f (c n)

/-- A conditional RH reduction, not a proof of its convergence premise. -/
theorem riemannHypothesis_of_identity (c : ℕ → ℕ) (hc : ∀ n, n ≤ c n)
    (h : ∀ f : ThresholdHilbert,
      Tendsto (fun n => cutoffProjection c n f) atTop (𝓝 f)) :
    RiemannHypothesis := by
  apply IntegerDPP.riemannHypothesis_of_vacancy_tendsto_zero
  apply IntegerDPP.vacancy_tendsto_zero_iff_top.mpr
  exact (tendsto_identity_iff_top c hc).mp h

/-- Under not-RH, every one of these schedules retains the same positive defect. -/
theorem not_identity_of_not_RH (c : ℕ → ℕ) (hc : ∀ n, n ≤ c n)
    (h : ¬ RiemannHypothesis) :
    ¬ (∀ f : ThresholdHilbert,
      Tendsto (fun n => cutoffProjection c n f) atTop (𝓝 f)) :=
  fun hid => h (riemannHypothesis_of_identity c hc hid)

theorem firstPoint_error_ge (c : ℕ → ℕ) (n : ℕ) :
    IntegerDPP.limitingVacancy ≤
      2 * ‖paretoPointHilbert 0 - cutoffProjection c n (paretoPointHilbert 0)‖ ^ 2 :=
  IntegerDPP.limitingVacancy_le_vacancy (c n)

/-- Adjacent differences give a distinct legal generator list. -/
def differenceAtom : ℕ → ThresholdHilbert
  | 0 => residueAtom 0
  | n + 1 => residueAtom (n + 1) - residueAtom n

theorem residueAtom_eq_difference_sum (n : ℕ) :
    residueAtom n = ∑ j ∈ Finset.range (n + 1), differenceAtom j := by
  induction n with
  | zero => simp [differenceAtom]
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih, differenceAtom]
    abel

theorem differenceAtom_mem (i : ℕ) : differenceAtom i ∈ finiteSpace (i + 1) := by
  cases i with
  | zero => exact generator_mem ordinaryCutoff ordinaryCutoff_ge 0
  | succ i =>
    apply Submodule.sub_mem
    · exact generator_mem ordinaryCutoff ordinaryCutoff_ge (i + 1)
    · exact walkSpan_mono residueAtom id (by omega : i + 1 ≤ i + 1 + 1)
        (generator_mem ordinaryCutoff ordinaryCutoff_ge i)

/-- The adjacent-difference family has exactly the same finite spans. -/
theorem difference_span_eq (n : ℕ) :
    walkSpan differenceAtom id n = finiteSpace n := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact walkSpan_mono residueAtom id (Nat.succ_le_of_lt i.isLt) (differenceAtom_mem i)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change residueAtom (i : ℕ) ∈ walkSpan differenceAtom id n
    rw [residueAtom_eq_difference_sum]
    apply Submodule.sum_mem
    intro j hj
    apply Submodule.subset_span
    exact ⟨⟨j, lt_of_lt_of_le (Finset.mem_range.mp hj)
      (Nat.succ_le_of_lt i.isLt)⟩, rfl⟩

theorem difference_tendsto (f : ThresholdHilbert) :
    Tendsto (fun n => (walkSpan differenceAtom id n).starProjection f) atTop
      (𝓝 (closedSpace.starProjection f)) := by
  simpa only [difference_span_eq] using
    walkProjection_tendsto residueAtom id Function.surjective_id f


end RiemannResearch.RH.Pareto.CoefficientStabilization.ExhaustiveFamilies
