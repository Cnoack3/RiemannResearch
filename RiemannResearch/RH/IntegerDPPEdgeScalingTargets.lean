import RiemannResearch.RH.IntegerDPPExistence

/-!
# Actual upper-edge CDF and open Airy scaling target

Source: user-provided Fredholm/KPZ discussion, 2026-09-20. The CDF below
uses the actual arithmetic integer DPP law. The benchmark is an explicitly
supplied real CDF; there is no invented implementation of the Airy Fredholm
determinant or GUE Tracy--Widom distribution.

`UpperEdgeCDFScalingTarget` is an open research proposition. When a separately
constructed Tracy--Widom CDF is supplied, it expresses precisely the chat's
one-point Airy endpoint. Full KPZ convergence additionally requires specified
growth dynamics and joint space-time distributions; it is not asserted here.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto.IntegerDPP

/-- Every occupied physical integer k+1 lies below the real threshold. -/
def upperEdgeEvent (a : ℝ) : Set (ℕ → Bool) :=
  {ω | ∀ k, ω k = true → ((k + 1 : ℕ) : ℝ) ≤ a}

theorem upperEdgeEvent_measurable (a : ℝ) : MeasurableSet (upperEdgeEvent a) := by
  have he : upperEdgeEvent a =
      ⋂ k : ℕ, {ω : ℕ → Bool | ω k = true → ((k + 1 : ℕ) : ℝ) ≤ a} := by
    ext ω
    simp [upperEdgeEvent]
  rw [he]
  apply MeasurableSet.iInter
  intro k
  by_cases hk : ((k + 1 : ℕ) : ℝ) ≤ a
  · have hset : {ω : ℕ → Bool | ω k = true → ((k + 1 : ℕ) : ℝ) ≤ a} =
        Set.univ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact fun _ => hk
    rw [hset]
    exact MeasurableSet.univ
  · have hm : MeasurableSet {ω : ℕ → Bool | ω k = true} :=
      (measurableSet_singleton true).preimage (measurable_pi_apply k)
    have hset : {ω : ℕ → Bool | ω k = true → ((k + 1 : ℕ) : ℝ) ≤ a} =
        {ω : ℕ → Bool | ω k = true}ᶜ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff]
      constructor
      · intro h hω
        exact hk (h hω)
      · intro h hω
        exact False.elim (h hω)
    rw [hset]
    exact hm.compl

def upperEdgeCDF (n : ℕ) (a : ℝ) : ℝ :=
  (integerLaw n).real (upperEdgeEvent a)

theorem upperEdgeCDF_monotone (n : ℕ) : Monotone (upperEdgeCDF n) := by
  intro a b hab
  apply measureReal_mono ?_ (measure_ne_top (integerLaw n) (upperEdgeEvent b))
  intro ω hω k hk
  exact (hω k hk).trans hab

/-- Candidate rank, center, and edge-width sequences. -/
structure UpperEdgeScaling where
  rank : ℕ → ℕ
  center : ℕ → ℝ
  width : ℕ → ℝ

/-- Open distributional limit for the actual arithmetic maximum. Continuity
points of the supplied benchmark CDF are the usual weak-convergence test.
Supplying that function does not assert that it is Tracy--Widom; that
identification is a separate obligation. -/
def UpperEdgeCDFScalingTarget (benchmarkCDF : ℝ → ℝ) : Prop :=
  ∃ p : UpperEdgeScaling,
    Tendsto p.rank atTop atTop ∧ (∀ m, 0 < p.width m) ∧
      ∀ s : ℝ, ContinuousAt benchmarkCDF s →
        Tendsto (fun m => upperEdgeCDF (p.rank m) (p.center m + p.width m * s))
          atTop (𝓝 (benchmarkCDF s))

end RiemannResearch.RH.Pareto.IntegerDPP
