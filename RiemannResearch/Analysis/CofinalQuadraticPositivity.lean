import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith

/-!
# Cofinal positivity with vanishing lower errors

Source: user-provided argument, `RH_Layer_Cake_Sublevel_Program_and_Next_Attack`
continuation, sections 25 and 29. These are general order/limit results.
They do not assert a Weil criterion, support exhaustion, spline density, or
an arithmetic lower bound. Those application obligations must be supplied.
-/

open Filter
open scoped Topology

namespace RiemannResearch.Analysis

/-- A fixed real value cannot stay below zero if its lower error tends to zero.
No sign assumption on the error or fixed energy is needed. -/
theorem nonneg_of_vanishing_lower_error {ι : Type*} {l : Filter ι} [l.NeBot]
    (q d : ℝ) (ε : ι → ℝ) (hε : Tendsto ε l (𝓝 0))
    (hbound : ∀ᶠ j in l, -(ε j) * d ≤ q) : 0 ≤ q := by
  have ht : Tendsto (fun j => -(ε j) * d) l (𝓝 0) := by
    simpa using hε.neg.mul_const d
  exact le_of_tendsto ht hbound

/-- Exhaustion is expressed at its actual point of use: each fixed test is
eventually in the tested domains. Uniform small-error lower bounds then
give positivity on every test. -/
theorem nonneg_of_cofinal_lower_error {T : Type*}
    (Q D : T → ℝ) (V : ℕ → Set T) (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 0))
    (hcover : ∀ f, ∀ᶠ j in atTop, f ∈ V j)
    (hbound : ∀ j f, f ∈ V j → -(ε j) * D f ≤ Q f) :
    ∀ f, 0 ≤ Q f := by
  intro f
  apply nonneg_of_vanishing_lower_error (Q f) (D f) ε hε
  filter_upwards [hcover f] with j hj
  exact hbound j f hj

/-- Locally consistent interior truncations need no operator-norm estimate:
they eventually agree with the full form on each fixed test. -/
theorem nonneg_of_eventually_consistent_lower_error {T : Type*}
    (Q D : T → ℝ) (Qj : ℕ → T → ℝ) (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 0))
    (hstable : ∀ f, ∀ᶠ j in atTop, Qj j f = Q f)
    (hbound : ∀ f, ∀ᶠ j in atTop, -(ε j) * D f ≤ Qj j f) :
    ∀ f, 0 ≤ Q f := by
  intro f
  apply nonneg_of_vanishing_lower_error (Q f) (D f) ε hε
  filter_upwards [hstable f, hbound f] with j hs hb
  rwa [hs] at hb

/-- Nested domains with a pointwise exhaustion provide eventual membership. -/
theorem eventually_mem_of_nested_exhaustion {T : Type*} (V : ℕ → Set T)
    (hmono : Monotone V) (hcover : ∀ f, ∃ j, f ∈ V j) (f : T) :
    ∀ᶠ j in atTop, f ∈ V j := by
  obtain ⟨j, hj⟩ := hcover f
  exact eventually_atTop.2 ⟨j, fun k hk => hmono hk hj⟩

/-- A lower bound in the stronger fixed energy is the correct conclusion
when both the interior estimate and the boundary error use that energy. -/
theorem lower_bound_of_relative_form_error (q qInterior d ε η : ℝ)
    (hInterior : -ε * d ≤ qInterior)
    (hError : |q - qInterior| ≤ η * d) :
    -(ε + η) * d ≤ q := by
  have := (abs_le.mp hError).1
  nlinarith

/-- Monotonicity plus arbitrarily low witnesses gives divergence, without
claiming that such witnesses exist for any actual RH matrix. -/
theorem antitone_tendsto_atBot_of_arbitrarily_low (a : ℕ → ℝ)
    (ha : Antitone a) (hlow : ∀ b : ℝ, ∃ j, a j ≤ b) :
    Tendsto a atTop atBot := by
  apply tendsto_atBot.2
  intro b
  obtain ⟨j, hj⟩ := hlow b
  exact eventually_atTop.2 ⟨j, fun k hk => (ha hk).trans hj⟩

end RiemannResearch.Analysis
