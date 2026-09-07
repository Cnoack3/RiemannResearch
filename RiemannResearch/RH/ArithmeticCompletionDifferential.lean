import RiemannResearch.RH.ArithmeticReturnConvolution
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# The actual differential completion and the remote-tail support theorem

Source: user-provided argument, Theorem 9.1.  This module applies the actual
operator D²−1/4 to the actual nested arithmetic return.  Its support theorem
is derived from equality on a neighborhood, including both derivatives.
-/

open scoped Topology

namespace RiemannResearch.RH

/-- The concrete differential operator D²−1/4. -/
noncomputable def poleCancellationOperator (u : ℝ → ℂ) : ℝ → ℂ :=
  fun y => deriv (deriv u) y - (1 / 4 : ℝ) • u y

theorem poleCancellationOperator_contDiff {u : ℝ → ℂ}
    (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (poleCancellationOperator u) := by
  have hd2 : ContDiff ℝ (↑(⊤ : ℕ∞)) (deriv (deriv u)) := by
    simpa only [Function.iterate_succ_apply, Function.iterate_zero_apply] using
      ContDiff.iterate_deriv 2 hu
  exact hd2.sub ((contDiff_const : ContDiff ℝ (↑(⊤ : ℕ∞))
    (fun _ : ℝ => (1 / 4 : ℝ))).smul hu)

/-- An equality on a neighborhood is preserved by D²−1/4. -/
theorem poleCancellationOperator_eq_of_eventuallyEq {u v : ℝ → ℂ} {y : ℝ}
    (h : u =ᶠ[𝓝 y] v) : poleCancellationOperator u y = poleCancellationOperator v y := by
  have h0 : u y = v y := mem_of_mem_nhds (s := {x : ℝ | u x = v x}) h
  simp only [poleCancellationOperator, h.deriv.deriv_eq, h0]

/-- The completed test G_M from equation (9.3). -/
noncomputable def nymanCompletedTest (n M : ℕ) (hn : 2 ≤ n)
    (v : ℝ → ℂ) : ℝ → ℂ :=
  poleCancellationOperator (nymanFullReturn n (nymanInversePotential n M hn v))

/-- The actual differential tail G_M−Lv. -/
noncomputable def nymanCompletionTail (n M : ℕ) (hn : 2 ≤ n)
    (v : ℝ → ℂ) : ℝ → ℂ :=
  nymanCompletedTest n M hn v - poleCancellationOperator v

theorem nymanCompletionTail_zero_below (n M : ℕ) (hn : 2 ≤ n)
    {v : ℝ → ℂ} {a y : ℝ} (hv : ∀ x < a, v x = 0)
    (hy : y < a + Real.log (M + 1 : ℕ)) :
    nymanCompletionTail n M hn v y = 0 := by
  have hgap := nymanFullReturn_inversePotential_tsupport n M hn hv
  have heq : nymanFullReturn n (nymanInversePotential n M hn v) =ᶠ[𝓝 y] v := by
    filter_upwards [Iio_mem_nhds hy] with x hx
    apply sub_eq_zero.mp
    by_contra hne
    have hs : x ∈ tsupport (nymanFullReturn n (nymanInversePotential n M hn v) - v) :=
      subset_closure hne
    have hle : a + Real.log (M + 1 : ℕ) ≤ x := hgap hs
    have hxlt : x < a + Real.log (M + 1 : ℕ) := hx
    exact (not_le_of_gt hxlt) hle
  exact sub_eq_zero.mpr (poleCancellationOperator_eq_of_eventuallyEq heq)

/-- The complete physical support statement of equation (9.4), including L.
No smoothness assumption is needed for this locality claim itself. -/
theorem nymanCompletionTail_tsupport (n M : ℕ) (hn : 2 ≤ n)
    {v : ℝ → ℂ} {a : ℝ} (hv : ∀ x < a, v x = 0) :
    tsupport (nymanCompletionTail n M hn v) ⊆
      Set.Ici (a + Real.log (M + 1 : ℕ)) := by
  apply closure_minimal _ isClosed_Ici
  intro y hy
  by_contra hnot
  exact hy (nymanCompletionTail_zero_below n M hn hv
    (by simpa only [Set.mem_Ici, not_le] using hnot))

theorem nymanCompletedTest_contDiff (n M : ℕ) (hn : 2 ≤ n)
    {v : ℝ → ℂ} {a : ℝ} (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (ha : ∀ x < a, v x = 0) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (nymanCompletedTest n M hn v) := by
  apply poleCancellationOperator_contDiff
  apply arithmeticReturn_contDiff _ (nymanInversePotential_contDiff n M hn hv)
  intro x hx
  rw [nymanInversePotential_eq_return]
  exact arithmeticReturn_zero_below _ ha hx

theorem nymanCompletionTail_contDiff (n M : ℕ) (hn : 2 ≤ n)
    {v : ℝ → ℂ} {a : ℝ} (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (ha : ∀ x < a, v x = 0) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (nymanCompletionTail n M hn v) :=
  (nymanCompletedTest_contDiff n M hn hv ha).sub (poleCancellationOperator_contDiff hv)

end RiemannResearch.RH
