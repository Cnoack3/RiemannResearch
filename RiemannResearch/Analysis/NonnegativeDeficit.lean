import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# Nonnegative deficit tests

Source: ArithmeticProjectionDPPDraft20260921.md (2026-09-21), Section 7.
This general order/measure layer uses extended nonnegative values, so an
unbounded deficit cannot acquire a spurious real-valued liminf of zero.
-/

noncomputable section
open Filter MeasureTheory
open scoped Topology ENNReal

namespace RiemannResearch.Analysis.NonnegativeDeficit

def CofinallySmall (d : ℕ → ℝ≥0∞) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∀ N : ℕ, ∃ M, N ≤ M ∧ d M < ε

theorem liminf_eq_zero_iff_cofinallySmall (d : ℕ → ℝ≥0∞) :
    Filter.liminf d atTop = 0 ↔ CofinallySmall d := by
  rw [Filter.liminf_eq_iSup_iInf_of_nat]
  constructor
  · intro h ε hε N
    have hN : (⨅ i, ⨅ (_ : i ≥ N), d i) = 0 := by
      apply le_antisymm _ bot_le
      calc
        _ ≤ ⨆ n, ⨅ i, ⨅ (_ : i ≥ n), d i := le_iSup _ N
        _ = 0 := h
    have hl : (⨅ i, ⨅ (_ : i ≥ N), d i) < ε := by rw [hN]; exact hε
    obtain ⟨M, hM⟩ := iInf_lt_iff.mp hl
    obtain ⟨hNM, hM⟩ := iInf_lt_iff.mp hM
    exact ⟨M, hNM, hM⟩
  · intro h
    apply le_antisymm _ bot_le
    apply iSup_le
    intro N
    by_contra hn
    have hp : 0 < ⨅ i, ⨅ (_ : i ≥ N), d i := lt_of_not_ge hn
    obtain ⟨M, hNM, hM⟩ := h _ hp N
    exact (not_lt_of_ge (iInf_le_of_le M (iInf_le_of_le hNM le_rfl))) hM

theorem liminf_pos_of_eventual_floor {d : ℕ → ℝ≥0∞} {c : ℝ≥0∞}
    (hc : 0 < c) (hfloor : ∀ᶠ M in atTop, c ≤ d M) :
    0 < Filter.liminf d atTop :=
  hc.trans_le (Filter.le_liminf_of_le (by isBoundedDefault) hfloor)

theorem not_cofinallySmall_of_eventual_floor {d : ℕ → ℝ≥0∞} {c : ℝ≥0∞}
    (hc : 0 < c) (hfloor : ∀ᶠ M in atTop, c ≤ d M) : ¬ CofinallySmall d := by
  intro h
  have hp := liminf_pos_of_eventual_floor hc hfloor
  rw [(liminf_eq_zero_iff_cofinallySmall d).mpr h] at hp
  exact (lt_irrefl _) hp

theorem integral_le_liminf_of_dominated_profile
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f : ℕ → α → ℝ≥0∞) (g : α → ℝ≥0∞) (d : ℕ → ℝ≥0∞)
    (hmeas : ∀ M, Measurable (f M))
    (hconv : ∀ x, Tendsto (fun M => f M x) atTop (𝓝 (g x)))
    (hdom : ∀ M, (∫⁻ x, f M x ∂μ) ≤ d M) :
    (∫⁻ x, g x ∂μ) ≤ Filter.liminf d atTop := by
  calc
    _ = ∫⁻ x, Filter.liminf (fun M => f M x) atTop ∂μ := by
      apply lintegral_congr
      intro x
      exact (hconv x).liminf_eq.symm
    _ ≤ Filter.liminf (fun M => ∫⁻ x, f M x ∂μ) atTop :=
      lintegral_liminf_le hmeas
    _ ≤ Filter.liminf d atTop :=
      Filter.liminf_le_liminf (Eventually.of_forall hdom)

end RiemannResearch.Analysis.NonnegativeDeficit
