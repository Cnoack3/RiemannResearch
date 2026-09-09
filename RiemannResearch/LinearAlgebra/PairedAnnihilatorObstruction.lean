import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Two-channel obstructions from quantitatively paired annihilators

Source: user-provided `ParetoCovarianceRepairReport_Advanced_2026-09-08.md`,
Section 3, and its phase-centering audit.  This module proves the functional
analytic implication.  Construction of the compressed Mellin witnesses for
the actual two residue-seed modules is a separate, unresolved provider.

The parameter `δ` controls the difference of the two witnesses; their individual
operator norms are allowed to grow like `1 / δ`.  This growth is essential.
-/

namespace RiemannResearch.LinearAlgebra.PairedAnnihilatorObstruction
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Exact cancellation identity, before any norm estimate. -/
theorem pairing_identity (L R : E →L[ℝ] ℂ) (u f g : E)
    (hf : L f = 0) (hg : R g = 0) :
    L u = (L - R) g + L (u - (f + g)) := by
  simp only [ContinuousLinearMap.sub_apply, map_sub, map_add, hf, hg]
  abel

/-- A witness that annihilates the first channel measures the second channel
through the difference of witnesses and the complete residual. -/
theorem pairing_bound (L R : E →L[ℝ] ℂ) (u f g : E)
    (hf : L f = 0) (hg : R g = 0) :
    ‖L u‖ ≤ ‖L - R‖ * ‖g‖ + ‖L‖ * ‖u - (f + g)‖ := by
  rw [pairing_identity L R u f g hf hg]
  exact (norm_add_le _ _).trans
    (add_le_add ((L - R).le_opNorm g) (L.le_opNorm (u - (f + g))))

/-- Precisely quantified analytic input for the two-channel obstruction.
The vectors may lie in closed seed spaces; no finite-support assumption occurs.
This proposition is an assumption, not a construction of the Mellin witnesses. -/
structure PairedAnnihilatorEstimates (M N : Submodule ℝ E) (u : E)
    (C δ₀ : ℝ) : Prop where
  cost_pos : 0 < C
  radius_pos : 0 < δ₀
  witnesses : ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
    ∃ L R : E →L[ℝ] ℂ,
      (∀ f ∈ M, L f = 0) ∧ (∀ g ∈ N, R g = 0) ∧
      1 ≤ ‖L u‖ ∧ 1 ≤ ‖R u‖ ∧
      ‖L‖ ≤ C / δ ∧ ‖R‖ ≤ C / δ ∧ ‖L - R‖ ≤ δ

variable {M N : Submodule ℝ E} {u : E} {C δ₀ : ℝ}

/-- The exact two-channel representation is impossible under the paired-dual
provider, even though membership in the closure of the sum is not excluded. -/
theorem ne_add (h : PairedAnnihilatorEstimates M N u C δ₀)
    (f g : E) (hf : f ∈ M) (hg : g ∈ N) : u ≠ f + g := by
  intro heq
  let δ : ℝ := min δ₀ (1 / (2 * (‖g‖ + 1)))
  have hden : 0 < 2 * (‖g‖ + 1) := by positivity
  have hδ : 0 < δ := lt_min h.radius_pos (div_pos zero_lt_one hden)
  obtain ⟨L, R, hL, hR, hLu, _, _, _, hdiff⟩ :=
    h.witnesses δ hδ (min_le_left _ _)
  have hb := pairing_bound L R u f g (hL f hf) (hR g hg)
  have herr : u - (f + g) = 0 := sub_eq_zero.mpr heq
  rw [herr, norm_zero, mul_zero, add_zero] at hb
  have hm := mul_le_mul_of_nonneg_right hdiff (norm_nonneg g)
  have hsmall : δ * (2 * (‖g‖ + 1)) ≤ 1 :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  nlinarith

theorem no_exact_decomposition (h : PairedAnnihilatorEstimates M N u C δ₀) :
    ¬ ∃ f ∈ M, ∃ g ∈ N, u = f + g := by
  rintro ⟨f, hf, g, hg, heq⟩
  exact ne_add h f g hf hg heq

/-- Every sufficiently accurate joint approximation has both channel norms
at least `1 / (4*C*ε)`.  The residual is the full norm, with no truncation. -/
theorem reciprocal_error_lower_bound
    (h : PairedAnnihilatorEstimates M N u C δ₀)
    (f g : E) (hf : f ∈ M) (hg : g ∈ N)
    (ε : ℝ) (hε : 0 < ε) (hsmall : 2 * C * ε ≤ δ₀)
    (herr : ‖u - (f + g)‖ ≤ ε) :
    1 / (4 * C * ε) ≤ ‖f‖ ∧ 1 / (4 * C * ε) ≤ ‖g‖ := by
  have hC := h.cost_pos
  have hδ : 0 < 2 * C * ε := by positivity
  obtain ⟨L, R, hL, hR, hLu, hRu, hLn, hRn, hdiff⟩ :=
    h.witnesses (2 * C * ε) hδ hsmall
  have hfrac : C / (2 * C * ε) * ε = 1 / 2 := by
    field_simp [ne_of_gt hC, ne_of_gt hε]
  have hg₁ := pairing_bound L R u f g (hL f hf) (hR g hg)
  have hg₂ : ‖L - R‖ * ‖g‖ ≤ (2 * C * ε) * ‖g‖ :=
    mul_le_mul_of_nonneg_right hdiff (norm_nonneg g)
  have hg₃ : ‖L‖ * ‖u - (f + g)‖ ≤ C / (2 * C * ε) * ε :=
    mul_le_mul hLn herr (norm_nonneg _) (by positivity)
  have hfg : ‖R - L‖ ≤ 2 * C * ε := by
    simpa only [norm_sub_rev] using hdiff
  have hf₁ := pairing_bound R L u g f (hR g hg) (hL f hf)
  rw [add_comm g f] at hf₁
  have hf₂ : ‖R - L‖ * ‖f‖ ≤ (2 * C * ε) * ‖f‖ :=
    mul_le_mul_of_nonneg_right hfg (norm_nonneg f)
  have hf₃ : ‖R‖ * ‖u - (f + g)‖ ≤ C / (2 * C * ε) * ε :=
    mul_le_mul hRn herr (norm_nonneg _) (by positivity)
  have hden : 0 < 4 * C * ε := by positivity
  constructor
  · apply (div_le_iff₀ hden).mpr
    nlinarith
  · apply (div_le_iff₀ hden).mpr
    nlinarith

end
end RiemannResearch.LinearAlgebra.PairedAnnihilatorObstruction
