import RiemannResearch.Analysis.OrdinateWindowVariance
import RiemannResearch.Analysis.ActualZeroOrdinate

/-!
# Exact count-window variance for actual zero occurrences

This assembly uses the actual zeta-zero multiplicity-copy type. No simplicity
or RH hypothesis is used. The geometric premise `hlow` states that the window
is below every included ordinate; it is retained explicitly. The mean premise
is the exact normalization `N(T) * h = T * lam`.

Source: the elementary count-window argument in the user's ordinate
pair-correlation program, 2026-10-11. Analytic limiting providers are separate.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory Zeta23

namespace RiemannResearch.Analysis.ActualZeroWindowVariance

open ActualZeroOrdinate OrdinateWindowVariance

def actualWindowCount (T h t : ℝ) : ℝ :=
  windowCount (Finset.univ : Finset (Copies T)) (fun c => c.1.1.im) T h t

def actualCenteredCount (T h lam t : ℝ) : ℝ :=
  centeredCount (Finset.univ : Finset (Copies T)) (fun c => c.1.1.im) T h lam t

def actualPhysicalTriangleEnergy (T h : ℝ) : ℝ :=
  (∑ i : Copies T, ∑ j : Copies T,
    max (h - |i.1.1.im - j.1.1.im|) 0) / T

lemma actual_window_support (T h : ℝ) (hlow : ∀ c : Copies T, h ≤ c.1.1.im) :
    ∀ c ∈ (Finset.univ : Finset (Copies T)), h ≤ c.1.1.im ∧ c.1.1.im ≤ T := by
  intro c _
  exact ⟨hlow c, (mem_cutoff.mp c.1.2).2.2⟩

theorem integral_actualWindowCount (T h : ℝ) (hh : 0 ≤ h)
    (hlow : ∀ c : Copies T, h ≤ c.1.1.im) :
    (∫ t : ℝ, actualWindowCount T h t) = (Ncount 0 T : ℝ) * h := by
  have hc := integral_windowCount_of_supported
    (Finset.univ : Finset (Copies T)) (fun c => c.1.1.im) T h hh
    (actual_window_support T h hlow)
  simpa only [actualWindowCount, Finset.card_univ, card_copies] using hc

theorem integral_actualWindowCount_sq (T h : ℝ)
    (hlow : ∀ c : Copies T, h ≤ c.1.1.im) :
    (∫ t : ℝ, actualWindowCount T h t ^ 2) =
      ∑ i : Copies T, ∑ j : Copies T, max (h - |i.1.1.im - j.1.1.im|) 0 := by
  exact integral_windowCount_sq_of_supported
    (Finset.univ : Finset (Copies T)) (fun c => c.1.1.im) T h
    (actual_window_support T h hlow)

/-- Actual, multiplicity-preserving exact triangle/count-variance identity. -/
theorem actual_triangle_eq_mean_sq_add_variance (T h lam : ℝ)
    (hT : 0 < T) (hh : 0 ≤ h) (hlow : ∀ c : Copies T, h ≤ c.1.1.im)
    (hmean : (Ncount 0 T : ℝ) * h = T * lam) :
    actualPhysicalTriangleEnergy T h =
      lam ^ 2 + (∫ t : ℝ, actualCenteredCount T h lam t ^ 2) / T := by
  apply triangle_eq_mean_sq_add_variance
    (Finset.univ : Finset (Copies T)) (fun c => c.1.1.im) T h lam hT hh
    (actual_window_support T h hlow)
  simpa only [Finset.card_univ, card_copies] using hmean

end RiemannResearch.Analysis.ActualZeroWindowVariance
