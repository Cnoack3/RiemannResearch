import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith

/-!
# Finite-coordinate decoding with adversarial corruptions and erasures

Source: *Modular Phase Reconstruction of Zeta Zeros from Pole Lattices*,
Drive file 1opJNKzINIeBMDA_k6mr1jEtfW26_-2Cj, research agenda on noisy
finite-prime reconstruction. This strengthens the all-coordinate nearest
neighbor condition in PhaseDecoding: distinct candidates need separation
in more than the total two error budgets. Coordinates can be arbitrary
pseudo-metric spaces, so the theorem applies directly to circle phases.

This deterministic result requires the stated finite-code separation.
It does not assert a separation rate for actual zeta ordinates or permit
reconstruction without phase data.
-/

noncomputable section
namespace RiemannResearch.Analysis.FiniteCoordinateDecoding

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [PseudoMetricSpace E]

/-- Coordinates whose discrepancy exceeds the tolerance. -/
def bad (ε : ℝ) (u v : ι → E) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => ε < dist (u i) (v i))

theorem bad_triangle_subset (ε δ : ℝ) (u v z : ι → E) :
    bad (ε + δ) u v ⊆ bad ε u z ∪ bad δ v z := by
  classical
  intro i hi
  have hi' : ε + δ < dist (u i) (v i) := by simpa [bad] using hi
  simp only [bad, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hx : ε < dist (u i) (z i)
  · exact Or.inl hx
  · by_cases hy : δ < dist (v i) (z i)
    · exact Or.inr hy
    · have htri := dist_triangle (u i) (z i) (v i)
      rw [dist_comm (z i) (v i)] at htri
      have hx' := le_of_not_gt hx
      have hy' := le_of_not_gt hy
      exfalso
      linarith

/-- Any two explanations of one observation have at most the combined number
of far-apart coordinates. No probabilistic noise model is used. -/
theorem separation_card_le (ε δ : ℝ) (u v z : ι → E)
    (r s : ℕ) (hu : (bad ε u z).card ≤ r) (hv : (bad δ v z).card ≤ s) :
    (bad (ε + δ) u v).card ≤ r + s := by
  classical
  calc
    _ ≤ (bad ε u z ∪ bad δ v z).card :=
      Finset.card_le_card (bad_triangle_subset ε δ u v z)
    _ ≤ (bad ε u z).card + (bad δ v z).card := Finset.card_union_le _ _
    _ ≤ r + s := Nat.add_le_add hu hv

/-- Unequal tolerances and unequal corruption budgets are allowed. -/
theorem unique_of_error_budgets {X : Type*} (code : X → ι → E)
    (ε δ : ℝ) (r s : ℕ)
    (hsep : ∀ x y, x ≠ y → r + s < (bad (ε + δ) (code x) (code y)).card)
    (x y : X) (z : ι → E)
    (hx : (bad ε (code x) z).card ≤ r)
    (hy : (bad δ (code y) z).card ≤ s) :
    x = y := by
  by_contra h
  exact (Nat.not_lt_of_ge (separation_card_le ε δ (code x) (code y) z r s hx hy))
    (hsep x y h)

/-- Explicit discarded coordinates cover both erasures and arbitrary outliers.
Good coordinates need only satisfy a deterministic error bound. -/
theorem bad_card_le_of_good_outside (ε : ℝ) (u z : ι → E) (S : Finset ι)
    (hgood : ∀ i, i ∉ S → dist (u i) (z i) ≤ ε) :
    (bad ε u z).card ≤ S.card := by
  classical
  apply Finset.card_le_card
  intro i hi
  by_contra hn
  have hbad : ε < dist (u i) (z i) := by simpa [bad] using hi
  exact (not_lt_of_ge (hgood i hn)) hbad

end RiemannResearch.Analysis.FiniteCoordinateDecoding
