import RiemannResearch.RH.QCRTBoundedCriterion
import RiemannResearch.RH.QFullTargetTotality
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.Choose

/-!
# Complete-norm escape for the canonical CRT collocation family

Source: PQ_Density_Operators_and_RH_Agenda.pdf, agenda 6,
12 November 2026. The existing canonical solver matches the complete atomic-Q
divisor moments. Its finite solvability is unconditional. This theorem proves
that failure of totality forces every cofinal divisor-exhausting sequence of
these exact sources to escape to infinity in full norm.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QCRTCanonicalEscape
open ZetaTwoHilbert QCRTFiniteCollocation QCRTBoundedCriterion

theorem canonical_norm_tendsto_atTop
    (hn : QFullResidueProjection.closure ≠ ⊤)
    (L : ℕ → ℕ) (hL : ∀ j, 2 ≤ L j) (hlarge : Tendsto L atTop atTop)
    (hexhaust : ∀ d : ℕ, 0 < d → ∀ᶠ j in atTop, d ∣ L j) :
    Tendsto (fun j => ‖(canonical (L j) (hL j) : QHilbert)‖) atTop atTop := by
  classical
  apply tendsto_atTop.mpr
  intro C
  by_contra h
  have hcofinal : ∀ N : ℕ, ∃ j : ℕ, N ≤ j ∧
      ‖(canonical (L j) (hL j) : QHilbert)‖ < C := by
    intro N
    by_contra hnN
    apply h
    apply eventually_atTop.mpr
    refine ⟨N, ?_⟩
    intro j hj
    by_contra hjC
    exact hnN ⟨j, hj, lt_of_not_ge hjC⟩
  choose φ hφge hφbound using hcofinal
  have hφ : Tendsto φ atTop atTop := tendsto_atTop_mono hφge tendsto_id
  apply hn
  apply QFullTargetTotality.closure_eq_top_iff_one_mem.mpr
  exact qOne_mem_of_bounded_canonical (L ∘ φ) (fun j => hL (φ j))
    (hlarge.comp hφ) (fun d hd => hφ.eventually (hexhaust d hd))
    C (fun j => (hφbound j).le)

end RiemannResearch.RH.QCRTCanonicalEscape
