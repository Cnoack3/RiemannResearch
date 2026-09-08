import RiemannResearch.RH.ThresholdHilbertDilation
import RiemannResearch.RH.ThresholdSeedEuclidean
import RiemannResearch.RH.ThresholdPrimePackets
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Actual closed legal modules in the weighted Hilbert space

Source: Christian Noack, RH_Two_Seed_Threshold.tex, September 8, 2026,
Sections 1–4. These definitions use the original weighted H topology, not
pointwise convergence or a Haar norm. All positive integer dilations
preserve the closed module. The RH density equivalence remains unproved.
-/
namespace RiemannResearch.RH.Pareto
noncomputable section

/-- Physical finite legal combinations that belong to the actual Hilbert space. -/
def hilbertLegalSubspace (A : Set ℕ) : Submodule ℝ ThresholdHilbert :=
  (legalSeedSpan A).comap hilbertSequenceLinear

/-- The paper's closed legal module, in the weighted Hilbert norm. -/
def hilbertLegalClosure (A : Set ℕ) : Submodule ℝ ThresholdHilbert :=
  (hilbertLegalSubspace A).topologicalClosure

theorem hilbertLegal_dilation (A : Set ℕ) {f : ThresholdHilbert}
    (hf : f ∈ hilbertLegalSubspace A) (m : ℕ) (hm : 0 < m) :
    hilbertDilation m hm f ∈ hilbertLegalSubspace A := by
  change hilbertSequence (hilbertDilation m hm f) ∈ legalSeedSpan A
  rw [hilbertDilation_sequence]
  exact legalSeedSpan_dilation A hf m hm

/-- Closed-module invariance is proved by continuity of the actual operators. -/
theorem hilbertLegalClosure_dilation (A : Set ℕ) {f : ThresholdHilbert}
    (hf : f ∈ hilbertLegalClosure A) (m : ℕ) (hm : 0 < m) :
    hilbertDilation m hm f ∈ hilbertLegalClosure A := by
  have hmap : Set.MapsTo (hilbertDilationContinuous m hm)
      (hilbertLegalSubspace A : Set ThresholdHilbert)
      (hilbertLegalSubspace A : Set ThresholdHilbert) := by
    intro g hg
    exact hilbertLegal_dilation A hg m hm
  exact hmap.closure (hilbertDilationContinuous m hm).continuous hf

/-- Common-base finite exponent classification survives Hilbert closure exactly. -/
theorem hilbertLegalClosure_power_list (c : ℕ) (hc : 0 < c) (es : List ℕ) :
    hilbertLegalClosure {a | ∃ e ∈ es, a = c ^ e} =
      hilbertLegalClosure {c ^ es.foldr Nat.gcd 0} := by
  unfold hilbertLegalClosure hilbertLegalSubspace
  rw [legalSeedSpan_power_list c hc es]

end
end RiemannResearch.RH.Pareto
