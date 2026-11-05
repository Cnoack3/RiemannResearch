/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSquarefreeFiniteDisplacement
import RiemannResearch.RH.QSquarefreeLogDisplacement
import RiemannResearch.RH.QHilbertConvergence
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Topology.Algebra.Order.LiminfLimsup
/-!
# Site - dependent frequent polylog bounds on finite displacements
Source: standard passage to a pointwise limit, applied to the four - criteria paper.
The stages witnessing the bound may depend on the physical site; no common stage
subsequence is required. The envelope premise remains OPEN. The polylog rigidity
consumer is inherited from QSquarefreeLogDisplacement, not newly claimed here.
-/
noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QSquarefreeFiniteDisplacement
open ZetaTwoHilbert QSquarefreeDisplacementRigidity QSquarefreeLogDisplacement

theorem riemannHypothesis_of_sitewise_frequent_polylog
    (m : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ n : ℕ, ∃ᶠ J : ℕ in atTop,
      |qSequence (finiteDisplacement J) n| ≤ C * (6 + Real.log (n : ℝ)) ^ m) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_eventually_polylog_displacement m C hC
  apply Eventually.of_forall
  intro n
  have ht := (qSequence_tendsto_of_tendsto finiteDisplacement_tendsto n).abs
  by_contra hbad
  have he := ht.eventually (Ioi_mem_nhds (lt_of_not_ge hbad))
  obtain ⟨J, hJ, hgt⟩ := ((hb n).and_eventually he).exists
  exact (not_lt_of_ge hJ) hgt

end RiemannResearch.RH.QSquarefreeFiniteDisplacement
