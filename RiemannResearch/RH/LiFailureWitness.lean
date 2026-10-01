/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.LiCriterionImport.Lc.LiCriterion.XiOrderBridge

/-!
# A finite negative Li witness under failure of RH

Source: Xian-Jin Li's positivity criterion, through the unconditional imported
LiCriterion.li_criterion_rh_iff. All analytic order and Hadamard inputs have
been discharged in XiOrderBridge. This is contraposition, not a new RH proof.
The Taylor index n represents the coefficient lambda_(n+1).
Statement reference: Li (1997), Journal of Number Theory 65, 325-333,
https://doi.org/10.1006/jnth.1997.2137.
Formal upstream: https://github.com/nicholasbulka/li-criterion-rh-equivalence-lean
at 35df682f3b709ffe5fbcfdd452dfa964bd622b87; see the import's UPSTREAM.md.
-/

namespace RiemannResearch.RH.LiFailure

theorem not_RH_exists_negative_li (h : ¬ RiemannHypothesis) :
    ∃ n : ℕ, (LiCriterion.taylorCoeff LiCriterion.riemannXi n).re < 0 := by
  classical
  by_contra hn
  push_neg at hn
  exact h (LiCriterion.li_criterion_rh_iff.mpr hn)

end RiemannResearch.RH.LiFailure
