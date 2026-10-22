/-
Copyright (c) 2026 Nicholas Bulka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Bulka
-/
/- Ported into RiemannResearch on 2026-09-30 from nicholasbulka/li-criterion-rh-equivalence-lean at
35df682f3b709ffe5fbcfdd452dfa964bd622b87. Changes: project-local import paths and license
references only; original declaration namespaces, statements, and proofs are preserved. See the
adjacent UPSTREAM.md and LICENSE.md. -/

/-
General finite-order Hadamard factorization — public entry point.

Import this file for the multiplicity-aware, any-finite-order version of
Hadamard's factorization theorem (Conway XI.3.4).
-/

import RiemannResearch.Analysis.LiCriterionImport.Hadamard.General.Factorization

/-!
# Genus-1 Hadamard factorization

Aggregator for the general order-`≤ 1` factorization theorem.
-/

namespace Hadamard

export General
  ( canonicalProductZeroSetMultiplicityRank
    canonicalProductZeroSetMultiplicityRank_one
    hadamard_factorization_general )

end Hadamard
