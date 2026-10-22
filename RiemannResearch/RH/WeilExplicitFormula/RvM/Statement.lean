/-
Vendored from anthropics/formal-math, zeta23, commit
fbdc36bbf17d20af3fd0447c6d1a8a02773c9844.
Local modification (2026-09-28): intra-project imports relocated under
RiemannResearch.RH.WeilExplicitFormula; blanket Mathlib imports, where present,
replaced by focused imports. Declarations, proofs and namespaces unchanged.
Original copyright notices and Apache-2.0 license are preserved.
-/
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/RvM/Statement.lean — Riemann–von Mangoldt assembly:
  Zeta23.RvM.riemannVonMangoldt (hΓ : GammaFacts) : RiemannVonMangoldt zetaZeroConfig
from Zeta23.RvM.rvM_main (MainTerm.lean) and Zeta23.RvM.zetaZeroConfig_local_count
(LocalCount.lean). Conditional on the Γ-facts by design (Stirling enters only through
`GammaFacts`).
-/
import RiemannResearch.RH.WeilExplicitFormula.RvM.MainTerm

noncomputable section

namespace Zeta23.RvM

/-- **H-RvM for Mathlib's ζ**, given the Γ-facts. -/
theorem riemannVonMangoldt (hΓ : GammaFacts) : RiemannVonMangoldt zetaZeroConfig :=
  ⟨rvM_main hΓ, zetaZeroConfig_local_count⟩

end Zeta23.RvM
