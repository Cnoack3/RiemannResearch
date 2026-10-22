/-
Vendored from anthropics/formal-math, zeta23, commit
fbdc36bbf17d20af3fd0447c6d1a8a02773c9844.
Local modification (2026-09-28): imports relocated under
RiemannResearch.RH.WeilExplicitFormula; trailing whitespace normalized.
Declarations, proof bodies, namespaces and original license notices preserved.
Source supports the statements and proofs; see PROVENANCE.md for scope.
-/
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ThmE/RvMChiDefs.lean — shared vocabulary for the H-RvM(χ) contour argument.
The half-contour itself is function-agnostic: reuse Zeta23.RvM.halfContour.
-/
import RiemannResearch.RH.WeilExplicitFormula.ThmE.Statement
import RiemannResearch.RH.WeilExplicitFormula.RvM.Defs

noncomputable section

namespace Zeta23
namespace ThmE

variable {q : ℕ} [NeZero q]

/-- T is a zero-free ordinate for L(·,χ). -/
def GoodHeightL (χ : DirichletCharacter ℂ q) (T : ℝ) : Prop :=
  ∀ ρ : ℂ, IsNontrivialZeroL χ ρ → ρ.im ≠ T

end ThmE
end Zeta23
