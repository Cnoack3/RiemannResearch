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

import RiemannResearch.RH.WeilExplicitFormula.MV.Eigen
import RiemannResearch.RH.WeilExplicitFormula.MV.Duality

/-!
# The Montgomery–Vaughan weighted Hilbert inequality

`eigen_bound` (`Zeta23/MV/Eigen.lean`) is exactly `EigenBound 13`; the spectral reduction of
`Duality.lean` turns it into `MVDiag 13` and, via polarization (`Zeta23/MV.lean`), into the
bilinear `∃ C > 0, MVHilbert C` of `Hypotheses.lean` (C = 26) — discharging `PaperInputs.MV`.
-/

noncomputable section

namespace Zeta23
namespace MV

theorem eigenBound_thirteen : EigenBound 13 :=
  fun _ι _ _ _freq _δ h u hu μ heig => eigen_bound h u hu μ heig

/-- **`MVDiag 13`** — the weighted Hilbert inequality, literature (diagonal) form. -/
theorem mvDiag_thirteen : MVDiag 13 := mvDiag_of_eigenBound eigenBound_thirteen

/-- **H-MV:** `∃ C > 0, MVHilbert C` (the field `PaperInputs.MV`). -/
theorem mv_hilbert : ∃ C : ℝ, 0 < C ∧ MVHilbert C :=
  mvHilbert_of_eigenBound (by norm_num) eigenBound_thirteen

end MV
end Zeta23

end
