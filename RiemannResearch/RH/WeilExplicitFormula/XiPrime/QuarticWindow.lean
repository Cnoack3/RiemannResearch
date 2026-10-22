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
Zeta23/XiPrime/QuarticWindow.lean — umbrella for the ξ′ quartic-window admissibility component.
  QuarticWindow/Params.lean    — P.atV v T rfl-dictionary, atV_phi, localFun/a/b/φ̂/trace bridges
  QuarticWindow/ModWindow.lean — GENERIC: a modulated ramp taper f·φ is an Zeta23.AdmWindow (admWindow_phiM)
  QuarticWindow/Quartic.lean   — f_Q = √vQuartic(·/L) is a ModFactor (A = 3/2, B = 12) ⇒ admWindow_phiV_quartic
  QuarticWindow/ZeroSide.lean  — PoissonSq / BlockInputs / Gz=Gp / tail package / 1/2 ≤ a ≤ 1 for P.atV vQuartic T,
                                 windowZeroSide_atV (the WindowZeroSide bundle)
  QuarticWindow/Moments.lean   — |a−2777/3000|, |b−518783/600000| ≤ 2w/L, |g(y) − L·vConv(y/L)| ≤ 4w, b ≥ 1/2,
                                 localHypsCoreQ_eventually
  QuarticWindow/Family.lean    — admFamily_phiV_quartic / admFamily_atV_quartic (the AdmFamily bundle)
-/
import RiemannResearch.RH.WeilExplicitFormula.XiPrime.QuarticWindow.Params
import RiemannResearch.RH.WeilExplicitFormula.XiPrime.QuarticWindow.ModWindow
import RiemannResearch.RH.WeilExplicitFormula.XiPrime.QuarticWindow.Quartic
import RiemannResearch.RH.WeilExplicitFormula.XiPrime.QuarticWindow.ZeroSide
import RiemannResearch.RH.WeilExplicitFormula.XiPrime.QuarticWindow.Moments
import RiemannResearch.RH.WeilExplicitFormula.XiPrime.QuarticWindow.Family
