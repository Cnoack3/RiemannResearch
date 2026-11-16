/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.PrimeLogProjection
import RiemannResearch.RH.RiemannHypothesisStrip

/-!
# The exact radius formulation of RH

Source (geometric proposal): *Modular Phase Reconstruction of Zeta Zeros from
Pole Lattices*, pp. 1-3,
https://drive.google.com/file/d/1opJNKzINIeBMDA_k6mr1jEtfW26_-2Cj/view.

This equivalence precisely identifies the horizontal information omitted
by the ordinate-only phase code. It does not prove the radius condition.
No global local-factor meromorphy is assumed or constructed.
-/

namespace RiemannResearch.RH
open Analysis.PrimeLogProjection

/-- A single radius, for any integer base larger than one, is exactly the
critical-line condition. This is an equivalence, not a provider of RH. -/
theorem riemannHypothesis_iff_log_projection_radius {p : ℕ} (hp : 1 < p) :
    RiemannHypothesis ↔
      ∀ z : ℂ, riemannZeta z = 0 → 0 < z.re → z.re < 1 →
        ‖projection p z‖ = Real.exp (-Real.log p * (1 / 2)) := by
  rw [riemannHypothesis_iff_strip_zeros_on_line]
  constructor
  · intro h z hz h0 h1
    exact (norm_projection_eq_iff hp z (1 / 2)).mpr (h z hz h0 h1)
  · intro h z hz h0 h1
    exact (norm_projection_eq_iff hp z (1 / 2)).mp (h z hz h0 h1)

end RiemannResearch.RH
