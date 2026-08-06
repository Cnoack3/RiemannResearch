import Mathlib.NumberTheory.LSeries.RiemannZeta

/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
/-!
# Riemann hypothesis research namespace

This module provides a stable project-local name for mathlib's formal
statement of the Riemann hypothesis.
-/

namespace RiemannResearch.RH

/-- The Riemann hypothesis, using mathlib's kernel-checked definition. -/
abbrev Statement : Prop := RiemannHypothesis

end RiemannResearch.RH
