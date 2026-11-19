/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.RH.RiemannHypothesisStrip
import RiemannResearch.Analysis.ActualQuasiRiemannSupport

/-!
# Testing zero-free strips at countably many disk centers

The squared distance to a rational center on Re(s)=1 detects every
nontrivial zero to the right of the proposed boundary. Arbitrarily close
rational ordinates suffice, including when a zero has irrational ordinate.
The companion note gives the Cauchy–Hadamard interpretation for ξ′/ξ.
-/

namespace RiemannResearch.RH.RationalZeroFreeDisks
open Zeta23 RiemannResearch.Analysis.ActualZeroOrdinate

/-- Every open disk about 1+iq of the given squared radius is zero-free. -/
def RationalDiskBound (r : ℝ) : Prop :=
  ∀ (q : ℚ) (z : ℂ), IsNontrivialZero z → r^2 ≤ (1-z.re)^2 + ((q:ℝ)-z.im)^2

/-- The condition on the countable set of centers is exact, including the
closed supporting half-plane and zeros on its boundary. -/
theorem rationalDiskBound_iff {r : ℝ} (hr : 0 ≤ r) :
    RationalDiskBound r ↔ ∀ z : ℂ, IsNontrivialZero z → z.re ≤ 1-r := by
  constructor
  · intro h z hz
    by_contra! hβ
    have hwidth : 0 < r - (1-z.re) := by linarith
    obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn (show z.im < z.im+(r-(1-z.re)) by linarith)
    have hx : 0 < 1-z.re := sub_pos.mpr hz.2.2
    have hy : 0 < (q:ℝ)-z.im := sub_pos.mpr hq₁
    have hsum : 1-z.re + ((q:ℝ)-z.im) < r := by linarith
    have hs := (sq_lt_sq₀ (by linarith : 0 ≤ 1-z.re+((q:ℝ)-z.im)) hr).2 hsum
    nlinarith only [hs,h q z hz,mul_nonneg hx.le hy.le]
  · intro h q z hz
    have hgap : r ≤ 1-z.re := by linarith only [h z hz]
    exact (pow_le_pow_left₀ hr hgap 2).trans (le_add_of_nonneg_right (sq_nonneg _))

/-- Radius one half on a single rational line of centers is equivalent to
the actual Riemann hypothesis by the completed-zeta functional equation. -/
theorem riemannHypothesis_iff_half_disks :
    RiemannHypothesis ↔ RationalDiskBound (1/2) := by
  rw [rationalDiskBound_iff (by norm_num), riemannHypothesis_iff_strip_zeros_on_line]
  constructor
  · intro h z hz
    rw [h z hz.1 hz.2.1 hz.2.2]
    norm_num
  · intro h z hz h₀ h₁
    have hz' : IsNontrivialZero z := ⟨hz,h₀,h₁⟩
    have hcz := RvM.completedRiemannZeta_eq_zero_iff.mpr hz'
    have href : IsNontrivialZero (1-z) := RvM.completedRiemannZeta_eq_zero_iff.mp
      (by rwa [completedRiemannZeta_one_sub])
    have hleft := h (1-z) href
    rw [Complex.sub_re,Complex.one_re] at hleft
    linarith only [h z hz',hleft]

/-- The externally certified continuum contact gives a concrete starting
radius. -/
theorem continuumContact_disks (h : DirichletContinuumContactNonvanishing) :
    RationalDiskBound (1-continuumContact) := by
  apply (rationalDiskBound_iff (by linarith only [continuumContact_mem.2])).mpr
  intro z hz
  have h₀ := zeta_continuumContact_of_dirichlet h
  by_contra! hh
  have hn : z ≠ 1 := by
    rintro rfl
    simpa using hz.2.2
  exact h₀ z hn (by linarith) hz.1

end RiemannResearch.RH.RationalZeroFreeDisks
