/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Topology.Order.IntermediateValue
/-!
# Uniqueness and principal normalization of logarithm lifts

Mathlib's covering-map uniqueness proves equality on a connected domain.
The RH consumer is the exact Littlewood identity: normalization along one
right vertical side identifies both bounded horizontal phases without
omitting an independent winding correction. Source: the supplied
Conrey--Baluyot recovery note, 15 November 2026 (proof target).
-/

open Set Complex
namespace Complex
theorem logLifts_eqOn_of_exp_eq {X : Type*} [TopologicalSpace X]
    {S : Set X} {L K : X → ℂ} {x₀ : X}
    (hS : IsPreconnected S) (hL : ContinuousOn L S) (hK : ContinuousOn K S)
    (he : ∀ x ∈ S, exp (L x) = exp (K x))
    (hx₀ : x₀ ∈ S) (hbase : L x₀ = K x₀) : Set.EqOn L K S := by
  exact isCoveringMap_exp.eqOn_of_comp_eqOn hS hL hK
    (fun x hx => Subtype.ext (he x hx)) hx₀ hbase

theorem logLift_eq_principal_on_Icc {p L : ℝ → ℂ} {a b : ℝ}
    (hab : a ≤ b) (hL : ContinuousOn L (Icc a b))
    (hp : ContinuousOn p (Icc a b))
    (hs : ∀ t ∈ Icc a b, p t ∈ slitPlane)
    (he : ∀ t ∈ Icc a b, exp (L t) = p t)
    (hbase : L a = log (p a)) :
    Set.EqOn L (fun t => log (p t)) (Icc a b) := by
  apply logLifts_eqOn_of_exp_eq isPreconnected_Icc hL
    (hp.clog hs) _ ⟨le_rfl, hab⟩ hbase
  intro t ht
  rw [he t ht, exp_log (slitPlane_ne_zero (hs t ht))]

/-- A normalized continuous polar phase agrees with the imaginary part of
a continuous logarithm lift on the whole connected interval. -/
theorem logLift_im_eq_phase_on_Icc {p L : ℝ → ℂ} {φ : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hL : ContinuousOn L (Icc a b))
    (hφ : ContinuousOn φ (Icc a b))
    (he : ∀ t ∈ Icc a b, exp (L t) = p t)
    (hrep : ∀ t ∈ Icc a b, p t = (‖p t‖ : ℂ) * exp ((φ t : ℂ) * I))
    (hbase : (L b).im = φ b) :
    ∀ t ∈ Icc a b, (L t).im = φ t := by
  let K : ℝ → ℂ := fun t => ((L t).re : ℂ) + (φ t : ℂ) * I
  have hK : ContinuousOn K (Icc a b) :=
    (Complex.continuous_ofReal.comp_continuousOn
      (Complex.continuous_re.comp_continuousOn hL)).add
      ((Complex.continuous_ofReal.comp_continuousOn hφ).mul continuousOn_const)
  have hKe : ∀ t ∈ Icc a b, exp (K t) = p t := by
    intro t ht
    have hn : Real.exp (L t).re = ‖p t‖ := by rw [← he t ht, norm_exp]
    dsimp [K]
    rw [exp_add, ← ofReal_exp, hn]
    exact (hrep t ht).symm
  have hbase' : L b = K b := by
    apply Complex.ext
    · simp [K]
    · simpa [K] using hbase
  have heq := logLifts_eqOn_of_exp_eq isPreconnected_Icc hL hK
    (fun t ht => (he t ht).trans (hKe t ht).symm) ⟨hab, le_rfl⟩ hbase'
  intro t ht
  have hh := congrArg Complex.im (heq ht)
  simpa [K] using hh
end Complex
