/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QTriangularTargetDirection
import RiemannResearch.RH.QSquarefreeInverseCapacity
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Escape along the actual squarefree prefix dictionaries

Source: continuation of the user's Balazard triangular dual refinement.
The norm and weak escape mechanisms are reused from the concurrently
published QTriangularTargetDirection module. This application discharges
retention for the distinct squarefree prefix dictionaries, rather than
the primorial divisor dictionaries of QPrimorialChargeDirection.

For escaping squarefree stage indices s>=2 the Rayleigh gain tends to zero
and complete squared target error tends to one. No RH assumption is used.
-/
noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QTriangularCharge
open ZetaTwoHilbert QSquarefreeInverseCapacity

def squarefreeDirection (n : ℕ) : QHilbert := directionFit (conductor n)

theorem squarefreeDirection_norm_tendsto_atTop (s : ℕ → ℕ)
    (hs : Tendsto s atTop atTop) (hs2 : ∀ n, 2 ≤ s n)
    (hsf : ∀ n, Squarefree (s n)) :
    Tendsto (fun n => ‖squarefreeDirection (s n)‖) atTop atTop := by
  let select (n : ℕ) : Index (s n) :=
    ⟨⟨s n - 2, by have := hs2 n; omega⟩, by
      simpa only [Nat.sub_add_cancel (hs2 n)] using hsf n⟩
  apply directionFit_norm_tendsto_atTop
    (fun n => conductor (s n)) (fun n => conductor_gt_one (s n))
    (fun n => conductor_injective (s n)) select
  simpa only [conductor, select, Nat.sub_add_cancel (hs2 _)] using hs

theorem squarefreeDirection_rayleigh_tendsto_zero (s : ℕ → ℕ)
    (hs : Tendsto s atTop atTop) (hs2 : ∀ n, 2 ≤ s n)
    (hsf : ∀ n, Squarefree (s n)) :
    Tendsto (fun n => targetCorrelation (conductor (s n)) ^ 2 /
      directionCapacity (conductor (s n))) atTop (𝓝 0) := by
  change Tendsto (fun n => rayleighGain (conductor (s n))) atTop (𝓝 0)
  apply rayleighGain_tendsto_zero (fun n => conductor (s n))
    (fun n => conductor_gt_one (s n)) (fun n => conductor_injective (s n))
    (squarefreeDirection_norm_tendsto_atTop s hs hs2 hsf)
  intro m i
  filter_upwards [hs.eventually_ge_atTop (s m)] with n hn
  exact ⟨⟨⟨i.val.val, lt_of_lt_of_le i.val.isLt hn⟩, i.property⟩, rfl⟩

theorem squarefreeDirection_rayleighFit_error_tendsto_one (s : ℕ → ℕ)
    (hs : Tendsto s atTop atTop) (hs2 : ∀ n, 2 ≤ s n)
    (hsf : ∀ n, Squarefree (s n)) :
    Tendsto (fun n => ‖qOne - rayleighFit (conductor (s n))‖ ^ 2)
      atTop (𝓝 1) := by
  have h := (tendsto_const_nhds :
    Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub
      (squarefreeDirection_rayleigh_tendsto_zero s hs hs2 hsf)
  simpa only [sub_zero] using h.congr' (Eventually.of_forall (fun n =>
    (rayleighFit_error _ (conductor_gt_one _) (conductor_injective _)).symm))

end RiemannResearch.RH.QTriangularCharge
