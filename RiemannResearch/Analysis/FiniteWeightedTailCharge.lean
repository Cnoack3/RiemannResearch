import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite signed tail charges of weighted least-squares residuals

Source: user-provided `CRT Carries and Squarefree Residual Exhaustion`,
19 October 2026, Sections 8--9. This module formalizes the finite summation
and absorption algebra. Its normal-equation hypotheses are explicit.

The asymptotic signed lower bound is not supplied.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace RiemannResearch.Analysis.FiniteWeightedTailCharge

def energy (s : Finset ℕ) (w f : ℕ → ℝ) : ℝ :=
  ∑ a ∈ s, w a * (1 - f a) ^ 2

def tail (s : Finset ℕ) (w r : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ a ∈ s, if k ≤ a then w a * r a else 0

def countPrefix (c : Finset ℕ) (a : ℕ) : ℝ :=
  ∑ k ∈ c, if k ≤ a then 1 else 0

/-- The quadratic minimum equals its signed residual mass, when the
residual is orthogonal to its fitted vector. No sign is imposed on r. -/
theorem energy_eq_mass (s : Finset ℕ) (w f : ℕ → ℝ)
    (h : (∑ a ∈ s, w a * (1 - f a) * f a) = 0) :
    energy s w f = ∑ a ∈ s, w a * (1 - f a) := by
  have ht (a : ℕ) : w a * (1 - f a) ^ 2 =
      w a * (1 - f a) - w a * (1 - f a) * f a := by ring
  simp only [energy, ht, Finset.sum_sub_distrib, h, sub_zero]

/-- Finite Fubini, retaining every signed tail. -/
theorem sum_tail_eq_prefix (s c : Finset ℕ) (w r : ℕ → ℝ) :
    (∑ k ∈ c, tail s w r k) =
      ∑ a ∈ s, w a * r a * countPrefix c a := by
  unfold tail countPrefix
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  split_ifs <;> ring

theorem tail_one (s : Finset ℕ) (w r : ℕ → ℝ)
    (hs : ∀ a ∈ s, 1 ≤ a) :
    tail s w r 1 = ∑ a ∈ s, w a * r a := by
  apply Finset.sum_congr rfl
  intro a ha
  exact if_pos (hs a ha)

/-- A normal equation for a centered counting function supplies the
total charge. Legality of that counting function is a separate input
to an arithmetic application. -/
theorem total_charge (s c : Finset ℕ) (w r : ℕ → ℝ) (α : ℝ)
    (h : (∑ a ∈ s, w a * r a * (countPrefix c a - α * (a : ℝ))) = 0) :
    (∑ k ∈ c, tail s w r k) = α * ∑ a ∈ s, (a : ℝ) * w a * r a := by
  rw [sum_tail_eq_prefix]
  have he : (∑ a ∈ s, w a * r a * (countPrefix c a - α * (a : ℝ))) =
      (∑ a ∈ s, w a * r a * countPrefix c a) -
        α * ∑ a ∈ s, (a : ℝ) * w a * r a := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  rw [he] at h
  exact sub_eq_zero.mp h

/-- The signed coprime-tail identity in a generic finite weighted problem.
The distinguished first site is not dropped. -/
theorem energy_add_tail (s c : Finset ℕ) (w f : ℕ → ℝ) (α : ℝ)
    (hs : ∀ a ∈ s, 1 ≤ a) (hc : 1 ∈ c)
    (hfit : (∑ a ∈ s, w a * (1 - f a) * f a) = 0)
    (hcount : (∑ a ∈ s, w a * (1 - f a) *
      (countPrefix c a - α * (a : ℝ))) = 0) :
    energy s w f + (∑ k ∈ c.erase 1, tail s w (fun a => 1 - f a) k) =
      α * ∑ a ∈ s, (a : ℝ) * w a * (1 - f a) := by
  have ht := total_charge s c w (fun a => 1 - f a) α hcount
  have he := Finset.sum_erase_add
    (s := c) (f := tail s w (fun a => 1 - f a)) hc
  rw [tail_one s w _ hs, ← energy_eq_mass s w f hfit] at he
  linarith

/-- Equivalent forms of the one-sided absorption estimate. -/
theorem absorption_iff {E S t θ ε : ℝ} (h : E + S = t) :
    -θ * E - ε ≤ S ↔ (1 - θ) * E ≤ t + ε := by
  constructor <;> intro hs <;> nlinarith

theorem absorption_bound {E S t θ ε : ℝ} (h : E + S = t)
    (hs : -θ * E - ε ≤ S) (hθ : θ < 1) :
    E ≤ (t + ε) / (1 - θ) := by
  apply (le_div_iff₀ (sub_pos.mpr hθ)).mpr
  have hb := (absorption_iff h).mp hs
  nlinarith

/-- A positive persistent defect is incompatible with an asymptotically
smaller absorption budget. This is a finite obstruction, not RH. -/
theorem absorption_obstruction {E S t θ ε δ : ℝ} (h : E + S = t)
    (hE : δ ≤ E) (hθ : θ < 1)
    (hsmall : t + ε < (1 - θ) * δ) :
    ¬(-θ * E - ε ≤ S) := by
  intro hs
  have hb := (absorption_iff h).mp hs
  have hm := mul_le_mul_of_nonneg_left hE (sub_pos.mpr hθ).le
  linarith

/-- Once the energies have a limit, the signed charge tends to its negative.
This theorem assumes that limit; it does not show that it is zero. -/
theorem signed_limit {E S t : ℕ → ℝ} {D : ℝ}
    (hid : ∀ n, E n + S n = t n)
    (hE : Tendsto E atTop (𝓝 D)) (ht : Tendsto t atTop (𝓝 0)) :
    Tendsto S atTop (𝓝 (-D)) := by
  have he : S = fun n => t n - E n := by
    funext n
    linarith [hid n]
  rw [he]
  simpa only [zero_sub] using ht.sub hE

end RiemannResearch.Analysis.FiniteWeightedTailCharge
