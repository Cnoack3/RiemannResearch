/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.LocalizedMellinHeadSignature

/-!
# Forced weighted Mellin-signature decay at an off-line zero

Source: user-provided CRT and Four Improvements continuation, 6–7 October 2026.
The extensions retain complete signed identities and correction squares.


Subpolynomial complete residual energy forces the squared retained complex
signature to be little-o of every slightly weaker localized inverse power.
The full physical head square is retained in the obstruction. This is an
unconditional implication at a hypothetical zero, not a signature provider.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis.SubpolynomialWindow

theorem legal_subpolynomial_retained_signature_weighted_tendsto_zero
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (f : ℕ → ThresholdHilbert) (n : ℕ → ℕ) (C : ℕ → ℝ)
    (hn : Tendsto (fun i => (n i : ℝ)) atTop atTop)
    (hf : ∀ i, f i ∈ hilbertLegalClosure A)
    (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i, ‖hilbertOne - f i‖ ^ 2 ≤ C i + 1)
    (hsub : Tendsto (fun i => Real.log (1 + C i) / Real.log (n i : ℝ))
      atTop (𝓝 0))
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun i =>
      ‖1 / s - paretoMellin (compactHead (n i - 1) (hilbertOne - f i)) s‖ ^ 2 *
        (n i : ℝ) ^ (2 * s.re - 1 - ε)) atTop (𝓝 0) := by
  let d : ℝ := 2 * s.re - 1
  let W : ℕ → ℝ := fun i =>
    ‖1 / s - paretoMellin (compactHead (n i - 1) (hilbertOne - f i)) s‖ ^ 2 *
      (n i : ℝ) ^ (d - ε)
  have hd : 0 < d := by dsimp [d]; linarith
  have hW : ∀ i, 0 ≤ W i := by
    intro i
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hn1 : ∀ᶠ i in atTop, (1 : ℝ) ≤ (n i : ℝ) :=
    hn.eventually (eventually_ge_atTop 1)
  have hsmall : ∀ c : ℝ, 0 < c → ∀ᶠ i in atTop, W i < c := by
    intro c hc
    by_contra hnot
    have hfreq : ∃ᶠ i in atTop, c ≤ W i := by
      change ¬ ∀ᶠ i in atTop, ¬ c ≤ W i
      simpa only [not_le] using hnot
    have hfloor : ∃ᶠ i in atTop, (d*c) * (n i : ℝ)^ε ≤ C i + 1 := by
      apply (hfreq.and_eventually hn1).mono
      rintro i ⟨hi, hni⟩
      have hniNat : 1 ≤ n i := by exact_mod_cast hni
      have hniPos : (0 : ℝ) < (n i : ℝ) := by linarith
      have hp : 0 ≤ (n i : ℝ)^ε := Real.rpow_nonneg hniPos.le _
      have hw : W i * (n i : ℝ)^ε =
          ‖1 / s - paretoMellin (compactHead (n i - 1) (hilbertOne - f i)) s‖ ^ 2 *
            (n i : ℝ)^d := by
        dsimp [W]
        rw [mul_assoc, ← Real.rpow_add hniPos]
        congr 2
        ring
      have hb := legal_residual_head_signature_power_lower A hA (hf i)
        (n i) hniNat s hs hs1 hz
      have hdrop : ‖hilbertOne - f i‖ ^ 2 -
          ‖compactHead (n i - 1) (hilbertOne - f i)‖ ^ 2 ≤
          ‖hilbertOne - f i‖ ^ 2 := sub_le_self _ (sq_nonneg _)
      calc
        (d*c) * (n i : ℝ)^ε = d * (c * (n i : ℝ)^ε) := by ring
        _ ≤ d * (W i * (n i : ℝ)^ε) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hi hp) hd.le
        _ = d *
            ‖1 / s - paretoMellin (compactHead (n i - 1) (hilbertOne - f i)) s‖ ^ 2 *
              (n i : ℝ)^d := by rw [hw]; ring
        _ ≤ ‖hilbertOne - f i‖ ^ 2 -
            ‖compactHead (n i - 1) (hilbertOne - f i)‖ ^ 2 := hb
        _ ≤ C i + 1 := hdrop.trans (hbound i)
    exact no_positive_power_floor_frequently (fun i => (n i : ℝ)) C 1
      (d*c) ε hn hC (by norm_num) (mul_pos hd hc) hε hsub hfloor
  change Tendsto W atTop (𝓝 0)
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall (fun i => ha.trans_le (hW i))
  · intro b hb
    exact hsmall b hb

end RiemannResearch.RH.Pareto
