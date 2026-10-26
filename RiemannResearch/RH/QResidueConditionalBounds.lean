/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QResidueConditional
import RiemannResearch.RH.QPeriodicTailEnergy
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-!
# Complete residue-fiber deviations under Q

Source: the user's infinite-CRT squarefree response request, 26 October 2026.
The first atom and the entire remaining progression are separated exactly.
For bounded data the deviation from the first atom is O(L^(-2)) at every
fixed positive anchor. The consumer is the conditioned reciprocal source.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QResidueConditional
open ZetaTwoProbability ZetaTwoHilbert

/-- Exact first-site contribution plus the entire remaining residue fiber. -/
theorem fiberSum_first_tail (L a : ℕ) (hL : 0 < L) (ha : 0 < a)
    (f : ℕ → ℝ) {C : ℝ} (hf : ∀ n, |f n| ≤ C) :
    fiberSum L a f = positiveQWeight a * f a + fiberSum L (a + L) f := by
  have hs := fiber_terms_summable L a hL ha f hf
  rw [fiberSum, hs.tsum_eq_zero_add]
  simp only [Nat.mul_zero, Nat.add_zero]
  congr 1
  unfold fiberSum
  apply tsum_congr
  intro j
  rw [show a + L * (j + 1) = a + L + L * j by ring]

/-- The complete tail mass controls deviation from the first positive site. -/
theorem conditionalValue_deviation_tail_bound
    (L a : ℕ) (hL : 0 < L) (ha : 0 < a)
    (f : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C) (hf : ∀ n, |f n| ≤ C) :
    |conditionalValue L a f - f a| ≤
      2 * C * residuePowerWeight 0 L ((a : ℝ) + L) /
        residuePowerWeight 0 L a := by
  have hwpos : 0 < residuePowerWeight 0 L a :=
    residuePowerWeight_pos 0 (by exact_mod_cast hL) (by exact_mod_cast ha)
  have htpos : 0 < residuePowerWeight 0 L (a + L : ℕ) :=
    residuePowerWeight_pos 0 (by exact_mod_cast hL)
      (by exact_mod_cast (show 0 < a + L by omega))
  have hshift := residuePowerWeight_shift 0
    (show (0 : ℝ) < L by exact_mod_cast hL)
    (show (0 : ℝ) < a by exact_mod_cast ha)
  change residuePowerWeight 0 L a = positiveQWeight a +
    residuePowerWeight 0 L ((a : ℝ) + L) at hshift
  have hfshift := fiberSum_first_tail L a hL ha f hf
  have htail := conditionalValue_abs_le L (a + L) hL (by omega) f C hC hf
  unfold conditionalValue at htail
  rw [abs_div, abs_of_pos htpos] at htail
  have htail' := (div_le_iff₀ htpos).mp htail
  have hnum : |fiberSum L a f - residuePowerWeight 0 L a * f a| ≤
      2 * C * residuePowerWeight 0 L ((a : ℝ) + L) := by
    rw [hfshift, hshift]
    have he : positiveQWeight a * f a + fiberSum L (a + L) f -
        (positiveQWeight a + residuePowerWeight 0 L ((a : ℝ) + L)) * f a =
        fiberSum L (a + L) f - residuePowerWeight 0 L ((a : ℝ) + L) * f a := by ring
    rw [he]
    have htpos' : 0 ≤ residuePowerWeight 0 L ((a : ℝ) + L) := by
      exact (residuePowerWeight_pos 0 (by exact_mod_cast hL) (by positivity)).le
    calc
      _ ≤ |fiberSum L (a + L) f| +
          |residuePowerWeight 0 L ((a : ℝ) + L) * f a| := by
        simpa only [sub_zero, zero_sub, abs_neg] using
          abs_sub_le (fiberSum L (a + L) f) 0
            (residuePowerWeight 0 L ((a : ℝ) + L) * f a)
      _ ≤ _ := by
        rw [abs_mul, abs_of_nonneg htpos']
        have hfprod := mul_le_mul_of_nonneg_left (hf a) htpos'
        push_cast at htail'
        nlinarith
  have he : conditionalValue L a f - f a =
      (fiberSum L a f - residuePowerWeight 0 L a * f a) /
        residuePowerWeight 0 L a := by
    unfold conditionalValue
    field_simp [hwpos.ne'] <;> ring
  rw [he, abs_div, abs_of_pos hwpos]
  exact div_le_div_of_nonneg_right hnum hwpos.le

/-- Equivalent exact retained-tail form using mass minus its first atom. -/
theorem conditionalValue_deviation_mass_bound
    (L a : ℕ) (hL : 0 < L) (ha : 0 < a)
    (f : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C) (hf : ∀ n, |f n| ≤ C) :
    |conditionalValue L a f - f a| ≤
      2 * C * (residuePowerWeight 0 L a - positiveQWeight a) /
        residuePowerWeight 0 L a := by
  have hshift := residuePowerWeight_shift 0
    (show (0 : ℝ) < L by exact_mod_cast hL)
    (show (0 : ℝ) < a by exact_mod_cast ha)
  change residuePowerWeight 0 L a = positiveQWeight a +
    residuePowerWeight 0 L ((a : ℝ) + L) at hshift
  have he : residuePowerWeight 0 L a - positiveQWeight a =
      residuePowerWeight 0 L ((a : ℝ) + L) := by linarith
  rw [he]
  exact conditionalValue_deviation_tail_bound L a hL ha f C hC hf

/-- A quantitative bound valid for every positive anchor, without truncating its fiber. -/
theorem conditionalValue_deviation_bound
    (L a : ℕ) (hL : 0 < L) (ha : 0 < a)
    (f : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C) (hf : ∀ n, |f n| ≤ C) :
    |conditionalValue L a f - f a| ≤
      2 * C * zetaTwo * (a : ℝ) ^ 2 / (L : ℝ) ^ 2 := by
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hwpos : 0 < residuePowerWeight 0 L a := residuePowerWeight_pos 0 hLR haR
  have htail : residuePowerWeight 0 L ((a : ℝ) + L) ≤ 1 / (L : ℝ) ^ 2 := by
    rw [← residuePowerWeight_zeroClass L]
    exact residuePowerWeight_antitone_anchor 0 hLR hLR (by linarith)
  have hfirst := residueSquareWeight_lower hLR haR
  have hqpos : 0 < (1 / (zetaTwo * (a : ℝ) ^ 2)) := by
    have := zetaTwo_pos
    positivity
  have hratio : residuePowerWeight 0 L ((a : ℝ) + L) /
      residuePowerWeight 0 L a ≤ zetaTwo * (a : ℝ) ^ 2 / (L : ℝ) ^ 2 := by
    calc
      _ ≤ (1 / (L : ℝ) ^ 2) / residuePowerWeight 0 L a :=
        div_le_div_of_nonneg_right htail hwpos.le
      _ ≤ (1 / (L : ℝ) ^ 2) / (1 / (zetaTwo * (a : ℝ) ^ 2)) :=
        div_le_div_of_nonneg_left (by positivity) hqpos hfirst
      _ = _ := by field_simp [zetaTwo_pos.ne', haR.ne', hLR.ne'] <;> ring
  have hh := mul_le_mul_of_nonneg_left hratio (show 0 ≤ 2 * C by positivity)
  exact (conditionalValue_deviation_tail_bound L a hL ha f C hC hf).trans
    (by simpa only [mul_div_assoc, mul_assoc] using hh)

end RiemannResearch.RH.QResidueConditional
