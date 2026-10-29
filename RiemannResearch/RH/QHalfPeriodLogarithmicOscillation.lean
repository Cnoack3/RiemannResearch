/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.NumberTheory.Primorial
import RiemannResearch.RH.QSquarefreeLatticePackets
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.QHalfPeriodHeadOscillation
import RiemannResearch.RH.QCRTMinimumEnergy
import RiemannResearch.RH.QPrimePowerSieve
import RiemannResearch.RH.QCRTCoprimeApproximation
import RiemannResearch.RH.QResidueHeadSpace
import RiemannResearch.RH.QSquarefreeAffineHead
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Logarithmic half-period oscillation

Source: the user's exact-head energy research agenda, 28 October 2026.
The complete signed increment is forced by the head. The prime-power count
is supplied by the existing `sieveCount_eq_log` theorem.

This obstructs uniform pointwise amplitude, not a uniform complete-Q energy.
-/

noncomputable section
namespace RiemannResearch.RH.QHalfPeriodLogarithmicOscillation
open ZetaTwoHilbert ArithmeticCumulative QSquarefreeLatticePackets
open QResidueHeadSpace QSquarefreeAffineHead QCRTCoprimeApproximation
open QPrimePowerSieve QHalfPeriodHeadOscillation QCRTMinimumEnergy

/-- Translation by half an even squarefree period exchanges the coprime
class and the gcd-two class. Oddness of the half-period is all this uses. -/
theorem gcd_half_shift_iff (m i : ℕ) (hm : m % 2 = 1) :
    Nat.gcd (m + i) (2 * m) = 1 ↔ Nat.gcd i (2 * m) = 2 := by
  have hcm : Nat.Coprime 2 m := (Nat.odd_iff.mpr hm).coprime_two_left
  rw [hcm.gcd_mul (m + i), hcm.gcd_mul i, Nat.gcd_self_add_left]
  by_cases hi : i % 2 = 0
  · have hgi : Nat.gcd i 2 = 2 := Nat.gcd_eq_right (Nat.dvd_of_mod_eq_zero hi)
    have hgs : Nat.gcd (m + i) 2 = 1 :=
      (Nat.odd_iff.mpr (show (m + i) % 2 = 1 by omega)).coprime_two_right
    rw [hgi, hgs, one_mul]
    omega
  · have hi1 : i % 2 = 1 := by omega
    have hgi : Nat.gcd i 2 = 1 := (Nat.odd_iff.mpr hi1).coprime_two_right
    have hgs : Nat.gcd (m + i) 2 = 2 :=
      Nat.gcd_eq_right (Nat.dvd_of_mod_eq_zero (show (m + i)%2=0 by omega))
    have hne : Nat.gcd i m ≠ 2 := by
      intro he
      have hd := Nat.gcd_dvd_right i m
      rw [he] at hd
      have hmod := Nat.mod_eq_zero_of_dvd hd
      omega
    rw [hgi, hgs, one_mul]
    omega

/-- Exact count increment, before imposing prime coverage. -/
theorem sieveCount_half_increment (m t : ℕ) (hm : m % 2 = 1) :
    sieveCount (2 * m) 1 (m + t) - sieveCount (2 * m) 1 m =
      sieveCount (2 * m) 2 t := by
  induction t with
  | zero => simp
  | succ t ih =>
      have hi : (if Nat.gcd (m + (t + 1)) (2 * m) = 1 then (1:ℝ) else 0) =
          (if Nat.gcd (t + 1) (2 * m) = 2 then (1:ℝ) else 0) := by
        simp only [gcd_half_shift_iff m (t + 1) hm]
      simp only [sieveCount] at ih ⊢
      rw [Nat.add_succ, cumulative_succ, cumulative_succ]
      simp only [Nat.add_assoc]
      rw [← hi]
      linarith

/-- The actual coprime seed has the complete logarithmic increment. -/
theorem coprimeApprox_half_increment_log (m H t : ℕ) (hm : m % 2 = 1)
    (hsf : Squarefree (2 * m))
    (hcover : ∀ p : ℕ, p.Prime → p ≤ H → p ∣ 2 * m)
    (htH : t ≤ H) (hmt : m + t < 2 * m) :
    qSequence (coprimeApprox (2 * m)) (m + t) -
      qSequence (coprimeApprox (2 * m)) m = (Nat.log 2 t : ℝ) := by
  have hmpos : 0 < m := by omega
  rw [coprimeApprox_sequence _ _ (by omega), coprimeApprox_sequence _ _ (by omega)]
  simp only [Nat.div_eq_of_lt hmt, Nat.div_eq_of_lt (show m < 2 * m by omega),
    Nat.cast_zero, mul_zero, sub_zero]
  rw [sieveCount_half_increment m t hm]
  exact sieveCount_eq_log (2 * m) 2 H t Nat.prime_two hsf
    (dvd_mul_right 2 m) hcover htH

theorem compensated_half_increment_zero (m d t : ℕ) (hdiv : d ∣ 2 * m)
    (hdt : 2 * t < d) (htL : 2 * t < 2 * m) :
    qSequence (compensatedResidue d (2 * m)) (m + t) -
      qSequence (compensatedResidue d (2 * m)) m = 0 := by
  rw [compensatedResidue_sequence, compensatedResidue_sequence]
  calc
    _ = (residueFraction d (m + t) - residueFraction d m) -
        ((2 * m : ℕ) : ℝ) / (d : ℝ) *
          (residueFraction (2 * m) (m + t) - residueFraction (2 * m) m) := by ring
    _ = (t : ℝ) / (d : ℝ) - ((2 * m : ℕ) : ℝ) / (d : ℝ) *
        ((t : ℝ) / ((2 * m : ℕ) : ℝ)) := by
      rw [half_shift_no_wrap m d t (by omega) hdiv hdt,
        half_shift_no_wrap m (2 * m) t (by omega) (dvd_refl _) htL]
    _ = 0 := by
      have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
      have hLR : ((2 * m : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast (show 2 * m ≠ 0 by omega)
      field_simp [hdR, hLR]
      ring

/-- Every allowed correction has zero increment on this half-period window. -/
theorem zeroHeadSpan_half_increment_zero (m H t : ℕ)
    (hHL : H < 2 * m) (htH : 2 * t ≤ H) (u : QHilbert)
    (hu : u ∈ zeroHeadSpan (conductors (2 * m)) H (2 * m)) :
    qSequence u (m + t) - qSequence u m = 0 := by
  let ev (n : ℕ) : (ℕ → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj n
  let ell : QHilbert →ₗ[ℝ] ℝ := (ev (m + t) - ev m).comp qSequenceLinear
  have hle : zeroHeadSpan (conductors (2 * m)) H (2 * m) ≤ ell.ker := by
    apply Submodule.span_le.mpr
    rintro x ⟨d, rfl⟩
    have hd := Finset.mem_filter.mp d.property
    have hdiv := (Nat.mem_divisors.mp (Finset.mem_filter.mp hd.1).1).1
    change qSequence (compensatedResidue d (2 * m)) (m + t) -
      qSequence (compensatedResidue d (2 * m)) m = 0
    exact compensated_half_increment_zero m d t hdiv (by omega) (by omega)
  exact hle hu

/-- A finite exact head forces a logarithmic oscillation far out in the period.
All signed values are retained; this is an identity, not a norm estimate. -/
theorem exact_head_half_increment_log (m H t : ℕ) (hm : m % 2 = 1)
    (hsf : Squarefree (2 * m))
    (hcover : ∀ p : ℕ, p.Prime → p ≤ H → p ∣ 2 * m)
    (hHL : H < 2 * m) (ht : 0 < t) (htH : 2 * t ≤ H)
    (f : QHilbert) (hf : f ∈ divisorStage (2 * m))
    (hh : ∀ n, 0 < n → n ≤ H → qSequence f n = 1) :
    qSequence f (m + t) - qSequence f m = (Nat.log 2 t : ℝ) := by
  have hL : 0 < 2 * m := by omega
  have hr : 2 * m ∈ conductors (2 * m) := Finset.mem_filter.mpr
    ⟨Nat.mem_divisors.mpr ⟨dvd_refl _, ne_of_gt hL⟩, by omega⟩
  have hb : coprimeApprox (2 * m) ∈ dictionary (conductors (2 * m)) := by
    rw [← divisorStage_eq_dictionary _ hL]
    exact coprimeApprox_mem_divisorStage _
  have hsub := (exact_head_iff_sub_mem_zeroHeadSpan (conductors (2 * m))
    (conductor_gt_one _) H (2 * m) (by omega) hr hHL (coprimeApprox (2 * m)) hb
    (fun n hn hnH => coprimeApprox_exact_head (2 * m) H n hL hcover hHL hn hnH) f).mp
      ⟨by simpa only [← divisorStage_eq_dictionary _ hL] using hf, hh⟩
  have hz := zeroHeadSpan_half_increment_zero m H t hHL htH
    (f - coprimeApprox (2 * m)) hsub
  change qSequenceLinear (f - coprimeApprox (2 * m)) (m + t) -
    qSequenceLinear (f - coprimeApprox (2 * m)) m = 0 at hz
  simp only [map_sub, Pi.sub_apply] at hz
  change (qSequence f (m + t) - qSequence (coprimeApprox (2 * m)) (m + t)) -
    (qSequence f m - qSequence (coprimeApprox (2 * m)) m) = 0 at hz
  have hs := coprimeApprox_half_increment_log m H t hm hsf hcover
    (by omega) (by omega)
  linarith

/-- Arithmetic hypotheses discharged for the actual canonical family. -/
theorem minimumEnergyApproximant_half_increment_log (j t : ℕ)
    (ht : 0 < t) (htj : 2 * t ≤ j + 1) :
    let m := primorial (j + 2) / 2
    qSequence (minimumEnergyApproximant j) (m + t) -
      qSequence (minimumEnergyApproximant j) m = (Nat.log 2 t : ℝ) := by
  dsimp only
  let L := primorial (j + 2)
  have h2 : 2 ∣ L := Nat.prime_two.dvd_primorial_iff.mpr (by omega)
  have he : 2 * (L / 2) = L := Nat.mul_div_cancel' h2
  have hsf : Squarefree (2 * (L / 2)) := he.symm ▸ squarefree_primorial (j + 2)
  have hc : Nat.Coprime 2 (L / 2) := Nat.coprime_of_squarefree_mul hsf
  have hm : (L / 2) % 2 = 1 := Nat.odd_iff.mp hc.odd_of_left
  have hcover : ∀ p : ℕ, p.Prime → p ≤ j + 1 → p ∣ 2 * (L / 2) := by
    intro p hp hpH
    rw [he]
    exact hp.dvd_primorial_iff.mpr (by omega)
  have hHL : j + 1 < 2 * (L / 2) := by
    rw [he]
    exact lt_of_lt_of_le (by omega : j + 1 < j + 2) le_primorial_self
  have hf : minimumEnergyApproximant j ∈ divisorStage (2 * (L / 2)) := by
    rw [he, divisorStage_eq_dictionary _ (primorial_pos _)]
    exact minimumEnergyApproximant_mem_dictionary j
  exact exact_head_half_increment_log (L / 2) (j + 1) t hm hsf hcover hHL ht htj
    (minimumEnergyApproximant j) hf (minimumEnergyApproximant_exact_head j)

/-- Complete-Q boundedness cannot be sought through a common global amplitude
bound for the canonical exact-head family. -/
theorem minimumEnergyApproximant_no_uniform_abs_bound :
    ¬ (∃ B : ℝ, ∀ j n : ℕ, |qSequence (minimumEnergyApproximant j) n| ≤ B) := by
  rintro ⟨B, hb⟩
  obtain ⟨k, hk⟩ := exists_nat_gt (2 * B)
  let t := 2 ^ k
  let j := 2 * t
  let m := primorial (j + 2) / 2
  have ht : 0 < t := by dsimp [t]; positivity
  have he := minimumEnergyApproximant_half_increment_log j t ht (by dsimp [j]; omega)
  have hlog : Nat.log 2 t = k := by
    dsimp [t]
    exact Nat.log_pow (by norm_num : 1 < 2) k
  dsimp only at he
  rw [hlog] at he
  have hlo := (abs_le.mp (hb j m)).1
  have hhi := (abs_le.mp (hb j (m + t))).2
  change qSequence (minimumEnergyApproximant j) (m + t) -
    qSequence (minimumEnergyApproximant j) m = (k : ℝ) at he
  linarith

end RiemannResearch.RH.QHalfPeriodLogarithmicOscillation
