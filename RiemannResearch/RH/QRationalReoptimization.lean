/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QRationalStageCorrelation
import RiemannResearch.LinearAlgebra.FiniteHilbertSchur
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-!
# Reoptimization in the same later rational metric

Source: independent development from the user-provided signed-tail continuation
agenda, 20 October 2026. An actual old-space optimizer is constructed in the
later metric, including singular dictionaries. This separates metric drift
from genuine legal-space gain. No arithmetic lower bound for those gains is
assumed or asserted here.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QRationalCoprimeTail
open RiemannResearch.LinearAlgebra
open ArithmeticCumulative ZetaTwoHilbert
open QSquarefreePrimorialCofinality
open Pareto.SquarefreeStageExhaustion

/-- Normal equations for an arbitrary target, the old dictionary and the
later metric. The two periods need not agree. -/
theorem exists_divisor_normal_target (L M : ℕ) (t : ℕ → ℝ) :
    ∃ c : ℕ → ℝ, ∀ d ∈ L.divisors,
      rationalPair M (fun a => t a - divisorFit L c a)
        (residueFraction d) = 0 := by
  classical
  let x : EuclideanSpace ℝ (sites M) :=
    WithLp.toLp 2 (fun a => Real.sqrt (weight M a) * t a)
  let z : L.divisors → EuclideanSpace ℝ (sites M) :=
    fun d => WithLp.toLp 2
      (fun a => Real.sqrt (weight M a) * residueFraction d a)
  obtain ⟨b, hb⟩ := finiteSchur_exists_normal x z
  let c : ℕ → ℝ := fun d => if hd : d ∈ L.divisors then b ⟨d, hd⟩ else 0
  have hfit (a : ℕ) :
      divisorFit L c a = ∑ d : L.divisors, b d * residueFraction d a := by
    calc
      divisorFit L c a = ∑ d : L.divisors, c d * residueFraction d a :=
        (Finset.sum_coe_sort L.divisors (fun d => c d * residueFraction d a)).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro d hd
        simp only [c, dif_pos d.property]
  have hcomb (a : sites M) :
      (finiteSchurCombination z b).ofLp a =
        Real.sqrt (weight M a) * divisorFit L c a := by
    have hsum (s : Finset L.divisors) :
        (∑ d ∈ s, b d • z d).ofLp a =
          ∑ d ∈ s, b d * (z d).ofLp a := by
      induction s using Finset.induction_on with
      | empty => simp
      | @insert i s hi ih =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi]
        change b i * (z i).ofLp a + (∑ d ∈ s, b d • z d).ofLp a = _
        rw [ih]
    rw [hfit]
    change (∑ d, b d • z d).ofLp a = _
    rw [hsum Finset.univ]
    simp [z, Finset.mul_sum, mul_assoc, mul_comm]
  refine ⟨c, ?_⟩
  intro d hd
  have ho := finiteSchurResidual_orthogonal x z b hb ⟨d, hd⟩
  have he : rationalPair M (fun a => t a - divisorFit L c a)
        (residueFraction d) =
      inner ℝ (z ⟨d, hd⟩) (finiteSchurResidual x z b) := by
    rw [PiLp.inner_apply]
    unfold rationalPair
    rw [← Finset.sum_coe_sort (sites M)
      (fun a => weight M a * (t a - divisorFit L c a) * residueFraction d a)]
    apply Finset.sum_congr rfl
    intro a ha
    change weight M a * (t a - divisorFit L c a) * residueFraction d a =
      (Real.sqrt (weight M a) * t a - (finiteSchurCombination z b).ofLp a) *
        (Real.sqrt (weight M a) * residueFraction d a)
    rw [hcomb]
    calc
      _ = Real.sqrt (weight M a) ^ 2 * (t a - divisorFit L c a) *
          residueFraction d a := by rw [Real.sq_sqrt (weight_nonneg M a)]
      _ = _ := by ring
  rw [he]
  exact ho

def rationalOldCoefficients (L M : ℕ) (t : ℕ → ℝ) : ℕ → ℝ :=
  Classical.choose (exists_divisor_normal_target L M t)

theorem rationalOldCoefficients_normal (L M : ℕ) (t : ℕ → ℝ) :
    ∀ d ∈ L.divisors,
      rationalPair M (fun a => t a - divisorFit L (rationalOldCoefficients L M t) a)
        (residueFraction d) = 0 :=
  Classical.choose_spec (exists_divisor_normal_target L M t)

def rationalOldProjection (n m : ℕ) (t : ℕ → ℝ) : QHilbert :=
  qDivisorFit (primorialPeriod n)
    (rationalOldCoefficients (primorialPeriod n) (primorialPeriod m) t)

theorem rationalOldProjection_mem (n m : ℕ) (t : ℕ → ℝ) :
    rationalOldProjection n m t ∈ primorialStage n := by
  rw [← qDivisorLinear_range_eq_primorialStage]
  exact ⟨rationalOldCoefficients (primorialPeriod n) (primorialPeriod m) t, rfl⟩

/-- Every old divisor synthesis vanishes at the old period, independently
of the target and the metric used to choose its coefficients. -/
theorem rationalOldProjection_at_period (n m : ℕ) (t : ℕ → ℝ) :
    qSequence (rationalOldProjection n m t) (primorialPeriod n) = 0 := by
  unfold rationalOldProjection
  rw [qSequence_qDivisorFit]
  unfold divisorFit
  apply Finset.sum_eq_zero
  intro d hd
  simp only [residueFraction,
    Nat.mod_eq_zero_of_dvd (Nat.dvd_of_mem_divisors hd),
    Nat.cast_zero, zero_div, mul_zero]

theorem rationalOldProjection_normal_fit (L M : ℕ) (t b : ℕ → ℝ) :
    rationalPair M
      (fun a => t a - divisorFit L (rationalOldCoefficients L M t) a)
      (divisorFit L b) = 0 := by
  calc
    _ = ∑ d ∈ L.divisors, b d * rationalPair M
        (fun a => t a - divisorFit L (rationalOldCoefficients L M t) a)
        (residueFraction d) := by
      unfold rationalPair divisorFit
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro d hd
      rw [rationalOldCoefficients_normal L M t d hd, mul_zero]

theorem rationalOldProjection_normal_mem {n : ℕ} (m : ℕ) (t : ℕ → ℝ)
    {v : QHilbert} (hv : v ∈ primorialStage n) :
    rationalPair (primorialPeriod m)
      (fun a => t a - qSequence (rationalOldProjection n m t) a)
      (qSequence v) = 0 := by
  obtain ⟨b, rfl⟩ := exists_qDivisorFit_of_mem hv
  simp only [rationalOldProjection, qSequence_qDivisorFit]
  exact rationalOldProjection_normal_fit _ _ t b

def rationalReoptimized (n m : ℕ) : QHilbert :=
  rationalOldProjection n m (fun _ => 1)

theorem rationalReoptimized_mem (n m : ℕ) :
    rationalReoptimized n m ∈ primorialStage n :=
  rationalOldProjection_mem n m _

theorem rationalReoptimized_normal_mem {n : ℕ} (m : ℕ)
    {v : QHilbert} (hv : v ∈ primorialStage n) :
    rationalPair (primorialPeriod m)
      (fun a => 1 - qSequence (rationalReoptimized n m) a)
      (qSequence v) = 0 :=
  rationalOldProjection_normal_mem m _ hv

/-- Motion caused solely by changing the metric on the old legal space. -/
def rationalMetricDrift (n m : ℕ) : ℝ :=
  rationalPair (primorialPeriod m)
    (fun a => qSequence (rationalMinimizer (primorialPeriod n)) a -
      qSequence (rationalReoptimized n m) a)
    (fun a => qSequence (rationalMinimizer (primorialPeriod n)) a -
      qSequence (rationalReoptimized n m) a)

/-- Gain from adding legal directions, with the metric held fixed. -/
def rationalLegalGain (n m : ℕ) : ℝ :=
  rationalPair (primorialPeriod m)
    (fun a => qSequence (rationalMinimizer (primorialPeriod m)) a -
      qSequence (rationalReoptimized n m) a)
    (fun a => qSequence (rationalMinimizer (primorialPeriod m)) a -
      qSequence (rationalReoptimized n m) a)

theorem rationalMetricDrift_nonneg (n m : ℕ) : 0 ≤ rationalMetricDrift n m :=
  rationalPair_self_nonneg _ _

theorem rationalLegalGain_nonneg (n m : ℕ) : 0 ≤ rationalLegalGain n m :=
  rationalPair_self_nonneg _ _

theorem rationalStageDisplacement_split {n m : ℕ} (hnm : n ≤ m) :
    rationalStageDisplacement n m = rationalMetricDrift n m + rationalLegalGain n m := by
  let f := qSequence (rationalMinimizer (primorialPeriod n))
  let g := qSequence (rationalMinimizer (primorialPeriod m))
  let t := qSequence (rationalReoptimized n m)
  have hgf := rationalMinimizer_normal_mem
    (primorialStage_mono hnm (rationalMinimizer_mem n))
  have hgt := rationalMinimizer_normal_mem
    (primorialStage_mono hnm (rationalReoptimized_mem n m))
  have htf := rationalReoptimized_normal_mem m (rationalMinimizer_mem n)
  have htt := rationalReoptimized_normal_mem m (rationalReoptimized_mem n m)
  have hcross : rationalPair (primorialPeriod m)
      (fun a => g a - t a) (fun a => f a - t a) = 0 := by
    have hid : rationalPair (primorialPeriod m)
        (fun a => g a - t a) (fun a => f a - t a) =
        rationalPair (primorialPeriod m) (fun a => 1 - t a) f -
        rationalPair (primorialPeriod m) (fun a => 1 - t a) t -
        rationalPair (primorialPeriod m) (fun a => 1 - g a) f +
        rationalPair (primorialPeriod m) (fun a => 1 - g a) t := by
      unfold rationalPair
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a ha
      ring
    rw [hid]
    change _ = 0
    change rationalPair (primorialPeriod m) (fun a => 1 - g a) f = 0 at hgf
    change rationalPair (primorialPeriod m) (fun a => 1 - g a) t = 0 at hgt
    change rationalPair (primorialPeriod m) (fun a => 1 - t a) f = 0 at htf
    change rationalPair (primorialPeriod m) (fun a => 1 - t a) t = 0 at htt
    rw [hgf, hgt, htf, htt]
    ring
  have he : rationalStageDisplacement n m = rationalMetricDrift n m +
      rationalLegalGain n m - 2 * rationalPair (primorialPeriod m)
        (fun a => g a - t a) (fun a => f a - t a) := by
    unfold rationalStageDisplacement rationalMetricDrift rationalLegalGain rationalPair
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    dsimp [f, g, t]
    ring
  simpa only [hcross, mul_zero, sub_zero] using he

/-- A legal direction with its old-space projection removed in the same metric. -/
def rationalScreened (n m : ℕ) (v : QHilbert) : QHilbert :=
  v - rationalOldProjection n m (qSequence v)

theorem rationalScreened_mem {n m : ℕ} (hnm : n ≤ m) {v : QHilbert}
    (hv : v ∈ primorialStage m) : rationalScreened n m v ∈ primorialStage m :=
  (primorialStage m).sub_mem hv
    (primorialStage_mono hnm (rationalOldProjection_mem n m _))

theorem rationalScreened_orthogonal {n m : ℕ} (v : QHilbert)
    {u : QHilbert} (hu : u ∈ primorialStage n) :
    rationalPair (primorialPeriod m) (qSequence u)
      (qSequence (rationalScreened n m v)) = 0 := by
  have hseq : qSequence (rationalScreened n m v) =
      fun a => qSequence v a - qSequence (rationalOldProjection n m (qSequence v)) a := by
    change qSequenceLinear (v - rationalOldProjection n m (qSequence v)) =
      qSequenceLinear v - qSequenceLinear (rationalOldProjection n m (qSequence v))
    exact map_sub _ _ _
  rw [rationalPair_comm, hseq]
  exact rationalOldProjection_normal_mem m (qSequence v) hu

/-- A genuinely new conductor survives screening: the old period itself is
a positive weighted site at which every old fit is zero. -/
theorem rationalScreened_residue_energy_pos {n m e : ℕ} (hnm : n ≤ m)
    (he : 2 ≤ e) (henot : ¬ e ∣ primorialPeriod n) :
    0 < rationalPair (primorialPeriod m)
      (qSequence (rationalScreened n m (qResidue e)))
      (qSequence (rationalScreened n m (qResidue e))) := by
  have hseq : qSequence (rationalScreened n m (qResidue e)) (primorialPeriod n) =
      residueFraction e (primorialPeriod n) := by
    change qSequenceLinear (qResidue e -
      rationalOldProjection n m (qSequence (qResidue e))) (primorialPeriod n) = _
    rw [map_sub]
    change qSequence (qResidue e) (primorialPeriod n) -
      qSequence (rationalOldProjection n m (qSequence (qResidue e)))
        (primorialPeriod n) = _
    rw [qSequence_qResidue, rationalOldProjection_at_period, sub_zero]
  have hmod : 0 < primorialPeriod n % e := by
    apply Nat.pos_of_ne_zero
    intro hz
    exact henot (Nat.dvd_of_mod_eq_zero hz)
  have hres : 0 < residueFraction e (primorialPeriod n) := by
    unfold residueFraction
    exact div_pos (by exact_mod_cast hmod) (by exact_mod_cast (by omega : 0 < e))
  have hs : primorialPeriod n ∈ sites (primorialPeriod m) := by
    apply Finset.mem_Icc.mpr
    exact ⟨primorialPeriod_pos n,
      Nat.le_of_dvd (primorialPeriod_pos m) (primorialPeriod_nested hnm)⟩
  have hweight : 0 < weight (primorialPeriod m) (primorialPeriod n) := by
    have hL : (0 : ℝ) < primorialPeriod n := by exact_mod_cast primorialPeriod_pos n
    unfold weight
    positivity
  apply Finset.sum_pos'
  · intro a ha
    simpa only [mul_assoc, ← sq] using
      mul_nonneg (weight_nonneg (primorialPeriod m) a)
        (sq_nonneg (qSequence (rationalScreened n m (qResidue e)) a))
  · refine ⟨primorialPeriod n, hs, ?_⟩
    rw [hseq]
    exact mul_pos (mul_pos hweight hres) hres

/-- A direction screened in the later metric measures only genuine new-space
gain. Its signed target charge is retained until the final square. -/
theorem rationalLegalGain_ge_screened_charge {n m : ℕ} {v : QHilbert}
    (hv : v ∈ primorialStage m)
    (horth : ∀ u ∈ primorialStage n,
      rationalPair (primorialPeriod m) (qSequence u) (qSequence v) = 0)
    (hpos : 0 < rationalPair (primorialPeriod m) (qSequence v) (qSequence v)) :
    rationalPair (primorialPeriod m) (fun _ => 1) (qSequence v) ^ 2 /
        rationalPair (primorialPeriod m) (qSequence v) (qSequence v) ≤
      rationalLegalGain n m := by
  have hn := rationalMinimizer_normal_mem hv
  have ht := horth _ (rationalReoptimized_mem n m)
  have he : rationalPair (primorialPeriod m)
      (fun a => qSequence (rationalMinimizer (primorialPeriod m)) a -
        qSequence (rationalReoptimized n m) a) (qSequence v) =
      rationalPair (primorialPeriod m) (fun _ => 1) (qSequence v) := by
    rw [rationalPair_sub_left] at hn ⊢
    linarith
  have hc := rationalPair_cauchy_div (primorialPeriod m)
    (fun a => qSequence (rationalMinimizer (primorialPeriod m)) a -
      qSequence (rationalReoptimized n m) a) (qSequence v) hpos
  rw [he] at hc
  exact hc

/-- The projection construction supplies screening and legality, so only
positive screened energy remains as the one-direction nondegeneracy condition. -/
theorem rationalLegalGain_ge_actual_screened_charge {n m : ℕ} (hnm : n ≤ m)
    {v : QHilbert} (hv : v ∈ primorialStage m)
    (hpos : 0 < rationalPair (primorialPeriod m)
      (qSequence (rationalScreened n m v)) (qSequence (rationalScreened n m v))) :
    rationalPair (primorialPeriod m) (fun _ => 1)
        (qSequence (rationalScreened n m v)) ^ 2 /
        rationalPair (primorialPeriod m) (qSequence (rationalScreened n m v))
          (qSequence (rationalScreened n m v)) ≤ rationalLegalGain n m := by
  exact rationalLegalGain_ge_screened_charge (rationalScreened_mem hnm hv)
    (fun u hu => rationalScreened_orthogonal v hu) hpos

/-- A concrete certificate for every genuinely new divisor conductor. The
screened denominator is proved positive; no nondegeneracy hypothesis remains. -/
theorem rationalLegalGain_ge_new_divisor_charge {n m e : ℕ} (hnm : n ≤ m)
    (he : 2 ≤ e) (hedvd : e ∣ primorialPeriod m) (henot : ¬ e ∣ primorialPeriod n) :
    rationalPair (primorialPeriod m) (fun _ => 1)
        (qSequence (rationalScreened n m (qResidue e))) ^ 2 /
        rationalPair (primorialPeriod m) (qSequence (rationalScreened n m (qResidue e)))
          (qSequence (rationalScreened n m (qResidue e))) ≤ rationalLegalGain n m := by
  apply rationalLegalGain_ge_actual_screened_charge hnm
  · exact Submodule.subset_span ⟨e, he, hedvd, rfl⟩
  · exact rationalScreened_residue_energy_pos hnm he henot

end RiemannResearch.RH.QRationalCoprimeTail
