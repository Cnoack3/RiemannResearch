/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QHeadSlopeLimit
import RiemannResearch.RH.QDifferenceLimits
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Squarefree

/-! # Ordered prime prefixes and signed Möbius charge of the physical displacement

Source: the recursive carry argument in RecursivePrimeCarryResearch20261105.md.
The fixed-site limit uses the project's formalization of Balazard, Proposition 7.
The actual cofinal estimate is a hypothesis of the RH reductions below. -/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.QPrimeSubtreeBudget
open Pareto ZetaTwoHilbert QSquarefreeDisplacementRigidity QDisplacementTranslationCarry

/-- Removing the largest prime builds the ascending prime-prefix tree. -/
def parent (m : ℕ) : ℕ :=
  if h : 1 < m then m / m.primeFactors.max' (Nat.nonempty_primeFactors.mpr h) else 1

theorem parent_spec (m : ℕ) (hm : 1 < m) :
    0 < parent m ∧ parent m < m ∧ parent m ∣ m := by
  let p := m.primeFactors.max' (Nat.nonempty_primeFactors.mpr hm)
  have hmem : p ∈ m.primeFactors := Finset.max'_mem _ _
  have hd := Nat.dvd_of_mem_primeFactors hmem
  have hp := Nat.prime_of_mem_primeFactors hmem
  have hpos : 0 < m := by omega
  have hparent : parent m = m / p := dif_pos hm
  rw [hparent]
  exact ⟨Nat.div_pos (Nat.le_of_dvd hpos hd) hp.pos,
    Nat.div_lt_self hpos hp.one_lt, ⟨p, (Nat.div_mul_cancel hd).symm⟩⟩

def prefixes (m : ℕ) : Finset ℕ :=
  if _h : 1 < m then insert m (prefixes (parent m)) else ∅
termination_by m
decreasing_by exact (parent_spec m (by omega)).2.1

theorem prefix_bounds {r m : ℕ} (hr : r ∈ prefixes m) : 2 ≤ r ∧ r ≤ m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    rw [prefixes] at hr
    split at hr
    next hm =>
      rcases Finset.mem_insert.mp hr with h | h
      · omega
      · have hp := (parent_spec m hm).2.1
        obtain ⟨ha,hb⟩ := ih _ hp h
        omega
    next => simp at hr

/-- Integer size of the new digit before division by the conductor. -/
def stepDigit (r n : ℕ) : ℝ := ((n % r : ℕ) : ℝ) - ((n % parent r : ℕ) : ℝ)

theorem digit_bounds {r : ℕ} (hr : 1 < r) (n : ℕ) :
    0 ≤ stepDigit r n ∧ stepDigit r n ≤ ((r - parent r : ℕ) : ℝ) := by
  obtain ⟨hpos,hlt,hd⟩ := parent_spec r hr
  have hmod := Nat.mod_mod_of_dvd n hd
  have hrem := Nat.mod_add_div (n % r) (parent r)
  rw [hmod] at hrem
  have hquot : n % r / parent r < r / parent r := by
    apply (Nat.div_lt_iff_lt_mul hpos).mpr
    rw [Nat.div_mul_cancel hd]
    exact Nat.mod_lt n (by omega)
  have hh := Nat.mul_le_mul_left (parent r) (Nat.succ_le_of_lt hquot)
  rw [Nat.mul_succ, Nat.mul_div_cancel' hd] at hh
  unfold stepDigit
  rw [Nat.cast_sub hlt.le]
  constructor
  · apply sub_nonneg.mpr
    exact_mod_cast (show n % parent r ≤ n % r by omega)
  · have bound : ((n % r : ℕ) : ℝ) + parent r ≤ (r : ℝ) + (n % parent r : ℕ) := by
      exact_mod_cast (show n % r + parent r ≤ r + n % parent r by omega)
    linarith

private theorem path_sum (m n : ℕ) (hm : 0 < m) :
    ∑ r ∈ prefixes m, stepDigit r n = ((n % m : ℕ) : ℝ) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    rw [prefixes]
    split
    next h =>
      obtain ⟨hp,hlt,_⟩ := parent_spec m h
      have hout : m ∉ prefixes (parent m) := fun hx =>
        (Nat.not_le_of_lt hlt) (prefix_bounds hx).2
      rw [Finset.sum_insert hout, ih _ hlt hp]
      simp [stepDigit]
    next h =>
      have he : m = 1 := by omega
      simp [he, Nat.mod_one]

def subtree (b : ℕ → ℝ) (H r : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 H, if r ∈ prefixes m then b m / (m : ℝ) else 0

/-- No truncation error in the finite signed digit expansion. -/
theorem signed_subtree_identity (b : ℕ → ℝ) (H n : ℕ) :
    ∑ r ∈ Finset.Icc 2 H, stepDigit r n * subtree b H r =
      ∑ m ∈ Finset.Icc 1 H, ((n % m : ℕ) : ℝ) * (b m / (m : ℝ)) := by
  classical
  unfold subtree
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  have hm' := Finset.mem_Icc.mp hm
  rw [← path_sum m n hm'.1, Finset.sum_mul]
  have hsub : prefixes m ⊆ Finset.Icc 2 H := fun r hr =>
    Finset.mem_Icc.mpr ⟨(prefix_bounds hr).1, (prefix_bounds hr).2.trans hm'.2⟩
  simp_rw [mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  congr 1
  ext r
  simp only [Finset.mem_filter]
  exact ⟨And.right, fun h => ⟨hsub h, h⟩⟩

def charge (f : QHilbert) (m : ℕ) : ℝ := mobiusDifference m (qSequence f)

/-- Exact drift at a finite physical head. -/
theorem finite_drift (f : QHilbert) (H n : ℕ) (hn : n ≤ H) :
    ∑ r ∈ Finset.Icc 2 H, stepDigit r n * subtree (charge f) H r =
      (n : ℝ) * (∑ m ∈ Finset.Icc 1 H, charge f m / (m : ℝ)) - qSequence f n := by
  rw [signed_subtree_identity, finite_floor_reconstruction (qSequence f) (qSequence_zero f) H n hn,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  have hp : 0 < m := (Finset.mem_Icc.mp hm).1
  have hr : (m : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have he : ((n % m : ℕ) : ℝ) + (m : ℝ) * ((n / m : ℕ) : ℝ) = n := by
    exact_mod_cast Nat.mod_add_div n m
  change _ = _ - charge f m * _
  field_simp [hr]
  linear_combination (charge f m) * he

theorem signed_subtree_tendsto (f : QHilbert) (n : ℕ) :
    Tendsto (fun H => ∑ r ∈ Finset.Icc 2 H, stepDigit r n * subtree (charge f) H r)
      atTop (𝓝 (-qSequence f n)) := by
  have ht := ((qSequence_reciprocal_charge_tendsto f).const_mul (n : ℝ)).sub_const (qSequence f n)
  rw [mul_zero, zero_sub] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop n] with H hH
  exact (finite_drift f H n hH).symm

/-- Maximum possible digit, localized to the chosen physical site. -/
def siteWeight (r n : ℕ) : ℝ :=
  if n < parent r then 0 else (min n (r - parent r) : ℕ)

theorem digit_le_siteWeight {r : ℕ} (hr : 1 < r) (n : ℕ) : stepDigit r n ≤ siteWeight r n := by
  unfold siteWeight
  split
  next h =>
    have h' : n < r := h.trans (parent_spec r hr).2.1
    simp [stepDigit, Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt h']
  next =>
    rw [Nat.cast_min]
    apply le_min _ (digit_bounds hr n).2
    have ha : ((n % r : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.mod_le n r
    have hb : (0 : ℝ) ≤ (n % parent r : ℕ) := Nat.cast_nonneg _
    unfold stepDigit
    linarith

def siteBudget (b : ℕ → ℝ) (σ : ℝ) (H n : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 2 H, siteWeight r n * max 0 (-σ * subtree b H r)

def budget (b : ℕ → ℝ) (σ : ℝ) (H : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 2 H, (r : ℝ) * max 0 (-σ * subtree b H r)

private theorem signed_le_siteBudget (b : ℕ → ℝ) (σ : ℝ) (H n : ℕ) :
    -σ * (∑ r ∈ Finset.Icc 2 H, stepDigit r n * subtree b H r) ≤ siteBudget b σ H n := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hr
  have h := (Finset.mem_Icc.mp hr).1
  calc
    _ = stepDigit r n * (-σ * subtree b H r) := by ring
    _ ≤ stepDigit r n * max 0 (-σ * subtree b H r) :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) (digit_bounds h n).1
    _ ≤ _ := mul_le_mul_of_nonneg_right (digit_le_siteWeight h n) (le_max_left _ _)

/-- Each physical site can use its own cofinal horizons; only the sign and bound are shared. -/
theorem rh_of_site_subtree_budget (σ C : ℝ) (hσ : |σ| = 1) (hC : 0 ≤ C)
    (hb : ∀ n, ∃ᶠ H : ℕ in atTop, siteBudget (charge displacement) σ H n ≤ C) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_one_sided_bounded_displacement σ C hσ hC
  intro n
  have ht := (signed_subtree_tendsto displacement n).const_mul (-σ)
  rw [neg_mul_neg] at ht
  by_contra! h
  have hg := ht.eventually (lt_mem_nhds h)
  obtain ⟨H,hH,hgt⟩ := ((hb n).and_eventually hg).exists
  exact (not_lt_of_ge ((signed_le_siteBudget _ σ H n).trans hH)) hgt

/-- The paper's original one-sided budget for the actual displacement. -/
theorem rh_of_subtree_budget (σ C : ℝ) (hσ : |σ| = 1) (hC : 0 ≤ C)
    (hb : ∃ᶠ H : ℕ in atTop, budget (charge displacement) σ H ≤ C) : RiemannHypothesis := by
  apply rh_of_site_subtree_budget σ C hσ hC
  intro n
  apply hb.mono
  intro H hH
  apply le_trans _ hH
  apply Finset.sum_le_sum
  intro r hr
  apply mul_le_mul_of_nonneg_right _ (le_max_left _ _)
  unfold siteWeight
  split
  next => exact Nat.cast_nonneg _
  next => exact_mod_cast (Nat.min_le_right n (r - parent r)).trans (Nat.sub_le r _)

/-- Total physical digit seen by a harmonic head, retaining the exact remainders. -/
def harmonicWeight (X r : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (X + 1), stepDigit r n / (n : ℝ)

def harmonicBudget (b : ℕ → ℝ) (σ : ℝ) (H X : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 2 H, harmonicWeight X r * max 0 (-σ * subtree b H r)

/-- A choice of sign can discard the entire finite slope. At each physical head
one finite conductor horizon suffices; the arithmetic bound may grow polylogarithmically. -/
theorem harmonicSide_le_budget (σ : ℝ) (H X : ℕ) (hX : X ≤ H)
    (hs : σ * (∑ m ∈ Finset.Icc 1 H, charge displacement m / (m : ℝ)) ≤ 0) :
    harmonicSide σ X ≤ harmonicBudget (charge displacement) σ H X := by
  classical
  let T := subtree (charge displacement) H
  have hsite (n : ℕ) (hn : n ≤ X) :
      max (σ * qSequence displacement n) 0 ≤
        ∑ r ∈ Finset.Icc 2 H, stepDigit r n * max 0 (-σ * T r) := by
    have hfloor := finite_drift displacement H n (hn.trans hX)
    have hprod : (n : ℝ) * (σ * (∑ m ∈ Finset.Icc 1 H, charge displacement m / (m : ℝ))) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hs
    apply max_le
    · calc
        _ ≤ -σ * (∑ r ∈ Finset.Icc 2 H, stepDigit r n * T r) := by
          dsimp only [T]
          rw [hfloor]
          linarith only [hprod]
        _ = ∑ r ∈ Finset.Icc 2 H, stepDigit r n * (-σ * T r) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r _
          ring
        _ ≤ _ := Finset.sum_le_sum (fun r hr => mul_le_mul_of_nonneg_left (le_max_right _ _)
          (digit_bounds (Finset.mem_Icc.mp hr).1 n).1)
    · exact Finset.sum_nonneg (fun r hr => mul_nonneg (digit_bounds (Finset.mem_Icc.mp hr).1 n).1
        (le_max_left _ _))
  calc
    _ ≤ ∑ n ∈ Finset.range (X + 1),
        (∑ r ∈ Finset.Icc 2 H, stepDigit r n * max 0 (-σ * T r)) / (n : ℝ) :=
      Finset.sum_le_sum fun n hn => div_le_div_of_nonneg_right
        (hsite n (by have := Finset.mem_range.mp hn; omega)) (Nat.cast_nonneg _)
    _ = _ := by
      simp_rw [Finset.sum_div]
      rw [Finset.sum_comm]
      unfold harmonicBudget harmonicWeight
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro n _
      dsimp only [T]
      ring

/-- A single finite cutoff H ≥ X and a sign may be selected afresh at each good X. -/
theorem rh_of_harmonic_subtree_budget (B C : ℝ) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hb : ∃ᶠ X : ℕ in atTop, ∃ H : ℕ, X ≤ H ∧ ∃ σ : ℝ, |σ| = 1 ∧
      σ * (∑ m ∈ Finset.Icc 1 H, charge displacement m / (m : ℝ)) ≤ 0 ∧
      harmonicBudget (charge displacement) σ H X ≤ C * (Real.log (X : ℝ)) ^ B) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_cofinal_harmonic_polylog B C hB hC
  apply hb.mono
  rintro X ⟨H, hX, σ, hσ, hs, ht⟩
  have hmin : minimumHarmonicPrefix X ≤ harmonicSide σ X := by
    rcases le_total 0 σ with h | h
    · rw [abs_of_nonneg h] at hσ
      rw [hσ]
      exact min_le_left _ _
    · rw [abs_of_nonpos h] at hσ
      have he : σ = -1 := by linarith
      rw [he]
      exact min_le_right _ _
  exact hmin.trans ((harmonicSide_le_budget σ H X hX hs).trans ht)

end RiemannResearch.RH.QPrimeSubtreeBudget

end
