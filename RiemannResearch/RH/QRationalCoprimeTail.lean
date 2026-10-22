import RiemannResearch.Analysis.FiniteWeightedTailCharge
import RiemannResearch.RH.ArithmeticCumulativeBasic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Rational periodic weights and the exact signed coprime-tail identity

Source: user-provided CRT-carry memorandum, 19 October 2026, Sections 7--8.
The weight is 1/a^2 + 2/(L*(2*a+L)), exactly as in the document.

The normal equations for the fitted vector, g_L, and the centered coprime
prefix are explicit hypotheses. In the manuscript they follow from legal
least-squares projection and the Mobius formula for the centered countPrefix.
The companion `QRationalCoprimeLegality` derives these hypotheses from
the full divisor normal equations. The infinite-Q upper-weight comparison
is not formalized in these modules.

-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QRationalCoprimeTail
open RiemannResearch.Analysis.FiniteWeightedTailCharge
open ArithmeticCumulative

def weight (L a : ℕ) : ℝ :=
  1 / (a : ℝ) ^ 2 + 2 / ((L : ℝ) * (2 * (a : ℝ) + L))

def sites (L : ℕ) : Finset ℕ := Finset.Icc 1 L

def coprimeSites (L : ℕ) : Finset ℕ :=
  (sites L).filter (fun k => Nat.Coprime k L)

def rationalError (L : ℕ) (f : ℕ → ℝ) : ℝ := energy (sites L) (weight L) f

def signedTail (L : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ k ∈ (coprimeSites L).erase 1,
    tail (sites L) (weight L) (fun a => 1 - f a) k

theorem weight_nonneg (L a : ℕ) : 0 ≤ weight L a := by
  unfold weight
  positivity

theorem weight_endpoint (L : ℕ) (hL : 0 < L) :
    weight L L = 5 / (3 * (L : ℝ) ^ 2) := by
  have hLR : (L : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hL)
  unfold weight
  rw [show 2 * (L : ℝ) + L = 3 * (L : ℝ) by ring]
  field_simp [hLR]
  ring

/-- The representative L denotes residue zero and must be retained. -/
theorem residue_on_period (L a : ℕ) (hL : 0 < L) (ha : a ∈ sites L) :
    residueFraction L a = (a : ℝ) / L - if a = L then 1 else 0 := by
  have haL := (Finset.mem_Icc.mp ha).2
  by_cases he : a = L
  · subst a
    have hLR : (L : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hL)
    simp [residueFraction, hLR]
  · have halt : a < L := by omega
    simp [residueFraction, Nat.mod_eq_of_lt halt, he]

/-- Orthogonality to g_L fixes the exact first moment of the signed
weighted residual. This formula includes the boundary mass at L. -/
theorem residual_moment (L : ℕ) (hL : 0 < L) (f : ℕ → ℝ)
    (hfL : f L = 0)
    (horth : (∑ a ∈ sites L, weight L a * (1 - f a) * residueFraction L a) = 0) :
    (∑ a ∈ sites L, (a : ℝ) * weight L a * (1 - f a)) =
      5 / (3 * (L : ℝ)) := by
  have hLR : (L : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hL)
  have hmem : L ∈ sites L := Finset.mem_Icc.mpr ⟨hL, le_rfl⟩
  have he : (∑ a ∈ sites L, weight L a * (1 - f a) * residueFraction L a) =
      (∑ a ∈ sites L, (a : ℝ) * weight L a * (1 - f a)) / (L : ℝ) -
        weight L L * (1 - f L) := by
    calc
      _ = ∑ a ∈ sites L,
          ((a : ℝ) * weight L a * (1 - f a) / (L : ℝ) -
            if a = L then weight L L * (1 - f L) else 0) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [residue_on_period L a hL ha]
        split_ifs with h
        · subst a
          ring
        · ring
      _ = _ := by
        rw [Finset.sum_sub_distrib, ← Finset.sum_div]
        simp [hmem]
  rw [he, hfL, sub_zero, mul_one] at horth
  have hm : (∑ a ∈ sites L, (a : ℝ) * weight L a * (1 - f a)) =
      weight L L * (L : ℝ) :=
    (div_eq_iff hLR).mp (sub_eq_zero.mp horth)
  rw [hm, weight_endpoint L hL]
  field_simp [hLR]

/-- The concrete finite identity of Section 8. The centered-prefix
normal equation is displayed rather than treated as an axiom. -/
theorem signed_identity (L : ℕ) (hL : 0 < L) (f : ℕ → ℝ)
    (hfL : f L = 0)
    (hfit : (∑ a ∈ sites L, weight L a * (1 - f a) * f a) = 0)
    (hfull : (∑ a ∈ sites L, weight L a * (1 - f a) * residueFraction L a) = 0)
    (hcount : (∑ a ∈ sites L, weight L a * (1 - f a) *
      (countPrefix (coprimeSites L) a -
        ((Nat.totient L : ℝ) / L) * (a : ℝ))) = 0) :
    rationalError L f + signedTail L f =
      5 * (Nat.totient L : ℝ) / (3 * (L : ℝ) ^ 2) := by
  have hs : ∀ a ∈ sites L, 1 ≤ a :=
    fun a ha => (Finset.mem_Icc.mp ha).1
  have hc : 1 ∈ coprimeSites L := by
    simp [coprimeSites, sites, Nat.succ_le_iff.mpr hL]
  have h := energy_add_tail (sites L) (coprimeSites L) (weight L) f
    ((Nat.totient L : ℝ) / L) hs hc hfit hcount
  rw [residual_moment L hL f hfL hfull] at h
  change rationalError L f + signedTail L f =
    ((Nat.totient L : ℝ) / L) * (5 / (3 * (L : ℝ))) at h
  rw [h]
  have hLR : (L : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hL)
  field_simp [hLR]

/-- Positivity comes from the retained zero residue, not from a
positivity assertion about any of the signed coprime tails. -/
theorem rationalError_boundary_lower (L : ℕ) (hL : 0 < L)
    (f : ℕ → ℝ) (hfL : f L = 0) :
    5 / (3 * (L : ℝ) ^ 2) ≤ rationalError L f := by
  have hmem : L ∈ sites L := Finset.mem_Icc.mpr ⟨hL, le_rfl⟩
  have h := Finset.single_le_sum
    (s := sites L) (a := L)
    (f := fun a => weight L a * (1 - f a) ^ 2)
    (fun a ha => mul_nonneg (weight_nonneg L a) (sq_nonneg _)) hmem
  simpa only [hfL, sub_zero, one_pow, mul_one, weight_endpoint L hL,
    rationalError, energy] using h

end RiemannResearch.RH.QRationalCoprimeTail
