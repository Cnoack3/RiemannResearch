import RiemannResearch.Analysis.FiniteProfileEnergy
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite Green scores and boundary digits
Source: user - provided "Exact - Head Green Profiles in the Nyman--Beurling Program",
27 July 2026, sections 3--5 and agenda R3. All identities below allow arbitrary
finite weights. The digit multiplier need not be prime and the weight need not
be uniform. Vanishing of a boundary grid score is explicitly supplied.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.ExactHeadGreenProfile
open RiemannResearch.Analysis.FiniteProfileEnergy

def grid (d r : ℕ) : ℝ := (r / d : ℕ)
def centeredResidue (d r : ℕ) : ℝ := (r % d : ℕ) - ((d : ℝ) - 1) / 2
def digit (p d r : ℕ) : ℝ := ((r / d) % p : ℕ)
def score (s : Finset ℕ) (w R : ℕ → ℝ) (d : ℕ) : ℝ :=
  pairing s w R (grid d)

theorem grid_residue_identity (d r : ℕ) :
    (d : ℝ) * grid d r = (r : ℝ) - (r % d : ℕ) := by
  have h : (r % d : ℝ) + (d : ℝ) * (r / d : ℕ) = (r : ℝ) := by
    exact_mod_cast Nat.mod_add_div r d
  unfold grid
  linarith

/-- Exact canonical affine residual, with the signed centered - residue score. -/
theorem canonical_profile_identity (s : Finset ℕ) (w R : ℕ → ℝ) (d : ℕ) :
    (d : ℝ) * score s w R d -
      (pairing s w R (fun r => (r : ℝ)) +
        pairing s w R (fun _ => 1) / 2 -
        (d : ℝ) * pairing s w R (fun _ => 1) / 2) =
      -pairing s w R (centeredResidue d) := by
  unfold score pairing
  rw [Finset.mul_sum]
  have hg (r : ℕ) : (d : ℝ) * (w r * R r * grid d r) =
      w r * R r * (r : ℝ) - w r * R r * (r % d : ℕ) := by
    have h := grid_residue_identity d r
    nlinarith only [congrArg (fun a : ℝ => w r * R r * a) h]
  simp_rw [hg, centeredResidue, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring

/-- Digit recursion holds for every natural multiplier, even without primality,
coprimality or a conductor - boundary premise. -/
theorem grid_digit_recursion (p d r : ℕ) :
    grid d r = (p : ℝ) * grid (p * d) r + digit p d r := by
  have h : (r / d) % p + p * (r / (p * d)) = r / d := by
    simpa [Nat.div_div_eq_div_mul, Nat.mul_comm d p] using Nat.mod_add_div (r / d) p
  unfold grid digit
  exact_mod_cast h.symm.trans (Nat.add_comm _ _)

theorem score_digit_recursion (s : Finset ℕ) (w R : ℕ → ℝ) (p d : ℕ) :
    score s w R d = (p : ℝ) * score s w R (p * d) +
      pairing s w R (digit p d) := by
  unfold score pairing
  simp_rw [grid_digit_recursion p d, mul_add, Finset.sum_add_distrib]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  ring

/-- The boundary - digit score formula under its exact optimizer equation. -/
theorem boundary_digit_score (s : Finset ℕ) (w R : ℕ → ℝ) (p d : ℕ)
    (hzero : score s w R (p * d) = 0) :
    score s w R d = pairing s w R (digit p d) := by
  simpa [hzero] using score_digit_recursion s w R p d

/-- Every centered residue obeys the sharp pointwise square bound. -/
theorem centeredResidue_sq_le (d r : ℕ) (hd : 0 < d) :
    centeredResidue d r ^ 2 ≤ ((d : ℝ) - 1) ^ 2 / 4 := by
  have h0 : (0:ℝ) ≤ (r % d : ℕ) := by positivity
  have h1 : (r % d : ℝ) ≤ (d : ℝ) - 1 := by
    have h := Nat.mod_lt r hd
    have h' : r % d + 1 ≤ d := h
    have h'' : (r % d : ℝ) + 1 ≤ (d : ℝ) := by exact_mod_cast h'
    linarith
  unfold centeredResidue
  nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1)]

/-- Finite inclusion--exclusion and optimizer orthogonality give the root
identity. The high - conductor terms are removed only when their scores vanish. -/
theorem root_identity (s D : Finset ℕ) (w R C coeff : ℕ → ℝ) (x : ℕ)
    (hC : ∀ r, C r = (∑ d ∈ D, coeff d * grid d r) - 1)
    (hprojection : pairing s w R C = energy s w R)
    (hupper : ∀ d ∈ D, x < d → score s w R d = 0) :
    (∑ d ∈ D.filter (fun d => d ≤ x), coeff d * score s w R d) =
      energy s w R + pairing s w R (fun _ => 1) := by
  have hpair : pairing s w R C =
      (∑ d ∈ D, coeff d * score s w R d) - pairing s w R (fun _ => 1) := by
    unfold score pairing
    simp_rw [hC, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    rw [Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro r hr
    ring
  have hfilter :
      (∑ d ∈ D.filter (fun d => d ≤ x), coeff d * score s w R d) =
        ∑ d ∈ D, coeff d * score s w R d := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro d hd hn
    have hx : x < d := by
      have : ¬ d ≤ x := by
        intro hx
        exact hn (Finset.mem_filter.mpr ⟨hd, hx⟩)
      exact Nat.lt_of_not_ge this
    rw [hupper d hd hx, mul_zero]
  rw [hfilter]
  linarith

end RiemannResearch.RH.ExactHeadGreenProfile
