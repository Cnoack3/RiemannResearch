import RiemannResearch.RH.ArithmeticCumulativeBasic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact residue refinement and a finite weighted sieve update

Source: user-requested investigation of the zeta-two residue Gram matrix.
The elementary quotient/remainder identity is proved directly. The finite
weighted update retains its correction term and requires no primality
assumption. It is an identity of actual residue functions, not an assertion
that the resulting family has bounded or vanishing L²(Q) error.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.QResidueRefinement
open ArithmeticCumulative

/-- Splitting the residue modulo `d*p` first at scale `p`. -/
theorem nat_mod_refinement (d p n : ℕ) :
    n % (d * p) = p * ((n / p) % d) + n % p := by
  have hquot : (n / p) / d = n / (d * p) := by
    rw [Nat.div_div_eq_div_mul, Nat.mul_comm p d]
  have hq := Nat.div_add_mod (n / p) d
  rw [hquot] at hq
  have hpq := congrArg (fun k : ℕ => p * k) hq
  nlinarith [Nat.div_add_mod n p, Nat.div_add_mod n (d * p)]

/-- Refinement of actual legal residue atoms. The argument `n/p` is natural
number division; the last term is the complete remainder correction. -/
theorem residueFraction_refinement (d p n : ℕ) (hd : 0 < d) (hp : 0 < p) :
    residueFraction (d * p) n =
      residueFraction d (n / p) + residueFraction p n / (d : ℝ) := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hp)
  unfold residueFraction
  rw [nat_mod_refinement]
  push_cast
  field_simp [hdR, hpR] <;> ring

/-- A finite signed combination, using the Möbius-sieve sign convention. -/
def weightedResidue (S : Finset ℕ) (w : ℕ → ℝ) (n : ℕ) : ℝ :=
  -(∑ d ∈ S, w d * residueFraction d n)

def reciprocalCoefficient (S : Finset ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ d ∈ S, w d / (d : ℝ)

/-- The explicit paired coefficient extension `w(d), -u*w(d)` at the old
conductors `d` and the enlarged conductors `d*p`. This definition remains
meaningful when conductors coincide; the theorem does not assert otherwise. -/
def pairedResidueExtension (S : Finset ℕ) (w : ℕ → ℝ)
    (p : ℕ) (u : ℝ) (n : ℕ) : ℝ :=
  weightedResidue S w n + u * ∑ d ∈ S, w d * residueFraction (d * p) n

theorem weighted_refinement_sum (S : Finset ℕ) (w : ℕ → ℝ)
    (p n : ℕ) (hp : 0 < p) (hS : ∀ d ∈ S, 0 < d) :
    (∑ d ∈ S, w d * residueFraction (d * p) n) =
      -weightedResidue S w (n / p) +
        reciprocalCoefficient S w * residueFraction p n := by
  calc
    (∑ d ∈ S, w d * residueFraction (d * p) n) =
        ∑ d ∈ S, (w d * residueFraction d (n / p) +
          (w d / (d : ℝ)) * residueFraction p n) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [residueFraction_refinement d p n (hS d hd) hp]
      ring
    _ = -weightedResidue S w (n / p) +
        reciprocalCoefficient S w * residueFraction p n := by
      simp only [Finset.sum_add_distrib, ← Finset.sum_mul,
        weightedResidue, reciprocalCoefficient, neg_neg]

/-- Exact finite weighted prime-step formula, valid in fact for any positive
multiplier `p`. No probabilistic or asymptotic assumption is used. -/
theorem pairedResidueExtension_eq (S : Finset ℕ) (w : ℕ → ℝ)
    (p : ℕ) (u : ℝ) (n : ℕ) (hp : 0 < p) (hS : ∀ d ∈ S, 0 < d) :
    pairedResidueExtension S w p u n =
      weightedResidue S w n - u * weightedResidue S w (n / p) +
        u * reciprocalCoefficient S w * residueFraction p n := by
  unfold pairedResidueExtension
  rw [weighted_refinement_sum S w p n hp hS]
  ring

@[simp] theorem weightedResidue_zero (S : Finset ℕ) (w : ℕ → ℝ) :
    weightedResidue S w 0 = 0 := by
  simp [weightedResidue, residueFraction]

/-- On the initial interval below `p`, the downscaled term is exactly zero. -/
theorem pairedResidueExtension_below (S : Finset ℕ) (w : ℕ → ℝ)
    (p : ℕ) (u : ℝ) (n : ℕ) (hp : 0 < p) (hn : n < p)
    (hS : ∀ d ∈ S, 0 < d) :
    pairedResidueExtension S w p u n =
      weightedResidue S w n +
        u * reciprocalCoefficient S w * ((n : ℝ) / (p : ℝ)) := by
  rw [pairedResidueExtension_eq S w p u n hp hS,
    Nat.div_eq_of_lt hn, weightedResidue_zero]
  simp [residueFraction, Nat.mod_eq_of_lt hn]

/-- The matching reciprocal coefficient acquires the exact Euler factor.
This algebraic identity also covers zero denominators under Lean's convention. -/
theorem paired_reciprocalCoefficient (S : Finset ℕ) (w : ℕ → ℝ)
    (p : ℕ) (u : ℝ) :
    (∑ d ∈ S, (w d / (d : ℝ) - u * w d / ((d * p : ℕ) : ℝ))) =
      reciprocalCoefficient S w * (1 - u / (p : ℝ)) := by
  calc
    _ = ∑ d ∈ S, (w d / (d : ℝ)) * (1 - u / (p : ℝ)) := by
      apply Finset.sum_congr rfl
      intro d _
      simp only [Nat.cast_mul, div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := by rw [← Finset.sum_mul]; rfl

end RiemannResearch.RH.QResidueRefinement
