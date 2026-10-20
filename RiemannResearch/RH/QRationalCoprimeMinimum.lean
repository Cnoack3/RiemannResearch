import RiemannResearch.RH.QRationalCoprimeLegality
import RiemannResearch.LinearAlgebra.FiniteHilbertSchur
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Actual least-squares minima for the rational periodic weights

Source: user-provided CRT-carry memorandum, Sections 7--8, 19 October 2026.
Existence uses finite Hilbert-space projection after multiplying each row by
the square root of its weight. Singular dictionaries are allowed; the d=1
atom is therefore retained. Coefficients here are real. No assertion that
the coefficients are rational is formalized in this module.

-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QRationalCoprimeTail
open RiemannResearch.LinearAlgebra
open RiemannResearch.Analysis.FiniteWeightedTailCharge
open ArithmeticCumulative

/-- The complete divisor dictionary, including its harmless zero d=1 atom. -/
def divisorFit (L : ℕ) (c : ℕ → ℝ) (a : ℕ) : ℝ :=
  ∑ d ∈ L.divisors, c d * residueFraction d a

/-- The actual finite weighted normal equations have a solution, including
the singular dictionary with its zero d=1 atom. -/
theorem exists_divisor_normal (L : ℕ) :
    ∃ c : ℕ → ℝ, ∀ d ∈ L.divisors,
      (∑ a ∈ sites L, weight L a * (1 - divisorFit L c a) *
        residueFraction d a) = 0 := by
  classical
  let x : EuclideanSpace ℝ (sites L) :=
    WithLp.toLp 2 (fun a => Real.sqrt (weight L a))
  let z : L.divisors → EuclideanSpace ℝ (sites L) :=
    fun d => WithLp.toLp 2
      (fun a => Real.sqrt (weight L a) * residueFraction d a)
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
  have hcomb (a : sites L) :
      (finiteSchurCombination z b).ofLp a =
        Real.sqrt (weight L a) * divisorFit L c a := by
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
  have he : (∑ a ∈ sites L, weight L a * (1 - divisorFit L c a) *
        residueFraction d a) =
      inner ℝ (z ⟨d, hd⟩) (finiteSchurResidual x z b) := by
    rw [PiLp.inner_apply]
    rw [← Finset.sum_coe_sort (sites L)
      (fun a => weight L a * (1 - divisorFit L c a) * residueFraction d a)]
    apply Finset.sum_congr rfl
    intro a ha
    change weight L a * (1 - divisorFit L c a) * residueFraction d a =
      (Real.sqrt (weight L a) - (finiteSchurCombination z b).ofLp a) *
        (Real.sqrt (weight L a) * residueFraction d a)
    rw [hcomb]
    calc
      _ = Real.sqrt (weight L a) ^ 2 * (1 - divisorFit L c a) *
          residueFraction d a := by rw [Real.sq_sqrt (weight_nonneg L a)]
      _ = _ := by ring
  rw [he]
  exact ho

/-- Exact completion of the square, retaining the complete weighted
remainder for every competing divisor synthesis. -/
theorem divisorFit_completion (L : ℕ) (c b : ℕ → ℝ)
    (hdiv : ∀ d ∈ L.divisors,
      (∑ a ∈ sites L, weight L a * (1 - divisorFit L c a) *
        residueFraction d a) = 0) :
    rationalError L (divisorFit L b) =
      rationalError L (divisorFit L c) +
        ∑ a ∈ sites L, weight L a * (divisorFit L b a - divisorFit L c a) ^ 2 := by
  have hcross : (∑ a ∈ sites L,
      weight L a * (1 - divisorFit L c a) *
        (divisorFit L b a - divisorFit L c a)) = 0 := by
    calc
      _ = ∑ a ∈ sites L, ∑ d ∈ L.divisors,
          (b d - c d) * (weight L a * (1 - divisorFit L c a) *
            residueFraction d a) := by
        apply Finset.sum_congr rfl
        intro a ha
        conv_lhs => rhs; unfold divisorFit
        rw [← Finset.sum_sub_distrib, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d hd
        ring
      _ = ∑ d ∈ L.divisors, (b d - c d) *
          ∑ a ∈ sites L, weight L a * (1 - divisorFit L c a) *
            residueFraction d a := by
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro d hd
        rw [hdiv d hd, mul_zero]
  have hexact : rationalError L (divisorFit L b) =
      rationalError L (divisorFit L c) +
        (∑ a ∈ sites L, weight L a * (divisorFit L b a - divisorFit L c a) ^ 2) -
        2 * (∑ a ∈ sites L, weight L a * (1 - divisorFit L c a) *
          (divisorFit L b a - divisorFit L c a)) := by
    unfold rationalError energy
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  simpa only [hcross, mul_zero, sub_zero] using hexact

/-- An actual finite minimizer exists and satisfies the exact signed identity.
No normal-equation hypothesis is left to an external provider. -/
theorem exists_signed_minimum (L : ℕ) (hL : 0 < L) :
    ∃ c : ℕ → ℝ,
      (∀ d ∈ L.divisors,
        (∑ a ∈ sites L, weight L a * (1 - divisorFit L c a) *
          residueFraction d a) = 0) ∧
      rationalError L (divisorFit L c) + signedTail L (divisorFit L c) =
        5 * (Nat.totient L : ℝ) / (3 * (L : ℝ) ^ 2) ∧
      ∀ b : ℕ → ℝ,
        rationalError L (divisorFit L c) ≤ rationalError L (divisorFit L b) := by
  obtain ⟨c, hc⟩ := exists_divisor_normal L
  refine ⟨c, hc, ?_, ?_⟩
  · exact signed_identity_of_divisor_synthesis L hL (divisorFit L c) c
      (fun _ => rfl) hc
  · intro b
    rw [divisorFit_completion L c b hc]
    have hn : 0 ≤ ∑ a ∈ sites L,
        weight L a * (divisorFit L b a - divisorFit L c a) ^ 2 :=
      Finset.sum_nonneg (fun a ha => mul_nonneg (weight_nonneg L a) (sq_nonneg _))
    linarith

end RiemannResearch.RH.QRationalCoprimeTail
