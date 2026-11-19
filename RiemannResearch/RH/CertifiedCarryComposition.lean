import RiemannResearch.RH.UniversalAtomCarryPresentation
import RiemannResearch.RH.QRecursivePrimeCarry
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Composition of finite reciprocal carry certificates

Source: the user's atom/carry CRT handoff, §14.4. Substituting one finite
certificate for each input produces a single certified floor. Integer
coefficients transport both the reciprocal charges and the local floor carries.
The existing finite CRT chain is the path case of the same propagation rule.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.UniversalAtomCarry
open ArithmeticCumulative

namespace Certificate

/-- Flatten a family with unequal arities into a single finite index set. -/
private def leafEquiv (outer : Certificate) (inner : Fin outer.arity → Certificate) :
    Fin (Fintype.card ((i : Fin outer.arity) × Fin (inner i).arity)) ≃
      ((i : Fin outer.arity) × Fin (inner i).arity) :=
  (Fintype.equivFin _).symm

private theorem sum_leaves (outer : Certificate) (inner : Fin outer.arity → Certificate)
    (f : ℕ → ℝ) :
    (∑ t, ((outer.coeff (leafEquiv outer inner t).1 *
          (inner (leafEquiv outer inner t).1).coeff (leafEquiv outer inner t).2 : ℤ) : ℝ) *
        f ((inner (leafEquiv outer inner t).1).input (leafEquiv outer inner t).2)) =
      ∑ i, (outer.coeff i : ℝ) * ∑ j, ((inner i).coeff j : ℝ) * f ((inner i).input j) := by
  let F (z : (i : Fin outer.arity) × Fin (inner i).arity) : ℝ :=
    ((outer.coeff z.1 * (inner z.1).coeff z.2 : ℤ) : ℝ) * f ((inner z.1).input z.2)
  change (∑ t, F (leafEquiv outer inner t)) = _
  rw [(leafEquiv outer inner).sum_comp F, Fintype.sum_sigma]
  simp only [F, Int.cast_mul, mul_assoc, Finset.mul_sum]

/-- Substitution multiplies coefficients along each branch. Its integer charge
is the outer charge plus the coefficient-weighted inner charges. -/
def flatten (outer : Certificate) (inner : Fin outer.arity → Certificate)
    (hmatch : ∀ i, (inner i).output = outer.input i) : Certificate where
  arity := Fintype.card ((i : Fin outer.arity) × Fin (inner i).arity)
  input t := (inner (leafEquiv outer inner t).1).input (leafEquiv outer inner t).2
  input_gt_one t := (inner (leafEquiv outer inner t).1).input_gt_one _
  coeff t := outer.coeff (leafEquiv outer inner t).1 *
    (inner (leafEquiv outer inner t).1).coeff (leafEquiv outer inner t).2
  output := outer.output
  output_gt_one := outer.output_gt_one
  charge := outer.charge + ∑ i, outer.coeff i * (inner i).charge
  reciprocal := by
    simp only [div_eq_mul_inv, one_mul]
    rw [sum_leaves outer inner (fun d => (d : ℝ)⁻¹)]
    have hi (i : Fin outer.arity) :
        (∑ j, ((inner i).coeff j : ℝ) * (((inner i).input j : ℕ) : ℝ)⁻¹) =
          (outer.input i : ℝ)⁻¹ + ((inner i).charge : ℝ) := by
      simpa only [div_eq_mul_inv, one_mul, hmatch i] using (inner i).reciprocal
    have ho := outer.reciprocal
    simp only [div_eq_mul_inv, one_mul] at ho
    simp_rw [hi, mul_add]
    rw [Finset.sum_add_distrib, ho]
    simp only [Int.cast_add, Int.cast_sum, Int.cast_mul, add_assoc]

/-- Exact composition of the realized floor carries for arbitrary signed
coefficients and independent inner arities. -/
theorem flatten_carry (outer : Certificate) (inner : Fin outer.arity → Certificate)
    (hmatch : ∀ i, (inner i).output = outer.input i) (n : ℕ) :
    (outer.flatten inner hmatch).carry n =
      outer.carry n + ∑ i, (outer.coeff i : ℝ) * (inner i).carry n := by
  have hi (i : Fin outer.arity) :
      (∑ j, ((inner i).coeff j : ℝ) * residueFraction ((inner i).input j) n) =
        residueFraction (outer.input i) n + (inner i).carry n := by
    have h := (inner i).carry_eq n
    rw [hmatch i] at h
    linarith
  rw [carry_eq, outer.carry_eq]
  change (∑ t, ((outer.coeff (leafEquiv outer inner t).1 *
      (inner (leafEquiv outer inner t).1).coeff (leafEquiv outer inner t).2 : ℤ) : ℝ) *
      residueFraction ((inner (leafEquiv outer inner t).1).input (leafEquiv outer inner t).2) n) -
      residueFraction outer.output n = _
  rw [sum_leaves outer inner (fun d => residueFraction d n)]
  simp_rw [hi, mul_add]
  rw [Finset.sum_add_distrib]
  ring

end Certificate
end RiemannResearch.RH.UniversalAtomCarry

namespace RiemannResearch.RH.CRTCarryArithmetic
open ArithmeticCumulative

/-- The reciprocal certificate of the expanded path retains every site charge,
with exactly the same downstream integer multipliers as the site floors. -/
theorem recursivePrimeCarry_reciprocal_charge (d : ℕ) (p : ℕ → ℕ) (a b t : ℕ → ℤ) (k : ℕ)
    (hd : 0 < d) (hp : ∀ i < k, 0 < p i)
    (hc : ∀ i < k, (a i : ℝ) * (p i : ℝ) + (b i : ℝ) * (carryConductor d p i : ℝ) =
      1 + (t i : ℝ) * (carryConductor d p i : ℝ) * (p i : ℝ)) :
    (∏ i ∈ Finset.range k, (a i : ℝ)) * (1 / (d : ℝ)) +
      ∑ i ∈ Finset.range k, (∏ j ∈ Finset.Ico (i + 1) k, (a j : ℝ)) *
        ((b i : ℝ) / (p i : ℝ)) =
      1 / (carryConductor d p k : ℝ) +
        ((∑ i ∈ Finset.range k, (∏ j ∈ Finset.Ico (i + 1) k, a j) * t i : ℤ) : ℝ) := by
  have recur (r : ℕ) (hr : r ≤ k) :
      carryFold (1 / (d : ℝ)) (fun i => (a i : ℝ)) (fun i => (b i : ℝ) / (p i : ℝ)) r =
        1 / (carryConductor d p r : ℝ) + ((carryFold (0 : ℤ) a t r : ℤ) : ℝ) := by
    induction r with
    | zero => simp [carryFold, carryConductor]
    | succ r ih =>
      have hrk : r < k := hr
      have hprev := ih (Nat.le_of_lt hrk)
      have hpos : 0 < carryConductor d p r := Nat.mul_pos hd
        (Finset.prod_pos (fun i hi => hp i ((Finset.mem_range.mp hi).trans hrk)))
      have hC : (carryConductor d p r : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hpos
      have hP : (p r : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt (hp r hrk)
      have hsucc : carryConductor d p (r + 1) = carryConductor d p r * p r := by
        simp [carryConductor, Finset.prod_range_succ, Nat.mul_assoc]
      have hsite : (a r : ℝ) * (1 / (carryConductor d p r : ℝ)) + (b r : ℝ) / (p r : ℝ) =
          1 / ((carryConductor d p r : ℝ) * (p r : ℝ)) + (t r : ℝ) := by
        field_simp [hC, hP]
        linear_combination hc r hrk
      rw [carryFold, carryFold, hprev, hsucc, Nat.cast_mul, Int.cast_add, Int.cast_mul]
      linear_combination hsite
  have h := recur k le_rfl
  rw [carryFold_eq_sum, carryFold_eq_sum] at h
  simpa only [mul_zero, zero_add] using h

/-- On an arbitrary finite CRT factor chain, expand both the raw argument and
its integer carries with their exact downstream multipliers. The one outer
floor is the sum of these transported local floors. -/
theorem recursivePrimeCarry_flattened (d : ℕ) (p : ℕ → ℕ) (a b t : ℕ → ℤ) (n k : ℕ)
    (hd : 0 < d) (hp : ∀ i < k, 0 < p i)
    (hc : ∀ i < k, (a i : ℝ) * (p i : ℝ) + (b i : ℝ) * (carryConductor d p i : ℝ) =
      1 + (t i : ℝ) * (carryConductor d p i : ℝ) * (p i : ℝ)) :
    let raw := (∏ i ∈ Finset.range k, (a i : ℝ)) * residueFraction d n +
      ∑ i ∈ Finset.range k, (∏ j ∈ Finset.Ico (i + 1) k, (a j : ℝ)) *
        ((b i : ℝ) * residueFraction (p i) n)
    let floors := ∑ i ∈ Finset.range k, (∏ j ∈ Finset.Ico (i + 1) k, a j) *
      carry (carryConductor d p i) (p i) (a i) (b i) n
    raw = residueFraction (carryConductor d p k) n + (floors : ℝ) ∧
      Int.fract raw = residueFraction (carryConductor d p k) n ∧ ⌊raw⌋ = floors := by
  dsimp only
  have hraw := carryFold_eq_sum (residueFraction d n) (fun i => (a i : ℝ))
    (fun i => (b i : ℝ) * residueFraction (p i) n) k
  have hfloors := carryFold_eq_sum (0 : ℤ) a
    (fun i => carry (carryConductor d p i) (p i) (a i) (b i) n) k
  simp only [mul_zero, zero_add] at hfloors
  have he := recursivePrimeCarry_exact d p a b t n k hd hp hc
  have hf := recursivePrimeCarry_fract_floor d p a b t n k hd hp hc
  dsimp only at hf
  rw [hraw, hfloors] at he hf
  exact ⟨he, hf⟩

end RiemannResearch.RH.CRTCarryArithmetic
