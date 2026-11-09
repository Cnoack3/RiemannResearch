import RiemannResearch.RH.ChebyshevEnergyCriterion
import RiemannResearch.Analysis.NatStepIntegral
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Discrete damped Pareto energy of the Chebyshev error

The discrete weight n^(-a)/(n(n+1)) is comparable, with constants 1 and 2,
to n^(-2-a). Unit-cell estimates transfer summability to the actual
continuous Chebyshev energy. All positive damping therefore implies RH
through ChebyshevEnergyCriterion's proved Mellin pole exclusion.
This file does not assert RH implies these energy bounds.
-/

noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators
namespace RiemannResearch.RH.ChebyshevDiscreteEnergy
open ChebyshevMellin

def powerTerm (a : ℝ) (n : ℕ) : ℝ :=
  (Chebyshev.psi (n : ℝ) - (n : ℝ)) ^ 2 * (n : ℝ) ^ (-2-a)

def paretoTerm (a : ℝ) (n : ℕ) : ℝ :=
  (Chebyshev.psi (n : ℝ) - (n : ℝ)) ^ 2 * (n : ℝ) ^ (-a) /
    ((n : ℝ) * ((n : ℝ)+1))

theorem powerTerm_nonneg (a : ℝ) (n : ℕ) : 0 ≤ powerTerm a n :=
  mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem paretoTerm_nonneg (a : ℝ) (n : ℕ) : 0 ≤ paretoTerm a n := by
  unfold paretoTerm
  positivity

theorem powerTerm_eq_div (a : ℝ) {n : ℕ} (hn : 0 < n) :
    powerTerm a n =
      (Chebyshev.psi (n : ℝ) - (n : ℝ)) ^ 2 * (n : ℝ) ^ (-a) /
        (n : ℝ)^2 := by
  unfold powerTerm
  rw [show -2-a = -a-2 by ring, Real.rpow_sub (Nat.cast_pos.mpr hn), Real.rpow_two]
  ring

theorem paretoTerm_le_powerTerm (a : ℝ) (n : ℕ) :
    paretoTerm a n ≤ powerTerm a n := by
  by_cases hn : n = 0
  · subst n
    simp [paretoTerm, powerTerm, Chebyshev.psi_eq_zero_iff.mpr (by norm_num : (0:ℝ)<2)]
  rw [powerTerm_eq_div a (Nat.pos_of_ne_zero hn)]
  unfold paretoTerm
  have hpos : (0:ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  apply div_le_div_of_nonneg_left
  · positivity
  · positivity
  · nlinarith

theorem powerTerm_le_twice_paretoTerm (a : ℝ) (n : ℕ) :
    powerTerm a n ≤ 2 * paretoTerm a n := by
  by_cases hn : n = 0
  · subst n
    simp [paretoTerm, powerTerm, Chebyshev.psi_eq_zero_iff.mpr (by norm_num : (0:ℝ)<2)]
  rw [powerTerm_eq_div a (Nat.pos_of_ne_zero hn)]
  unfold paretoTerm
  have hpos : (0:ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hone : (1:ℝ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
  have hA : 0 ≤ (Chebyshev.psi (n : ℝ) - (n : ℝ)) ^ 2 * (n : ℝ) ^ (-a) := by positivity
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [mul_nonneg hA (show 0 ≤ (n:ℝ)^2-(n:ℝ) by nlinarith)]

theorem summable_power_iff_pareto (a : ℝ) :
    Summable (powerTerm a) ↔ Summable (paretoTerm a) := by
  constructor
  · intro h
    exact Summable.of_nonneg_of_le (paretoTerm_nonneg a) (paretoTerm_le_powerTerm a) h
  · intro h
    exact Summable.of_nonneg_of_le (powerTerm_nonneg a)
      (powerTerm_le_twice_paretoTerm a) (h.mul_left 2)

theorem cell_error_bound {x : ℝ} (hx : 1 < x) :
    (Chebyshev.psi x-x)^2 ≤
      2 * ((Chebyshev.psi (⌊x⌋₊ : ℝ) - (⌊x⌋₊ : ℝ))^2+1) := by
  have hl := Nat.floor_le (show 0 ≤ x by linarith)
  have hu := Nat.lt_floor_add_one x
  rw [Chebyshev.psi_eq_psi_coe_floor]
  nlinarith [sq_nonneg (Chebyshev.psi (⌊x⌋₊ : ℝ) - (⌊x⌋₊ : ℝ) +
    (x-(⌊x⌋₊ : ℝ))), sq_nonneg (x-(⌊x⌋₊ : ℝ)),
    mul_nonneg (show 0 ≤ x-(⌊x⌋₊ : ℝ) by linarith)
      (show 0 ≤ 1-(x-(⌊x⌋₊ : ℝ)) by linarith)]

theorem continuousEnergy_of_summable_power {a : ℝ} (ha : 0 < a)
    (h : Summable (powerTerm a)) : ErrorFiniteEnergy (1+a) := by
  let b : ℕ → ℝ := fun n => 2 * (powerTerm a n + (n:ℝ)^(-2-a))
  have hb : Summable b :=
    (h.add (Real.summable_nat_rpow.mpr (by linarith : -2-a < -1))).mul_left 2
  have hi := (RiemannResearch.Analysis.natStep_integrable_Ici b hb).mono_set
    (show Ioi (1:ℝ) ⊆ Ici 0 by intro x hx; simp only [mem_Ioi, mem_Ici] at *; linarith)
  unfold ErrorFiniteEnergy
  have hm : Measurable (fun x : ℝ => (Chebyshev.psi x-x)^2*x^(-(1+a)-1)) :=
    ((psi_measurable.sub measurable_id).pow_const 2).mul (measurable_id.pow_const _)
  apply hi.mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx1 : 1 < x := hx
  have hn : 0 < (⌊x⌋₊ : ℝ) := by
    have hh := (Nat.one_le_floor_iff x).mpr hx1.le
    exact_mod_cast (show 0 < ⌊x⌋₊ by omega)
  have hp := Real.rpow_le_rpow_of_nonpos hn
    (Nat.floor_le (by linarith : 0 ≤ x)) (show -2-a ≤ 0 by linarith)
  rw [Real.norm_of_nonneg (by positivity), show -(1+a)-1 = -2-a by ring]
  calc
    _ ≤ (2 * ((Chebyshev.psi (⌊x⌋₊ : ℝ)-(⌊x⌋₊ : ℝ))^2+1)) * x^(-2-a) :=
      mul_le_mul_of_nonneg_right (cell_error_bound hx1) (Real.rpow_nonneg (by linarith) _)
    _ ≤ (2 * ((Chebyshev.psi (⌊x⌋₊ : ℝ)-(⌊x⌋₊ : ℝ))^2+1)) * (⌊x⌋₊ : ℝ)^(-2-a) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = b ⌊x⌋₊ := by dsimp [b, powerTerm]; ring

theorem continuousEnergy_of_summable_pareto {a : ℝ} (ha : 0 < a)
    (h : Summable (paretoTerm a)) : ErrorFiniteEnergy (1+a) :=
  continuousEnergy_of_summable_power ha ((summable_power_iff_pareto a).mpr h)

theorem riemannHypothesis_of_all_discrete_pareto_damping
    (h : ∀ a : ℝ, 0 < a → Summable (paretoTerm a)) : RiemannHypothesis :=
  riemannHypothesis_of_all_chebyshev_damping
    (fun a ha => continuousEnergy_of_summable_pareto ha (h a ha))

end RiemannResearch.RH.ChebyshevDiscreteEnergy
