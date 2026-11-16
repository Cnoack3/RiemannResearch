import RiemannResearch.NumberTheory.DivisorIncidence
import RiemannResearch.RH.ArithmeticCumulativeBasic
import RiemannResearch.RH.ExactHeadGreenProfile
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic

/-!
# Exact cumulative gcd-atom and floor change of basis
Source: user-provided "Exact-Head Green Profiles in the Nyman--Beurling Program",
27 July 2026. The finite arithmetic bridge uses the repository's divisor
incidence inversion. Both directions and equality of every upper span hold
for arbitrary positive periods; squarefreeness is not required.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.ExactHeadGcdAtoms
open RiemannResearch.NumberTheory.DivisorIncidence
open RiemannResearch.RH.ArithmeticCumulative
open RiemannResearch.RH.ExactHeadGreenProfile

def atom (P d r : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 r, if Nat.gcd n P = d then 1 else 0

theorem atom_eq_moebius_grid_sum (P d r : ℕ) (hP : P ≠ 0)
    (hd : d ∈ P.divisors) :
    atom P d r = ∑ e ∈ P.divisors,
      if d ∣ e then (ArithmeticFunction.moebius (e / d) : ℝ) * grid e r else 0 := by
  have heq (e : ℕ) (he : e ∈ P.divisors) :
      (∑ n ∈ Finset.Icc 1 r, if e ∣ n then (1 : ℝ) else 0) = grid e r := by
    rw [sum_Icc_one]
    exact cumulative_divisorIndicator e r (Nat.pos_of_mem_divisors he)
  simpa only [atom, Finset.sum_filter] using
    gcd_class_charge_moebius P hP (Finset.Icc 1 r) (fun _ => 1)
      (fun e => grid e r) heq d hd

theorem grid_eq_atom_sum (P d r : ℕ) (hP : P ≠ 0)
    (hd : d ∈ P.divisors) :
    grid d r = ∑ e ∈ P.divisors, if d ∣ e then atom P e r else 0 := by
  have hg (n : ℕ) : Nat.gcd n P ∈ P.divisors :=
    Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right n P, hP⟩
  have hi (n : ℕ) :
      (∑ e ∈ P.divisors, if d ∣ e then
        (if Nat.gcd n P = e then (1 : ℝ) else 0) else 0) =
          if d ∣ n then 1 else 0 := by
    calc
      _ = ∑ e ∈ P.divisors,
          if Nat.gcd n P = e then (if d ∣ e then (1 : ℝ) else 0) else 0 := by
        apply Finset.sum_congr rfl
        intro e he
        split_ifs <;> rfl
      _ = if d ∣ Nat.gcd n P then 1 else 0 := by simp [hg n]
      _ = _ := by simp [Nat.dvd_gcd_iff, Nat.dvd_of_mem_divisors hd]
  calc
    grid d r = ∑ n ∈ Finset.Icc 1 r, if d ∣ n then (1 : ℝ) else 0 := by
      rw [sum_Icc_one]
      exact (cumulative_divisorIndicator d r (Nat.pos_of_mem_divisors hd)).symm
    _ = ∑ n ∈ Finset.Icc 1 r, ∑ e ∈ P.divisors,
          if d ∣ e then (if Nat.gcd n P = e then (1 : ℝ) else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      exact (hi n).symm
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e he
      by_cases hde : d ∣ e <;> simp [hde, atom]

def upperDivisors (P x : ℕ) : Finset ℕ :=
  P.divisors.filter (fun d => x < d)

def upperSpan (P x : ℕ) (a : ℕ → ℕ → ℝ) : Submodule ℝ (ℕ → ℝ) :=
  Submodule.span ℝ (a '' (upperDivisors P x : Set ℕ))

theorem upper_grid_mem_atom_span (P x d : ℕ) (hP : P ≠ 0)
    (hd : d ∈ upperDivisors P x) :
    grid d ∈ upperSpan P x (atom P) := by
  have hdP := (Finset.mem_filter.mp hd).1
  have hxd := (Finset.mem_filter.mp hd).2
  have heq : grid d = ∑ e ∈ P.divisors,
      if d ∣ e then atom P e else 0 := by
    funext r
    simpa only [Finset.sum_apply, Pi.zero_apply, ite_apply] using
      grid_eq_atom_sum P d r hP hdP
  rw [heq]
  apply Submodule.sum_mem
  intro e he
  by_cases hde : d ∣ e
  · rw [if_pos hde]
    apply Submodule.subset_span
    refine ⟨e, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨he,
      hxd.trans_le (Nat.le_of_dvd (Nat.pos_of_mem_divisors he) hde)⟩
  · rw [if_neg hde]
    exact Submodule.zero_mem _

theorem upper_atom_mem_grid_span (P x d : ℕ) (hP : P ≠ 0)
    (hd : d ∈ upperDivisors P x) :
    atom P d ∈ upperSpan P x grid := by
  have hdP := (Finset.mem_filter.mp hd).1
  have hxd := (Finset.mem_filter.mp hd).2
  have heq : atom P d = ∑ e ∈ P.divisors,
      if d ∣ e then (ArithmeticFunction.moebius (e / d) : ℝ) • grid e else 0 := by
    funext r
    simpa only [Finset.sum_apply, Pi.zero_apply, ite_apply, Pi.smul_apply, smul_eq_mul] using
      atom_eq_moebius_grid_sum P d r hP hdP
  rw [heq]
  apply Submodule.sum_mem
  intro e he
  by_cases hde : d ∣ e
  · rw [if_pos hde]
    apply Submodule.smul_mem
    apply Submodule.subset_span
    refine ⟨e, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨he,
      hxd.trans_le (Nat.le_of_dvd (Nat.pos_of_mem_divisors he) hde)⟩
  · rw [if_neg hde]
    exact Submodule.zero_mem _

theorem upper_spans_eq (P x : ℕ) (hP : P ≠ 0) :
    upperSpan P x (atom P) = upperSpan P x grid := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨d,hd,rfl⟩
    exact upper_atom_mem_grid_span P x d hP hd
  · apply Submodule.span_le.mpr
    rintro _ ⟨d,hd,rfl⟩
    exact upper_grid_mem_atom_span P x d hP hd

theorem atom_one_eq_moebius_grid (P r : ℕ) (hP : P ≠ 0) :
    atom P 1 r = ∑ e ∈ P.divisors, (ArithmeticFunction.moebius e : ℝ) * grid e r := by
  simpa using atom_eq_moebius_grid_sum P 1 r hP (Nat.one_mem_divisors.mpr hP)

end RiemannResearch.RH.ExactHeadGcdAtoms
