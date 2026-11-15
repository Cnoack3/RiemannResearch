import RiemannResearch.RH.WeilExplicitFormula.FromPNTPlus.Mertens
import Mathlib.NumberTheory.Primorial
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
/-!
# Elementary lower bounds for the finite prime density

The exact finite Euler product is positive, at most one, and has a logarithm
bounded below by -(log N)/6 minus one absolute constant. Consequently
N * density(N)^3 tends to infinity.

The arithmetic input is the already checked elementary first Mertens theorem
in FromPNTPlus.Mertens. Source for that input and its proof strategy:
Leo Goldmakher, "A quick proof of Mertens' theorem",
https://web.williams.edu/Mathematics/lg5/mertens.pdf.
The weaker product consequence here is derived directly by splitting at a
fixed prime cutoff; neither RH nor Mertens' third theorem is assumed.
Its consumer is the uniform primorial-cutoff source obstruction.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.PrimorialDensity
def density (N : ℕ) : ℝ := ∏ p ∈ N.primesLE, (1 - 1/(p : ℝ))
theorem factor_pos (p : ℕ) (hp : Nat.Prime p) : 0 < (1 : ℝ) - 1/(p : ℝ) := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  exact sub_pos.mpr ((div_lt_one (by linarith : (0 : ℝ) < p)).mpr hpR)
theorem density_pos (N : ℕ) : 0 < density N :=
  Finset.prod_pos (fun p hp => factor_pos p (Nat.prime_of_mem_primesLE hp))
theorem density_le_one (N : ℕ) : density N ≤ 1 := by
  apply Finset.prod_le_one
  · intro p hp
    exact (factor_pos p (Nat.prime_of_mem_primesLE hp)).le
  · intro p hp
    have : 0 ≤ 1/(p : ℝ) := by positivity
    linarith
theorem factor_neg_log_le (p : ℕ) (hp : Nat.Prime p) :
    -Real.log (1-1/(p : ℝ)) ≤ 2/(p : ℝ) := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hf := factor_pos p hp
  have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hf)
  rw [Real.log_inv] at hlog
  have hi : (1-1/(p : ℝ))⁻¹ - 1 = 1/((p : ℝ)-1) := by
    field_simp [show (p : ℝ) ≠ 0 by linarith,
      show (p : ℝ)-1 ≠ 0 by linarith]
    ring
  rw [hi] at hlog
  apply hlog.trans
  apply (div_le_div_iff₀ (by linarith : 0 < (p : ℝ)-1) (by linarith : (0 : ℝ) < p)).mpr
  linarith
theorem prime_log_sum_le (N : ℕ) (hN : 1 ≤ N) :
    (∑ p ∈ N.primesLE, Real.log (p : ℝ)/(p : ℝ)) ≤ Real.log (N : ℝ) + Real.log 4 + 4 := by
  have hm := Mertens.E₁Λ.le (x := (N : ℝ)) (by exact_mod_cast hN)
  simp only [Mertens.E₁Λ, Nat.floor_natCast] at hm
  have hp : (∑ p ∈ N.primesLE, Real.log (p : ℝ)/(p : ℝ)) ≤
      ∑ n ∈ Finset.Ioc 0 N, ArithmeticFunction.vonMangoldt n / (n : ℝ) := by
    calc
      _ = ∑ p ∈ N.primesLE, ArithmeticFunction.vonMangoldt p / (p : ℝ) := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [ArithmeticFunction.vonMangoldt_apply_prime (Nat.prime_of_mem_primesLE hp)]
      _ ≤ _ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          obtain ⟨hpn, hpp⟩ := Nat.mem_primesLE.mp hp
          exact Finset.mem_Ioc.mpr ⟨hpp.pos, hpn⟩
        · intro n hn hnp
          positivity
  linarith
/-- A weak subpolynomial lower bound, sufficient for the source obstruction.
The proof uses only the existing elementary Mertens first-theorem bound. -/
theorem exists_log_density_lower :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      -Real.log (N : ℝ)/6 - C ≤ Real.log (density N) := by
  obtain ⟨B, hB⟩ := exists_nat_gt (Real.exp 12)
  have hB0 : (0 : ℝ) < B := (Real.exp_pos 12).trans hB
  have hBlog : (12 : ℝ) ≤ Real.log (B : ℝ) := by
    have := Real.log_le_log (Real.exp_pos 12) hB.le
    simpa using this
  let C := (∑ p ∈ B.primesLE, 2/(p : ℝ)) + (Real.log 4 + 4)/6
  refine ⟨C, ?_⟩
  intro N hN
  have hlog : -Real.log (density N) ≤ ∑ p ∈ N.primesLE, 2/(p : ℝ) := by
    rw [density, Real.log_prod (fun p hp => (factor_pos p (Nat.prime_of_mem_primesLE hp)).ne'),
      ← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum (fun p hp => factor_neg_log_le p (Nat.prime_of_mem_primesLE hp))
  have hpoint (p : ℕ) (hp : p ∈ N.primesLE) :
      2/(p : ℝ) ≤ (if p ≤ B then 2/(p : ℝ) else 0) +
        Real.log (p : ℝ)/(6*(p : ℝ)) := by
    have hpr := Nat.prime_of_mem_primesLE hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpr.pos
    by_cases hb : p ≤ B
    · rw [if_pos hb]
      have : 0 ≤ Real.log (p : ℝ)/(6*(p : ℝ)) :=
        div_nonneg (Real.log_nonneg (by exact_mod_cast hpr.one_le)) (by positivity)
      linarith
    · rw [if_neg hb, zero_add]
      have hBpR : (B : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : B ≤ p)
      have hplog := hBlog.trans (Real.log_le_log hB0 hBpR)
      apply (div_le_div_iff₀ hp0 (by positivity : 0 < 6*(p : ℝ))).mpr
      nlinarith
  have hsmall : (∑ p ∈ N.primesLE, if p ≤ B then 2/(p : ℝ) else 0) ≤
      ∑ p ∈ B.primesLE, 2/(p : ℝ) := by
    rw [← Finset.sum_filter]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hpN, hpB⟩ := Finset.mem_filter.mp hp
      exact Nat.mem_primesLE.mpr ⟨hpB, Nat.prime_of_mem_primesLE hpN⟩
    · intro p hp hpn
      positivity
  have hsplit := Finset.sum_le_sum hpoint
  rw [Finset.sum_add_distrib] at hsplit
  have hlarge : (∑ p ∈ N.primesLE, Real.log (p : ℝ)/(6*(p : ℝ))) =
      (∑ p ∈ N.primesLE, Real.log (p : ℝ)/(p : ℝ))/6 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  rw [hlarge] at hsplit
  have hprime := prime_log_sum_le N hN
  dsimp [C]
  linarith
theorem density_cube_growth :
    Tendsto (fun N : ℕ => (N : ℝ) * density N ^ 3) atTop atTop := by
  obtain ⟨C, hC⟩ := exists_log_density_lower
  have htlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)/2 - 3*C) atTop atTop :=
    by
      simpa only [Function.comp_def, sub_eq_add_neg] using
        tendsto_atTop_add_const_right atTop (-(3*C))
        ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).atTop_div_const
          (by norm_num : (0 : ℝ) < 2))
  have hbound : ∀ᶠ N : ℕ in atTop,
      Real.exp (Real.log (N : ℝ)/2 - 3*C) ≤ (N : ℝ) * density N ^ 3 := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hn0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have ha := density_pos N
    apply (Real.log_le_log_iff (Real.exp_pos _) (by positivity : 0 < (N : ℝ)*density N^3)).mp
    rw [Real.log_exp, Real.log_mul hn0.ne' (by positivity : density N^3 ≠ 0), Real.log_pow]
    linarith [hC N hN]
  exact tendsto_atTop_mono' atTop hbound (Real.tendsto_exp_atTop.comp htlog)
end RiemannResearch.RH.PrimorialDensity
