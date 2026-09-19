import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Elementary finite prime-product bounds

Source: the user-provided first-coordinate/tail-capacity continuation, Section 28,
for the application to the failed prime-sieve approximant. The proof of decay uses
Mathlib's classical divergence of the prime reciprocal series. The quantitative
lower bound is the elementary comparison with all positive integers congruent to
1 or 5 modulo 6, together with the explicit cubic inequality proved below.
No prime number theorem or asymptotic prime-product estimate is assumed.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace RiemannResearch.Analysis

/-- The finite Euler product over primes at most `Y`. -/
def finitePrimeProduct (Y : ℕ) : ℝ :=
  ∏ p ∈ Y.succ.primesBelow, (1 - 1 / (p : ℝ))

private def primeFactor (n : ℕ) : ℝ :=
  if Nat.Prime n then 1 - 1 / (n : ℝ) else 1

private theorem primeFactor_nonneg (n : ℕ) : 0 ≤ primeFactor n := by
  unfold primeFactor
  split_ifs with hn
  · have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn.one_lt.le
    have : (1 : ℝ) / n ≤ 1 := (div_le_one (by positivity)).mpr hnR
    linarith
  · norm_num

private theorem primeFactor_le_one (n : ℕ) : primeFactor n ≤ 1 := by
  unfold primeFactor
  split_ifs <;> have := (show (0 : ℝ) ≤ 1 / (n : ℝ) by positivity) <;> linarith

private theorem primeFactor_ge (n : ℕ) : 1 - 1 / (n : ℝ) ≤ primeFactor n := by
  unfold primeFactor
  split_ifs <;> have := (show (0 : ℝ) ≤ 1 / (n : ℝ) by positivity) <;> linarith

private theorem finitePrimeProduct_eq_range (Y : ℕ) :
    finitePrimeProduct Y = ∏ n ∈ Finset.range (Y+1), primeFactor n := by
  simp only [finitePrimeProduct, Nat.primesBelow, Finset.prod_filter, primeFactor,
    Nat.succ_eq_add_one]

theorem finitePrimeProduct_nonneg (Y : ℕ) : 0 ≤ finitePrimeProduct Y := by
  rw [finitePrimeProduct_eq_range]
  exact Finset.prod_nonneg (fun n _ => primeFactor_nonneg n)

theorem finitePrimeProduct_le_one (Y : ℕ) : finitePrimeProduct Y ≤ 1 := by
  rw [finitePrimeProduct_eq_range]
  exact Finset.prod_le_one (fun n _ => primeFactor_nonneg n)
    (fun n _ => primeFactor_le_one n)

theorem finitePrimeProduct_antitone : Antitone finitePrimeProduct := by
  apply antitone_nat_of_succ_le
  intro n
  simp only [finitePrimeProduct_eq_range, Nat.succ_eq_add_one, Finset.prod_range_succ]
  exact mul_le_of_le_one_right
    (mul_nonneg (Finset.prod_nonneg fun k _ => primeFactor_nonneg k)
      (primeFactor_nonneg n)) (primeFactor_le_one (n+1))

/-- Decay follows from Euler's divergent prime reciprocal sum, with no rate assumption. -/
theorem finitePrimeProduct_tendsto_zero :
    Tendsto finitePrimeProduct atTop (𝓝 0) := by
  let a : ℕ → ℝ := fun n => if Nat.Prime n then 1 / (n : ℝ) else 0
  have ha : ∀ n, 0 ≤ a n := by
    intro n
    simp only [a]
    split_ifs <;> positivity
  have hns : ¬ Summable a := by
    have hEq : a = {p : ℕ | Nat.Prime p}.indicator
        (fun n : ℕ => (1 : ℝ) / (n : ℝ)) := by
      funext n
      simp only [a, Set.indicator_apply, Set.mem_setOf_eq]
    rw [hEq]
    exact not_summable_one_div_on_primes
  have ht := (not_summable_iff_tendsto_nat_atTop_of_nonneg ha).mp hns
  have hs : Tendsto (fun Y => ∑ n ∈ Finset.range (Y+1), a n) atTop atTop :=
    ht.comp (tendsto_add_atTop_nat 1)
  have he : Tendsto (fun Y => Real.exp (-(∑ n ∈ Finset.range (Y+1), a n)))
      atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hs
  apply squeeze_zero (fun Y => finitePrimeProduct_nonneg Y) _ he
  intro Y
  rw [finitePrimeProduct_eq_range, ← Finset.sum_neg_distrib, Real.exp_sum]
  apply Finset.prod_le_prod (fun n _ => primeFactor_nonneg n)
  intro n _
  have h := Real.add_one_le_exp (-a n)
  by_cases hn : Nat.Prime n
  · simpa [a, primeFactor, hn, add_comm, sub_eq_add_neg] using h
  · simp [a, primeFactor, hn]

/-- A pair of reciprocal factors at the two reduced residue classes modulo six. -/
def sixthPair (j : ℕ) : ℝ :=
  (6 * (j : ℝ) / (6 * j + 1)) * ((6 * j + 4) / (6 * j + 5))

theorem sixthPair_nonneg (j : ℕ) : 0 ≤ sixthPair j := by
  unfold sixthPair
  positivity

/-- The cubic comparison has a positive polynomial numerator. -/
theorem sixthPair_cube (j : ℕ) (hj : 1 ≤ j) :
    2 * (j : ℝ) - 1 ≤ sixthPair j ^ 3 * (2 * j + 1) := by
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hden : 0 < (6 * (j : ℝ) + 1) * (6 * j + 5) := by positivity
  have hn :
      0 ≤ 125 + 2450 * (j : ℝ) + 16740 * (j : ℝ)^2 +
        55080 * (j : ℝ)^3 + 78192 * (j : ℝ)^4 + 38880 * (j : ℝ)^5 := by
    positivity
  have hid :
      (6 * (j : ℝ) * (6 * j + 4))^3 * (2 * j + 1) -
        (2 * j - 1) * ((6 * j + 1) * (6 * j + 5))^3 =
      125 + 2450 * (j : ℝ) + 16740 * (j : ℝ)^2 +
        55080 * (j : ℝ)^3 + 78192 * (j : ℝ)^4 + 38880 * (j : ℝ)^5 := by
    ring
  unfold sixthPair
  rw [div_mul_div_comm, div_pow, div_mul_eq_mul_div]
  exact (le_div_iff₀ (pow_pos hden 3)).mpr (by nlinarith [hn])

private def sixthProduct (m : ℕ) : ℝ :=
  ∏ j ∈ Finset.range m, sixthPair (j+1)

private theorem sixthProduct_nonneg (m : ℕ) : 0 ≤ sixthProduct m := by
  exact Finset.prod_nonneg fun j _ => sixthPair_nonneg (j+1)

/-- The cubic pair inequalities telescope without a logarithmic approximation. -/
theorem sixthProduct_cube (m : ℕ) :
    1 ≤ (sixthProduct m)^3 * (2 * (m : ℝ) + 1) := by
  induction m with
  | zero => norm_num [sixthProduct]
  | succ m ih =>
      have hp := sixthPair_cube (m+1) (by omega)
      have hm := sixthProduct_nonneg m
      calc
        1 ≤ sixthProduct m ^ 3 * (2 * (m : ℝ) + 1) := ih
        _ = sixthProduct m ^ 3 * (2 * ((m+1 : ℕ) : ℝ) - 1) := by push_cast; ring
        _ ≤ sixthProduct m ^ 3 *
            (sixthPair (m+1)^3 * (2 * ((m+1 : ℕ) : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left hp (pow_nonneg hm 3)
        _ = _ := by
          simp only [sixthProduct, Nat.succ_eq_add_one, Finset.prod_range_succ,
            Nat.cast_add, Nat.cast_one]
          ring

private theorem primeFactor_eq_one_of_dvd {n d : ℕ} (hd : d ∣ n)
    (hd1 : d ≠ 1) (hdn : d ≠ n) : primeFactor n = 1 := by
  have hn : ¬ Nat.Prime n := by
    intro h
    rcases (Nat.dvd_prime h).mp hd with h | h
    · exact hd1 h
    · exact hdn h
  simp [primeFactor, hn]

private theorem primeProduct_six_step (m : ℕ) :
    finitePrimeProduct (6*m+5) * sixthPair (m+1) ≤
      finitePrimeProduct (6*(m+1)+5) := by
  have h0 : primeFactor (6*m+6) = 1 := primeFactor_eq_one_of_dvd
    (show 2 ∣ 6*m+6 from ⟨3*m+3, by omega⟩) (by decide) (by omega)
  have h2 : primeFactor (6*m+8) = 1 := primeFactor_eq_one_of_dvd
    (show 2 ∣ 6*m+8 from ⟨3*m+4, by omega⟩) (by decide) (by omega)
  have h3 : primeFactor (6*m+9) = 1 := primeFactor_eq_one_of_dvd
    (show 3 ∣ 6*m+9 from ⟨2*m+3, by omega⟩) (by decide) (by omega)
  have h4 : primeFactor (6*m+10) = 1 := primeFactor_eq_one_of_dvd
    (show 2 ∣ 6*m+10 from ⟨3*m+5, by omega⟩) (by decide) (by omega)
  have he :
      finitePrimeProduct (6*(m+1)+5) =
        finitePrimeProduct (6*m+5) * primeFactor (6*m+7) * primeFactor (6*m+11) := by
    rw [finitePrimeProduct_eq_range]
    rw [show 6*(m+1)+5+1 = (6*m+5+1)+1+1+1+1+1+1 by omega]
    rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ,
      Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ]
    simp only [show 6*m+5+1 = 6*m+6 by omega,
      show 6*m+5+1+1 = 6*m+7 by omega,
      show 6*m+5+1+1+1 = 6*m+8 by omega,
      show 6*m+5+1+1+1+1 = 6*m+9 by omega,
      show 6*m+5+1+1+1+1+1 = 6*m+10 by omega,
      show 6*m+5+1+1+1+1+1+1 = 6*m+11 by omega,
      h0, h2, h3, h4, mul_one, finitePrimeProduct_eq_range]
  have h7 : 0 ≤ 1 - 1 / ((6*m+7 : ℕ) : ℝ) := by
    have hR : (1 : ℝ) ≤ ((6*m+7 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ 6*m+7 by omega)
    have h := (div_le_one (by positivity : (0 : ℝ) < ((6*m+7 : ℕ) : ℝ))).mpr hR
    linarith
  have h11 : 0 ≤ 1 - 1 / ((6*m+11 : ℕ) : ℝ) := by
    have hR : (1 : ℝ) ≤ ((6*m+11 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ 6*m+11 by omega)
    have h := (div_le_one (by positivity : (0 : ℝ) < ((6*m+11 : ℕ) : ℝ))).mpr hR
    linarith
  have hpair :
      sixthPair (m+1) =
        (1 - 1 / ((6*m+7 : ℕ) : ℝ)) * (1 - 1 / ((6*m+11 : ℕ) : ℝ)) := by
    unfold sixthPair
    push_cast
    field_simp
    ring
  rw [he, hpair, mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul (primeFactor_ge _) (primeFactor_ge _) h11 (primeFactor_nonneg _))
      (finitePrimeProduct_nonneg _)

theorem finitePrimeProduct_six_lower (m : ℕ) :
    (4 / 15 : ℝ) * sixthProduct m ≤ finitePrimeProduct (6*m+5) := by
  induction m with
  | zero =>
      norm_num [sixthProduct, finitePrimeProduct_eq_range, primeFactor,
        Finset.prod_range_succ]
  | succ m ih =>
      calc
        (4 / 15 : ℝ) * sixthProduct (m+1) =
            ((4 / 15 : ℝ) * sixthProduct m) * sixthPair (m+1) := by
          simp only [sixthProduct, Finset.prod_range_succ]
          ring
        _ ≤ finitePrimeProduct (6*m+5) * sixthPair (m+1) :=
          mul_le_mul_of_nonneg_right ih (sixthPair_nonneg _)
        _ ≤ _ := primeProduct_six_step m

/-- A completely explicit cubic lower bound valid at every cutoff. -/
theorem finitePrimeProduct_cube_lower (Y : ℕ) :
    (4 / 15 : ℝ)^3 ≤ (finitePrimeProduct Y)^3 * (2 * (Y : ℝ) + 1) := by
  have hs := finitePrimeProduct_six_lower Y
  have hm := finitePrimeProduct_antitone (show Y ≤ 6*Y+5 by omega)
  have hle : (4 / 15 : ℝ) * sixthProduct Y ≤ finitePrimeProduct Y := hs.trans hm
  have hy := sixthProduct_nonneg Y
  have hcube := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (4/15)*sixthProduct Y) hle 3
  have ht := sixthProduct_cube Y
  have hpos : (0 : ℝ) ≤ 2 * (Y : ℝ) + 1 := by positivity
  have hmul := mul_le_mul_of_nonneg_right hcube hpos
  have ht' := mul_le_mul_of_nonneg_left ht (by norm_num : (0 : ℝ) ≤ (4/15)^3)
  nlinarith [hmul, ht']

/-- The retained head energy grows despite pointwise prime-product decay. -/
theorem finitePrimeProduct_square_mul_tendsto_atTop :
    Tendsto (fun Y => finitePrimeProduct Y ^ 2 * (Y : ℝ)) atTop atTop := by
  have hc : (0 : ℝ) < ((4/15)^3/3)^2 := by norm_num
  have ht : Tendsto (fun Y : ℕ => ((4/15 : ℝ)^3/3)^2 * (Y : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hc
  apply tendsto_atTop.2
  intro b
  filter_upwards [ht.eventually (eventually_ge_atTop ((max b 0)^3)),
    eventually_ge_atTop 1] with Y hY hY1
  have hYR : (1 : ℝ) ≤ Y := by exact_mod_cast hY1
  have hp := finitePrimeProduct_nonneg Y
  have hprod := finitePrimeProduct_cube_lower Y
  have hbase : (4 / 15 : ℝ)^3 / 3 ≤ finitePrimeProduct Y ^ 3 * (Y : ℝ) := by
    have h3 : 0 ≤ finitePrimeProduct Y ^ 3 := pow_nonneg hp 3
    have hmono := mul_nonneg h3 (sub_nonneg.mpr hYR)
    nlinarith
  have hsquare := sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ (4/15)^3/3)
    (by positivity : (0 : ℝ) ≤ finitePrimeProduct Y^3 * (Y : ℝ))
  have hsq := hsquare.mpr hbase
  have hrate := mul_le_mul_of_nonneg_right hsq (by positivity : (0 : ℝ) ≤ Y)
  have hh : (max b 0)^3 ≤ (finitePrimeProduct Y ^ 2 * (Y : ℝ))^3 := by
    nlinarith [hY, hrate]
  have hroot : max b 0 ≤ finitePrimeProduct Y ^ 2 * (Y : ℝ) := by
    by_contra h
    have hlt : finitePrimeProduct Y ^ 2 * (Y : ℝ) < max b 0 := lt_of_not_ge h
    have hcub := pow_lt_pow_left₀ hlt
      (by positivity : (0 : ℝ) ≤ finitePrimeProduct Y^2*(Y:ℝ))
      (by decide : (3 : ℕ) ≠ 0)
    linarith
  exact (le_max_left b 0).trans hroot

end RiemannResearch.Analysis
