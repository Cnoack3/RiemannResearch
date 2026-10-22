import RiemannResearch.RH.NymanConductorArithmetic
import RiemannResearch.RH.ParetoResidueDuality
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Closed Möbius/power coefficients of the actual conductor inverse

Möbius inversion turns the actual conductor coefficients into a first-order
arithmetic dilation recurrence. Iterating that exact recurrence gives the
finite geometric formula for the already constructed Dirichlet inverse.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH

private def arithmeticDilation (n : ℕ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ where
  toFun k := if n ∣ k then f (k / n) else 0
  map_zero' := by simp

private theorem arithmeticDilation_apply (n k : ℕ) (f : ArithmeticFunction ℝ) :
    arithmeticDilation n f k = if n ∣ k then f (k/n) else 0 := rfl

private theorem mobius_restrictedDivisors {n k : ℕ} (hk : k ≠ 0) (hnk : n ∣ k) :
    k.divisors.filter (fun d => n ∣ k/d) = (k/n).divisors := by
  have hquot : k/n ∣ k := ⟨n, (Nat.div_mul_cancel hnk).symm⟩
  calc
    k.divisors.filter (fun d => n ∣ k/d) = k.divisors.filter (fun d => d ∣ k/n) := by
      apply Finset.filter_congr
      intro d hd
      rw [Nat.dvd_div_iff_mul_dvd (Nat.dvd_of_mem_divisors hd),
        Nat.dvd_div_iff_mul_dvd hnk, Nat.mul_comm d n]
    _ = (k/n).divisors := Nat.divisors_filter_dvd_of_dvd hk hquot

/-- Actual Dirichlet convolution commutes with arithmetic dilation. -/
private theorem mul_arithmeticDilation (f g : ArithmeticFunction ℝ) (n : ℕ) :
    f * arithmeticDilation n g = arithmeticDilation n (f*g) := by
  ext k
  by_cases hk : k = 0
  · subst k
    simp
  rw [arithmeticDilation_apply, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b => f a * arithmeticDilation n g b)]
  by_cases hnk : n ∣ k
  · rw [if_pos hnk]
    calc
      (∑ d ∈ k.divisors, f d * arithmeticDilation n g (k/d)) =
          ∑ d ∈ k.divisors.filter (fun d => n ∣ k/d), f d * g ((k/n)/d) := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro d hd
        by_cases hnd : n ∣ k/d
        · simp [arithmeticDilation_apply, hnd, Nat.div_div_eq_div_mul, Nat.mul_comm]
        · simp [arithmeticDilation_apply, hnd]
      _ = (f*g) (k/n) := by
        rw [mobius_restrictedDivisors hk hnk, ArithmeticFunction.mul_apply,
          Nat.sum_divisorsAntidiagonal (fun a b => f a * g b)]
  · rw [if_neg hnk]
    apply Finset.sum_eq_zero
    intro d hd
    have hnd : ¬ n ∣ k/d := by
      intro h
      have hquot : k/d ∣ k := ⟨d, (Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)).symm⟩
      exact hnk (h.trans hquot)
    simp [arithmeticDilation_apply, hnd]

private theorem nymanConductorBeta_eq_zeta_dilation (n : ℕ) :
    nymanConductorBeta n =
      (1/(n:ℝ)) • (ArithmeticFunction.zeta : ArithmeticFunction ℝ) -
        arithmeticDilation n (ArithmeticFunction.zeta : ArithmeticFunction ℝ) := by
  ext k
  by_cases hk : k = 0
  · subst k
    simp
  rw [nymanConductorBeta_apply hk]
  change 1/(n:ℝ) - (if n ∣ k then 1 else 0) =
    ((1/(n:ℝ)) • (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) k -
      arithmeticDilation n (ArithmeticFunction.zeta : ArithmeticFunction ℝ) k
  simp only [ArithmeticFunction.smul_map, smul_eq_mul,
    arithmeticDilation_apply, ArithmeticFunction.natCoe_apply,
    ArithmeticFunction.zeta_apply_ne hk, Nat.cast_one, mul_one]
  by_cases hnk : n ∣ k
  · have hq : k/n ≠ 0 := by
      intro h
      exact hk (by simpa [h] using (Nat.div_mul_cancel hnk).symm)
    simp [hnk, ArithmeticFunction.zeta_apply_ne hq]
  · simp [hnk]

private theorem moebius_mul_nymanConductorBeta (n : ℕ) :
    (ArithmeticFunction.moebius : ArithmeticFunction ℝ) * nymanConductorBeta n =
      (1/(n:ℝ)) • (1 : ArithmeticFunction ℝ) - arithmeticDilation n 1 := by
  rw [nymanConductorBeta_eq_zeta_dilation, mul_sub, mul_smul_comm,
    mul_arithmeticDilation, ArithmeticFunction.coe_moebius_mul_coe_zeta]

/-- Exact scalar recurrence satisfied by the actual constructive inverse. -/
theorem nymanConductorInverse_moebius_recurrence (n : ℕ) (hn : 2 ≤ n) (k : ℕ) :
    nymanConductorInverse n hn k =
      (n : ℝ) * (ArithmeticFunction.moebius k : ℤ) +
        (n : ℝ) * (if n ∣ k then nymanConductorInverse n hn (k/n) else 0) := by
  let b := nymanConductorInverse n hn
  have he : (1/(n:ℝ)) • b - arithmeticDilation n b =
      (ArithmeticFunction.moebius : ArithmeticFunction ℝ) := by
    calc
      _ = ((ArithmeticFunction.moebius : ArithmeticFunction ℝ) * nymanConductorBeta n) * b := by
        rw [moebius_mul_nymanConductorBeta, sub_mul, smul_mul_assoc, one_mul,
          mul_comm (arithmeticDilation n 1) b, mul_arithmeticDilation, mul_one]
      _ = _ := by
        rw [mul_assoc, nymanConductorBeta_mul_inverse, mul_one]
  have hk := congrArg (fun f : ArithmeticFunction ℝ => f k) he
  change ((1/(n:ℝ)) • b) k - arithmeticDilation n b k =
    (ArithmeticFunction.moebius : ArithmeticFunction ℝ) k at hk
  simp only [ArithmeticFunction.smul_map, smul_eq_mul, arithmeticDilation_apply,
    ArithmeticFunction.intCoe_apply] at hk
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  change (1/(n:ℝ)) * nymanConductorInverse n hn k -
    (if n ∣ k then nymanConductorInverse n hn (k/n) else 0) =
      (ArithmeticFunction.moebius k : ℤ) at hk
  field_simp at hk
  nlinarith [hk]

/-- The exact summand in the closed Möbius/power formula. -/
def nymanMobiusPowerTerm (n k j : ℕ) : ℝ :=
  if n^j ∣ k then (n : ℝ)^j * (ArithmeticFunction.moebius (k/n^j) : ℤ) else 0

private theorem inverse_remainder_step (n : ℕ) (hn : 2 ≤ n) (k j : ℕ) :
    (if n^j ∣ k then (n : ℝ)^j * nymanConductorInverse n hn (k/n^j) else 0) =
      (n : ℝ) * nymanMobiusPowerTerm n k j +
        (if n^(j+1) ∣ k then
          (n : ℝ)^(j+1) * nymanConductorInverse n hn (k/n^(j+1)) else 0) := by
  by_cases hj : n^j ∣ k
  · rw [if_pos hj, nymanConductorInverse_moebius_recurrence]
    have hd : n ∣ k/n^j ↔ n^(j+1) ∣ k := by
      rw [Nat.dvd_div_iff_mul_dvd hj, pow_succ]
    have hq : (k/n^j)/n = k/n^(j+1) := by
      rw [Nat.div_div_eq_div_mul, pow_succ]
    simp only [nymanMobiusPowerTerm, if_pos hj, hd, hq]
    simp only [pow_succ]
    split_ifs <;> ring
  · have hj' : ¬ n^(j+1) ∣ k := by
      intro h
      have hpow : n^j ∣ n^(j+1) := ⟨n, by rw [pow_succ]⟩
      exact hj (hpow.trans h)
    simp only [nymanMobiusPowerTerm, hj, hj', if_false, mul_zero, add_zero]

/-- A finite geometric expansion with its exact arithmetic remainder retained. -/
theorem nymanConductorInverse_eq_prefix_add_remainder (n : ℕ) (hn : 2 ≤ n)
    (k J : ℕ) :
    nymanConductorInverse n hn k =
      (n : ℝ) * (∑ j ∈ Finset.range J, nymanMobiusPowerTerm n k j) +
        (if n^J ∣ k then
          (n : ℝ)^J * nymanConductorInverse n hn (k/n^J) else 0) := by
  induction J with
  | zero => simp
  | succ J ih =>
      rw [Finset.sum_range_succ]
      calc
        nymanConductorInverse n hn k =
          (n : ℝ) * (∑ j ∈ Finset.range J, nymanMobiusPowerTerm n k j) +
            (if n^J ∣ k then
              (n : ℝ)^J * nymanConductorInverse n hn (k/n^J) else 0) := ih
        _ = _ := by rw [inverse_remainder_step]; ring

private theorem exponent_lt_conductor_power (n : ℕ) (hn : 2 ≤ n) (j : ℕ) :
    j+1 ≤ n^j := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [pow_succ]
      have hmul := Nat.mul_le_mul_right (n^j) hn
      nlinarith

/-- The Möbius/power sum is genuinely finite for every positive coefficient. -/
theorem nymanMobiusPowerTerm_zero_of_large_exponent (n : ℕ) (hn : 2 ≤ n)
    {k j : ℕ} (hk : k ≠ 0) (hj : k < j) : nymanMobiusPowerTerm n k j = 0 := by
  have hpow : k < n^j := lt_of_lt_of_le (Nat.lt_succ_of_lt hj)
    (exponent_lt_conductor_power n hn j)
  have hnd : ¬ n^j ∣ k := by
    intro h
    exact (not_le_of_gt hpow) (Nat.le_of_dvd (Nat.pos_of_ne_zero hk) h)
  simp only [nymanMobiusPowerTerm, hnd, if_false]

/-- Identification with the actual constructive inverse, in finite form. -/
theorem nymanConductorInverse_eq_mobius_sum (n : ℕ) (hn : 2 ≤ n)
    (k : ℕ) (hk : k ≠ 0) :
    nymanConductorInverse n hn k =
      (n : ℝ) * ∑ j ∈ Finset.range (k+1),
        if n^j ∣ k then (n : ℝ)^j * (ArithmeticFunction.moebius (k/n^j) : ℤ) else 0 := by
  have hpow : k < n^(k+1) := lt_of_lt_of_le (by omega : k < (k+1)+1)
    (exponent_lt_conductor_power n hn (k+1))
  have hnd : ¬ n^(k+1) ∣ k := by
    intro h
    exact (not_le_of_gt hpow) (Nat.le_of_dvd (Nat.pos_of_ne_zero hk) h)
  simpa only [nymanMobiusPowerTerm, hnd, if_false, add_zero] using
    nymanConductorInverse_eq_prefix_add_remainder n hn k (k+1)

/-- The note's infinite-looking sum is exactly the proved finite sum. -/
theorem nymanConductorInverse_eq_mobius_tsum (n : ℕ) (hn : 2 ≤ n)
    (k : ℕ) (hk : k ≠ 0) :
    nymanConductorInverse n hn k =
      (n : ℝ) * ∑' j : ℕ,
        if n^j ∣ k then (n : ℝ)^j * (ArithmeticFunction.moebius (k/n^j) : ℤ) else 0 := by
  rw [nymanConductorInverse_eq_mobius_sum n hn k hk]
  congr 1
  symm
  apply tsum_eq_sum
  intro j hj
  exact nymanMobiusPowerTerm_zero_of_large_exponent n hn hk
    (by simp only [Finset.mem_range] at hj; omega)

/-!
## Exact finite matching forces the Möbius head

Source: user-provided argument
`RH_Candid_Assessment_Pareto_Green_CRT_2026-09-07.md`.
The following statements formalize the finite arithmetic conclusion itself.
They do not assume any estimate for the optimizer's tail.
-/

/-- If the positive divisor sums agree with the Dirichlet unit through `M`,
then every coefficient through `M` is the actual Möbius coefficient.
No constraint is imposed on coefficients beyond the finite head. -/
theorem finite_divisor_sums_force_moebius (e : ℕ → ℝ) (M : ℕ)
    (hhead : ∀ k, 0 < k → k ≤ M →
      (∑ d ∈ k.divisors, e d) = if k = 1 then 1 else 0)
    (k : ℕ) (hk : 0 < k) (hkM : k ≤ M) :
    e k = (ArithmeticFunction.moebius k : ℝ) := by
  have hi := (Pareto.mobius_inversion e
    (fun n => ∑ d ∈ n.divisors, e d)).mp (fun _ _ => rfl) k hk
  calc
    e k = ∑ d ∈ k.divisors, (ArithmeticFunction.moebius (k / d) : ℝ) *
        (∑ j ∈ d.divisors, e j) := hi.symm
    _ = ∑ d ∈ k.divisors, (ArithmeticFunction.moebius (k / d) : ℝ) *
        (if d = 1 then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [hhead d (Nat.pos_of_mem_divisors hd) ((Nat.divisor_le hd).trans hkM)]
    _ = (ArithmeticFunction.moebius k : ℝ) := by
      simp [mul_ite, Nat.mem_divisors, ne_of_gt hk]

/-- The exact coefficients of `(1/n - n^(-s)) D(s)`.
At `k`, dilation contributes the coefficient at `k/n` exactly when `n ∣ k`. -/
def nymanConductorSynthesis (n : ℕ) (d : ArithmeticFunction ℝ) :
    ArithmeticFunction ℝ where
  toFun k := d k / (n : ℝ) - if n ∣ k then d (k / n) else 0
  map_zero' := by simp

theorem nymanConductorSynthesis_apply (n k : ℕ) (d : ArithmeticFunction ℝ) :
    nymanConductorSynthesis n d k =
      d k / (n : ℝ) - if n ∣ k then d (k / n) else 0 := rfl

/-- The synthesis coefficient is the genuine Möbius transform of the
conductor's return coefficient; the equality holds at every natural index. -/
theorem nymanConductorSynthesis_eq_moebius_return (n : ℕ)
    (d : ArithmeticFunction ℝ) :
    nymanConductorSynthesis n d =
      (ArithmeticFunction.moebius : ArithmeticFunction ℝ) *
        (nymanConductorBeta n * d) := by
  rw [← mul_assoc, moebius_mul_nymanConductorBeta, sub_mul, smul_mul_assoc,
    one_mul, mul_comm (arithmeticDilation n 1) d, mul_arithmeticDilation, mul_one]
  ext k
  change d k / (n : ℝ) - (if n ∣ k then d (k / n) else 0) =
    ((1 / (n : ℝ)) • d) k - arithmeticDilation n d k
  simp only [ArithmeticFunction.smul_map, smul_eq_mul, arithmeticDilation_apply]
  ring

/-- The concrete combined coefficients in the two-conductor polynomial. -/
def nymanTwoThreeSynthesis (d₂ d₃ : ArithmeticFunction ℝ) :
    ArithmeticFunction ℝ :=
  nymanConductorSynthesis 2 d₂ + nymanConductorSynthesis 3 d₃

/-- Exact matching of the actual two-conductor return through `M` forces
the entire synthesized initial segment to be Möbius, independently of the
choice of redundant conductor coefficients or any tail optimization. -/
theorem nymanTwoThreeSynthesis_forced_moebius_head
    (d₂ d₃ : ArithmeticFunction ℝ) (M : ℕ)
    (hhead : ∀ k, k ≤ M →
      (nymanConductorBeta 2 * d₂ + nymanConductorBeta 3 * d₃) k =
        if k = 1 then 1 else 0)
    (k : ℕ) (hkM : k ≤ M) :
    nymanTwoThreeSynthesis d₂ d₃ k = (ArithmeticFunction.moebius k : ℝ) := by
  have hs : nymanTwoThreeSynthesis d₂ d₃ =
      (ArithmeticFunction.moebius : ArithmeticFunction ℝ) *
        (nymanConductorBeta 2 * d₂ + nymanConductorBeta 3 * d₃) := by
    rw [nymanTwoThreeSynthesis, nymanConductorSynthesis_eq_moebius_return,
      nymanConductorSynthesis_eq_moebius_return, mul_add]
  rw [hs]
  calc
    _ = ((ArithmeticFunction.moebius : ArithmeticFunction ℝ) * 1) k := by
      rw [ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply]
      apply Finset.sum_congr rfl
      intro p hp
      have hpM : p.2 ≤ M :=
        (Nat.divisor_le (Nat.snd_mem_divisors_of_mem_antidiagonal hp)).trans hkM
      rw [hhead p.2 hpM, ArithmeticFunction.one_apply]
    _ = (ArithmeticFunction.moebius k : ℝ) := by
      rw [mul_one, ArithmeticFunction.intCoe_apply]

/-- A conductor multiplication enlarges a genuinely finite coefficient
support from `M` to at most `n*M`; there is no concealed infinite tail. -/
theorem nymanConductorSynthesis_zero_above (n M : ℕ) (hn : 0 < n)
    (d : ArithmeticFunction ℝ) (hd : ∀ k, M < k → d k = 0)
    (k : ℕ) (hk : n * M < k) : nymanConductorSynthesis n d k = 0 := by
  have hMM : M ≤ n * M := by
    calc
      M = 1 * M := by simp
      _ ≤ n * M := Nat.mul_le_mul_right M (by omega : 1 ≤ n)
  have hkM : M < k := hMM.trans_lt hk
  by_cases hnk : n ∣ k
  · have hq : M < k / n := by
      by_contra hq
      have hle : k / n ≤ M := by omega
      have hmul := Nat.mul_le_mul_right n hle
      rw [Nat.div_mul_cancel hnk] at hmul
      nlinarith
    simp [nymanConductorSynthesis_apply, hnk, hd k hkM, hd (k / n) hq]
  · simp [nymanConductorSynthesis_apply, hnk, hd k hkM]

/-- The concrete two-conductor synthesis is supported through `3*M`
when each input polynomial is supported through `M`. -/
theorem nymanTwoThreeSynthesis_zero_above (d₂ d₃ : ArithmeticFunction ℝ) (M : ℕ)
    (hd₂ : ∀ k, M < k → d₂ k = 0) (hd₃ : ∀ k, M < k → d₃ k = 0)
    (k : ℕ) (hk : 3 * M < k) : nymanTwoThreeSynthesis d₂ d₃ k = 0 := by
  change nymanConductorSynthesis 2 d₂ k + nymanConductorSynthesis 3 d₃ k = 0
  rw [nymanConductorSynthesis_zero_above 2 M (by omega) d₂ hd₂ k (by omega),
    nymanConductorSynthesis_zero_above 3 M (by omega) d₃ hd₃ k hk, add_zero]

end RiemannResearch.RH

/-!
## The synthesized Dirichlet polynomial vanishes at one

The proof below reindexes the actual coefficient sum.  In particular its
vanishing is not introduced as a hypothesis or encoded in an unrelated
polynomial definition.  Source: user-provided two-conductor synthesis argument.
-/

namespace RiemannResearch.RH

noncomputable section
open scoped BigOperators

private theorem conductor_dilation_reciprocal_sum (n M : ℕ) (hn : 0 < n)
    (d : ArithmeticFunction ℝ) :
    (∑ k ∈ Finset.Icc 1 (n * M),
      (if n ∣ k then d (k / n) else 0) / (k : ℝ)) =
      ∑ j ∈ Finset.Icc 1 M, d j / ((n : ℝ) * (j : ℝ)) := by
  classical
  have hprod (j : ℕ) : n * j / n = j := by
    have hdiv : n ∣ n * j := ⟨j, rfl⟩
    have he : n * (n * j / n) = n * j := by
      simpa only [Nat.mul_comm] using Nat.div_mul_cancel hdiv
    exact mul_left_cancel₀ (ne_of_gt hn) he
  have himage : (Finset.Icc 1 M).image (fun j => n * j) =
      (Finset.Icc 1 (n * M)).filter (fun k => n ∣ k) := by
    ext k
    constructor
    · intro hk
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
      have hj' := Finset.mem_Icc.mp hj
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, ⟨j, rfl⟩⟩
      · exact Nat.mul_pos hn hj'.1
      · exact Nat.mul_le_mul_left n hj'.2
    · intro hk
      obtain ⟨hk, hdiv⟩ := Finset.mem_filter.mp hk
      have hk' := Finset.mem_Icc.mp hk
      have he : n * (k / n) = k := by
        simpa only [Nat.mul_comm] using Nat.div_mul_cancel hdiv
      have hqpos : 0 < k / n := by
        apply Nat.pos_of_ne_zero
        intro hq0
        rw [hq0, mul_zero] at he
        exact (ne_of_gt (show 0 < k from hk'.1)) he.symm
      have hqM : k / n ≤ M := by
        by_contra hq
        have hlarge : M + 1 ≤ k / n := by omega
        have hmul := Nat.mul_le_mul_left n hlarge
        nlinarith [hk'.2]
      exact Finset.mem_image.mpr
        ⟨k / n, Finset.mem_Icc.mpr ⟨hqpos, hqM⟩, he⟩
  simp_rw [ite_div, zero_div]
  rw [← Finset.sum_filter, ← himage]
  rw [Finset.sum_image (fun a _ b _ hab => mul_left_cancel₀ (ne_of_gt hn) hab)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hprod j, Nat.cast_mul]

/-- The genuine finite coefficient sum of `(1/n - n^(-s)) D(s)` at `s=1`
is zero.  `L` may be any cutoff beyond the complete synthesized support.
The proof retains all coefficients and reindexes the dilated sum exactly. -/
theorem nymanConductorSynthesis_reciprocal_sum (n M L : ℕ) (hn : 0 < n)
    (d : ArithmeticFunction ℝ) (hd : ∀ k, M < k → d k = 0)
    (hL : n * M ≤ L) :
    (∑ k ∈ Finset.Icc 1 L, nymanConductorSynthesis n d k / (k : ℝ)) = 0 := by
  have hMM : M ≤ n * M := by
    calc
      M = 1 * M := by simp
      _ ≤ n * M := Nat.mul_le_mul_right M (by omega : 1 ≤ n)
  have hfirst :
      (∑ k ∈ Finset.Icc 1 (n * M), d k / (n : ℝ) / (k : ℝ)) =
        ∑ k ∈ Finset.Icc 1 M, d k / (n : ℝ) / (k : ℝ) := by
    symm
    apply Finset.sum_subset
    · intro k hk
      have hk' := Finset.mem_Icc.mp hk
      exact Finset.mem_Icc.mpr ⟨hk'.1, hk'.2.trans hMM⟩
    · intro k hk hknot
      have hk' := Finset.mem_Icc.mp hk
      have hlarge : M < k := by
        simp only [Finset.mem_Icc] at hknot
        omega
      rw [hd k hlarge, zero_div, zero_div]
  have hcanonical :
      (∑ k ∈ Finset.Icc 1 (n * M),
        nymanConductorSynthesis n d k / (k : ℝ)) = 0 := by
    simp_rw [nymanConductorSynthesis_apply, sub_div]
    rw [Finset.sum_sub_distrib, hfirst, conductor_dilation_reciprocal_sum n M hn d]
    simp_rw [div_div]
    exact sub_self _
  calc
    (∑ k ∈ Finset.Icc 1 L, nymanConductorSynthesis n d k / (k : ℝ)) =
        ∑ k ∈ Finset.Icc 1 (n * M),
          nymanConductorSynthesis n d k / (k : ℝ) := by
      symm
      apply Finset.sum_subset
      · intro k hk
        have hk' := Finset.mem_Icc.mp hk
        exact Finset.mem_Icc.mpr ⟨hk'.1, hk'.2.trans hL⟩
      · intro k hk hknot
        have hk' := Finset.mem_Icc.mp hk
        have hlarge : n * M < k := by
          simp only [Finset.mem_Icc] at hknot
          omega
        rw [nymanConductorSynthesis_zero_above n M hn d hd k hlarge, zero_div]
    _ = 0 := hcanonical

/-- `A_M(1)=0` for the actual two-conductor coefficient polynomial
`A_M(s)=sum_{1≤k≤3M} e_k k^(-s)`, including every synthesized coefficient. -/
theorem nymanTwoThreeSynthesis_reciprocal_sum
    (d₂ d₃ : ArithmeticFunction ℝ) (M : ℕ)
    (hd₂ : ∀ k, M < k → d₂ k = 0) (hd₃ : ∀ k, M < k → d₃ k = 0) :
    (∑ k ∈ Finset.Icc 1 (3 * M),
      nymanTwoThreeSynthesis d₂ d₃ k / (k : ℝ)) = 0 := by
  change (∑ k ∈ Finset.Icc 1 (3 * M),
    (nymanConductorSynthesis 2 d₂ k + nymanConductorSynthesis 3 d₃ k) / (k : ℝ)) = 0
  simp_rw [add_div]
  rw [Finset.sum_add_distrib,
    nymanConductorSynthesis_reciprocal_sum 2 M (3 * M) (by omega) d₂ hd₂ (by omega),
    nymanConductorSynthesis_reciprocal_sum 3 M (3 * M) (by omega) d₃ hd₃ (by omega),
    add_zero]

end
end RiemannResearch.RH
