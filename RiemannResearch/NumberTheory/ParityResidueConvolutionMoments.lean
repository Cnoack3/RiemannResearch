import RiemannResearch.NumberTheory.ParityResidueConvolution
import RiemannResearch.NumberTheory.DirichletExponentialMoments
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Exact divisor-square and parity-convolution moments

The divisor-square Euler product is classical; see Hill, Huxley, Lettington,
and Schmidt, Ramanujan J. 51 (2020), Remark 1,
https://doi.org/10.1007/s11139-018-0093-9.
Convergence is supplied independently by `DirichletExponentialMoments` before
Euler-product identities are used. No atom-closure or RH assertion is assumed.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.NumberTheory.DivisorSquareMoment
open DirichletExponential

theorem hasSum_square_succ_geometric {x : ℝ} (hx : ‖x‖ < 1) :
    HasSum (fun a : ℕ => ((a : ℝ) + 1) ^ 2 * x ^ a)
      ((1 + x) / (1 - x) ^ 3) := by
  have h2 := (hasSum_choose_mul_geometric_of_norm_lt_one 2 hx).mul_left 2
  have h1 := hasSum_choose_mul_geometric_of_norm_lt_one 1 hx
  have h := h2.sub h1
  have he (a : ℕ) :
      2 * (((a + 2).choose 2 : ℝ) * x ^ a) -
        ((a + 1).choose 1 : ℝ) * x ^ a =
      ((a : ℝ) + 1) ^ 2 * x ^ a := by
    have hchoose : ∀ b : ℕ, (2 : ℝ) * ((b + 2).choose 2 : ℝ) =
        ((b : ℝ) + 1) * ((b : ℝ) + 2) := by
      intro b
      induction b with
      | zero => norm_num
      | succ b ih =>
        rw [show b + 1 + 2 = (b + 2) + 1 by omega, Nat.choose_succ_succ]
        simp only [Nat.choose_one_right, Nat.cast_add, Nat.cast_one] at *
        norm_num only [Nat.succ_eq_add_one, Nat.cast_ofNat] at *
        nlinarith
    simp only [Nat.choose_one_right, Nat.cast_add, Nat.cast_one]
    calc
      _ = (2 * ((a + 2).choose 2 : ℝ) - ((a : ℝ) + 1)) * x ^ a := by ring
      _ = _ := by rw [hchoose]; ring
  have hv : (2 : ℝ) * (1 / (1 - x) ^ (2 + 1)) -
      1 / (1 - x) ^ (1 + 1) = (1 + x) / (1 - x) ^ 3 := by
    have hx1 : 1 - x ≠ 0 := by
      have := (abs_lt.mp hx).2
      linarith
    field_simp
    ring
  rw [hv] at h
  exact h.congr_fun (fun a => (he a).symm)

def reciprocalPower (k : ℕ) (hk : 0 < k) : ℕ →*₀ ℝ where
  toFun n := 1 / (n : ℝ) ^ k
  map_zero' := by simp [ne_of_gt hk]
  map_one' := by simp
  map_mul' m n := by simp [Nat.cast_mul, mul_pow, one_div, mul_comm]

theorem local_factor {p : ℕ} (hp : p.Prime) :
    (∑' a : ℕ, divisorMomentTerm 2 (p ^ a)) =
      (1 + 1 / (p : ℝ) ^ 2) / (1 - 1 / (p : ℝ) ^ 2) ^ 3 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hq : ‖1 / (p : ℝ) ^ 2‖ < 1 := by
    rw [Real.norm_of_nonneg (by positivity)]
    apply (div_lt_one (by positivity)).mpr
    nlinarith
  have h := hasSum_square_succ_geometric hq
  have he (a : ℕ) : divisorMomentTerm 2 (p ^ a) =
      ((a : ℝ) + 1) ^ 2 * (1 / (p : ℝ) ^ 2) ^ a := by
    have hz : (zetaReal ^ 2) (p ^ a) = (a : ℝ) + 1 := by
      simpa using zetaReal_pow_succ_prime_pow hp 1 a
    rw [divisorMomentTerm, hz, Nat.cast_pow]
    simp only [div_eq_mul_inv, one_mul, inv_pow]
    congr 1
    rw [← pow_mul, ← pow_mul, Nat.mul_comm a 2]
  simpa only [← he] using h.tsum_eq

theorem local_factor_identity (x : ℝ) (h1 : 1 - x ≠ 0) (h2 : 1 - x ^ 2 ≠ 0) :
    (1 + x) / (1 - x) ^ 3 * (1 - x ^ 2)⁻¹ = ((1 - x)⁻¹) ^ 4 := by
  field_simp [h1, h2]
  ring

theorem divisor_square_sum :
    (∑' n : ℕ, divisorMomentTerm 2 n) = 5 * Real.pi ^ 4 / 72 := by
  have hd := EulerProduct.eulerProduct_hasProd
    (divisorMomentTerm_one 2) (divisorMomentTerm_mul 2)
    ((divisorMomentTerm_summable_and_bound 2 (by decide)).1.norm)
    (divisorMomentTerm_zero 2)
  have h2 := EulerProduct.eulerProduct_completely_multiplicative_hasProd
    (f := reciprocalPower 2 (by decide)) hasSum_zeta_two.summable.norm
  have h4 := EulerProduct.eulerProduct_completely_multiplicative_hasProd
    (f := reciprocalPower 4 (by decide)) hasSum_zeta_four.summable.norm
  change HasProd (fun p : Nat.Primes => (1 - 1 / (p : ℝ) ^ 2)⁻¹)
    (∑' n : ℕ, 1 / (n : ℝ) ^ 2) at h2
  change HasProd (fun p : Nat.Primes => (1 - 1 / (p : ℝ) ^ 4)⁻¹)
    (∑' n : ℕ, 1 / (n : ℝ) ^ 4) at h4
  rw [hasSum_zeta_two.tsum_eq] at h2
  rw [hasSum_zeta_four.tsum_eq] at h4
  have hmul := hd.mul h4
  have he (p : Nat.Primes) :
      (∑' a : ℕ, divisorMomentTerm 2 (p.val ^ a)) *
        (1 - 1 / (p : ℝ) ^ 4)⁻¹ =
      ((1 - 1 / (p : ℝ) ^ 2)⁻¹) ^ 4 := by
    rw [local_factor p.property]
    have hp1 : (1 : ℝ) < p := by exact_mod_cast p.property.one_lt
    have hp0 : (p : ℝ) ≠ 0 := by positivity
    have h2ne : 1 - 1 / (p : ℝ) ^ 2 ≠ 0 := by
      apply ne_of_gt
      have : 1 / (p : ℝ) ^ 2 < 1 := (div_lt_one (by positivity)).mpr (by nlinarith)
      linarith
    have h4ne : 1 - 1 / (p : ℝ) ^ 4 ≠ 0 := by
      apply ne_of_gt
      have : 1 / (p : ℝ) ^ 4 < 1 :=
        (div_lt_one (by positivity)).mpr (by nlinarith [sq_nonneg ((p : ℝ) ^ 2 - 1)])
      linarith
    have hh : (1 / (p : ℝ) ^ 2) ^ 2 = 1 / (p : ℝ) ^ 4 := by ring
    rw [← hh]
    exact local_factor_identity _ h2ne (by simpa only [hh] using h4ne)
  have hu := (hmul.congr_fun (fun p => (he p).symm)).unique (h2.pow 4)
  apply (mul_right_cancel₀ (pow_ne_zero 4 Real.pi_ne_zero))
  calc
    (∑' n : ℕ, divisorMomentTerm 2 n) * Real.pi ^ 4 =
        90 * ((∑' n : ℕ, divisorMomentTerm 2 n) * (Real.pi ^ 4 / 90)) := by ring
    _ = 90 * ((Real.pi ^ 2 / 6) ^ 4) := by rw [hu]
    _ = (5 * Real.pi ^ 4 / 72) * Real.pi ^ 4 := by ring
end RiemannResearch.NumberTheory.DivisorSquareMoment

namespace RiemannResearch.NumberTheory.DivisorSquareMoment
open DirichletExponential

theorem zetaReal_square_eq_card (n : ℕ) :
    (zetaReal ^ 2) n = (n.divisors.card : ℝ) := by
  rw [pow_two, ArithmeticFunction.coe_mul_zeta_apply]
  calc
    (∑ d ∈ n.divisors, zetaReal d) = ∑ _d ∈ n.divisors, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro d hd
      simp [zetaReal_apply, Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)]
    _ = _ := by simp

def oddMoment (n : ℕ) : ℝ := if n % 2 = 1 then divisorMomentTerm 2 n else 0

theorem oddMoment_nonneg (n : ℕ) : 0 ≤ oddMoment n := by
  unfold oddMoment
  split_ifs
  · exact divisorMomentTerm_nonneg 2 n
  · exact le_rfl

theorem oddMoment_summable : Summable oddMoment := by
  apply Summable.of_nonneg_of_le oddMoment_nonneg _
    (divisorMomentTerm_summable_and_bound 2 (by decide)).1
  intro n
  unfold oddMoment
  split_ifs
  · exact le_rfl
  · exact divisorMomentTerm_nonneg 2 n

theorem oddMoment_mul {m n : ℕ} (hmn : m.Coprime n) :
    oddMoment (m * n) = oddMoment m * oddMoment n := by
  rcases Nat.mod_two_eq_zero_or_one m with hm | hm <;>
    rcases Nat.mod_two_eq_zero_or_one n with hn | hn <;>
    simp [oddMoment, Nat.mul_mod, hm, hn, divisorMomentTerm_mul 2 hmn]

theorem oddMoment_two_local :
    (∑' a : ℕ, oddMoment (2 ^ a)) = 1 := by
  have he (a : ℕ) : oddMoment (2 ^ a) = if a = 0 then 1 else 0 := by
    cases a with
    | zero => simp [oddMoment]
    | succ a => simp [oddMoment, pow_succ, Nat.mul_mod]
  simp_rw [he]
  simp

theorem oddMoment_odd_local {p : ℕ} (hpodd : p % 2 = 1) :
    (∑' a : ℕ, oddMoment (p ^ a)) =
      ∑' a : ℕ, divisorMomentTerm 2 (p ^ a) := by
  apply tsum_congr
  intro a
  simp [oddMoment, Nat.pow_mod, hpodd]

theorem odd_divisor_square_sum :
    (∑' n : ℕ, oddMoment n) = 3 * Real.pi ^ 4 / 128 := by
  classical
  have hd := EulerProduct.eulerProduct_hasProd
    (divisorMomentTerm_one 2) (divisorMomentTerm_mul 2)
    ((divisorMomentTerm_summable_and_bound 2 (by decide)).1.norm)
    (divisorMomentTerm_zero 2)
  have ho := EulerProduct.eulerProduct_hasProd
    (f := oddMoment) (by simp [oddMoment]) oddMoment_mul oddMoment_summable.norm
    (by simp [oddMoment])
  let p2 : Nat.Primes := ⟨2, by decide⟩
  have hf (p : Nat.Primes) :
      (∑' a : ℕ, oddMoment (p.val ^ a)) =
      Function.update (fun p : Nat.Primes => ∑' a : ℕ, divisorMomentTerm 2 (p.val ^ a))
        p2 1 p := by
    by_cases he : p = p2
    · subst p
      rw [Function.update_self]
      exact oddMoment_two_local
    · have hne : p.val ≠ 2 := by
        intro h
        apply he
        exact Subtype.ext h
      have hpodd : p.val % 2 = 1 := by
        rcases Nat.mod_two_eq_zero_or_one p.val with h0 | h1
        · rcases (Nat.dvd_prime p.property).mp (Nat.dvd_of_mod_eq_zero h0) with h | h
          · norm_num at h
          · exact False.elim (hne h.symm)
        · exact h1
      rw [Function.update_of_ne he]
      exact oddMoment_odd_local hpodd
  have hr := hd.update' p2 1 (ho.congr_fun (fun p => (hf p).symm))
  rw [divisor_square_sum] at hr
  have htwo : (∑' a : ℕ, divisorMomentTerm 2 (p2.val ^ a)) = 80 / 27 := by
    rw [local_factor p2.property]
    norm_num [p2]
  rw [htwo] at hr
  nlinarith
end RiemannResearch.NumberTheory.DivisorSquareMoment

namespace RiemannResearch.NumberTheory.ParityResidueConvolution
open DirichletExponential DivisorSquareMoment

theorem paritySquare_sq_inv_eq (n : ℕ) :
    paritySquare n ^ 2 / (n : ℝ) ^ 2 = (1 / 16 : ℝ) * oddMoment n := by
  rw [paritySquare_parity, oddMoment]
  split_ifs
  · rw [divisorMomentTerm, zetaReal_square_eq_card]
    ring
  · ring

theorem paritySquare_exact_moment :
    (∑' n : ℕ, paritySquare n ^ 2 / (n : ℝ) ^ 2) = 3 * Real.pi ^ 4 / 2048 := by
  simp_rw [paritySquare_sq_inv_eq]
  rw [tsum_mul_left, odd_divisor_square_sum]
  ring

end RiemannResearch.NumberTheory.ParityResidueConvolution

namespace RiemannResearch.NumberTheory.DivisorSquareMoment
open DirichletExponential

theorem bounded_convolution_abs_le (f g : ArithmeticFunction ℝ) {C D : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hf : ∀ n, |f n| ≤ C) (hg : ∀ n, |g n| ≤ D) (n : ℕ) :
    |(f * g) n| ≤ C * D * (n.divisors.card : ℝ) := by
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b => f a * g b)]
  calc
    |∑ d ∈ n.divisors, f d * g (n / d)| ≤
        ∑ d ∈ n.divisors, |f d * g (n / d)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ n.divisors, C * D := by
      apply Finset.sum_le_sum
      intro d hd
      rw [abs_mul]
      exact mul_le_mul (hf d) (hg (n / d)) (abs_nonneg _) hC
    _ = C * D * (n.divisors.card : ℝ) := by simp; ring

theorem bounded_convolution_moment (f g : ArithmeticFunction ℝ) {C D : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hf : ∀ n, |f n| ≤ C) (hg : ∀ n, |g n| ≤ D) :
    Summable (fun n => (f * g) n ^ 2 / (n : ℝ) ^ 2) ∧
    (∑' n : ℕ, (f * g) n ^ 2 / (n : ℝ) ^ 2) ≤
      (C * D) ^ 2 * (5 * Real.pi ^ 4 / 72) := by
  have hbound (n : ℕ) :
      (f * g) n ^ 2 / (n : ℝ) ^ 2 ≤ (C * D) ^ 2 * divisorMomentTerm 2 n := by
    rw [divisorMomentTerm, zetaReal_square_eq_card]
    have ha := bounded_convolution_abs_le f g hC hD hf hg n
    have hb : 0 ≤ C * D * (n.divisors.card : ℝ) := by positivity
    have hc : (f * g) n ^ 2 ≤ (C * D * (n.divisors.card : ℝ)) ^ 2 := by
      nlinarith [sq_abs ((f * g) n), abs_nonneg ((f * g) n)]
    calc
      _ ≤ (C * D * (n.divisors.card : ℝ)) ^ 2 / (n : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hc (sq_nonneg _)
      _ = _ := by ring
  have hmajor := ((divisorMomentTerm_summable_and_bound 2 (by decide)).1).mul_left
    ((C * D) ^ 2)
  have hs : Summable (fun n => (f * g) n ^ 2 / (n : ℝ) ^ 2) :=
    Summable.of_nonneg_of_le (fun n => by positivity) hbound hmajor
  refine ⟨hs, ?_⟩
  calc
    _ ≤ ∑' n : ℕ, (C * D) ^ 2 * divisorMomentTerm 2 n :=
      hs.tsum_le_tsum hbound hmajor
    _ = _ := by rw [tsum_mul_left, divisor_square_sum]

end RiemannResearch.NumberTheory.DivisorSquareMoment
