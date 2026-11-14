import RiemannResearch.RH.ParetoExponentialLegality
import Mathlib.Analysis.PSeries
import Mathlib.Logic.Function.Basic

/-!
# Dirichlet exponentiation does not preserve the whole legal space

Source: Christian Noack's exp-star(V) question, 13 November 2026.
The explicit positive input is f(2^a)=2^a/(a+1)^(3/4), zero elsewhere.
Mathlib's p-series theorem gives its finite energy. Prime-power divisor
enumeration and a harmonic lower bound prove that its convolution square and
actual exponential have infinite energy. Combining this with the checked
zero-input density obstruction refutes full V-legality preservation.
This does not refute RH or bounded-input legality preservation.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.ExponentialCounterexample
open RiemannResearch.NumberTheory.DirichletExponential
open ConvolutionExponential ExponentialLegality

def decay (a : ℕ) : ℝ := ((a : ℝ) + 1) ^ (-(3 / 4 : ℝ))

theorem decay_pos (a : ℕ) : 0 < decay a := Real.rpow_pos_of_pos (by positivity) _

theorem decay_sq (a : ℕ) :
    decay a ^ 2 = ((a : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by
  rw [decay, ← Real.rpow_two, ← Real.rpow_mul (by positivity)]
  norm_num

theorem decay_sq_summable : Summable (fun a => decay a ^ 2) := by
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ (-(3 / 2 : ℝ))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have ht := (summable_nat_add_iff 1).mpr hs
  simpa only [decay_sq, Nat.cast_add, Nat.cast_one] using ht

def sparseInput : ArithmeticFunction ℝ where
  toFun := Function.extend (fun a : ℕ => 2 ^ a)
    (fun a => (2 : ℝ) ^ a * decay a) (fun _ => 0)
  map_zero' := by
    apply Function.extend_apply'
    rintro ⟨a, ha⟩
    exact (pow_ne_zero a (by decide : (2 : ℕ) ≠ 0)) ha

theorem sparseInput_pow (a : ℕ) :
    sparseInput (2 ^ a) = (2 : ℝ) ^ a * decay a := by
  change Function.extend (fun a : ℕ => 2 ^ a)
    (fun a => (2 : ℝ) ^ a * decay a) (fun _ => 0) (2 ^ a) = _
  exact (Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ))).extend_apply _ _ a

theorem sparseInput_outside {n : ℕ}
    (hn : n ∉ Set.range (fun a : ℕ => 2 ^ a)) : sparseInput n = 0 := by
  change Function.extend (fun a : ℕ => 2 ^ a)
    (fun a => (2 : ℝ) ^ a * decay a) (fun _ => 0) n = _
  exact Function.extend_apply' _ _ _ hn

theorem sparseInput_nonneg (n : ℕ) : 0 ≤ sparseInput n := by
  classical
  by_cases hn : n ∈ Set.range (fun a : ℕ => 2 ^ a)
  · obtain ⟨a, rfl⟩ := hn
    rw [sparseInput_pow]
    exact mul_nonneg (by positivity) (decay_pos a).le
  · rw [sparseInput_outside hn]

theorem sparseInput_inv_sq_summable :
    Summable (fun n => sparseInput n ^ 2 / (n : ℝ) ^ 2) := by
  have hzero : ∀ n ∉ Set.range (fun a : ℕ => 2 ^ a),
      sparseInput n ^ 2 / (n : ℝ) ^ 2 = 0 := by
    intro n hn
    rw [sparseInput_outside hn]
    simp
  apply ((Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ))).summable_iff hzero).mp
  change Summable (fun a : ℕ => sparseInput (2 ^ a) ^ 2 / ((2 ^ a : ℕ) : ℝ) ^ 2)
  have he (a : ℕ) : sparseInput (2 ^ a) ^ 2 / ((2 ^ a : ℕ) : ℝ) ^ 2 = decay a ^ 2 := by
    rw [sparseInput_pow, Nat.cast_pow, Nat.cast_ofNat]
    field_simp
  simpa only [he] using decay_sq_summable

theorem sparseInput_pareto_summable :
    Summable (fun n => positiveWeight n * sparseInput n ^ 2) :=
  weighted_square_summable_of_inv_sq _ sparseInput_inv_sq_summable


theorem sparseInput_square_pow (a : ℕ) :
    (sparseInput * sparseInput) (2 ^ a) =
      (2 : ℝ) ^ a * ∑ j ∈ Finset.range (a + 1), decay j * decay (a - j) := by
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun d e => sparseInput d * sparseInput e),
    Nat.sum_divisors_prime_pow (by decide : Nat.Prime 2), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ a := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  rw [sparseInput_pow, Nat.pow_div hj' (by decide), sparseInput_pow]
  have hp : (2 : ℝ) ^ a = (2 : ℝ) ^ j * (2 : ℝ) ^ (a - j) := by
    rw [← pow_add, Nat.add_sub_of_le hj']
  rw [hp]
  ring

theorem decay_antitone : Antitone decay := by
  intro a b hab
  exact Real.rpow_le_rpow_of_nonpos (by positivity)
    (by exact_mod_cast Nat.add_le_add_right hab 1) (by norm_num)

theorem convolution_sum_lower (a : ℕ) :
    ((a : ℝ) + 1) ^ (-(1 / 2 : ℝ)) ≤
      ∑ j ∈ Finset.range (a + 1), decay j * decay (a - j) := by
  have hsum : ∑ j ∈ Finset.range (a + 1), decay a ^ 2 ≤
      ∑ j ∈ Finset.range (a + 1), decay j * decay (a - j) := by
    apply Finset.sum_le_sum
    intro j hj
    have hj' : j ≤ a := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    rw [pow_two]
    exact mul_le_mul (decay_antitone hj') (decay_antitone (Nat.sub_le a j))
      (decay_pos a).le (decay_pos j).le
  have hid : ((a : ℝ) + 1) * decay a ^ 2 =
      ((a : ℝ) + 1) ^ (-(1 / 2 : ℝ)) := by
    rw [decay_sq]
    calc
      _ = ((a : ℝ) + 1) ^ (1 : ℝ) *
          ((a : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by rw [Real.rpow_one]
      _ = ((a : ℝ) + 1) ^ ((1 : ℝ) + -(3 / 2 : ℝ)) :=
        (Real.rpow_add (by positivity) _ _).symm
      _ = _ := by norm_num
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one, hid] using hsum

theorem sparseInput_square_inv_sq_lower (a : ℕ) :
    1 / ((a : ℝ) + 1) ≤
      (sparseInput * sparseInput) (2 ^ a) ^ 2 / ((2 ^ a : ℕ) : ℝ) ^ 2 := by
  let S := ∑ j ∈ Finset.range (a + 1), decay j * decay (a - j)
  have he : (sparseInput * sparseInput) (2 ^ a) ^ 2 / ((2 ^ a : ℕ) : ℝ) ^ 2 =
      S ^ 2 := by
    rw [sparseInput_square_pow, Nat.cast_pow, Nat.cast_ofNat]
    dsimp [S]
    field_simp
  rw [he]
  have hs : ((a : ℝ) + 1) ^ (-(1 / 2 : ℝ)) ≤ S := convolution_sum_lower a
  have h0 : 0 ≤ ((a : ℝ) + 1) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_nonneg (by positivity) _
  have hsq : (((a : ℝ) + 1) ^ (-(1 / 2 : ℝ))) ^ 2 = 1 / ((a : ℝ) + 1) := by
    rw [← Real.rpow_two, ← Real.rpow_mul (by positivity)]
    norm_num [Real.rpow_neg_one, one_div]
  rw [← hsq]
  nlinarith

theorem inv_sq_le_twice_positiveWeight {n : ℕ} (hn : 0 < n) :
    (1 : ℝ) / (n : ℝ) ^ 2 ≤ 2 * positiveWeight n := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  unfold positiveWeight
  rw [mul_one_div]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith

theorem sparseInput_square_pareto_lower (a : ℕ) :
    1 / ((a : ℝ) + 1) ≤
      2 * (positiveWeight (2 ^ a) * (sparseInput * sparseInput) (2 ^ a) ^ 2) := by
  calc
    _ ≤ (sparseInput * sparseInput) (2 ^ a) ^ 2 / ((2 ^ a : ℕ) : ℝ) ^ 2 :=
      sparseInput_square_inv_sq_lower a
    _ = (1 / ((2 ^ a : ℕ) : ℝ) ^ 2) *
        (sparseInput * sparseInput) (2 ^ a) ^ 2 := by ring
    _ ≤ (2 * positiveWeight (2 ^ a)) *
        (sparseInput * sparseInput) (2 ^ a) ^ 2 :=
      mul_le_mul_of_nonneg_right (inv_sq_le_twice_positiveWeight (by positivity)) (sq_nonneg _)
    _ = _ := by ring

theorem sparseInput_square_not_pareto_summable :
    ¬ Summable (fun n => positiveWeight n * (sparseInput * sparseInput) n ^ 2) := by
  intro hs
  have ht := hs.comp_injective (Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ)))
  have hh : Summable (fun a : ℕ => 1 / ((a : ℝ) + 1)) :=
    Summable.of_nonneg_of_le (fun a => by positivity) sparseInput_square_pareto_lower
      (ht.mul_left 2)
  have hh' : Summable (fun a : ℕ => (a : ℝ) ^ (-(1 : ℝ))) := by
    apply (summable_nat_add_iff 1).mp
    simpa only [Nat.cast_add, Nat.cast_one, Real.rpow_neg_one, one_div] using hh
  have hfalse := Real.summable_nat_rpow.mp hh'
  norm_num at hfalse

theorem sparseInput_exp_not_pareto_summable :
    ¬ Summable (fun n => positiveWeight n * convolutionExp sparseInput n ^ 2) :=
  exponential_not_square_summable_of_square_not_summable sparseInput
    sparseInput_nonneg sparseInput_square_not_pareto_summable

def sparseVector : ThresholdHilbert :=
  sequenceHilbert sparseInput sparseInput_pareto_summable

theorem sparseVector_sequence : hilbertSequence sparseVector = sparseInput :=
  hilbertSequence_sequenceHilbert _ _ (ArithmeticFunction.map_zero)

theorem sparseVector_arithmeticInput : arithmeticInput sparseVector = sparseInput := by
  ext n
  exact congrFun sparseVector_sequence n

theorem sparseVector_exp_not_pareto_summable :
    ¬ Summable (fun n => positiveWeight n * physicalExp sparseVector n ^ 2) := by
  simpa only [physicalExp, sparseVector_arithmeticInput] using
    sparseInput_exp_not_pareto_summable

/-- The Pareto Hilbert space is not a Dirichlet convolution algebra. -/
theorem exists_square_outside_hilbert :
    ∃ f : ArithmeticFunction ℝ,
      (∀ n, 0 ≤ f n) ∧
      Summable (fun n => positiveWeight n * f n ^ 2) ∧
      ¬ Summable (fun n => positiveWeight n * (f * f) n ^ 2) :=
  ⟨sparseInput, sparseInput_nonneg, sparseInput_pareto_summable,
    sparseInput_square_not_pareto_summable⟩

/-- Coefficientwise exponentiation does not act on all of H. -/
theorem exists_exponential_outside_hilbert :
    ∃ v : ThresholdHilbert,
      ¬ ∃ w : ThresholdHilbert, hilbertSequence w = physicalExp v := by
  refine ⟨sparseVector, ?_⟩
  rintro ⟨w, hw⟩
  apply sparseVector_exp_not_pareto_summable
  rw [← hw]
  exact hilbertSequence_square_summable w

/-- Full legality preservation is false, independently of the truth of RH.
The zero input would force density; the positive sparse vector then contradicts
ambient square integrability. -/
theorem not_retainsLegality : ¬ RetainsLegality := by
  intro h
  have hd := retainsBoundedLegality_iff_density.mp (retainsLegality_implies_bounded h)
  obtain ⟨v, hv⟩ := exists_exponential_outside_hilbert
  have hvV : v ∈ CoefficientStabilization.closedSpace := by rw [hd]; trivial
  obtain ⟨w, hw, he⟩ := h v hvV
  exact hv ⟨w, he⟩

theorem exists_legal_input_without_legal_exponential :
    ∃ v : ThresholdHilbert, v ∈ CoefficientStabilization.closedSpace ∧
      ¬ ∃ w : ThresholdHilbert,
        w ∈ CoefficientStabilization.closedSpace ∧ hilbertSequence w = physicalExp v := by
  by_contra h
  apply not_retainsLegality
  intro v hv
  by_contra hno
  exact h ⟨v, hv, hno⟩

end RiemannResearch.RH.Pareto.ExponentialCounterexample
