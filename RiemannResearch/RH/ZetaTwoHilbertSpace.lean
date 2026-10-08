import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.ArithmeticCumulativeEnergy
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The actual inverse-square weighted Hilbert space

Source: user-provided exact optimizer cancellation manuscript (8 October 2026),
for the inverse-square law and reciprocal-coordinate operator. The realization
on real ℓ² follows the standard weighted-sequence unitary construction, also
used in `ThresholdHilbertSpace` for Pareto weights. This module gives the
inverse-square coordinates themselves, not an assumed Hilbert realization.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.ZetaTwoHilbert
open RiemannResearch.RH.ZetaTwoProbability
open RiemannResearch.RH.ArithmeticCumulative

abbrev QHilbert := lp (fun _ : ℕ => ℝ) 2

/-- Probability weight on positive physical coordinates; at zero it is zero. -/
def positiveQWeight (k : ℕ) : ℝ := 1/(zetaTwo*(k:ℝ)^2)

/-- The shifted weight on the ℓ² coordinate indexed by n. -/
def qWeight (n : ℕ) : ℝ := positiveQWeight (n+1)

theorem positiveQWeight_nonneg (k : ℕ) : 0 ≤ positiveQWeight k :=
  div_nonneg zero_le_one (mul_nonneg zetaTwo_pos.le (sq_nonneg _))

theorem qWeight_pos (n : ℕ) : 0 < qWeight n := by
  have hZ := zetaTwo_pos
  unfold qWeight positiveQWeight
  positivity

theorem positiveQWeight_summable : Summable positiveQWeight := by
  have h := (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2:ℕ))).div_const zetaTwo
  apply h.congr
  intro k
  unfold positiveQWeight
  simp only [div_eq_mul_inv, mul_inv_rev, one_mul]

theorem positiveQWeight_tsum : (∑' k, positiveQWeight k) = 1 := by
  have he : positiveQWeight = fun k : ℕ => (1/(k:ℝ)^2)/zetaTwo := by
    funext k
    unfold positiveQWeight
    simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
  rw [he, tsum_div_const, ← zetaTwo_eq_nat_sum, div_self (ne_of_gt zetaTwo_pos)]

def qSequence (f : QHilbert) : ℕ → ℝ
  | 0 => 0
  | n+1 => f n / Real.sqrt (qWeight n)

@[simp] theorem qSequence_zero (f : QHilbert) : qSequence f 0 = 0 := rfl
@[simp] theorem qSequence_succ (f : QHilbert) (n : ℕ) :
    qSequence f (n+1) = f n/Real.sqrt (qWeight n) := rfl

private theorem sqrt_qWeight_ne (n : ℕ) : Real.sqrt (qWeight n) ≠ 0 :=
  ne_of_gt (Real.sqrt_pos.mpr (qWeight_pos n))

theorem qSequence_weighted_square (f : QHilbert) (n : ℕ) :
    positiveQWeight (n+1)*(qSequence f (n+1))^2 = (f n)^2 := by
  rw [qSequence_succ, div_pow, Real.sq_sqrt (qWeight_pos n).le]
  change qWeight n * ((f n)^2/qWeight n) = (f n)^2
  field_simp [ne_of_gt (qWeight_pos n)]

theorem qCoordinate_square_summable (f : QHilbert) : Summable (fun n => (f n)^2) := by
  have h := Memℓp.summable (show 0 < (2:ENNReal).toReal by norm_num) f.property
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using h

theorem qSequence_square_summable (f : QHilbert) :
    Summable (fun k => positiveQWeight k*(qSequence f k)^2) := by
  apply (summable_nat_add_iff 1).mp
  simpa only [qSequence_weighted_square] using qCoordinate_square_summable f

theorem qNorm_sq (f : QHilbert) : ‖f‖^2 = ∑' n, (f n)^2 := by
  rw [← real_inner_self_eq_norm_sq, lp.inner_eq_tsum]
  congr 1
  funext n
  simp [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

/-- Exact equality with the original probability-weighted infinite norm. -/
theorem qNorm_weighted_sq (f : QHilbert) :
    ‖f‖^2 = ∑' k, positiveQWeight k*(qSequence f k)^2 := by
  rw [(qSequence_square_summable f).tsum_eq_zero_add]
  simp only [qSequence_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero,
    zero_add, qSequence_weighted_square]
  exact qNorm_sq f

def qSequenceLinear : QHilbert →ₗ[ℝ] (ℕ → ℝ) where
  toFun := qSequence
  map_add' f g := by
    funext k
    cases k with
    | zero => simp [qSequence]
    | succ n => simp [qSequence, add_div]
  map_smul' c f := by
    funext k
    cases k with
    | zero => simp [qSequence]
    | succ n => simp [qSequence, mul_div_assoc]

theorem qSequence_injective : Function.Injective qSequence := by
  intro f g h
  apply Subtype.ext
  funext n
  have hn := congrFun h (n+1)
  simpa only [qSequence_succ, div_left_inj' (sqrt_qWeight_ne n)] using hn

/-- Every physically square-summable sequence has an actual QHilbert encoding. -/
def encodeQ (g : ℕ → ℝ) (hg : Summable (fun k => positiveQWeight k*(g k)^2)) : QHilbert :=
  ⟨fun n => Real.sqrt (qWeight n)*g (n+1), by
    apply (memℓp_gen_iff (show 0 < (2:ENNReal).toReal by norm_num)).mpr
    have hs := (summable_nat_add_iff 1).mpr hg
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]
    simp_rw [mul_pow, Real.sq_sqrt (qWeight_pos _).le]
    simpa only [qWeight] using hs⟩

@[simp] theorem qSequence_encodeQ (g : ℕ → ℝ)
    (hg : Summable (fun k => positiveQWeight k*(g k)^2)) (hg0 : g 0 = 0) :
    qSequence (encodeQ g hg) = g := by
  funext k
  cases k with
  | zero => exact hg0.symm
  | succ n =>
    change Real.sqrt (qWeight n)*g (n+1)/Real.sqrt (qWeight n) = g (n+1)
    field_simp [sqrt_qWeight_ne n]

theorem qSequence_range (g : ℕ → ℝ) :
    (∃ f : QHilbert, qSequence f = g) ↔
      g 0 = 0 ∧ Summable (fun k => positiveQWeight k*(g k)^2) := by
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨rfl, qSequence_square_summable f⟩
  · rintro ⟨h0, hs⟩
    exact ⟨encodeQ g hs, qSequence_encodeQ g hs h0⟩

private theorem qCoordinate_product_summable (f g : QHilbert) :
    Summable (fun n => f n*g n) := by
  apply ((qCoordinate_square_summable f).add (qCoordinate_square_summable g)).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · nlinarith [sq_nonneg (f n+g n), sq_nonneg (f n), sq_nonneg (g n)]
  · nlinarith [sq_nonneg (f n-g n), sq_nonneg (f n), sq_nonneg (g n)]

theorem qSequence_weighted_product (f g : QHilbert) (n : ℕ) :
    positiveQWeight (n+1)*qSequence f (n+1)*qSequence g (n+1) = f n*g n := by
  rw [qSequence_succ, qSequence_succ]
  change qWeight n*(f n/Real.sqrt (qWeight n))*(g n/Real.sqrt (qWeight n)) = _
  have hs := Real.sq_sqrt (qWeight_pos n).le
  field_simp [sqrt_qWeight_ne n]
  rw [hs]
  ring

theorem qSequence_product_summable (f g : QHilbert) :
    Summable (fun k => positiveQWeight k*qSequence f k*qSequence g k) := by
  apply (summable_nat_add_iff 1).mp
  simpa only [qSequence_weighted_product] using qCoordinate_product_summable f g

/-- Actual Q pairings, including their entire infinite tail. -/
theorem qInner_weighted (f g : QHilbert) :
    inner ℝ f g = ∑' k, positiveQWeight k*qSequence f k*qSequence g k := by
  rw [lp.inner_eq_tsum, (qSequence_product_summable f g).tsum_eq_zero_add]
  simp only [qSequence_zero, mul_zero, zero_add, qSequence_weighted_product]
  congr 1
  funext n
  change g n*f n = f n*g n
  ring

theorem boundedQ_square_summable (g : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hg : ∀ k, |g k| ≤ C) : Summable (fun k => positiveQWeight k*(g k)^2) := by
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (positiveQWeight_nonneg k) (sq_nonneg _))
    _ (positiveQWeight_summable.mul_right (C^2))
  intro k
  have hs := mul_le_mul (hg k) (hg k) (abs_nonneg _) hC
  apply mul_le_mul_of_nonneg_left _ (positiveQWeight_nonneg k)
  simpa only [← pow_two, sq_abs] using hs

def qOneSequence (k : ℕ) : ℝ := if k = 0 then 0 else 1

private theorem qOneSequence_square_summable :
    Summable (fun k => positiveQWeight k*(qOneSequence k)^2) :=
  boundedQ_square_summable qOneSequence 1 zero_le_one (by
    intro k
    by_cases hk : k = 0 <;> simp [qOneSequence, hk])

def qOne : QHilbert := encodeQ qOneSequence qOneSequence_square_summable

@[simp] theorem qSequence_qOne : qSequence qOne = qOneSequence :=
  qSequence_encodeQ _ _ (by simp [qOneSequence])

theorem qOne_norm_sq : ‖qOne‖^2 = 1 := by
  rw [qNorm_weighted_sq, qSequence_qOne]
  have he : (fun k => positiveQWeight k*(qOneSequence k)^2) = positiveQWeight := by
    funext k
    by_cases hk : k = 0
    · simp [hk, qOneSequence, positiveQWeight]
    · simp [qOneSequence, hk]
  rw [he, positiveQWeight_tsum]

theorem qOne_norm : ‖qOne‖ = 1 := by
  have h := qOne_norm_sq
  nlinarith [norm_nonneg qOne]

private theorem qResidueFraction_abs_le_one (d k : ℕ) : |residueFraction d k| ≤ 1 := by
  by_cases hd : d = 0
  · simp [hd, residueFraction]
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    have hdR : (0:ℝ) < d := by exact_mod_cast hdpos
    unfold residueFraction
    rw [abs_of_nonneg (by positivity)]
    apply (div_le_iff₀ hdR).mpr
    simpa only [one_mul] using (show ((k%d:ℕ):ℝ) ≤ (d:ℝ) by
      exact_mod_cast (Nat.mod_lt k hdpos).le)

def qResidue (d : ℕ) : QHilbert :=
  encodeQ (residueFraction d) (boundedQ_square_summable _ 1 zero_le_one (qResidueFraction_abs_le_one d))

@[simp] theorem qSequence_qResidue (d : ℕ) : qSequence (qResidue d) = residueFraction d :=
  qSequence_encodeQ _ _ (by simp [residueFraction])

@[simp] theorem qResidue_one : qResidue 1 = 0 := by
  apply qSequence_injective
  funext k
  rw [qSequence_qResidue]
  cases k <;> simp [qSequence, residueFraction, Nat.mod_one]

/-- The actual coordinatewise reciprocal contraction on ℓ². -/
def reciprocalCoordinates (f : QHilbert) : QHilbert :=
  ⟨fun n => f n/((n:ℝ)+1), by
    apply (memℓp_gen_iff (show 0 < (2:ENNReal).toReal by norm_num)).mpr
    have hs : Summable (fun n : ℕ => (f n/((n:ℝ)+1))^2) := by
      apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ (qCoordinate_square_summable f)
      intro n
      rw [div_pow]
      have hd : 1 ≤ ((n:ℝ)+1)^2 := by nlinarith [Nat.cast_nonneg (α:=ℝ) n]
      simpa only [div_one] using
        div_le_div_of_nonneg_left (sq_nonneg (f n)) zero_lt_one hd
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using hs⟩

@[simp] theorem reciprocalCoordinates_apply (f : QHilbert) (n : ℕ) :
    reciprocalCoordinates f n = f n/((n:ℝ)+1) := rfl

theorem reciprocalCoordinates_norm_le (f : QHilbert) : ‖reciprocalCoordinates f‖ ≤ ‖f‖ := by
  have hsq : ‖reciprocalCoordinates f‖^2 ≤ ‖f‖^2 := by
    rw [qNorm_sq, qNorm_sq]
    apply Summable.tsum_le_tsum _ (qCoordinate_square_summable _) (qCoordinate_square_summable _)
    intro n
    rw [reciprocalCoordinates_apply, div_pow]
    have hd : 1 ≤ ((n:ℝ)+1)^2 := by nlinarith [Nat.cast_nonneg (α:=ℝ) n]
    simpa only [div_one] using div_le_div_of_nonneg_left (sq_nonneg (f n)) zero_lt_one hd
  nlinarith [norm_nonneg f, norm_nonneg (reciprocalCoordinates f)]

def reciprocalLinear : QHilbert →ₗ[ℝ] QHilbert where
  toFun := reciprocalCoordinates
  map_add' f g := by
    apply Subtype.ext
    funext n
    change (f n+g n)/((n:ℝ)+1) = f n/((n:ℝ)+1) + g n/((n:ℝ)+1)
    exact add_div _ _ _
  map_smul' c f := by
    apply Subtype.ext
    funext n
    change (c*f n)/((n:ℝ)+1) = c*(f n/((n:ℝ)+1))
    ring

def reciprocalD : QHilbert →L[ℝ] QHilbert :=
  reciprocalLinear.mkContinuous 1 (fun f => by
    change ‖reciprocalCoordinates f‖ ≤ 1*‖f‖
    simpa using reciprocalCoordinates_norm_le f)

@[simp] theorem reciprocalD_apply (f : QHilbert) (n : ℕ) :
    reciprocalD f n = f n/((n:ℝ)+1) := rfl

theorem qSequence_reciprocalD (f : QHilbert) (k : ℕ) :
    qSequence (reciprocalD f) k = qSequence f k/(k:ℝ) := by
  cases k with
  | zero => simp
  | succ n =>
    simp only [qSequence_succ, reciprocalD_apply, Nat.cast_add, Nat.cast_one]
    ring

theorem reciprocalD_positive (f : QHilbert) : 0 ≤ inner ℝ f (reciprocalD f) := by
  rw [lp.inner_eq_tsum]
  apply tsum_nonneg
  intro n
  change 0 ≤ (f n/((n:ℝ)+1))*f n
  have he : (f n/((n:ℝ)+1))*f n = (f n)^2/((n:ℝ)+1) := by ring
  rw [he]
  positivity

theorem reciprocalD_norm_le (f : QHilbert) : ‖reciprocalD f‖ ≤ ‖f‖ :=
  reciprocalCoordinates_norm_le f

/-- Exact diagonal quadratic form, retaining every coordinate. -/
theorem reciprocalD_inner_tsum (f : QHilbert) :
    inner ℝ f (reciprocalD f) = ∑' n : ℕ, (f n)^2/((n:ℝ)+1) := by
  rw [lp.inner_eq_tsum]
  congr 1
  funext n
  change (f n/((n:ℝ)+1))*f n = (f n)^2/((n:ℝ)+1)
  ring

/-- The reciprocal multiplier is strictly positive on every nonzero vector.
No uniform positive lower bound is claimed for this compact diagonal. -/
theorem reciprocalD_faithful (f : QHilbert)
    (hf : inner ℝ f (reciprocalD f) = 0) : f = 0 := by
  have hs : Summable (fun n : ℕ => (f n)^2/((n:ℝ)+1)) := by
    apply (qCoordinate_product_summable f (reciprocalD f)).congr
    intro n
    rw [reciprocalD_apply]
    ring
  have ht : (∑' n : ℕ, (f n)^2/((n:ℝ)+1)) = 0 := by
    rwa [reciprocalD_inner_tsum] at hf
  apply Subtype.ext
  funext n
  change f n = 0
  have hl : (f n)^2/((n:ℝ)+1) ≤ 0 := by
    have hsingle := Summable.sum_le_tsum ({n}:Finset ℕ)
      (fun j _ => show 0 ≤ (f j)^2/((j:ℝ)+1) by positivity) hs
    simpa only [Finset.sum_singleton, ht] using hsingle
  have hz : (f n)^2/((n:ℝ)+1) = 0 := le_antisymm hl (by positivity)
  have hden : (n:ℝ)+1 ≠ 0 := by positivity
  have hsq : (f n)^2 = 0 := (div_eq_zero_iff.mp hz).resolve_right hden
  nlinarith

theorem reciprocalD_inner_physical (f : QHilbert) :
    inner ℝ f (reciprocalD f) =
      ∑' k : ℕ, positiveQWeight k*(qSequence f k)^2/(k:ℝ) := by
  rw [qInner_weighted]
  congr 1
  funext k
  rw [qSequence_reciprocalD]
  ring

theorem reciprocalD_symmetric (f g : QHilbert) :
    inner ℝ (reciprocalD f) g = inner ℝ f (reciprocalD g) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  congr 1
  funext n
  change g n*(f n/((n:ℝ)+1)) = (g n/((n:ℝ)+1))*f n
  ring

end RiemannResearch.RH.ZetaTwoHilbert
