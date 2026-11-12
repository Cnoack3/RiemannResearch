import RiemannResearch.Analysis.SubsetSumSummability
import RiemannResearch.RH.PrimeTreeConstants
import RiemannResearch.RH.SquarefreeRadicalDifference
import RiemannResearch.RH.QConductorLimits
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Canonical prime coefficients and exact summability budgets

Every vector in the closed physical Q prime span satisfies the finite-product
increment identity. Splitting a finite prime set by coefficient sign gives
its exact absolute coefficient budget. Bounded product increments are
equivalent to absolute summability; that bound for the actual displacement
component d_W remains Open.

Source: user-directed canonical coefficient research, 12 November 2026.
Balazard, arXiv:1812.04309, Proposition 4 and formula (6), provides context
for continuous arithmetic coefficient functionals and the distinction
between pointwise and Hilbert series. The proof here instead extends a
finite prime identity by continuity and does not assume that paper as an axiom.
No RH implication is asserted.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.QPrimeCoefficientSummability
open ZetaTwoHilbert SquarefreeRadicalDifference ArithmeticCumulative

abbrev PrimeIndex := {p : ℕ // p.Prime}

def canonicalCoefficient (x : QHilbert) (p : PrimeIndex) : ℝ :=
  qSequence x 1 - qDifference x p.val

def primeProduct (s : Finset PrimeIndex) : ℕ := ∏ p ∈ s, p.val

theorem primeProduct_pos (s : Finset PrimeIndex) : 0 < primeProduct s := by
  unfold primeProduct
  exact Finset.prod_pos fun p _ => p.property.pos

theorem prime_dvd_primeProduct_iff (q : PrimeIndex) (s : Finset PrimeIndex) :
    q.val ∣ primeProduct s ↔ q ∈ s := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [primeProduct, q.property.ne_one]
  | @insert p s hp ih =>
    rw [primeProduct, Finset.prod_insert hp, q.property.dvd_mul]
    change (q.val ∣ p.val ∨ q.val ∣ primeProduct s) ↔ q ∈ insert p s
    rw [p.property.dvd_iff_eq q.property.ne_one, ih]
    simp only [Finset.mem_insert]
    have he : p.val = q.val ↔ q = p := by
      constructor
      · intro h
        exact Subtype.ext h.symm
      · intro h
        exact congrArg Subtype.val h.symm
    rw [he]

theorem canonicalCoefficient_qResidue (p q : PrimeIndex) :
    canonicalCoefficient (qResidue q.val) p = if p = q then 1 else 0 := by
  classical
  unfold canonicalCoefficient qDifference
  simp only [qSequence_qResidue]
  rw [show residueFraction q.val 1 = 1 / (q.val : ℝ) by
    simp [residueFraction, Nat.mod_eq_of_lt q.property.one_lt]]
  rw [residueFraction_difference q.val p.val q.property.two_le p.property.one_lt.le]
  simp only [p.property.dvd_iff_eq q.property.ne_one]
  have he : p.val = q.val ↔ p = q := Subtype.ext_iff.symm
  simp only [he]
  split_ifs <;> ring

theorem continuous_canonicalCoefficient (p : PrimeIndex) :
    Continuous (fun x : QHilbert => canonicalCoefficient x p) :=
  (continuous_qSequence 1).sub (continuous_qDifference p.val)

theorem canonicalCoefficient_tendsto {u : ℕ → QHilbert} {x : QHilbert}
    (hu : Tendsto u atTop (𝓝 x)) (p : PrimeIndex) :
    Tendsto (fun N => canonicalCoefficient (u N) p) atTop
      (𝓝 (canonicalCoefficient x p)) :=
  (continuous_canonicalCoefficient p).tendsto x |>.comp hu

private theorem sequence_zero (k : ℕ) : qSequence (0 : QHilbert) k = 0 :=
  congrFun (map_zero qSequenceLinear) k

private theorem sequence_add (x y : QHilbert) (k : ℕ) :
    qSequence (x+y) k = qSequence x k + qSequence y k :=
  congrFun (map_add qSequenceLinear x y) k

private theorem sequence_smul (c : ℝ) (x : QHilbert) (k : ℕ) :
    qSequence (c • x) k = c * qSequence x k :=
  congrFun (map_smul qSequenceLinear c x) k

private theorem coefficient_zero (p : PrimeIndex) :
    canonicalCoefficient (0 : QHilbert) p = 0 := by
  simp [canonicalCoefficient, qDifference_zero]

private theorem coefficient_add (x y : QHilbert) (p : PrimeIndex) :
    canonicalCoefficient (x+y) p = canonicalCoefficient x p +
      canonicalCoefficient y p := by
  simp only [canonicalCoefficient, sequence_add, qDifference_add]
  ring

private theorem coefficient_smul (c : ℝ) (x : QHilbert) (p : PrimeIndex) :
    canonicalCoefficient (c • x) p = c * canonicalCoefficient x p := by
  simp only [canonicalCoefficient, sequence_smul, qDifference_smul]
  ring

/-- Every finite subset of canonical prime coefficients is recovered exactly
by one squarefree-product increment. This identity holds throughout W. -/
theorem primeProduct_difference (x : QHilbert)
    (hx : x ∈ primeAtomSpan.topologicalClosure) (s : Finset PrimeIndex) :
    qDifference x (primeProduct s) =
      qSequence x 1 - ∑ p ∈ s, canonicalCoefficient x p := by
  classical
  have hc : IsClosed {y : QHilbert | qDifference y (primeProduct s) =
      qSequence y 1 - ∑ p ∈ s, canonicalCoefficient y p} :=
    isClosed_eq (continuous_qDifference _)
      ((continuous_qSequence 1).sub
        (continuous_finsetSum s (fun p _ => continuous_canonicalCoefficient p)))
  apply (closure_minimal ?_ hc) hx
  intro y hy
  change y ∈ Submodule.span ℝ {z | ∃ p : ℕ, p.Prime ∧ z = qResidue p} at hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨q, hq, rfl⟩ := hy
    change qDifference (qResidue q) (primeProduct s) = _
    have hd : qDifference (qResidue q) (primeProduct s) =
        1 / (q : ℝ) - (if (⟨q,hq⟩ : PrimeIndex) ∈ s then 1 else 0) := by
      unfold qDifference
      simp only [qSequence_qResidue]
      rw [residueFraction_difference q _ hq.two_le (primeProduct_pos s)]
      simp only [prime_dvd_primeProduct_iff ⟨q,hq⟩ s]
    rw [hd]
    have ha (p : PrimeIndex) :
        canonicalCoefficient (qResidue q) p = if p = ⟨q,hq⟩ then 1 else 0 :=
      by simpa only using canonicalCoefficient_qResidue p ⟨q,hq⟩
    have h1 : qSequence (qResidue q) 1 = 1 / (q : ℝ) := by
      rw [qSequence_qResidue]
      simp [residueFraction, Nat.mod_eq_of_lt hq.one_lt]
    rw [h1]
    simp [ha]
  | zero =>
    change qDifference 0 (primeProduct s) = _
    simp only [qDifference_zero, sequence_zero, coefficient_zero,
      Finset.sum_const_zero, sub_zero]
  | add u v hu hv ihu ihv =>
    change qDifference (u+v) (primeProduct s) = _
    rw [qDifference_add, sequence_add]
    simp only [coefficient_add, Finset.sum_add_distrib]
    change qDifference u (primeProduct s) = _ at ihu
    change qDifference v (primeProduct s) = _ at ihv
    rw [ihu, ihv]
    ring
  | smul c u hu ihu =>
    change qDifference (c • u) (primeProduct s) = _
    rw [qDifference_smul, sequence_smul]
    simp only [coefficient_smul, ← Finset.mul_sum]
    change qDifference u (primeProduct s) = _ at ihu
    rw [ihu]
    ring

/-- The entire absolute coefficient budget is a difference of two increments;
both signs and both boundary values remain present. -/
theorem finite_absolute_budget_exact (x : QHilbert)
    (hx : x ∈ primeAtomSpan.topologicalClosure) (s : Finset PrimeIndex) :
    (∑ p ∈ s, |canonicalCoefficient x p|) =
      qDifference x (primeProduct (s.filter (fun p => canonicalCoefficient x p < 0))) -
      qDifference x (primeProduct (s.filter (fun p => 0 ≤ canonicalCoefficient x p))) := by
  classical
  rw [RiemannResearch.Analysis.SubsetSumSummability.sum_abs_eq_positive_sub_negative,
    primeProduct_difference x hx, primeProduct_difference x hx]
  ring

/-- Conditional research reduction: the interval bound on the actual
prime-product increments remains an arithmetic obligation. -/
theorem summable_abs_of_increment_bounds (x : QHilbert)
    (hx : x ∈ primeAtomSpan.topologicalClosure) (L U : ℝ)
    (h : ∀ s : Finset PrimeIndex,
      L ≤ qDifference x (primeProduct s) ∧ qDifference x (primeProduct s) ≤ U) :
    Summable (fun p => |canonicalCoefficient x p|) ∧
      (∑' p, |canonicalCoefficient x p|) ≤ U-L := by
  have hs : ∀ s : Finset PrimeIndex,
      qSequence x 1-U ≤ ∑ p ∈ s, canonicalCoefficient x p ∧
      (∑ p ∈ s, canonicalCoefficient x p) ≤ qSequence x 1-L := by
    intro s
    have hi := h s
    rw [primeProduct_difference x hx s] at hi
    constructor <;> linarith [hi.1, hi.2]
  refine ⟨RiemannResearch.Analysis.SubsetSumSummability.summable_abs_of_subset_sum_bounds
    _ _ _ hs, ?_⟩
  have hb := RiemannResearch.Analysis.SubsetSumSummability.tsum_abs_le_of_subset_sum_bounds
    _ _ _ hs
  linarith

/-- The converse bound is unconditional once absolute summability is supplied. -/
theorem increment_bounds_of_summable_abs (x : QHilbert)
    (hx : x ∈ primeAtomSpan.topologicalClosure)
    (ha : Summable (fun p => |canonicalCoefficient x p|)) (s : Finset PrimeIndex) :
    qSequence x 1 - (∑' p, |canonicalCoefficient x p|) ≤
      qDifference x (primeProduct s) ∧
    qDifference x (primeProduct s) ≤
      qSequence x 1 + (∑' p, |canonicalCoefficient x p|) := by
  have hb : |∑ p ∈ s, canonicalCoefficient x p| ≤
      ∑' p, |canonicalCoefficient x p| :=
    (Finset.abs_sum_le_sum_abs _ _).trans
      (Summable.sum_le_tsum s (fun p _ => abs_nonneg _) ha)
  rw [abs_le] at hb
  rw [primeProduct_difference x hx]
  constructor <;> linarith [hb.1, hb.2]

theorem summable_abs_iff_increment_bounds (x : QHilbert)
    (hx : x ∈ primeAtomSpan.topologicalClosure) :
    Summable (fun p => |canonicalCoefficient x p|) ↔
      ∃ L U : ℝ, ∀ s : Finset PrimeIndex,
        L ≤ qDifference x (primeProduct s) ∧ qDifference x (primeProduct s) ≤ U := by
  constructor
  · intro ha
    exact ⟨_, _, increment_bounds_of_summable_abs x hx ha⟩
  · rintro ⟨L, U, h⟩
    exact (summable_abs_of_increment_bounds x hx L U h).1

/-- A uniform physical bound supplies a total variation bound of 4C. -/
theorem summable_abs_of_physically_bounded (x : QHilbert)
    (hx : x ∈ primeAtomSpan.topologicalClosure) (C : ℝ)
    (hC : ∀ n, |qSequence x n| ≤ C) :
    Summable (fun p => |canonicalCoefficient x p|) ∧
      (∑' p, |canonicalCoefficient x p|) ≤ 4*C := by
  have hb (s : Finset PrimeIndex) :
      -(2*C) ≤ qDifference x (primeProduct s) ∧
      qDifference x (primeProduct s) ≤ 2*C := by
    apply abs_le.mp
    unfold qDifference
    exact (abs_sub _ _).trans (add_le_add (hC _) (hC _)) |>.trans (by linarith)
  have h := summable_abs_of_increment_bounds x hx (-(2*C)) (2*C) hb
  refine ⟨h.1, ?_⟩
  linarith [h.2]

/-- There is no bound for all canonical coefficients by one fixed multiple of
the Q norm, even on single prime atoms. This does not refute summability for
the particular projection displacement. -/
theorem no_uniform_coefficient_norm_bound :
    ¬ ∃ C : ℝ, ∀ x : QHilbert, x ∈ primeAtomSpan.topologicalClosure →
      ∀ p : PrimeIndex, |canonicalCoefficient x p| ≤ C * ‖x‖ := by
  rintro ⟨C, hC⟩
  choose p hle hp using Nat.exists_infinite_primes
  have ht : Tendsto p atTop atTop := tendsto_atTop.mpr fun k =>
    (eventually_ge_atTop k).mono fun j hj => hj.trans (hle j)
  have hn : Tendsto (fun j => C * ‖qResidue (p j)‖) atTop (𝓝 0) := by
    simpa using ((qResidue_tendsto_zero p ht).norm.const_mul C)
  have hh (j : ℕ) : (1 : ℝ) ≤ C * ‖qResidue (p j)‖ := by
    have hm : qResidue (p j) ∈ primeAtomSpan.topologicalClosure :=
      primeAtomSpan.le_topologicalClosure (Submodule.subset_span ⟨p j, hp j, rfl⟩)
    have h := hC (qResidue (p j)) hm ⟨p j, hp j⟩
    have ha := canonicalCoefficient_qResidue
      (⟨p j, hp j⟩ : PrimeIndex) (⟨p j, hp j⟩ : PrimeIndex)
    simp only [ite_true] at ha
    rw [ha, abs_one] at h
    exact h
  have hf : (1 : ℝ) ≤ 0 := ge_of_tendsto hn (Eventually.of_forall hh)
  norm_num at hf

end RiemannResearch.RH.QPrimeCoefficientSummability
