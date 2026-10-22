import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp

/-!
# Conditioning countable product partitions

Source: elementary normalization of a factored joint mass function, applied
to the user's arithmetic DPP residue-lift construction. The countable union
is an actual measurable conditioning event, and positivity is its ordinary
positive-probability conditioning requirement.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical ENNReal

namespace RiemannResearch.Probability.ProductConditioning

theorem tsum_fin_pi_prod_ennreal (n : ℕ) :
    ∀ (α : Fin n → Type*) (w : (i : Fin n) → α i → ℝ≥0∞),
      (∑' f : (i : Fin n) → α i, ∏ i, w i (f i)) = ∏ i, ∑' a, w i a := by
  induction n with
  | zero =>
    intro α w
    letI : Unique ((i : Fin 0) → α i) :=
      { default := fun i => Fin.elim0 i
        uniq := fun a => by funext i; exact Fin.elim0 i }
    simp
  | succ n ih =>
    intro α w
    let E : ((i : Fin (n + 1)) → α i) ≃
        α 0 × ((i : Fin n) → α i.succ) :=
      { toFun := fun f => (f 0, fun i => f i.succ)
        invFun := fun p => Fin.cases p.1 p.2
        left_inv := fun f => by
          funext i
          refine Fin.cases ?_ (fun j => ?_) i <;> rfl
        right_inv := fun p => by cases p; rfl }
    calc
      _ = ∑' p : α 0 × ((i : Fin n) → α i.succ),
          ∏ i, w i (E.symm p i) := (E.symm.tsum_eq _).symm
      _ = ∑' p : α 0 × ((i : Fin n) → α i.succ),
          w 0 p.1 * ∏ i : Fin n, w i.succ (p.2 i) := by
        apply tsum_congr
        intro p
        simp [Fin.prod_univ_succ, E]
      _ = ∑' a : α 0, ∑' f : (i : Fin n) → α i.succ,
          w 0 a * ∏ i : Fin n, w i.succ (f i) :=
        ENNReal.tsum_prod (f := fun (a : α 0) (f : (i : Fin n) → α i.succ) =>
          w 0 a * ∏ i, w i.succ (f i))
      _ = (∑' a : α 0, w 0 a) * ∏ i : Fin n, ∑' a, w i.succ a := by
        simp_rw [ENNReal.tsum_mul_left, ih (fun i => α i.succ) (fun i => w i.succ)]
        exact ENNReal.tsum_mul_right
      _ = _ := by rw [Fin.prod_univ_succ]

theorem tsum_fin_pi_prod_nonneg (n : ℕ) (α : Fin n → Type*)
    (w : (i : Fin n) → α i → ℝ) (hw : ∀ i a, 0 ≤ w i a) :
    (∑' f : (i : Fin n) → α i, ∏ i, w i (f i)) = ∏ i, ∑' a, w i a := by
  have he := congrArg ENNReal.toReal
    (tsum_fin_pi_prod_ennreal n α (fun i a => ENNReal.ofReal (w i a)))
  have htop (f : (i : Fin n) → α i) :
      (∏ i, ENNReal.ofReal (w i (f i))) ≠ ∞ :=
    ENNReal.prod_ne_top (fun i hi => ENNReal.ofReal_ne_top)
  rw [ENNReal.tsum_toReal_eq htop, ENNReal.toReal_prod] at he
  simp_rw [ENNReal.toReal_prod,
    ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top),
    ENNReal.toReal_ofReal (hw _ _)] at he
  exact he

variable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Point masses of the actual conditional law on a countable product
partition factor as the individually normalized coordinate weights. -/
theorem conditional_product_partition (n : ℕ) (α : Fin n → Type*)
    [∀ i, Countable (α i)]
    (A : ((i : Fin n) → α i) → Set Ω)
    (hdisj : Pairwise (fun f g => Disjoint (A f) (A g)))
    (hA : ∀ f, MeasurableSet (A f))
    (w : (i : Fin n) → α i → ℝ) (hw : ∀ i a, 0 ≤ w i a)
    (c : ℝ) (hmass : ∀ f, μ.real (A f) = c * ∏ i, w i (f i))
    (hpos : 0 < μ.real (⋃ f, A f)) (f : (i : Fin n) → α i) :
    μ.real (A f) / μ.real (⋃ g, A g) = ∏ i, w i (f i) / (∑' a, w i a) := by
  have hU : μ.real (⋃ f, A f) = c * ∏ i, ∑' a, w i a := by
    calc
      _ = ∑' f : (i : Fin n) → α i, μ.real (A f) := by
        unfold Measure.real
        rw [measure_iUnion hdisj hA]
        exact ENNReal.tsum_toReal_eq (fun f => measure_ne_top μ (A f))
      _ = ∑' f : (i : Fin n) → α i, c * ∏ i, w i (f i) := tsum_congr hmass
      _ = c * (∑' f : (i : Fin n) → α i, ∏ i, w i (f i)) := tsum_mul_left
      _ = _ := by rw [tsum_fin_pi_prod_nonneg n α w hw]
  have hc : c ≠ 0 := by
    intro hz
    rw [hU, hz, zero_mul] at hpos
    exact (lt_irrefl 0) hpos
  have hW : (∏ i, ∑' a, w i a) ≠ 0 := by
    intro hz
    rw [hU, hz, mul_zero] at hpos
    exact (lt_irrefl 0) hpos
  rw [hmass f, hU, Finset.prod_div_distrib]
  field_simp

end RiemannResearch.Probability.ProductConditioning
