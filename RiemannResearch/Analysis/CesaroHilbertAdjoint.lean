import RiemannResearch.Analysis.CesaroWeightedContraction
import RiemannResearch.Analysis.CesaroPosteriorKernel
import RiemannResearch.RH.ThresholdHilbertAdjoint
import Mathlib.Tactic

/-!
# Identification of the actual Hilbert adjoint with posterior averaging

Source: `CesaroOperatorProof.md`, completing Section 4 of the user-provided
conditional-iid manuscript. The actual continuous operator's adjoint is tested
against existing physical point atoms, reducing identification to one convergent
tail sum, without an assumed Fubini identity.
-/
noncomputable section
open Filter
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.Analysis.Cesaro
open RH.ArithmeticCumulative RH.Pareto Probability.ConditionalIID

/-- Physical J coordinates in the square-root-q realization. -/
def conditionalSequence (g : ThresholdHilbert) : ℕ → ℝ
  | 0 => 0
  | k + 1 => g k / Real.sqrt (mixtureWeight (k + 1))

private theorem sqrt_q_ne (k : ℕ) : Real.sqrt (mixtureWeight (k + 1)) ≠ 0 := by
  apply ne_of_gt
  apply Real.sqrt_pos.mpr
  unfold mixtureWeight
  positivity

@[simp] theorem conditionalSequence_square (g : ThresholdHilbert) (k : ℕ) :
    mixtureWeight (k + 1) * conditionalSequence g (k + 1) ^ 2 = (g k) ^ 2 := by
  simp only [conditionalSequence, div_pow, Real.sq_sqrt (mixtureWeight_nonneg _)]
  have hq : mixtureWeight (k + 1) ≠ 0 := by unfold mixtureWeight; positivity
  field_simp

theorem conditionalSequence_mem (g : ThresholdHilbert) : InConditionalL2 (conditionalSequence g) := by
  simpa only [InConditionalL2, conditionalSequence_square] using hilbert_coordinate_square_summable g

theorem conditionalSequence_injective : Function.Injective conditionalSequence := by
  intro f g h
  apply Subtype.ext
  funext k
  have hk := congrFun h (k + 1)
  exact (div_left_inj' (sqrt_q_ne k)).mp hk

/-- The bundled operator's decoded coordinates are the original arithmetic means. -/
@[simp] theorem conditionalSequence_cesaroOperator (f : ThresholdHilbert) (k : ℕ) :
    conditionalSequence (cesaroOperator f) (k + 1) = cesaro (hilbertSequence f) (k + 1) := by
  change Real.sqrt (mixtureWeight (k + 1)) * cesaro (hilbertSequence f) (k + 1) /
    Real.sqrt (mixtureWeight (k + 1)) = _
  field_simp [sqrt_q_ne k]

/-- J inner products in the actual physical coordinates. -/
theorem conditional_inner_weighted (f g : ThresholdHilbert) :
    inner ℝ f g = ∑' k : ℕ, mixtureWeight (k + 1) *
      (conditionalSequence f (k + 1) * conditionalSequence g (k + 1)) := by
  rw [lp.inner_eq_tsum]
  apply tsum_congr
  intro k
  rw [RCLike.inner_apply']
  change f k * g k = mixtureWeight (k + 1) *
    ((f k / Real.sqrt (mixtureWeight (k + 1))) *
      (g k / Real.sqrt (mixtureWeight (k + 1))))
  rw [div_mul_div_comm, ← pow_two, Real.sq_sqrt (mixtureWeight_nonneg _)]
  have hq : mixtureWeight (k + 1) ≠ 0 := by unfold mixtureWeight; positivity
  field_simp

/-- Shift a one-sided series after its identically zero initial segment. -/
private theorem tsum_ge_tail (v : ℕ → ℝ) (n : ℕ)
    (hv : Summable (fun k : ℕ => v (n + k))) :
    (∑' k : ℕ, if n ≤ k then v k else 0) = ∑' k : ℕ, v (n + k) := by
  let u : ℕ → ℝ := fun k => if n ≤ k then v k else 0
  have he : (fun k : ℕ => u (k + n)) = fun k : ℕ => v (n + k) := by
    funext k
    simp [u, Nat.add_comm]
  have hs : Summable u := (summable_nat_add_iff n).mp (he.symm ▸ hv)
  have hz : ∑ k ∈ Finset.range n, u k = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    simp [u, show ¬ n ≤ k by exact Nat.not_le.mpr (Finset.mem_range.mp hk)]
  have hsum := Summable.sum_add_tsum_nat_add n hs
  rw [hz, zero_add, he] at hsum
  exact hsum.symm

/-- A physical point atom has the expected step tail of arithmetic means. -/
theorem cesaro_hilbertAtom (n : ℕ) (hn : 0 < n) (t : ℕ) :
    cesaro (hilbertSequence (hilbertAtom n hn)) t = if n ≤ t then 1 / (t : ℝ) else 0 := by
  rw [hilbertAtom_sequence]
  unfold cesaro
  simp only [Finset.sum_ite_eq', Finset.mem_Icc]
  have hn1 : 1 ≤ n := hn
  simp only [hn1, true_and]
  split_ifs <;> simp_all

/-- Pairing the actual image of a point atom with a J vector is its posterior tail. -/
theorem cesaroOperator_atom_inner (n : ℕ) (g : ThresholdHilbert) :
    inner ℝ (cesaroOperator (hilbertAtom (n + 1) (by omega))) g =
      ∑' k : ℕ, mixtureWeight ((n + 1) + k) / (((n + 1) + k : ℕ) : ℝ) *
        conditionalSequence g ((n + 1) + k) := by
  rw [conditional_inner_weighted]
  simp_rw [conditionalSequence_cesaroOperator, cesaro_hilbertAtom]
  have he : (fun k : ℕ => mixtureWeight (k + 1) *
      ((if n + 1 ≤ k + 1 then 1 / ((k + 1 : ℕ) : ℝ) else 0) * conditionalSequence g (k + 1))) =
    (fun k : ℕ => if n ≤ k then mixtureWeight (k + 1) / ((k + 1 : ℕ) : ℝ) *
      conditionalSequence g (k + 1) else 0) := by
    funext k
    by_cases h : n ≤ k
    · simp only [if_pos h, if_pos (show n + 1 ≤ k + 1 by omega)]
      ring
    · simp [h, show ¬ n + 1 ≤ k + 1 by omega]
  rw [he, tsum_ge_tail]
  · apply tsum_congr
    intro k
    rw [show n + k + 1 = (n + 1) + k by omega]
  · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      adjointTail_summable (conditionalSequence g) (conditionalSequence_mem g) (n + 1) (by omega)

/-- Full coordinate formula for the actual continuous Hilbert adjoint. -/
theorem cesaroOperator_adjoint_coordinate (g : ThresholdHilbert) (n : ℕ) (hn : 0 < n) :
    hilbertSequence (cesaroOperator.adjoint g) n = adjointSequence (conditionalSequence g) n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have h := ContinuousLinearMap.adjoint_inner_right cesaroOperator
    (hilbertAtom (k + 1) (by omega)) g
  rw [hilbertAtom_inner, cesaroOperator_atom_inner] at h
  have hw : positiveWeight (k + 1) = weight (k + 1) := by
    unfold positiveWeight weight
    rfl
  rw [hw] at h
  unfold adjointSequence
  exact (eq_div_iff (by unfold weight; positivity : weight (k + 1) ≠ 0)).mpr
    (by simpa only [mul_comm] using h)

/-- The actual bundled adjoint is injective, using its proved tail formula. -/
theorem cesaroOperator_adjoint_injective : Function.Injective cesaroOperator.adjoint := by
  intro f g h
  apply conditionalSequence_injective
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    apply adjointSequence_injective_on_positive (conditionalSequence f) (conditionalSequence g)
      (conditionalSequence_mem f) (conditionalSequence_mem g) _ (n + 1) (by omega)
    intro k hk
    rw [← cesaroOperator_adjoint_coordinate f k hk, ← cesaroOperator_adjoint_coordinate g k hk, h]

private theorem cesaro_one_positive (t : ℕ) (ht : 0 < t) :
    cesaro (hilbertSequence hilbertOne) t = 1 := by
  rw [hilbertOne_sequence]
  unfold cesaro
  have hs : (∑ n ∈ Finset.Icc 1 t, zeroAnchor (fun _ => (1 : ℝ)) n) = t := by
    calc
      _ = ∑ n ∈ Finset.Icc 1 t, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro n hn
        simp [zeroAnchor, show n ≠ 0 by have := Finset.mem_Icc.mp hn; omega]
      _ = _ := by simp
  rw [hs]
  exact div_self (by positivity)

/-- The target constant of J, constructed by the actual image of the constant of H. -/
def conditionalOne : ThresholdHilbert := cesaroOperator hilbertOne

@[simp] theorem conditionalOne_sequence (k : ℕ) : conditionalSequence conditionalOne (k + 1) = 1 := by
  rw [conditionalOne, conditionalSequence_cesaroOperator]
  exact cesaro_one_positive (k + 1) (by omega)

theorem conditionalOne_norm_sq : ‖conditionalOne‖ ^ 2 = 1 := by
  rw [conditionalOne, show cesaroOperator hilbertOne = hilbertCesaro hilbertOne from rfl,
    hilbertCesaro_norm_sq]
  have he : ∀ k : ℕ, cesaro (hilbertSequence hilbertOne) (k + 1) = 1 :=
    fun k => cesaro_one_positive (k + 1) (by omega)
  simp_rw [he, one_pow, mul_one]
  exact hasSum_mixtureWeight.tsum_eq

/-- The operator norm is exactly one, with the constant as an attaining vector. -/
theorem cesaroOperator_norm : ‖cesaroOperator‖ = 1 := by
  apply le_antisymm
  · exact cesaroOperator.opNorm_le_bound (by norm_num) (fun f => by
      change ‖hilbertCesaro f‖ ≤ 1 * ‖f‖
      simpa using hilbertCesaro_norm_le f)
  · have hs : ‖hilbertOne‖ = 1 := by
      nlinarith [hilbertOne_norm_sq, norm_nonneg hilbertOne]
    have ht : ‖conditionalOne‖ = 1 := by
      nlinarith [conditionalOne_norm_sq, norm_nonneg conditionalOne]
    have h := cesaroOperator.le_opNorm hilbertOne
    change ‖conditionalOne‖ ≤ ‖cesaroOperator‖ * ‖hilbertOne‖ at h
    simpa only [ht, hs, mul_one] using h

/-- Bayes normalization is the actual adjoint's constant-preservation identity. -/
theorem cesaroOperator_adjoint_one : cesaroOperator.adjoint conditionalOne = hilbertOne := by
  apply hilbertSequence_injective
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    rw [cesaroOperator_adjoint_coordinate _ _ (by omega), hilbertOne_sequence]
    have he : adjointSequence (conditionalSequence conditionalOne) (n + 1) =
        adjointSequence (fun _ => 1) (n + 1) := by
      unfold adjointSequence
      congr 1
      apply tsum_congr
      intro k
      have hp : (n + 1) + k = (n + k) + 1 := by omega
      rw [hp, conditionalOne_sequence]
    rw [he, adjointSequence_one _ (by omega)]
    simp [zeroAnchor]

end RiemannResearch.Analysis.Cesaro
