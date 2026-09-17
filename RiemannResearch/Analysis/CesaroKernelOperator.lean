import RiemannResearch.Analysis.CesaroHilbertAdjoint
import Mathlib.Tactic

/-!
# Actual reversible Markov kernel and its Cesaro Gram realization

Source: `CesaroOperatorProof.md`, Section 4. The row kernel is the exact signed
matrix of C* C on physical point atoms. Its row mass is proved by finite Abel
summation with the endpoint retained and then sent to zero.
-/
noncomputable section
open Filter
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.Analysis.Cesaro
open RH.ArithmeticCumulative RH.Pareto Probability.ConditionalIID

private theorem rowKernel_max_le (n k : ℕ) :
    rowKernel (max n (k + 1)) ≤ weight (k + 1) := by
  apply (rowKernel_le_weight _ (by omega)).trans
  unfold weight
  have hm : ((k + 1 : ℕ) : ℝ) ≤ (max n (k + 1) : ℕ) := by
    exact_mod_cast Nat.le_max_right n (k + 1)
  gcongr

/-- Every physical row of the pair kernel is genuinely summable. -/
theorem rowKernel_row_summable (n : ℕ) :
    Summable (fun k : ℕ => rowKernel (max n (k + 1))) := by
  apply Summable.of_nonneg_of_le (fun _ => rowKernel_nonneg _) (rowKernel_max_le n)
  simpa only [Nat.add_comm] using (hasSum_weight_from 1 (by norm_num)).summable

/-- Exact row prefix, with the kernel boundary contribution retained. -/
theorem rowKernel_row_prefix (n s : ℕ) (hn : 0 < n) :
    (∑ k ∈ Finset.range (n + s), rowKernel (max n (k + 1))) =
      weight n - weight (n + s + 1) + ((n + s : ℕ) : ℝ) * rowKernel (n + s + 1) := by
  induction s with
  | zero =>
    simp only [Nat.add_zero]
    have hsum : (∑ k ∈ Finset.range n, rowKernel (max n (k + 1))) = (n : ℝ) * rowKernel n := by
      calc
        _ = ∑ k ∈ Finset.range n, rowKernel n := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [max_eq_left (by have := Finset.mem_range.mp hk; omega)]
        _ = _ := by simp
    rw [hsum, rowKernel_recurrence n hn, ← mixture_density_step n hn]
    have hp : (n : ℝ) ≠ 0 := by positivity
    field_simp <;> ring
  | succ s ih =>
    have hidx : n + (s + 1) = (n + s) + 1 := by omega
    rw [hidx, Finset.sum_range_succ, ih, max_eq_right (by omega),
      rowKernel_recurrence (n + s + 1) (by omega)]
    have hd := mixture_density_step (n + s + 1) (by omega)
    have hp : (((n + s + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    push_cast at hd ⊢
    field_simp at hd ⊢
    nlinarith

private theorem rowKernel_boundary_le (R : ℕ) :
    (R : ℝ) * rowKernel (R + 1) ≤ 1 / ((R : ℝ) + 1) := by
  calc
    _ ≤ (R : ℝ) * weight (R + 1) :=
      mul_le_mul_of_nonneg_left (rowKernel_le_weight _ (by omega)) (Nat.cast_nonneg _)
    _ ≤ _ := by
      unfold weight
      push_cast
      have h1 : (0 : ℝ) < R + 1 := by positivity
      have h2 : (0 : ℝ) < R + 2 := by positivity
      apply (le_div_iff₀ h1).mpr
      field_simp
      nlinarith

private theorem rowKernel_boundary_tendsto :
    Tendsto (fun R : ℕ => (R : ℝ) * rowKernel (R + 1)) atTop (𝓝 0) := by
  have hi : Tendsto (fun R : ℕ => 1 / ((R : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one, Function.comp_def] using
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
  exact squeeze_zero (fun R => mul_nonneg (Nat.cast_nonneg _) (rowKernel_nonneg _))
    rowKernel_boundary_le hi

/-- The exact marginal identity for the full pair-row kernel. -/
theorem rowKernel_row_sum (n : ℕ) (hn : 0 < n) :
    (∑' k : ℕ, rowKernel (max n (k + 1))) = weight n := by
  have hl := (rowKernel_row_summable n).hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat n)
  have hw : Tendsto (fun s : ℕ => weight (n + s + 1)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      weight_tendsto_zero.comp (tendsto_add_atTop_nat (n + 1))
  have hb : Tendsto (fun s : ℕ => ((n + s : ℕ) : ℝ) * rowKernel (n + s + 1)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      rowKernel_boundary_tendsto.comp (tendsto_add_atTop_nat n)
  have hc : Tendsto (fun _ : ℕ => weight n) atTop (𝓝 (weight n)) := tendsto_const_nhds
  have hr := (hc.sub hw).add hb
  have hr' : Tendsto (fun s : ℕ => ∑ k ∈ Finset.range (n + s), rowKernel (max n (k + 1)))
      atTop (𝓝 (weight n)) := by
    simpa only [rowKernel_row_prefix n _ hn, sub_zero, add_zero] using hr
  exact tendsto_nhds_unique (by simpa only [Function.comp_def, Nat.add_comm] using hl) hr'

/-- The explicitly defined row transition is stochastic. -/
theorem rowTransition_hasSum (n : ℕ) (hn : 0 < n) :
    HasSum (fun k : ℕ => rowTransition n (k + 1)) 1 := by
  have h := (rowKernel_row_summable n).hasSum.div_const (weight n)
  rw [rowKernel_row_sum n hn] at h
  have hw : weight n ≠ 0 := by unfold weight; positivity
  simpa only [rowTransition, div_self hw] using h

/-- The stationary law is precisely the original Pareto marginal. -/
theorem rowTransition_stationary (m : ℕ) (hm : 0 < m) :
    HasSum (fun k : ℕ => weight (k + 1) * rowTransition (k + 1) m) (weight m) := by
  have he : (fun k : ℕ => weight (k + 1) * rowTransition (k + 1) m) =
      (fun k : ℕ => rowKernel (max m (k + 1))) := by
    funext k
    unfold rowTransition
    have hw : weight (k + 1) ≠ 0 := by unfold weight; positivity
    field_simp
    rw [max_comm]
  rw [he]
  rw [← rowKernel_row_sum m hm]
  exact (rowKernel_row_summable m).hasSum

/-- The row-to-row Markov operator as an actual continuous Hilbert operator. -/
def cesaroMarkovOperator : ThresholdHilbert →L[ℝ] ThresholdHilbert :=
  cesaroOperator.adjoint.comp cesaroOperator

/-- Exact full signed quadratic form of the actual Markov operator. -/
theorem cesaroMarkovOperator_quadratic (f : ThresholdHilbert) :
    inner ℝ f (cesaroMarkovOperator f) = ‖cesaroOperator f‖ ^ 2 := by
  change inner ℝ f (cesaroOperator.adjoint (cesaroOperator f)) = _
  rw [ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]

theorem cesaroMarkovOperator_positive (f : ThresholdHilbert) :
    0 ≤ inner ℝ f (cesaroMarkovOperator f) := by
  rw [cesaroMarkovOperator_quadratic]
  positivity

theorem cesaroMarkovOperator_symmetric (f g : ThresholdHilbert) :
    inner ℝ f (cesaroMarkovOperator g) = inner ℝ (cesaroMarkovOperator f) g := by
  change inner ℝ f (cesaroOperator.adjoint (cesaroOperator g)) =
    inner ℝ (cesaroOperator.adjoint (cesaroOperator f)) g
  calc
    _ = inner ℝ (cesaroOperator f) (cesaroOperator g) :=
      ContinuousLinearMap.adjoint_inner_right cesaroOperator f (cesaroOperator g)
    _ = inner ℝ (cesaroOperator g) (cesaroOperator f) := real_inner_comm _ _
    _ = inner ℝ g (cesaroOperator.adjoint (cesaroOperator f)) :=
      (ContinuousLinearMap.adjoint_inner_right cesaroOperator g (cesaroOperator f)).symm
    _ = _ := real_inner_comm _ _

theorem cesaroMarkovOperator_one : cesaroMarkovOperator hilbertOne = hilbertOne :=
  cesaroOperator_adjoint_one


/-- Exact point-atom Gram matrix, including every shared latent tail. -/
theorem cesaroOperator_atom_gram (n m : ℕ) :
    inner ℝ (cesaroOperator (hilbertAtom (n + 1) (by omega)))
      (cesaroOperator (hilbertAtom (m + 1) (by omega))) =
        rowKernel (max (n + 1) (m + 1)) := by
  rw [conditional_inner_weighted]
  simp_rw [conditionalSequence_cesaroOperator, cesaro_hilbertAtom]
  let a : ℕ → ℝ := fun k => mixtureWeight (k + 1) *
    ((if n + 1 ≤ k + 1 then 1 / ((k + 1 : ℕ) : ℝ) else 0) *
      (if m + 1 ≤ k + 1 then 1 / ((k + 1 : ℕ) : ℝ) else 0))
  change (∑' k, a k) = _
  let M := max n m
  have hmax : max (n + 1) (m + 1) = M + 1 := by dsimp [M]; omega
  have he : (fun k : ℕ => a (k + M)) =
      fun k : ℕ => mixtureWeight ((M + 1) + k) / ((((M + 1) + k : ℕ) : ℝ) ^ 2) := by
    funext k
    have hn : n + 1 ≤ (k + M) + 1 := by dsimp [M]; omega
    have hm : m + 1 ≤ (k + M) + 1 := by dsimp [M]; omega
    simp only [a, if_pos hn, if_pos hm]
    have hi : k + M + 1 = (M + 1) + k := by omega
    rw [hi]
    ring
  have hs : Summable a := (summable_nat_add_iff M).mp
    (he.symm ▸ rowKernel_summable (M + 1) (by omega))
  have hz : ∑ k ∈ Finset.range M, a k = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hk' : k < M := Finset.mem_range.mp hk
    by_cases hn : n + 1 ≤ k + 1
    · have hm : ¬ m + 1 ≤ k + 1 := by dsimp [M] at hk'; omega
      simp only [a, if_neg hm, mul_zero]
    · simp only [a, if_neg hn, zero_mul, mul_zero]
  have hsum := Summable.sum_add_tsum_nat_add M hs
  rw [hz, zero_add, he] at hsum
  rw [hmax]
  exact hsum.symm

/-- The kernel is the actual matrix of C* C, rather than a separate surrogate. -/
theorem cesaroMarkovOperator_atom_matrix (n m : ℕ) :
    inner ℝ (hilbertAtom (n + 1) (by omega))
      (cesaroMarkovOperator (hilbertAtom (m + 1) (by omega))) =
        rowKernel (max (n + 1) (m + 1)) := by
  change inner ℝ (hilbertAtom (n + 1) (by omega))
    (cesaroOperator.adjoint (cesaroOperator (hilbertAtom (m + 1) (by omega)))) = _
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact cesaroOperator_atom_gram n m

/-- Acting on an actual physical point atom returns the explicit transition column. -/
theorem cesaroMarkovOperator_atom_sequence (n m : ℕ) :
    hilbertSequence (cesaroMarkovOperator (hilbertAtom (m + 1) (by omega))) (n + 1) =
      rowTransition (n + 1) (m + 1) := by
  have h := cesaroMarkovOperator_atom_matrix n m
  rw [hilbertAtom_inner] at h
  have hw : positiveWeight (n + 1) = weight (n + 1) := by
    unfold positiveWeight weight
    rfl
  rw [hw] at h
  unfold rowTransition
  exact (eq_div_iff (by unfold weight; positivity : weight (n + 1) ≠ 0)).mpr
    (by simpa only [mul_comm] using h)


private theorem single_eq_physical_atom (f : ThresholdHilbert) (m : ℕ) :
    lp.single 2 m (f m) = hilbertSequence f (m + 1) • hilbertAtom (m + 1) (by omega) := by
  apply hilbertSequence_injective
  rw [hilbertSequence_smul, hilbertAtom_sequence]
  funext n
  cases n with
  | zero => simp [hilbertSequence]
  | succ k =>
    by_cases hk : k = m
    · subst k
      simp [hilbertSequence, lp.single_apply]
    · simp [hilbertSequence, lp.single_apply, hk, show k + 1 ≠ m + 1 by omega]

/-- The full infinite transition series is the actual operator on every H vector. -/
theorem cesaroMarkovOperator_hasSum (f : ThresholdHilbert) (n : ℕ) :
    HasSum (fun m : ℕ => rowTransition (n + 1) (m + 1) * hilbertSequence f (m + 1))
      (hilbertSequence (cesaroMarkovOperator f) (n + 1)) := by
  have h := ((innerSL ℝ (hilbertAtom (n + 1) (by omega))).comp cesaroMarkovOperator).hasSum
    (lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤) f)
  change HasSum (fun m : ℕ => inner ℝ (hilbertAtom (n + 1) (by omega))
    (cesaroMarkovOperator (lp.single 2 m (f m))))
    (inner ℝ (hilbertAtom (n + 1) (by omega)) (cesaroMarkovOperator f)) at h
  simp_rw [single_eq_physical_atom f, map_smul, real_inner_smul_right,
    cesaroMarkovOperator_atom_matrix] at h
  rw [hilbertAtom_inner] at h
  have hw : positiveWeight (n + 1) = weight (n + 1) := by
    unfold positiveWeight weight
    rfl
  rw [hw] at h
  have hw0 : weight (n + 1) ≠ 0 := by unfold weight; positivity
  have hd := h.div_const (weight (n + 1))
  have hcancel : weight (n + 1) * hilbertSequence (cesaroMarkovOperator f) (n + 1) /
      weight (n + 1) = hilbertSequence (cesaroMarkovOperator f) (n + 1) := by
    field_simp
  rw [hcancel] at hd
  have he : (fun m : ℕ => hilbertSequence f (m + 1) *
      rowKernel (max (n + 1) (m + 1)) / weight (n + 1)) =
      (fun m : ℕ => rowTransition (n + 1) (m + 1) * hilbertSequence f (m + 1)) := by
    funext m
    unfold rowTransition
    ring
  rw [he] at hd
  exact hd

/-- The coordinate form of the actual reversible Markov operator, for every H vector. -/
theorem cesaroMarkovOperator_series (f : ThresholdHilbert) (n : ℕ) :
    hilbertSequence (cesaroMarkovOperator f) (n + 1) =
      ∑' m : ℕ, rowTransition (n + 1) (m + 1) * hilbertSequence f (m + 1) :=
  (cesaroMarkovOperator_hasSum f n).tsum_eq.symm


/-- Exact signed kernel pairing for arbitrary H vectors. -/
theorem cesaroOperator_signed_kernel_pairing (f g : ThresholdHilbert) :
    inner ℝ (cesaroOperator f) (cesaroOperator g) =
      ∑' n : ℕ, ∑' m : ℕ, hilbertSequence f (n + 1) * hilbertSequence g (m + 1) *
        rowKernel (max (n + 1) (m + 1)) := by
  have hpair := weighted_product_summable_of_square
    (hilbertSequence_square_summable f)
    (hilbertSequence_square_summable (cesaroMarkovOperator g))
  rw [← ContinuousLinearMap.adjoint_inner_right]
  change inner ℝ f (cesaroMarkovOperator g) = _
  rw [hilbert_inner_weighted]
  unfold paretoInner
  rw [hpair.tsum_eq_zero_add]
  simp only [hilbertSequence_zero, mul_zero, zero_mul, zero_add]
  apply tsum_congr
  intro n
  rw [cesaroMarkovOperator_series]
  have hw : positiveWeight (n + 1) = weight (n + 1) := by
    unfold positiveWeight weight
    rfl
  rw [hw, ← mul_assoc, ← tsum_mul_left]
  apply tsum_congr
  intro m
  unfold rowTransition
  have hw0 : weight (n + 1) ≠ 0 := by unfold weight; positivity
  field_simp <;> ring

end RiemannResearch.Analysis.Cesaro
