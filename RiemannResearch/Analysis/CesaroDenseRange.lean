import RiemannResearch.Analysis.CesaroWeightedContraction
import Mathlib.Topology.Algebra.Module.ClosedSubmodule
import Mathlib.Tactic

/-!
# Dense nonclosed range of the actual Cesaro operator

Source: user-provided conditional-iid manuscript, Section 4, completed in
`CesaroOperatorProof.md`. Finite differences provide explicit preimages of every
finitely supported output. The alternating output is in J but has no H preimage.
-/
noncomputable section
open Filter
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.Analysis.Cesaro
open RH.ArithmeticCumulative RH.Pareto Probability.ConditionalIID

/-- The exact algebraic inverse of positive-index Cesaro means. -/
def inverseMean (y : ℕ → ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) * y n - ((n - 1 : ℕ) : ℝ) * y (n - 1)

@[simp] theorem inverseMean_zero (y : ℕ → ℝ) : inverseMean y 0 = 0 := by
  simp [inverseMean]

theorem inverseMean_sum (y : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, inverseMean y n) = (N : ℝ) * y N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    simp only [inverseMean, Nat.add_sub_cancel]
    ring

theorem cesaro_inverseMean (y : ℕ → ℝ) (N : ℕ) (hN : 0 < N) :
    cesaro (inverseMean y) N = y N := by
  rw [cesaro, inverseMean_sum]
  have hn : (N : ℝ) ≠ 0 := by positivity
  field_simp

/-- Finite output support gives finite support of its explicit inverse. -/
theorem inverseMean_finite_support (y : ℕ → ℝ) (N : ℕ)
    (hy : ∀ n, N < n → y n = 0) (n : ℕ) (hn : N + 1 < n) :
    inverseMean y n = 0 := by
  simp only [inverseMean, hy n (by omega), hy (n - 1) (by omega), mul_zero, sub_self]

/-- Every finite-support vector of J is in the actual bundled Cesaro range. -/
theorem cesaroOperator_finite_support_range (u : ThresholdHilbert) (N : ℕ)
    (hu : ∀ k, N ≤ k → u k = 0) : ∃ f : ThresholdHilbert, cesaroOperator f = u := by
  let y : ℕ → ℝ
    | 0 => 0
    | k + 1 => u k / Real.sqrt (mixtureWeight (k + 1))
  have hy : ∀ n, N < n → y n = 0 := by
    intro n hn
    cases n with
    | zero => simp [y]
    | succ k => simp [y, hu k (by omega)]
  have hs : Summable (fun n : ℕ => positiveWeight n * inverseMean y n ^ 2) := by
    apply summable_of_ne_finset_zero (s := Finset.range (N + 2))
    intro n hn
    have hn' : N + 1 < n := by
      simp only [Finset.mem_range, not_lt] at hn
      omega
    rw [inverseMean_finite_support y N hy n hn']
    simp
  refine ⟨sequenceHilbert (inverseMean y) hs, ?_⟩
  apply Subtype.ext
  funext k
  rw [cesaroOperator_apply, hilbertSequence_sequenceHilbert _ _ (inverseMean_zero y),
    cesaro_inverseMean y (k + 1) (by omega)]
  change Real.sqrt (mixtureWeight (k + 1)) *
    (u k / Real.sqrt (mixtureWeight (k + 1))) = u k
  have hp : Real.sqrt (mixtureWeight (k + 1)) ≠ 0 := by
    apply ne_of_gt
    apply Real.sqrt_pos.mpr
    unfold mixtureWeight
    positivity
  field_simp

/-- Exact coordinate vectors all have legal H-domain preimages. -/
theorem cesaroOperator_single_range (k : ℕ) (a : ℝ) :
    lp.single 2 k a ∈ LinearMap.range cesaroOperator.toLinearMap := by
  apply cesaroOperator_finite_support_range _ (k + 1)
  intro j hj
  simp [lp.single_apply, show j ≠ k by omega]

/-- The actual operator range is dense in the whole target J Hilbert space. -/
theorem cesaroOperator_range_closure :
    (LinearMap.range cesaroOperator.toLinearMap).topologicalClosure = ⊤ := by
  apply top_unique
  intro f hf
  exact (LinearMap.range cesaroOperator.toLinearMap).isClosed_topologicalClosure.mem_of_tendsto
    (lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤) f)
    (Filter.Eventually.of_forall (fun s =>
      (LinearMap.range cesaroOperator.toLinearMap).topologicalClosure.sum_mem (fun i hi =>
        (LinearMap.range cesaroOperator.toLinearMap).le_topologicalClosure
          (cesaroOperator_single_range i (f i)))))

private theorem minus_one_pow_square (n : ℕ) : ((-1 : ℝ) ^ n) ^ 2 = 1 := by
  rw [← pow_mul, Nat.mul_comm, pow_mul]
  norm_num

/-- The alternating physical sequence, encoded as a genuine J vector. -/
def alternatingOutput : ThresholdHilbert :=
  ⟨fun k => Real.sqrt (mixtureWeight (k + 1)) * (-1 : ℝ) ^ (k + 1), by
    apply (memℓp_gen_iff (show 0 < (2 : ENNReal).toReal by norm_num)).2
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs,
      mul_pow, Real.sq_sqrt (mixtureWeight_nonneg _), minus_one_pow_square, mul_one]
      using hasSum_mixtureWeight.summable⟩

/-- The explicit alternating J vector has no preimage in H. -/
theorem alternatingOutput_not_in_range :
    alternatingOutput ∉ LinearMap.range cesaroOperator.toLinearMap := by
  rintro ⟨f, hf⟩
  have hmean : ∀ n, 0 < n → cesaro (hilbertSequence f) n = (-1 : ℝ) ^ n := by
    intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    have h := congrArg (fun v : ThresholdHilbert => v k) hf
    change Real.sqrt (mixtureWeight (k + 1)) * cesaro (hilbertSequence f) (k + 1) =
      Real.sqrt (mixtureWeight (k + 1)) * (-1 : ℝ) ^ (k + 1) at h
    have hp : Real.sqrt (mixtureWeight (k + 1)) ≠ 0 := by
      apply ne_of_gt
      apply Real.sqrt_pos.mpr
      unfold mixtureWeight
      positivity
    exact (mul_left_cancel₀ hp) h
  have hval : ∀ k, hilbertSequence f (k + 1) = (2 * (k : ℝ) + 1) * (-1 : ℝ) ^ (k + 1) := by
    intro k
    have hr := recover (fun n => (hilbertSequence f n : ℂ)) k
    rw [mean_ofReal, mean_ofReal] at hr
    have hr' : hilbertSequence f (k + 1) =
        ((k + 1 : ℕ) : ℝ) * cesaro (hilbertSequence f) (k + 1) -
        (k : ℝ) * cesaro (hilbertSequence f) k := by exact_mod_cast hr
    rw [hmean (k + 1) (by omega)] at hr'
    cases k with
    | zero => simpa using hr'
    | succ k =>
      rw [hmean (k + 1) (by omega)] at hr'
      rw [hr']
      simp only [pow_succ, Nat.cast_add, Nat.cast_one]
      ring
  have hbound : ∀ k, (1 / 2 : ℝ) ≤ (f k) ^ 2 := by
    intro k
    rw [← hilbertSequence_weighted_square, hval, mul_pow, minus_one_pow_square, mul_one,
      positiveWeight_succ]
    unfold paretoWeight
    simp only [div_mul_eq_mul_div, one_mul]
    have hp : 0 < ((k : ℝ) + 1) * ((k : ℝ) + 2) := by positivity
    apply (le_div_iff₀ hp).mpr
    nlinarith [sq_nonneg (k : ℝ), Nat.cast_nonneg (α := ℝ) k]
  have hz := (hilbert_coordinate_square_summable f).tendsto_atTop_zero
  have he : ∀ᶠ k : ℕ in atTop, (f k) ^ 2 < (1 / 2 : ℝ) :=
    hz.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨k, hk⟩ := he.exists
  exact (not_lt_of_ge (hbound k)) hk

/-- The genuine H-to-J Cesaro operator has nonclosed range. -/
theorem cesaroOperator_range_not_closed :
    ¬ IsClosed (Set.range cesaroOperator) := by
  intro hc
  have hcl : (LinearMap.range cesaroOperator.toLinearMap).topologicalClosure =
      LinearMap.range cesaroOperator.toLinearMap := by
    exact hc.submodule_topologicalClosure_eq
  have htop : LinearMap.range cesaroOperator.toLinearMap = ⊤ := by
    rw [← hcl]
    exact cesaroOperator_range_closure
  exact alternatingOutput_not_in_range (by rw [htop]; trivial)

end RiemannResearch.Analysis.Cesaro
