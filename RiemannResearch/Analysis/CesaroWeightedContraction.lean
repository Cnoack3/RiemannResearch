import RiemannResearch.Analysis.CesaroFiniteCalculus
import RiemannResearch.RH.ThresholdHilbertSpace
import RiemannResearch.RH.ConditionalUniformMixture
import Mathlib.Tactic

/-!
# The actual weighted Cesaro contraction

Source: user-provided conditional-iid manuscript, Section 4, and
`CesaroOperatorProof.md`. A finite Abel identity retains the nonnegative terminal
term, proving the weighted contraction for every square-summable input. The map
is bundled on genuine complete `lp` spaces using square-root weight coordinates.
-/
noncomputable section
open Filter
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.Analysis.Cesaro
open RH.ArithmeticCumulative RH.Pareto Probability.ConditionalIID

private theorem cesaro_range (F : ℕ → ℝ) (N : ℕ) :
    cesaro F N = (∑ k ∈ Finset.range N, F (k + 1)) / (N : ℝ) := by
  have he : (∑ n ∈ Finset.Icc 1 N, F n) = ∑ k ∈ Finset.range N, F (k + 1) := by
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih]
  exact congrArg (fun x : ℝ => x / (N : ℝ)) he

/-- Finite Jensen inequality, for the actual arithmetic Cesaro mean. -/
theorem cesaro_square_le_average_square (F : ℕ → ℝ) (N : ℕ) (hN : 0 < N) :
    cesaro F N ^ 2 ≤ (∑ k ∈ Finset.range N, F (k + 1) ^ 2) / (N : ℝ) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range N)
    (fun _ => (1 : ℝ)) (fun k => F (k + 1))
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_one] at hcs
  have hp : (0 : ℝ) < N := by positivity
  rw [cesaro_range, div_pow]
  calc
    _ ≤ ((N : ℝ) * ∑ k ∈ Finset.range N, F (k + 1) ^ 2) / (N : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hcs (sq_nonneg _)
    _ = _ := by field_simp <;> ring

/-- The exact finite Abel identity behind the weighted contraction. -/
theorem cesaro_square_majorant_abel (F : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, mixtureWeight (k + 1) / ((k + 1 : ℕ) : ℝ) *
      ∑ j ∈ Finset.range (k + 1), F (j + 1) ^ 2) =
      (∑ k ∈ Finset.range N, weight (k + 1) * F (k + 1) ^ 2) -
        weight (N + 1) * ∑ j ∈ Finset.range N, F (j + 1) ^ 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih,
      mixture_density_step (N + 1) (by omega), Finset.sum_range_succ]
    ring

/-- Every prefix of smoothed energy is bounded by the matching input prefix. -/
theorem cesaro_energy_prefix_le (F : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, mixtureWeight (k + 1) * cesaro F (k + 1) ^ 2) ≤
      ∑ k ∈ Finset.range N, weight (k + 1) * F (k + 1) ^ 2 := by
  calc
    _ ≤ ∑ k ∈ Finset.range N, mixtureWeight (k + 1) / ((k + 1 : ℕ) : ℝ) *
        ∑ j ∈ Finset.range (k + 1), F (j + 1) ^ 2 := by
      apply Finset.sum_le_sum
      intro k hk
      have h := mul_le_mul_of_nonneg_left
        (cesaro_square_le_average_square F (k + 1) (by omega)) (mixtureWeight_nonneg (k + 1))
      convert h using 1 <;> ring
    _ = _ := cesaro_square_majorant_abel F N
    _ ≤ _ := sub_le_self _ (mul_nonneg (weight_nonneg _) (Finset.sum_nonneg (by
      intro j hj
      exact sq_nonneg _)))

/-- Cesaro averaging preserves the actual weighted l² domain. -/
theorem cesaro_weighted_square_summable (F : ℕ → ℝ)
    (hF : Summable (fun k : ℕ => weight (k + 1) * F (k + 1) ^ 2)) :
    Summable (fun k : ℕ => mixtureWeight (k + 1) * cesaro F (k + 1) ^ 2) := by
  apply summable_of_sum_range_le
    (fun k => mul_nonneg (mixtureWeight_nonneg _) (sq_nonneg _))
    (c := ∑' k : ℕ, weight (k + 1) * F (k + 1) ^ 2)
  intro N
  exact (cesaro_energy_prefix_le F N).trans
    (Summable.sum_le_tsum (Finset.range N)
      (fun k hk => mul_nonneg (weight_nonneg _) (sq_nonneg _)) hF)

/-- The exact H-to-J contraction inequality for arbitrary H vectors. -/
theorem cesaro_weighted_energy_le (F : ℕ → ℝ)
    (hF : Summable (fun k : ℕ => weight (k + 1) * F (k + 1) ^ 2)) :
    (∑' k : ℕ, mixtureWeight (k + 1) * cesaro F (k + 1) ^ 2) ≤
      ∑' k : ℕ, weight (k + 1) * F (k + 1) ^ 2 := by
  apply le_of_tendsto (cesaro_weighted_square_summable F hF).hasSum.tendsto_sum_nat
  exact Filter.Eventually.of_forall (fun N => (cesaro_energy_prefix_le F N).trans
    (Summable.sum_le_tsum (Finset.range N)
      (fun k hk => mul_nonneg (weight_nonneg _) (sq_nonneg _)) hF))

private theorem physical_weight (k : ℕ) : weight (k + 1) = paretoWeight k := by
  unfold weight paretoWeight
  push_cast
  ring

private theorem source_summable (f : ThresholdHilbert) :
    Summable (fun k : ℕ => weight (k + 1) * hilbertSequence f (k + 1) ^ 2) := by
  simpa only [physical_weight, ← positiveWeight_succ, hilbertSequence_weighted_square]
    using hilbert_coordinate_square_summable f

/-- Coordinates of the actual Cesaro operator, in the unitary l² realization of J. -/
def hilbertCesaro (f : ThresholdHilbert) : ThresholdHilbert :=
  ⟨fun k => Real.sqrt (mixtureWeight (k + 1)) * cesaro (hilbertSequence f) (k + 1), by
    apply (memℓp_gen_iff (show 0 < (2 : ENNReal).toReal by norm_num)).2
    have hs := cesaro_weighted_square_summable (hilbertSequence f) (source_summable f)
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs,
      mul_pow, Real.sq_sqrt (mixtureWeight_nonneg _)] using hs⟩

@[simp] theorem hilbertCesaro_apply (f : ThresholdHilbert) (k : ℕ) :
    hilbertCesaro f k =
      Real.sqrt (mixtureWeight (k + 1)) * cesaro (hilbertSequence f) (k + 1) := rfl

theorem hilbertCesaro_norm_sq (f : ThresholdHilbert) :
    ‖hilbertCesaro f‖ ^ 2 =
      ∑' k : ℕ, mixtureWeight (k + 1) * cesaro (hilbertSequence f) (k + 1) ^ 2 := by
  rw [hilbert_norm_sq]
  congr 1
  funext k
  simp only [hilbertCesaro_apply, mul_pow, Real.sq_sqrt (mixtureWeight_nonneg _)]

theorem hilbertCesaro_norm_le (f : ThresholdHilbert) : ‖hilbertCesaro f‖ ≤ ‖f‖ := by
  have h := cesaro_weighted_energy_le (hilbertSequence f) (source_summable f)
  have hs : (∑' k : ℕ, weight (k + 1) * hilbertSequence f (k + 1) ^ 2) = ‖f‖ ^ 2 := by
    rw [hilbert_norm_sq]
    congr 1
    funext k
    rw [physical_weight, ← positiveWeight_succ, hilbertSequence_weighted_square]
  rw [← hilbertCesaro_norm_sq, hs] at h
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

/-- The actual linear operator before bundling continuity. -/
def hilbertCesaroLinear : ThresholdHilbert →ₗ[ℝ] ThresholdHilbert where
  toFun := hilbertCesaro
  map_add' f g := by
    apply Subtype.ext
    funext k
    simp only [hilbertCesaro_apply, lp.coeFn_add, Pi.add_apply]
    have h : hilbertSequence (f + g) = hilbertSequence f + hilbertSequence g :=
      hilbertSequenceLinear.map_add f g
    rw [h]
    simp [cesaro, Pi.add_apply, Finset.sum_add_distrib, add_div, mul_add]
  map_smul' c f := by
    apply Subtype.ext
    funext k
    simp only [hilbertCesaro_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    have h : hilbertSequence (c • f) = c • hilbertSequence f :=
      hilbertSequenceLinear.map_smul c f
    rw [h]
    simp only [cesaro, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, RingHom.id_apply]
    ring

/-- C : H → J, under the explicit square-root-weight unitary coordinates. -/
def cesaroOperator : ThresholdHilbert →L[ℝ] ThresholdHilbert :=
  hilbertCesaroLinear.mkContinuous 1 (fun f => by
    change ‖hilbertCesaro f‖ ≤ 1 * ‖f‖
    simpa using hilbertCesaro_norm_le f)

@[simp] theorem cesaroOperator_apply (f : ThresholdHilbert) (k : ℕ) :
    cesaroOperator f k =
      Real.sqrt (mixtureWeight (k + 1)) * cesaro (hilbertSequence f) (k + 1) := rfl

theorem cesaroOperator_injective : Function.Injective cesaroOperator := by
  intro f g h
  apply hilbertSequence_injective
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    have hm : mean (fun k => (hilbertSequence f k : ℂ)) =
        mean (fun k => (hilbertSequence g k : ℂ)) := by
      funext k
      cases k with
      | zero => simp
      | succ k =>
        rw [mean_ofReal, mean_ofReal]
        have hk := congrArg (fun v : ThresholdHilbert => v k) h
        simp only [cesaroOperator_apply] at hk
        have hp : Real.sqrt (mixtureWeight (k + 1)) ≠ 0 := by
          apply ne_of_gt
          apply Real.sqrt_pos.mpr
          unfold mixtureWeight
          positivity
        exact congrArg (fun x : ℝ => (x : ℂ)) ((mul_left_cancel₀ hp) hk)
    exact Complex.ofReal_injective (mean_injective_on_positive hm n)

end RiemannResearch.Analysis.Cesaro
