import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.BigOperators.Fin

/-! # Recovery of a finite collision atom by two torus coordinates

Average squared character sums over differences of two independent rectangular
word windows. The resulting product Fejér weights are nonnegative on phase
differences and are exactly one on collisions. The frequency window grows
with the sampled finite configuration held fixed.
-/

noncomputable section
open Filter
open scoped BigOperators ComplexConjugate Topology Classical

namespace RiemannResearch.Analysis.TorusCollisionReconstruction
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Transposition preserves the squared Hilbert--Schmidt norm of the associated
Gram operator. Both index sets may contain repeated feature rows. -/
theorem sum_normSq_gram_swap (u : κ → ι → ℂ) :
    (∑ a, ∑ b, Complex.normSq (∑ i, u a i * conj (u b i))) =
      ∑ i, ∑ j, Complex.normSq (∑ a, u a i * conj (u a j)) := by
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum, ← Complex.mul_conj, map_sum, map_mul, Complex.conj_conj,
    Finset.sum_mul, Finset.mul_sum]
  let P (a : κ × κ) (j : ι × ι) :=
    u a.1 j.2 * conj (u a.2 j.2) * (conj (u a.1 j.1) * u a.2 j.1)
  have hs := Finset.sum_comm (s := (Finset.univ : Finset (κ × κ)))
    (t := (Finset.univ : Finset (ι × ι))) (f := P)
  simp only [Fintype.sum_prod_type, P] at hs
  refine hs.trans ?_
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  ring

/-- A normalized character sum over one coordinate. -/
def modeMean (M : ℕ) (z : ℂ) : ℂ :=
  (∑ k ∈ Finset.range (M+1), z ^ k) / (M+1 : ℕ)

@[simp] theorem modeMean_one (M : ℕ) : modeMean M 1 = 1 := by
  have h : ((M+1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero M)
  simp only [modeMean, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, div_self h]

theorem modeMean_tendsto (z : ℂ) (hz : ‖z‖ = 1) :
    Tendsto (fun M => modeMean M z) atTop (𝓝 (if z = 1 then 1 else 0)) := by
  by_cases he : z = 1
  · simp [he]
  rw [if_neg he, tendsto_zero_iff_norm_tendsto_zero]
  have hN : Tendsto (fun M : ℕ => ((M+1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  apply squeeze_zero (fun M => norm_nonneg _) ?_ (hN.const_div_atTop (2/‖z-1‖))
  intro M
  simp only [modeMean, geom_sum_eq he, norm_div, Complex.norm_natCast]
  gcongr
  exact (norm_sub_le _ _).trans (by simp [hz]; norm_num)

/-- Ordered pairs with equal values in both coordinates. -/
def phaseCollision (z w : ι → ℂ) : ℕ :=
  ∑ i, ∑ j, if z i = z j ∧ w i = w j then 1 else 0

/-- A rectangular compact-group character. -/
def word (z w : ι → ℂ) {M : ℕ} (a : Fin (M+1) × Fin (M+1)) (i : ι) : ℂ :=
  z i ^ a.1.val * w i ^ a.2.val

/-- Product Fejér average of squared amplitudes. The windows in the two
squared-character factors are independently sampled. -/
def fejerEnergy (z w : ι → ℂ) (M : ℕ) : ℝ :=
  (∑ a : Fin (M+1) × Fin (M+1), ∑ b : Fin (M+1) × Fin (M+1),
    Complex.normSq (∑ i, word z w a i * conj (word z w b i))) / ((M+1 : ℕ) : ℝ)^4

omit [Fintype ι] in
private theorem word_gram_factor (z w : ι → ℂ) (M : ℕ) (i j : ι) :
    (∑ a : Fin (M+1) × Fin (M+1), word z w a i * conj (word z w a j)) =
      (∑ k ∈ Finset.range (M+1), (z i * conj (z j))^k) *
      ∑ k ∈ Finset.range (M+1), (w i * conj (w j))^k := by
  rw [← Fin.sum_univ_eq_sum_range (fun k => (z i * conj (z j))^k),
      ← Fin.sum_univ_eq_sum_range (fun k => (w i * conj (w j))^k)]
  simp only [Fintype.sum_prod_type, word, Finset.sum_mul, Finset.mul_sum, mul_pow, map_mul, map_pow]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  ring

/-- On the observation side every summand is nonnegative, and both coordinate
averages factor independently. -/
theorem fejerEnergy_eq_pair_kernel (z w : ι → ℂ) (M : ℕ) :
    fejerEnergy z w M = ∑ i, ∑ j,
      Complex.normSq (modeMean M (z i * conj (z j))) *
      Complex.normSq (modeMean M (w i * conj (w j))) := by
  rw [fejerEnergy, sum_normSq_gram_swap (word z w (M := M))]
  simp only [word_gram_factor, Complex.normSq_mul, modeMean,
    Complex.normSq_div, Complex.normSq_natCast]
  conv_lhs => rw [div_eq_mul_inv, Finset.sum_mul]; enter [2, i]; rw [Finset.sum_mul]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

private theorem unit_ratio_eq_one_iff (z u : ℂ) (hu : ‖u‖ = 1) :
    z * conj u = 1 ↔ z = u := by
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  rw [← RCLike.inv_eq_conj hu, ← div_eq_mul_inv, div_eq_one_iff_eq hu0]

/-- A single finite word window upper-bounds the full ordered collision count. -/
theorem phaseCollision_le_fejerEnergy (z w : ι → ℂ)
    (hz : ∀ i, ‖z i‖ = 1) (hw : ∀ i, ‖w i‖ = 1) (M : ℕ) :
    (phaseCollision z w : ℝ) ≤ fejerEnergy z w M := by
  rw [fejerEnergy_eq_pair_kernel, phaseCollision]
  push_cast
  apply Finset.sum_le_sum; intro i _
  apply Finset.sum_le_sum; intro j _
  split_ifs with hij
  · rw [(unit_ratio_eq_one_iff _ _ (hz j)).mpr hij.1,
        (unit_ratio_eq_one_iff _ _ (hw j)).mpr hij.2]
    simp
  · exact mul_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)

/-- For each fixed finite sample, growing the word window recovers precisely
the number of ordered pairs equal in both phase coordinates. -/
theorem fejerEnergy_tendsto_collision (z w : ι → ℂ)
    (hz : ∀ i, ‖z i‖ = 1) (hw : ∀ i, ‖w i‖ = 1) :
    Tendsto (fejerEnergy z w) atTop (𝓝 (phaseCollision z w : ℝ)) := by
  change Tendsto (fun M => fejerEnergy z w M) _ _
  simp only [fejerEnergy_eq_pair_kernel, phaseCollision, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero]
  apply tendsto_finsetSum; intro i _
  apply tendsto_finsetSum; intro j _
  have ha := modeMean_tendsto (z i * conj (z j)) (by simp [hz])
  have hb := modeMean_tendsto (w i * conj (w j)) (by simp [hw])
  simp only [unit_ratio_eq_one_iff _ _ (hz j)] at ha
  simp only [unit_ratio_eq_one_iff _ _ (hw j)] at hb
  have h := (Complex.continuous_normSq.continuousAt.tendsto.comp ha).mul
    (Complex.continuous_normSq.continuousAt.tendsto.comp hb)
  by_cases hjz : z i = z j <;> by_cases hjw : w i = w j <;>
    simpa [Function.comp_def, hjz, hjw] using h

/-- Identical word pairs contribute the zero-frequency amplitude exactly.
Their contribution yields a bandwidth floor independently of collisions. -/
theorem zero_word_floor_le_fejerEnergy (z w : ι → ℂ)
    (hz : ∀ i, ‖z i‖ = 1) (hw : ∀ i, ‖w i‖ = 1) (M : ℕ) :
    (Fintype.card ι : ℝ)^2 / ((M+1 : ℕ) : ℝ)^2 ≤ fejerEnergy z w M := by
  let W := Fin (M+1) × Fin (M+1)
  let E (a b : W) := Complex.normSq (∑ i, word z w a i * conj (word z w b i))
  have hd (a : W) : E a a = (Fintype.card ι : ℝ)^2 := by
    have hu (i : ι) : word z w a i * conj (word z w a i) = 1 := by
      apply (unit_ratio_eq_one_iff _ _ _).mpr rfl
      simp [word, hz, hw]
    simp only [E, hu, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      Complex.normSq_natCast, pow_two]
  have hrow (a : W) : (Fintype.card ι : ℝ)^2 ≤ ∑ b, E a b := by
    rw [← hd a]
    exact Finset.single_le_sum (f := E a) (fun b _ => Complex.normSq_nonneg _) (Finset.mem_univ a)
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset W)) (fun a _ => hrow a)
  have hc : ((M+1 : ℕ) : ℝ)^2 * (Fintype.card ι : ℝ)^2 ≤ ∑ a, ∑ b, E a b := by
    simpa only [W, Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_mul, pow_two] using hs
  change _ ≤ (∑ a, ∑ b, E a b) / ((M+1 : ℕ) : ℝ)^4
  calc
    _ = (((M+1 : ℕ) : ℝ)^2 * (Fintype.card ι : ℝ)^2) / ((M+1 : ℕ) : ℝ)^4 := by
      have hp : 0 < ((M+1 : ℕ) : ℝ) := by positivity
      field_simp
    _ ≤ _ := div_le_div_of_nonneg_right hc (by positivity)

/-- At fixed height the natural-number floor is eventually the exact collision
count. The threshold in word order can depend on all sampled phases. -/
theorem eventually_floor_fejerEnergy_eq_collision (z w : ι → ℂ)
    (hz : ∀ i, ‖z i‖ = 1) (hw : ∀ i, ‖w i‖ = 1) :
    ∀ᶠ M in atTop, ⌊fejerEnergy z w M⌋₊ = phaseCollision z w := by
  have hlim := fejerEnergy_tendsto_collision z w hz hw
  filter_upwards [hlim.eventually_lt_const
    (show (phaseCollision z w : ℝ) < (phaseCollision z w : ℝ) + 1 by linarith)] with M hM
  have hl := phaseCollision_le_fejerEnergy z w hz hw M
  exact (Nat.floor_eq_iff ((Nat.cast_nonneg _).trans hl)).mpr ⟨hl, hM⟩

end RiemannResearch.Analysis.TorusCollisionReconstruction
