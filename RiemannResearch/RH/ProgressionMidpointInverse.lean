import RiemannResearch.LinearAlgebra.FiniteMatrixInverseComparison
import RiemannResearch.RH.CRTExactDigamma

/-!
# Uniform midpoint comparison for actual finite weighted Gram inverses

Source: user-provided trigamma/DPP discussion, 21 September 2026.
The existing exact progression midpoint theorem supplies the weight bounds.
Only ordinary finite Gram nondegeneracy is required; no saturation is assumed.
-/
noncomputable section
open Filter
open scoped BigOperators
namespace RiemannResearch.RH.Pareto
open RiemannResearch.LinearAlgebra.FiniteConstrainedMatrix
variable {ι : Type*} [Fintype ι]

def progressionGram (Q : ℕ) (I : Finset ℕ) (a : ℕ → ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => ∑ r ∈ I, progressionWeight Q r * a r i * a r j

def midpointGram (Q : ℕ) (I : Finset ℕ) (a : ℕ → ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => ∑ r ∈ I, progressionMidpointWeight Q r * a r i * a r j

theorem weightedGram_quadratic (I : Finset ℕ) (w : ℕ → ℝ) (a : ℕ → ι → ℝ)
    (c : ι → ℝ) :
    gramQuadratic (fun i j => ∑ r ∈ I, w r * a r i * a r j) c =
      ∑ r ∈ I, w r * (dotProduct c (a r))^2 := by
  simp only [gramQuadratic, Matrix.mulVec, dotProduct, Finset.mul_sum,
    Finset.sum_mul, pow_two]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := Finset.univ) (t := I)]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem midpointGram_quadratic_bounds (Q : ℕ) (hQ : 0 < Q) (I : Finset ℕ)
    (hI : ∀ r ∈ I, 0 < r) (a : ℕ → ι → ℝ) (c : ι → ℝ) :
    (1 - 1 / (2*(Q : ℝ)+3)^2) * gramQuadratic (progressionGram Q I a) c ≤
        gramQuadratic (midpointGram Q I a) c ∧
      gramQuadratic (midpointGram Q I a) c ≤ gramQuadratic (progressionGram Q I a) c := by
  have hg : gramQuadratic (progressionGram Q I a) c =
      ∑ r ∈ I, progressionWeight Q r * (dotProduct c (a r))^2 :=
    weightedGram_quadratic I (progressionWeight Q) a c
  have hm : gramQuadratic (midpointGram Q I a) c =
      ∑ r ∈ I, progressionMidpointWeight Q r * (dotProduct c (a r))^2 :=
    weightedGram_quadratic I (progressionMidpointWeight Q) a c
  rw [hg, hm]
  exact progressionMidpoint_quadratic_comparison Q hQ I hI (fun r => dotProduct c (a r))

theorem midpointGram_posDef (Q : ℕ) (hQ : 0 < Q) (I : Finset ℕ)
    (hI : ∀ r ∈ I, 0 < r) (a : ℕ → ι → ℝ)
    (hG : (progressionGram Q I a).PosDef) : (midpointGram Q I a).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial, midpointGram]
    apply Finset.sum_congr rfl
    intro r hr
    ring
  · intro c hc
    have hp : 0 < gramQuadratic (progressionGram Q I a) c := by
      simpa only [gramQuadratic, star_trivial] using
        (Matrix.posDef_iff_dotProduct_mulVec.mp hG).2 hc
    have ht := (midpointGram_quadratic_bounds Q hQ I hI a c).1
    have hp' := mul_pos (progressionMidpoint_relative_factor_pos Q) hp
    simpa only [gramQuadratic, star_trivial] using lt_of_lt_of_le hp' ht

theorem midpointGram_inverse_bounds (Q : ℕ) (hQ : 0 < Q) (I : Finset ℕ)
    (hI : ∀ r ∈ I, 0 < r) (a : ℕ → ι → ℝ)
    (hG : (progressionGram Q I a).PosDef) (b : ι → ℝ) :
    (1 - 1 / (2*(Q : ℝ)+3)^2) *
      inverseQuadratic (midpointGram Q I a) (midpointGram_posDef Q hQ I hI a hG) b ≤
        inverseQuadratic (progressionGram Q I a) hG b ∧
      inverseQuadratic (progressionGram Q I a) hG b ≤
        inverseQuadratic (midpointGram Q I a) (midpointGram_posDef Q hQ I hI a hG) b := by
  exact inverseQuadratic_relative _ _ hG (midpointGram_posDef Q hQ I hI a hG) _
    (progressionMidpoint_relative_factor_pos Q).le
    (fun c => (midpointGram_quadratic_bounds Q hQ I hI a c).1)
    (fun c => (midpointGram_quadratic_bounds Q hQ I hI a c).2) b

/-- The already proved midpoint weight uses the actual trigamma derivative. -/
theorem progressionMidpointWeight_eq_trigamma (Q r : ℕ) (hQ : 0 < Q) :
    progressionMidpointWeight Q r = positiveWeight r +
      CRTBlock.trigamma (1 + ((r : ℝ) + 1/2)/Q) / (Q : ℝ)^2 := by
  unfold progressionMidpointWeight
  rw [CRTBlock.trigamma_eq_series (by positivity)]
  rfl

/-- The normalized row inverse energy is at most one for every positive Gram. -/
theorem weightedGram_leverage_le_one (I : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ r ∈ I, 0 ≤ w r) (a : ℕ → ι → ℝ)
    (hG : Matrix.PosDef (fun i j : ι => ∑ r ∈ I, w r * a r i * a r j))
    (k : ℕ) (hk : k ∈ I) :
    w k * inverseQuadratic (fun i j => ∑ r ∈ I, w r * a r i * a r j) hG (a k) ≤ 1 := by
  classical
  let G : Matrix ι ι ℝ := fun i j => ∑ r ∈ I, w r * a r i * a r j
  let C := inverseQuadratic G hG (a k)
  let x := (gramEquiv G hG).symm (a k)
  have hpair : dotProduct x (a k) = C := rfl
  have henergy : gramQuadratic G x = C := (inverseQuadratic_eq_energy G hG (a k)).symm
  have hbound : w k * C^2 ≤ C := by
    calc
      _ = w k * (dotProduct x (a k))^2 := by rw [hpair]
      _ ≤ ∑ r ∈ I, w r * (dotProduct x (a r))^2 :=
        Finset.single_le_sum
          (fun r hr => mul_nonneg (hw r hr) (sq_nonneg (dotProduct x (a r)))) hk
      _ = C := by rw [← weightedGram_quadratic]; exact henergy
  have hnonneg : 0 ≤ C := inverseQuadratic_nonneg G hG (a k)
  change w k * C ≤ 1
  rcases eq_or_lt_of_le hnonneg with hz | hp
  · rw [← hz]
    norm_num
  · by_contra hnot
    have hpos : 0 < w k * C - 1 := sub_pos.mpr (lt_of_not_ge hnot)
    have hprod := mul_pos hp hpos
    nlinarith

/-- Relative inverse comparison and relative row-weight comparison give a
uniform probability comparison, with no condition-number assumption. -/
theorem probability_comparison_of_relative_bounds
    {δ w wm C Cm : ℝ} (hδ : 0 ≤ δ) (hwm : 0 ≤ wm)
    (hC : 0 ≤ C)
    (hwlo : (1-δ)*w ≤ wm) (hwhi : wm ≤ w)
    (hClo : (1-δ)*Cm ≤ C) (hChi : C ≤ Cm)
    (hq : w*C ≤ 1) (hqm : wm*Cm ≤ 1) :
    |w*C - wm*Cm| ≤ δ := by
  have hlo : (1-δ)*(w*C) ≤ wm*Cm := by
    calc
      _ = ((1-δ)*w)*C := by ring
      _ ≤ wm*C := mul_le_mul_of_nonneg_right hwlo hC
      _ ≤ wm*Cm := mul_le_mul_of_nonneg_left hChi hwm
  have hhi : (1-δ)*(wm*Cm) ≤ w*C := by
    calc
      _ = wm*((1-δ)*Cm) := by ring
      _ ≤ wm*C := mul_le_mul_of_nonneg_left hClo hwm
      _ ≤ w*C := mul_le_mul_of_nonneg_right hwhi hC
  apply abs_le.mpr
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hqm hδ]
  · nlinarith [mul_le_mul_of_nonneg_left hq hδ]

/-- Exact-versus-midpoint row probabilities satisfy an explicit uniform bound.
The two positive matrices and both inverses are constructed from their weights. -/
theorem progressionMidpoint_occupation_error (Q : ℕ) (hQ : 0 < Q) (I : Finset ℕ)
    (hI : ∀ r ∈ I, 0 < r) (a : ℕ → ι → ℝ)
    (hG : (progressionGram Q I a).PosDef) (k : ℕ) (hk : k ∈ I) :
    |progressionWeight Q k * inverseQuadratic (progressionGram Q I a) hG (a k) -
      progressionMidpointWeight Q k * inverseQuadratic (midpointGram Q I a)
        (midpointGram_posDef Q hQ I hI a hG) (a k)| ≤
      1 / (2*(Q : ℝ)+3)^2 := by
  have hwm (r) (hr : r ∈ I) : 0 ≤ progressionMidpointWeight Q r := by
    exact (mul_nonneg (progressionMidpoint_relative_factor_pos Q).le
      (progressionWeight_nonneg Q r)).trans
      (progressionMidpointWeight_relative_bounds Q r hQ (hI r hr)).1
  have hw := progressionMidpointWeight_relative_bounds Q k hQ (hI k hk)
  have hc := midpointGram_inverse_bounds Q hQ I hI a hG (a k)
  exact probability_comparison_of_relative_bounds (by positivity)
    (hwm k hk) (inverseQuadratic_nonneg _ hG _)
    hw.1 hw.2 hc.1 hc.2
    (weightedGram_leverage_le_one I (progressionWeight Q)
      (fun r _ => progressionWeight_nonneg Q r) a hG k hk)
    (weightedGram_leverage_le_one I (progressionMidpointWeight Q) hwm a
      (midpointGram_posDef Q hQ I hI a hG) k hk)

theorem probability_tendsto_iff_of_error
    {α : Type*} (l : Filter α) (q qm δ : α → ℝ) (limit : ℝ)
    (he : ∀ n, |q n - qm n| ≤ δ n)
    (hδ : Filter.Tendsto δ l (nhds 0)) :
    Filter.Tendsto q l (nhds limit) ↔ Filter.Tendsto qm l (nhds limit) := by
  have hz : Filter.Tendsto (fun n => q n - qm n) l (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      (by simpa only [neg_zero] using hδ.neg) hδ
      (fun n => (abs_le.mp (he n)).1) (fun n => (abs_le.mp (he n)).2)
  constructor
  · intro h
    have ht := h.sub hz
    convert ht using 1
    · funext n
      ring
    · norm_num
  · intro h
    have ht := h.add hz
    convert ht using 1
    · funext n
      ring
    · norm_num

theorem progressionMidpoint_error_tendsto (Q : ℕ → ℕ)
    (hQt : Tendsto Q atTop atTop) :
    Tendsto (fun n => 1 / (2*(Q n : ℝ)+3)^2) atTop (nhds 0) := by
  have hn : Tendsto (fun n => Q n + 1) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_succ (Q n)) hQt
  have hr := (tendsto_natCast_atTop_atTop :
    Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop).comp hn
  have hi := tendsto_inv_atTop_zero.comp hr
  have hs : Tendsto (fun n => 1 / ((Q n : ℝ)+1)^2) atTop (nhds 0) := by
    simpa only [Function.comp_apply, Nat.cast_add, Nat.cast_one, one_div,
      inv_pow, zero_pow (by decide : (2 : ℕ) ≠ 0)] using hi.pow 2
  apply squeeze_zero (fun n => by positivity) _ hs
  intro n
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith [Nat.cast_nonneg (Q n) (α := ℝ)]

/-- The dictionary dimension may grow arbitrarily. The only limiting assumption
is divergence of the common conductors, not any spectral regularity.
Taking `limit = 1` gives equivalence of exact and midpoint saturation. -/
theorem progressionMidpoint_occupation_tendsto_iff
    {κ : ℕ → Type*} [∀ n, Fintype (κ n)]
    (Q : ℕ → ℕ) (hQ : ∀ n, 0 < Q n) (hQt : Tendsto Q atTop atTop)
    (I : ℕ → Finset ℕ) (hI : ∀ n, ∀ r ∈ I n, 0 < r)
    (a : ∀ n, ℕ → κ n → ℝ)
    (hG : ∀ n, (progressionGram (Q n) (I n) (a n)).PosDef)
    (hk : ∀ n, 1 ∈ I n) (limit : ℝ) :
    Tendsto (fun n => progressionWeight (Q n) 1 *
      inverseQuadratic (progressionGram (Q n) (I n) (a n)) (hG n) (a n 1))
      atTop (nhds limit) ↔
    Tendsto (fun n => progressionMidpointWeight (Q n) 1 *
      inverseQuadratic (midpointGram (Q n) (I n) (a n))
        (midpointGram_posDef (Q n) (hQ n) (I n) (hI n) (a n) (hG n)) (a n 1))
      atTop (nhds limit) := by
  exact probability_tendsto_iff_of_error atTop _ _ _ limit
    (fun n => progressionMidpoint_occupation_error
      (Q n) (hQ n) (I n) (hI n) (a n) (hG n) 1 (hk n))
    (progressionMidpoint_error_tendsto Q hQt)

end RiemannResearch.RH.Pareto
