import RiemannResearch.Probability.DeterminantalSpectralCount
import RiemannResearch.Probability.FiniteDeterminantalGenerating
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Probability.Independence.Basic

/-!
# Independent Bernoulli representation of a determinantal count

Source: Hough--Krishnapur--Peres--Virag, *Determinantal Processes and
Independence*, arXiv:math/0503110, Theorem 7, for the statement. This module
constructs the finite Bernoulli subset law explicitly and identifies the DPP
count law with its cardinality pushforward.
-/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

namespace PMF

/-- The real mass of a pushforward of a PMF with finite source is the finite
sum of the real masses in the corresponding fiber. -/
theorem map_apply_toReal_of_fintype {α β : Type*} [Fintype α] [DecidableEq β]
    (p : PMF α) (f : α → β) (b : β) :
    ((p.map f) b).toReal = ∑ a, if b = f a then (p a).toReal else 0 := by
  rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp
  · intro a _
    split_ifs <;> simp [PMF.apply_ne_top]

/-- Equality of finite-support probability generating functions determines the
pushforward distribution on the natural numbers. -/
theorem map_nat_eq_of_generating_eq {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (q : PMF β) (f : α → ℕ) (g : β → ℕ)
    (h : ∀ z : ℝ, (∑ a, z ^ f a * (p a).toReal) =
      ∑ b, z ^ g b * (q b).toReal) : p.map f = q.map g := by
  let P : Polynomial ℝ := ∑ a, Polynomial.monomial (f a) (p a).toReal
  let Q : Polynomial ℝ := ∑ b, Polynomial.monomial (g b) (q b).toReal
  have hPQ : P = Q := by
    apply Polynomial.funext
    intro z
    simpa [P, Q, Polynomial.eval_finsetSum, mul_comm] using h z
  have hcoeff (k : ℕ) :
      (∑ a, if k = f a then (p a).toReal else 0) =
        ∑ b, if k = g b then (q b).toReal else 0 := by
    have hc := congrArg (fun R : Polynomial ℝ => R.coeff k) hPQ
    simpa [P, Q, Polynomial.coeff_monomial, eq_comm] using hc
  ext k
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  have hp : ((p.map f) k).toReal =
      ∑ a, if k = f a then (p a).toReal else 0 := by
    simpa using (map_apply_toReal_of_fintype p f k)
  have hq : ((q.map g) k).toReal =
      ∑ b, if k = g b then (q b).toReal else 0 := by
    simpa using (map_apply_toReal_of_fintype q g k)
  exact hp.trans ((hcoeff k).trans hq.symm)

end PMF

namespace RiemannResearch.Probability.DPP
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A diagonal determinantal law is exactly a Bernoulli product law. -/
theorem exactWeight_diagonal (p : ι → ℝ) (S : Finset ι) :
    exactWeight (Matrix.diagonal p) S =
      ∏ i : ι, if i ∈ S then p i else 1 - p i := by
  have hm : mixedRows (Matrix.diagonal p) S =
      Matrix.diagonal (fun i => if i ∈ S then p i else 1 - p i) := by
    ext i j
    by_cases hi : i ∈ S <;> by_cases hij : i = j
    · subst j
      simp [mixedRows, Finset.piecewise, hi]
    · simp [mixedRows, Finset.piecewise, Matrix.diagonal, hi, hij]
    · subst j
      simp [mixedRows, Finset.piecewise, hi]
    · simp [mixedRows, Finset.piecewise, Matrix.diagonal, hi, hij]
  unfold exactWeight
  rw [hm, Matrix.det_diagonal]

theorem exactWeight_diagonal_nonneg (p : ι → ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) (S : Finset ι) :
    0 ≤ exactWeight (Matrix.diagonal p) S := by
  rw [exactWeight_diagonal]
  apply Finset.prod_nonneg
  intro i _
  split_ifs
  · exact (hp i).1
  · exact sub_nonneg.mpr (hp i).2

/-- The random subset whose occupation indicators are independent Bernoulli
variables with success parameters `p i`. -/
def bernoulliSubsetLaw (p : ι → ℝ) (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) :
    PMF (Finset ι) :=
  finiteLaw (Matrix.diagonal p) (exactWeight_diagonal_nonneg p hp)

/-- Every exact configuration probability factors into its one-site Bernoulli
probabilities. -/
theorem bernoulliSubsetLaw_apply_toReal (p : ι → ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) (S : Finset ι) :
    ((bernoulliSubsetLaw p hp) S).toReal =
      ∏ i : ι, if i ∈ S then p i else 1 - p i := by
  change (ENNReal.ofReal (exactWeight (Matrix.diagonal p) S)).toReal = _
  rw [ENNReal.toReal_ofReal (exactWeight_diagonal_nonneg p hp S), exactWeight_diagonal]

theorem bernoulliSubsetLaw_count_generating (p : ι → ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) (z : ℝ) :
    (∑ S : Finset ι, z ^ S.card * ((bernoulliSubsetLaw p hp) S).toReal) =
      ∏ i, (1 - p i + z * p i) := by
  rw [bernoulliSubsetLaw, finiteLaw_count_generating]
  have hm : Matrix.diagonal (fun _ : ι => z) * Matrix.diagonal p +
      (1 - Matrix.diagonal p) =
      Matrix.diagonal (fun i => 1 - p i + z * p i) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.diagonal_mul, Matrix.sub_apply]
    by_cases hij : i = j
    · subst j
      simp
      ring
    · simp [Matrix.diagonal, hij]
  rw [hm, Matrix.det_diagonal]

section MeasurableLaw
variable [MeasurableSpace (Finset ι)] [MeasurableSingletonClass (Finset ι)]

/-- Joint success probabilities of the Bernoulli subset law factor over every
finite set of indices. -/
theorem bernoulliSubsetLaw_inclusion_real (p : ι → ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) (T : Finset ι) :
    (bernoulliSubsetLaw p hp).toMeasure.real {S | T ⊆ S} =
      ∏ i ∈ T, p i := by
  rw [bernoulliSubsetLaw, finiteLaw_inclusion]
  have hm : (Matrix.diagonal p).submatrix (fun i : T => (i : ι))
      (fun i : T => (i : ι)) = Matrix.diagonal (fun i : T => p i) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [Matrix.submatrix, Matrix.diagonal, hij]
  rw [hm, Matrix.det_diagonal, Finset.prod_coe_sort]

/-- The occupation events of the Bernoulli subset law are mutually independent
in Mathlib's measure-theoretic sense. -/
theorem bernoulliSubsetLaw_iIndepSet (p : ι → ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) :
    iIndepSet (fun i => {S : Finset ι | i ∈ S})
      (bernoulliSubsetLaw p hp).toMeasure := by
  apply (iIndepSet_iff_meas_biInter (fun _ => (Set.toFinite _).measurableSet)).2
  intro T
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
    (ENNReal.prod_ne_top (fun _ _ => measure_ne_top _ _))).mp
  rw [ENNReal.toReal_prod]
  change (bernoulliSubsetLaw p hp).toMeasure.real
      (⋂ i ∈ T, {S : Finset ι | i ∈ S}) =
    ∏ i ∈ T, (bernoulliSubsetLaw p hp).toMeasure.real {S | i ∈ S}
  have he : (⋂ i ∈ T, {S : Finset ι | i ∈ S}) = {S | T ⊆ S} := by
    ext S
    simp [Finset.subset_iff]
  rw [he, bernoulliSubsetLaw_inclusion_real]
  apply Finset.prod_congr rfl
  intro i _
  symm
  simpa using bernoulliSubsetLaw_inclusion_real p hp {i}

end MeasurableLaw

/-- The finite DPP's count distribution equals the sum-of-independent-Bernoulli
distribution whose parameters are the eigenvalues of its kernel. The Bernoulli
sum is represented as cardinality under the explicit product subset law. -/
theorem finiteLaw_count_eq_bernoulliSubset_count (Q : Matrix ι ι ℝ)
    (hQ : Q.PosSemidef) (hI : (1 - Q).PosSemidef) :
    (finiteLaw Q (exactWeight_nonneg Q hQ hI)).map Finset.card =
      (bernoulliSubsetLaw hQ.isHermitian.eigenvalues
        (hQ.eigenvalues_mem_Icc hI)).map Finset.card := by
  apply PMF.map_nat_eq_of_generating_eq
  intro z
  rw [finiteLaw_count_generating_spectral Q hQ.isHermitian,
    bernoulliSubsetLaw_count_generating]

variable {α Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : Ω → Set α} {K : α → α → ℝ}

/-- The actual count in any finite spatial window has the independent
Bernoulli-sum law, using the eigenvalues of the window compression. -/
theorem IsDPP.window_count_law_eq_bernoulli (h : IsDPP μ X K) (e : ι ↪ α)
    (hQ : (Matrix.of (fun i j : ι => K (e i) (e j))).PosSemidef)
    (hI : (1 - Matrix.of (fun i j : ι => K (e i) (e j))).PosSemidef) :
    Measure.map (fun ω => (Finset.univ.filter (fun i => e i ∈ X ω)).card) μ =
      ((bernoulliSubsetLaw hQ.isHermitian.eigenvalues
        (hQ.eigenvalues_mem_Icc hI)).map Finset.card).toMeasure := by
  let : MeasurableSpace (Finset ι) := ⊤
  let Q := Matrix.of (fun i j : ι => K (e i) (e j))
  let hp := exactWeight_nonneg Q hQ hI
  let r : Ω → (ι → Bool) := fun ω i => decide (e i ∈ X ω)
  let b : Finset ι → (ι → Bool) := fun S i => decide (i ∈ S)
  let c : (ι → Bool) → ℕ := fun x => (Finset.univ.filter (fun i => x i = true)).card
  have hr : Measurable r := by
    apply measurable_pi_lambda
    intro i
    change Measurable (({ω | e i ∈ X ω} : Set Ω).piecewise
      (fun _ => true) (fun _ => false))
    exact measurable_const.piecewise (h.measurable_occupancy (e i)) measurable_const
  have hc : Measurable c := measurable_of_finite c
  have hcb : c ∘ b = Finset.card := by
    funext S
    simp [c, b]
  have hw : (fun ω => (Finset.univ.filter (fun i => e i ∈ X ω)).card) = c ∘ r := by
    funext ω
    simp [c, r]
  rw [hw, ← Measure.map_map hc hr]
  change Measure.map c (μ.map r) = _
  rw [show μ.map r = (finiteBoolLaw Q hp).toMeasure from h.finite_restriction_law e hp,
    PMF.toMeasure_map c (finiteBoolLaw Q hp) hc]
  change (((finiteLaw Q hp).map b).map c).toMeasure = _
  rw [PMF.map_comp, hcb, finiteLaw_count_eq_bernoulliSubset_count Q hQ hI]

end RiemannResearch.Probability.DPP
