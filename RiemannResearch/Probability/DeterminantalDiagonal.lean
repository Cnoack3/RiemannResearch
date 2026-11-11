import RiemannResearch.Probability.DeterminantalIndependentLimit
import RiemannResearch.Probability.DeterminantalMoments
import RiemannResearch.Probability.DeterminantalCardinality

/-!
# Diagonal determinantal laws and their infinite limits

Source: user-provided `V_vector_space_RH.pdf`, Sections 2--3, for the diagonal
covariance limit motivating this application. The DPP interpretation follows
Lyons, *Determinantal probability measures*, arXiv:math/0204325, Sections 7--8.
The construction below proves every mixed finite configuration probability;
it does not identify a deterministic zeta-zero set with a DPP.

The diagonal covariance weights yield an independent Bernoulli law. The quite
different projection-exhaustion limit has diagonal one and is deterministic.
All statements below concern real diagonal kernels on a discrete ground set.
-/

noncomputable section
open MeasureTheory Matrix Filter
open scoped BigOperators Classical Topology ENNReal

namespace RiemannResearch.Probability.DPP
open RiemannResearch.Probability.BooleanProjective

variable {α ι : Type*}

def diagonalKernel (p : α → ℝ) (i j : α) : ℝ := if i = j then p i else 0

@[simp] theorem diagonalKernel_self (p : α → ℝ) (i : α) :
    diagonalKernel p i i = p i := by simp [diagonalKernel]

theorem diagonalKernel_restrict [DecidableEq ι]
    (p : α → ℝ) (e : ι ↪ α) :
    Matrix.of (fun i j => diagonalKernel p (e i) (e j)) =
      Matrix.diagonal (fun i => p (e i)) := by
  ext i j
  simp [diagonalKernel, Matrix.diagonal_apply, e.injective.eq_iff]

theorem diagonalKernel_exactWeight_nonneg
    (p : α → ℝ) (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1)
    (I : Finset α) (S : Finset I) :
    0 ≤ exactWeight (Matrix.of (fun i j : I => diagonalKernel p i.1 j.1)) S := by
  have he : Matrix.of (fun i j : I => diagonalKernel p i.1 j.1) =
      Matrix.diagonal (fun i : I => p i.1) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [diagonalKernel]
    · have hv : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
      simp [diagonalKernel, Matrix.diagonal_apply, hij, hv]
  rw [he, exactWeight_diagonal]
  apply Finset.prod_nonneg
  intro i hi
  split_ifs
  · exact (hp i.1).1
  · exact sub_nonneg.mpr (hp i.1).2

/-- Actual probability measure, including infinitely many sites. -/
def diagonalLaw (p : α → ℝ) (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) :
    Measure (α → Bool) :=
  boolProjectiveLimit (finiteBoolFamily_projective (diagonalKernel p)
    (diagonalKernel_exactWeight_nonneg p hp))

instance diagonalLaw_probability
    (p : α → ℝ) (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) :
    IsProbabilityMeasure (diagonalLaw p hp) := by
  unfold diagonalLaw
  infer_instance

theorem diagonalLaw_isDPP
    (p : α → ℝ) (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) :
    IsDPP (diagonalLaw p hp) (fun x => {i | x i = true}) (diagonalKernel p) :=
  boolProjectiveLimit_isDPP _ _
    (finiteBoolFamily_isDPP _ (diagonalKernel_exactWeight_nonneg p hp))

/-- Every occupied/vacant pattern factors, proving independence rather than
merely vanishing pair covariances. -/
theorem diagonalLaw_configuration [Fintype ι] [DecidableEq ι]
    (p : α → ℝ) (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1)
    (e : ι ↪ α) (S : Finset ι) :
    (diagonalLaw p hp).real {x | ∀ i, x (e i) = decide (i ∈ S)} =
      ∏ i, if i ∈ S then p (e i) else 1 - p (e i) := by
  have hpos : ∀ S, 0 ≤ exactWeight
      (Matrix.of (fun i j => diagonalKernel p (e i) (e j))) S := by
    intro S
    rw [diagonalKernel_restrict, exactWeight_diagonal]
    apply Finset.prod_nonneg
    intro i hi
    split_ifs
    · exact (hp (e i)).1
    · exact sub_nonneg.mpr (hp (e i)).2
  have h := (diagonalLaw_isDPP p hp).finite_configuration e hpos S
  simpa only [Set.mem_ofPred_eq, Bool.decide_eq_true, diagonalKernel_restrict,
    exactWeight_diagonal] using h

theorem diagonalLaw_gap [Fintype ι] [DecidableEq ι]
    (p : α → ℝ) (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) (e : ι ↪ α) :
    (diagonalLaw p hp).real {x | ∀ i, x (e i) = false} =
      ∏ i, (1 - p (e i)) := by
  simpa using diagonalLaw_configuration p hp e ∅

/-- The particle-hole dual is again a diagonal DPP, with weights `1-p`. -/
theorem diagonalLaw_holes_isDPP
    (p : α → ℝ) (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) :
    IsDPP (diagonalLaw p hp) (fun x => {i | x i = false})
      (diagonalKernel (fun i => 1 - p i)) := by
  constructor
  · intro i
    exact (measurableSet_singleton false).preimage (measurable_pi_apply i)
  · intro n e
    rw [diagonalKernel_restrict, Matrix.det_diagonal]
    exact diagonalLaw_gap p hp e

/-- On a countable ground set, the projection limit with diagonal one occupies
all sites almost surely. Thus this limit cannot be a nontrivial sine process. -/
theorem diagonalLaw_full_occupation_iff [Countable α]
    (p : α → ℝ) (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) :
    (∀ᵐ x ∂diagonalLaw p hp, ∀ i, x i = true) ↔ ∀ i, p i = 1 := by
  simpa only [Set.eq_univ_iff_forall, Set.mem_ofPred_eq, diagonalKernel_self] using
    (diagonalLaw_isDPP p hp).full_occupation_ae_iff

/-- The particle configuration is empty exactly when every covariance weight is zero. -/
theorem diagonalLaw_empty_iff [Countable α]
    (p : α → ℝ) (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) :
    (∀ᵐ x ∂diagonalLaw p hp, ∀ i, x i = false) ↔ ∀ i, p i = 0 := by
  have h := (diagonalLaw_holes_isDPP p hp).full_occupation_ae_iff
  simpa only [Set.eq_univ_iff_forall, Set.mem_ofPred_eq, diagonalKernel_self, sub_eq_self] using h

/-- Exact count variance in any finite window of the limiting product law. -/
theorem diagonalLaw_variance_window [Fintype ι] [DecidableEq ι]
    (p : α → ℝ) (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) (e : ι ↪ α) :
    ProbabilityTheory.variance
      (windowCount (fun x : α → Bool => {i | x i = true}) e) (diagonalLaw p hp) =
        ∑ i, p (e i) * (1 - p (e i)) := by
  rw [(diagonalLaw_isDPP p hp).variance_windowCount]
  simp only [diagonalKernel, e.injective.eq_iff, if_true]
  have he : (∑ i : ι, ∑ j : ι,
      (if i = j then p (e i) else 0) * (if j = i then p (e j) else 0)) =
      ∑ i : ι, p (e i) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_eq_single i]
    · simp [pow_two]
    · intro j hj hij
      simp [hij, Ne.symm hij]
    · simp
  rw [he, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- A summable covariance diagonal gives an exact finite expected total count,
even though the ground set is infinite. -/
theorem diagonalLaw_expected_total (p : ℕ → ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) (hs : Summable p) :
    (∫⁻ x, setCount {i | x i = true} ∂diagonalLaw p hp) =
      ENNReal.ofReal (∑' i, p i) := by
  simpa only [diagonalKernel_self] using
    (diagonalLaw_isDPP p hp).expected_setCount (by simpa using hs)

/-- A summable covariance diagonal produces only finitely many particles almost
surely, by the first Borel--Cantelli lemma; independence is not needed here. -/
theorem diagonalLaw_finite_ae (p : ℕ → ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) (hs : Summable p) :
    ∀ᵐ x ∂diagonalLaw p hp, {i | x i = true}.Finite := by
  have he (i : ℕ) : diagonalLaw p hp {x | x i = true} = ENNReal.ofReal (p i) := by
    have ho := (diagonalLaw_isDPP p hp).occupation i
    simp only [Set.mem_ofPred_eq, diagonalKernel_self] at ho
    rw [← ho, Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hsum : (∑' i, diagonalLaw p hp {x | x i = true}) ≠ ⊤ := by
    simp_rw [he]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => (hp i).1) hs]
    exact ENNReal.ofReal_ne_top
  exact ae_finite_setOfPred_mem hsum

/-- Entrywise convergence to a diagonal kernel implies every finite exact
configuration probability converges to the corresponding Bernoulli product.
The positive-contraction assumptions construct the approximating laws. -/
theorem contractionDPP_configuration_tendsto_diagonal
    (K : ℕ → α → α → ℝ)
    (hK : ∀ n (I : Finset α),
      (Matrix.of (fun i j : I => K n i.1 j.1)).PosSemidef)
    (hI : ∀ n (I : Finset α),
      (1 - Matrix.of (fun i j : I => K n i.1 j.1)).PosSemidef)
    [Fintype ι] [DecidableEq ι] (p : α → ℝ)
    (hlim : ∀ i j, Tendsto (fun n => K n i j) atTop
      (𝓝 (diagonalKernel p i j))) (e : ι ↪ α) (S : Finset ι) :
    Tendsto (fun n => (contractionDPP (K n) (hK n) (hI n)).real
      {x | ∀ i, x (e i) = decide (i ∈ S)}) atTop
      (𝓝 (∏ i, if i ∈ S then p (e i) else 1 - p (e i))) := by
  let J : Finset α := Finset.univ.map e
  let f : ι → J := fun i => ⟨e i, by simp [J]⟩
  have hf : Function.Injective f := by
    intro i j hij
    exact e.injective (congrArg Subtype.val hij)
  have hpos (n : ℕ) (S : Finset ι) : 0 ≤ exactWeight
      (Matrix.of (fun i j => K n (e i) (e j))) S := by
    apply exactWeight_nonneg
    · exact (hK n J).submatrix f
    · convert (hI n J).submatrix f using 1
      ext i j
      simp [Matrix.submatrix, Matrix.sub_apply, Matrix.one_apply, hf.eq_iff, f]
  have he (n : ℕ) : (contractionDPP (K n) (hK n) (hI n)).real
      {x | ∀ i, x (e i) = decide (i ∈ S)} =
      exactWeight (Matrix.of (fun i j => K n (e i) (e j))) S := by
    simpa only [Set.mem_ofPred_eq, Bool.decide_eq_true] using
      (contractionDPP_isDPP (K n) (hK n) (hI n)).finite_configuration e (hpos n) S
  simp_rw [he]
  apply exactWeight_tendsto_of_diagonal _ (fun i => p (e i)) _ S
  intro i j
  simpa only [Matrix.of_apply, diagonalKernel, e.injective.eq_iff] using hlim (e i) (e j)

end RiemannResearch.Probability.DPP
