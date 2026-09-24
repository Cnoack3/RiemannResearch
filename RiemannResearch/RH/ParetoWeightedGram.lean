import RiemannResearch.RH.ParetoWeightedCells
import RiemannResearch.RH.ParetoTailCapacity
import RiemannResearch.Analysis.FiniteHilbertGramMatrix

/-!
# Actual weighted Gram minima

Source: RH_Research_Agenda_2026-09-24(1).md, Priority 2.
The positive physical cell weights define an injective contraction on the
actual Pareto Hilbert space. Finite residue independence therefore survives
at every u ≥ 1, and the complete weighted Gram inverse exists unconditionally.
This finite minimum identity does not establish its vanishing as N tends
to infinity at any fixed 1 < u < 2.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto.WeightedGram
open WeightedMellin
open CoefficientStabilization CoefficientStabilization.TailCapacity
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.ExhaustiveWalk

/-- Positive diagonal multiplier transporting full weighted cells into real l2. -/
def scale (u : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (weightedCellWeight u n / paretoWeight n)

theorem scale_pos {u : ℝ} (hu : 1 ≤ u) (n : ℕ) : 0 < scale u n :=
  Real.sqrt_pos.2 (div_pos (weightedCellWeight_pos (by linarith) n) (paretoWeight_pos n))

theorem scale_sq {u : ℝ} (hu : 1 ≤ u) (n : ℕ) :
    scale u n ^ 2 = weightedCellWeight u n / paretoWeight n :=
  Real.sq_sqrt (le_of_lt (div_pos (weightedCellWeight_pos (by linarith) n)
    (paretoWeight_pos n)))

theorem scale_sq_le_one {u : ℝ} (hu : 1 ≤ u) (n : ℕ) : scale u n ^ 2 ≤ 1 := by
  rw [scale_sq hu]
  exact (div_le_one (paretoWeight_pos n)).2 (weightedCellWeight_le_pareto hu n)

private theorem scaled_sq_le {u : ℝ} (hu : 1 ≤ u) (f : ThresholdHilbert) (n : ℕ) :
    (scale u n * f n) ^ 2 ≤ (f n) ^ 2 := by
  rw [mul_pow]
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right (scale_sq_le_one hu n) (sq_nonneg (f n))

/-- The full diagonal operator, retaining every physical cell. -/
def embedding (u : ℝ) (hu : 1 ≤ u) (f : ThresholdHilbert) : ThresholdHilbert :=
  ⟨fun n => scale u n * f n, by
    apply (memℓp_gen_iff (show 0 < (2 : ENNReal).toReal by norm_num)).2
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using
      (Summable.of_nonneg_of_le (fun n => sq_nonneg (scale u n * f n))
        (scaled_sq_le hu f) (hilbert_coordinate_square_summable f))⟩

@[simp] theorem embedding_apply (u : ℝ) (hu : 1 ≤ u) (f : ThresholdHilbert) (n : ℕ) :
    embedding u hu f n = scale u n * f n := rfl

def embeddingLinear (u : ℝ) (hu : 1 ≤ u) : ThresholdHilbert →ₗ[ℝ] ThresholdHilbert where
  toFun := embedding u hu
  map_add' f g := by
    apply Subtype.ext
    funext n
    change scale u n * (f n + g n) = scale u n * f n + scale u n * g n
    ring
  map_smul' c f := by
    apply Subtype.ext
    funext n
    change scale u n * (c * f n) = c * (scale u n * f n)
    ring

theorem embedding_injective (u : ℝ) (hu : 1 ≤ u) : Function.Injective (embedding u hu) := by
  intro f g h
  apply Subtype.ext
  funext n
  have hn := congrArg (fun z : ThresholdHilbert => z n) h
  exact (mul_left_cancel₀ (ne_of_gt (scale_pos hu n))) hn

theorem embedding_norm_le (u : ℝ) (hu : 1 ≤ u) (f : ThresholdHilbert) :
    ‖embedding u hu f‖ ≤ ‖f‖ := by
  have hs : ‖embedding u hu f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    rw [hilbert_norm_sq, hilbert_norm_sq]
    exact Summable.tsum_le_tsum (scaled_sq_le hu f)
      (hilbert_coordinate_square_summable (embedding u hu f))
      (hilbert_coordinate_square_summable f)
  nlinarith [norm_nonneg f, norm_nonneg (embedding u hu f)]

def embeddingContinuous (u : ℝ) (hu : 1 ≤ u) :
    ThresholdHilbert →L[ℝ] ThresholdHilbert :=
  (embeddingLinear u hu).mkContinuous 1 (fun f => by
    change ‖embedding u hu f‖ ≤ 1 * ‖f‖
    simpa only [one_mul] using embedding_norm_le u hu f)

theorem embedding_norm_sq (u : ℝ) (hu : 1 ≤ u) (f : ThresholdHilbert) :
    ‖embedding u hu f‖ ^ 2 = WeightedMellin.energy (complexPhysicalStep f) u := by
  rw [hilbert_norm_sq, complexPhysicalStep_weighted_energy f hu]
  apply tsum_congr
  intro n
  rw [embedding_apply, mul_pow, scale_sq hu, hilbertSequence_succ, div_pow,
    Real.sq_sqrt (paretoWeight_pos n).le]
  ring

def atom (u : ℝ) (hu : 1 ≤ u) (i : ℕ) : ThresholdHilbert :=
  embedding u hu (residueAtom i)

def target (u : ℝ) (hu : 1 ≤ u) : ThresholdHilbert := embedding u hu hilbertOne

theorem target_norm_sq (u : ℝ) (hu : 1 ≤ u) : ‖target u hu‖ ^ 2 = 1 / u := by
  rw [target, embedding_norm_sq, complexPhysicalStep_one_energy hu]

/-- Positivity of the actual weights proves independence, not a new assumption. -/
theorem atom_independent (u : ℝ) (hu : 1 ≤ u) (n : ℕ) :
    LinearIndependent ℝ (fun i : Fin n => atom u hu i.val) := by
  apply Fintype.linearIndependent_iff.mpr
  intro a ha
  apply Fintype.linearIndependent_iff.mp (finiteAtom_independent n) a
  apply embedding_injective u hu
  change embeddingLinear u hu (∑ i : Fin n, a i • residueAtom i.val) =
    embeddingLinear u hu 0
  rw [map_sum, map_zero]
  simp only [map_smul]
  change (∑ i : Fin n, a i • embedding u hu (residueAtom i.val)) = 0
  change (∑ i : Fin n, a i • embedding u hu (residueAtom i.val)) = 0 at ha
  exact ha

/-- Source and Gram use the entire weighted Hilbert inner product. -/
def source (u : ℝ) (hu : 1 ≤ u) (n : ℕ) : Fin n → ℝ :=
  cross (fun i : Fin n => atom u hu i.val) (target u hu)

def coefficients (u : ℝ) (hu : 1 ≤ u) (n : ℕ) : Fin n → ℝ :=
  inverseCoeff (atom_independent u hu n) (target u hu)

def approximant (u : ℝ) (hu : 1 ≤ u) (n : ℕ) : ThresholdHilbert :=
  ∑ i : Fin n, coefficients u hu n i • residueAtom i.val

/-- An actual constructed legal approximation at every cutoff and every weight. -/
theorem approximant_mem_legal (u : ℝ) (hu : 1 ≤ u) (n : ℕ) :
    approximant u hu n ∈ hilbertLegalSubspace {m : ℕ | 0 < m} := by
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (residueAtom_mem_legal i.val)

private theorem embedding_synthesis (u : ℝ) (hu : 1 ≤ u) (n : ℕ) (c : Fin n → ℝ) :
    embedding u hu (∑ i : Fin n, c i • residueAtom i.val) =
      Fintype.linearCombination ℝ (fun i : Fin n => atom u hu i.val) c := by
  change embeddingLinear u hu (∑ i : Fin n, c i • residueAtom i.val) = _
  simp only [map_sum, map_smul, Fintype.linearCombination_apply]
  rfl

/-- The explicit inverse-Gram formula for the complete weighted minimum. -/
theorem minimum_eq_inverseGram (u : ℝ) (hu : 1 ≤ u) (n : ℕ) :
    WeightedMellin.energy (complexPhysicalStep (hilbertOne - approximant u hu n)) u =
      1 / u - ∑ i : Fin n, coefficients u hu n i * source u hu n i := by
  rw [← embedding_norm_sq u hu]
  change ‖embeddingLinear u hu (hilbertOne - approximant u hu n)‖ ^ 2 = _
  rw [map_sub]
  change ‖target u hu - embedding u hu (approximant u hu n)‖ ^ 2 = _
  rw [approximant, embedding_synthesis, coefficients, residual_schur_value, target_norm_sq]
  rfl

/-- Every finite coefficient vector is compared in the full infinite weighted norm. -/
theorem approximant_minimizes (u : ℝ) (hu : 1 ≤ u) (n : ℕ) (c : Fin n → ℝ) :
    WeightedMellin.energy (complexPhysicalStep (hilbertOne - approximant u hu n)) u ≤
      WeightedMellin.energy (complexPhysicalStep
        (hilbertOne - ∑ i : Fin n, c i • residueAtom i.val)) u := by
  rw [← embedding_norm_sq u hu, ← embedding_norm_sq u hu]
  change ‖embeddingLinear u hu (hilbertOne - approximant u hu n)‖ ^ 2 ≤
    ‖embeddingLinear u hu (hilbertOne - ∑ i : Fin n, c i • residueAtom i.val)‖ ^ 2
  rw [map_sub, map_sub]
  change ‖target u hu - embedding u hu (approximant u hu n)‖ ^ 2 ≤
    ‖target u hu - embedding u hu (∑ i : Fin n, c i • residueAtom i.val)‖ ^ 2
  rw [approximant, embedding_synthesis, embedding_synthesis]
  exact residual_minimizes (atom_independent u hu n) (target u hu) c



/-- All physical cross terms in the actual weighted inner product. -/
theorem embedding_inner (u : ℝ) (hu : 1 ≤ u) (f g : ThresholdHilbert) :
    inner ℝ (embedding u hu f) (embedding u hu g) =
      ∑' n, weightedCellWeight u n *
        (hilbertSequence f (n + 1) * hilbertSequence g (n + 1)) := by
  rw [lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  rw [RCLike.inner_apply']
  change (scale u n * f n) * (scale u n * g n) = _
  rw [hilbertSequence_succ, hilbertSequence_succ, div_mul_div_comm,
    ← pow_two, Real.sq_sqrt (paretoWeight_pos n).le]
  calc
    _ = scale u n ^ 2 * (f n * g n) := by ring
    _ = _ := by rw [scale_sq hu]; ring

/-- Increasing the residue cutoff can only decrease the actual weighted minimum. -/
theorem minimum_antitone (u : ℝ) (hu : 1 ≤ u) :
    Antitone (fun n => WeightedMellin.energy
      (complexPhysicalStep (hilbertOne - approximant u hu n)) u) := by
  intro n m hnm
  have hn : approximant u hu n ∈ finiteSpace n := by
    apply Submodule.sum_mem
    intro i _
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨i, rfl⟩
  have hm : approximant u hu n ∈ finiteSpace m :=
    (walkSpan_mono residueAtom id hnm) hn
  obtain ⟨c, hc⟩ := finiteSpace_expansion m (approximant u hu n) hm
  have hb := approximant_minimizes u hu m c
  rwa [← hc] at hb

/-- Complete weighted error is continuous in the original Pareto topology. -/
theorem error_continuous (u : ℝ) (hu : 1 ≤ u) :
    Continuous (fun f : ThresholdHilbert =>
      WeightedMellin.energy (complexPhysicalStep (hilbertOne - f)) u) := by
  have he : (fun f : ThresholdHilbert =>
      WeightedMellin.energy (complexPhysicalStep (hilbertOne - f)) u) =
      (fun f => ‖embeddingContinuous u hu (hilbertOne - f)‖ ^ 2) := by
    funext f
    exact (embedding_norm_sq u hu (hilbertOne - f)).symm
  rw [he]
  exact ((embeddingContinuous u hu).continuous.comp
    (continuous_const.sub continuous_id)).norm.pow 2

/-- The weighted criterion may be checked using actual finite legal vectors:
passing to the original legal closure does not lower its infimum. -/
theorem finite_legal_approximation_iff_closure (A : Set ℕ) (u : ℝ) (hu : 1 ≤ u) :
    (∀ ε : ℝ, 0 < ε → ∃ f ∈ hilbertLegalSubspace A,
      WeightedMellin.energy (complexPhysicalStep (hilbertOne - f)) u < ε) ↔
    (∀ ε : ℝ, 0 < ε → ∃ f ∈ hilbertLegalClosure A,
      WeightedMellin.energy (complexPhysicalStep (hilbertOne - f)) u < ε) := by
  constructor
  · intro h ε hε
    obtain ⟨f, hf, he⟩ := h ε hε
    exact ⟨f, (hilbertLegalSubspace A).le_topologicalClosure hf, he⟩
  · intro h ε hε
    obtain ⟨f, hf, he⟩ := h ε hε
    have hopen : IsOpen {g : ThresholdHilbert |
        WeightedMellin.energy (complexPhysicalStep (hilbertOne - g)) u < ε} :=
      isOpen_lt (error_continuous u hu) continuous_const
    have hnhds := hopen.mem_nhds he
    obtain ⟨g, hgerr, hglegal⟩ := mem_closure_iff_nhds.mp hf _ hnhds
    exact ⟨g, hglegal, hgerr⟩



def matrix (u : ℝ) (hu : 1 ≤ u) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  gramMatrix (fun i : Fin n => atom u hu i.val)

theorem matrix_posDef (u : ℝ) (hu : 1 ≤ u) (n : ℕ) : (matrix u hu n).PosDef :=
  gramMatrix_posDef (atom_independent u hu n)

theorem matrix_entry (u : ℝ) (hu : 1 ≤ u) (n : ℕ) (i j : Fin n) :
    matrix u hu n i j = ∑' k, weightedCellWeight u k *
      (hilbertSequence (residueAtom i.val) (k + 1) *
        hilbertSequence (residueAtom j.val) (k + 1)) :=
  embedding_inner u hu _ _

theorem coefficients_eq_matrix_inverse (u : ℝ) (hu : 1 ≤ u) (n : ℕ) :
    coefficients u hu n = (matrix u hu n)⁻¹.mulVec (source u hu n) := by
  rw [matrix, gramMatrix_inverseSource (atom_independent u hu n)]
  rfl

/-- The agenda's exact 1/u - bᵀ G⁻¹ b formula for the actual full-tail matrix. -/
theorem minimum_eq_matrix_inverse (u : ℝ) (hu : 1 ≤ u) (n : ℕ) :
    WeightedMellin.energy (complexPhysicalStep (hilbertOne - approximant u hu n)) u =
      1 / u - dotProduct (source u hu n) ((matrix u hu n)⁻¹.mulVec (source u hu n)) := by
  rw [minimum_eq_inverseGram, coefficients_eq_matrix_inverse]
  simp only [dotProduct, mul_comm]


/-- The optimized finite errors converge unconditionally at every fixed u≥2.
This uses the proved actual PNT endpoint family and its known finite support. -/
theorem minimum_tendsto_zero_of_two_le (u : ℝ) (hu : 2 ≤ u) :
    Tendsto (fun n => WeightedMellin.energy
      (complexPhysicalStep (hilbertOne - approximant u (by linarith) n)) u)
      atTop (𝓝 0) := by
  have hu1 : 1 ≤ u := le_trans (by norm_num : (1 : ℝ) ≤ 2) hu
  have hlow (n : ℕ) : 0 ≤ WeightedMellin.energy
      (complexPhysicalStep (hilbertOne - approximant u hu1 n)) u := by
    rw [← embedding_norm_sq u hu1]
    exact sq_nonneg _
  have hupp (n : ℕ) : WeightedMellin.energy
      (complexPhysicalStep (hilbertOne - approximant u hu1 n)) u ≤
      WeightedMellin.energy (complexPhysicalStep
        (hilbertOne - canonicalMobiusHilbert n)) u := by
    obtain ⟨c, hc⟩ := finiteSpace_expansion n (canonicalMobiusHilbert n)
      (canonicalMobiusHilbert_mem_finiteSpace n)
    have hb := approximant_minimizes u hu1 n c
    simpa only [← hc] using hb
  exact squeeze_zero hlow hupp
    (canonicalMobiusResidual_weighted_energy_tendsto_zero hu)

/-- The precise remaining arithmetic obligation for these constructed optimizers.
There is no assertion here that hsmall holds below u=2. -/
theorem riemannHypothesis_of_minima (u : ℕ → ℝ) (hu : ∀ j, 1 ≤ u j)
    (hlim : Tendsto u atTop (𝓝 1))
    (hsmall : ∀ j, Tendsto (fun n => WeightedMellin.energy
      (complexPhysicalStep (hilbertOne - approximant (u j) (hu j) n)) (u j))
        atTop (𝓝 0)) : RiemannHypothesis := by
  apply riemannHypothesis_of_independent_weighted_approximation
    {m : ℕ | 0 < m} (fun _ hm => hm) u hu hlim
  intro j ε hε
  obtain ⟨n, hn⟩ := ((hsmall j).eventually (gt_mem_nhds hε)).exists
  exact ⟨approximant (u j) (hu j) n,
    (hilbertLegalSubspace {m : ℕ | 0 < m}).le_topologicalClosure
      (approximant_mem_legal (u j) (hu j) n), hn⟩

end RiemannResearch.RH.Pareto.WeightedGram
