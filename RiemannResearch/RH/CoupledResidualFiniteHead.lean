import RiemannResearch.RH.CoupledResidualHeadBounds
import RiemannResearch.RH.CoupledResidualCorrections
import RiemannResearch.RH.ThresholdHilbertSpace
import RiemannResearch.RH.ThresholdHilbertDilation
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Signed finite-head certificates for actual coupled residual sources

Source: user-directed residual-projection investigation, 14 November 2026.
The exact parallelogram identities retain the complete nonnegative tail
remainders. The resulting finite-head intervals converge to each actual
signed source, at each fixed budget. No uniform cutoff or source lower bound
is asserted. In particular, the original two-coordinate positive-part
certificate can vanish in the explicit head cone proved below.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto.CoupledResidual
open FiniteTwoSeedCompletion RamanujanLaguerre AdjacentPacket

/-- Energy in the first K weighted Hilbert coordinates (physical sites 1,...,K). -/
def coordinateHeadEnergy (f : ThresholdHilbert) (K : ℕ) : ℝ :=
  ∑ n ∈ Finset.range K, (f n)^2

theorem coordinateHeadEnergy_physical (f : ThresholdHilbert) (K : ℕ) :
    coordinateHeadEnergy f K =
      ∑ n ∈ Finset.range K, positiveWeight (n+1) * hilbertSequence f (n+1)^2 := by
  simp only [coordinateHeadEnergy, hilbertSequence_weighted_square]

theorem coordinateHeadEnergy_le (f : ThresholdHilbert) (K : ℕ) :
    coordinateHeadEnergy f K ≤ ‖f‖^2 := by
  rw [hilbert_norm_sq]
  exact (hilbert_coordinate_square_summable f).sum_le_tsum
    (Finset.range K) (fun n _ => sq_nonneg (f n))

theorem coordinateHeadEnergy_tendsto (f : ThresholdHilbert) :
    Tendsto (coordinateHeadEnergy f) atTop (𝓝 (‖f‖^2)) := by
  rw [hilbert_norm_sq]
  exact (hilbert_coordinate_square_summable f).hasSum.tendsto_sum_nat

theorem coordinateHeadEnergy_mono (f : ThresholdHilbert) :
    Monotone (coordinateHeadEnergy f) := by
  apply monotone_nat_of_le_succ
  intro K
  simp only [coordinateHeadEnergy, Finset.sum_range_succ]
  linarith only [sq_nonneg (f K)]

/-- The actual dilated earlier residual, with the floor scale retained. -/
def sourceDilation (M p : ℕ) (hp : 0 < p) : ThresholdHilbert :=
  hilbertDilation p hp (error (2*M/p))

/-- Before subtracting the dilation correlation. For p=2,3 this is a finite head. -/
def sourceMain (M p : ℕ) (hp : 0 < p) : ℝ :=
  inner ℝ (error M) (hilbertDilation p hp hilbertOne)

theorem sourceMain_binary (M : ℕ) :
    sourceMain M 2 (by omega) = 2*distance M - hilbertSequence (error M) 1 := by
  have h := source_residual_identity M 2 (by omega)
  rw [binary_source] at h
  rw [show 2*M/2 = M by omega] at h
  dsimp only [sourceMain]
  linarith only [h]

theorem sourceMain_ternary (M : ℕ) :
    sourceMain M 3 (by omega) =
      3*distance M - (3/2:ℝ)*hilbertSequence (error M) 1 -
        (1/2:ℝ)*hilbertSequence (error M) 2 := by
  have h := source_residual_identity M 3 (by omega)
  rw [ternary_source] at h
  dsimp only [sourceMain]
  linarith only [h]

/-- Explicit lower endpoint obtained from the difference-vector head. -/
def finiteSourceLower (M p : ℕ) (hp : 0 < p) (K : ℕ) : ℝ :=
  sourceMain M p hp - (distance M + (p:ℝ)*distance (2*M/p))/2 +
    coordinateHeadEnergy (error M - sourceDilation M p hp) K / 2

/-- Explicit upper endpoint obtained from the sum-vector head. -/
def finiteSourceUpper (M p : ℕ) (hp : 0 < p) (K : ℕ) : ℝ :=
  sourceMain M p hp + (distance M + (p:ℝ)*distance (2*M/p))/2 -
    coordinateHeadEnergy (error M + sourceDilation M p hp) K / 2

/-- Full equality: the omitted difference energy is a nonnegative tail. -/
theorem source_lower_tail_identity (M p : ℕ) (hp : 0 < p) (K : ℕ) :
    source M p hp = finiteSourceLower M p hp K +
      (‖error M - sourceDilation M p hp‖^2 -
        coordinateHeadEnergy (error M - sourceDilation M p hp) K)/2 := by
  rw [source_residual_identity]
  dsimp only [finiteSourceLower, sourceMain, sourceDilation]
  rw [norm_sub_sq_real, hilbertDilation_norm_sq]
  dsimp only [distance]
  ring

/-- Full equality: the omitted sum energy is a nonnegative tail. -/
theorem source_upper_tail_identity (M p : ℕ) (hp : 0 < p) (K : ℕ) :
    finiteSourceUpper M p hp K = source M p hp +
      (‖error M + sourceDilation M p hp‖^2 -
        coordinateHeadEnergy (error M + sourceDilation M p hp) K)/2 := by
  rw [source_residual_identity]
  dsimp only [finiteSourceUpper, sourceMain, sourceDilation]
  rw [norm_add_sq_real, hilbertDilation_norm_sq]
  dsimp only [distance]
  ring

theorem finiteSource_interval (M p : ℕ) (hp : 0 < p) (K : ℕ) :
    finiteSourceLower M p hp K ≤ source M p hp ∧
      source M p hp ≤ finiteSourceUpper M p hp K := by
  constructor
  · linarith only [source_lower_tail_identity M p hp K,
      coordinateHeadEnergy_le (error M - sourceDilation M p hp) K]
  · linarith only [source_upper_tail_identity M p hp K,
      coordinateHeadEnergy_le (error M + sourceDilation M p hp) K]

theorem finiteSourceLower_tendsto (M p : ℕ) (hp : 0 < p) :
    Tendsto (finiteSourceLower M p hp) atTop (𝓝 (source M p hp)) := by
  have h := ((coordinateHeadEnergy_tendsto (error M - sourceDilation M p hp)).const_sub
    (‖error M - sourceDilation M p hp‖^2)).div_const 2
  have h' := h.const_sub (source M p hp)
  convert h' using 1
  · ext K
    linarith only [source_lower_tail_identity M p hp K]
  · simp

theorem finiteSourceUpper_tendsto (M p : ℕ) (hp : 0 < p) :
    Tendsto (finiteSourceUpper M p hp) atTop (𝓝 (source M p hp)) := by
  have h := ((coordinateHeadEnergy_tendsto (error M + sourceDilation M p hp)).const_sub
    (‖error M + sourceDilation M p hp‖^2)).div_const 2
  have h' := h.const_add (source M p hp)
  convert h' using 1
  · ext K
    exact source_upper_tail_identity M p hp K
  · simp

/-- Distance of the certified interval from zero; retains both signs. -/
def finiteSourceMagnitude (M p : ℕ) (hp : 0 < p) (K : ℕ) : ℝ :=
  max 0 (max (finiteSourceLower M p hp K) (-finiteSourceUpper M p hp K))

theorem finiteSourceMagnitude_nonneg (M p : ℕ) (hp : 0 < p) (K : ℕ) :
    0 ≤ finiteSourceMagnitude M p hp K := le_max_left _ _

theorem finiteSourceMagnitude_le_abs (M p : ℕ) (hp : 0 < p) (K : ℕ) :
    finiteSourceMagnitude M p hp K ≤ |source M p hp| := by
  obtain ⟨hl, hu⟩ := finiteSource_interval M p hp K
  exact max_le (abs_nonneg _) (max_le (hl.trans (le_abs_self _))
    ((neg_le_neg hu).trans (neg_le_abs _)))

theorem finiteSourceMagnitude_sq_le (M p : ℕ) (hp : 0 < p) (K : ℕ) :
    (finiteSourceMagnitude M p hp K)^2 ≤ (source M p hp)^2 := by
  have h := finiteSourceMagnitude_le_abs M p hp K
  have hn := finiteSourceMagnitude_nonneg M p hp K
  nlinarith [sq_abs (source M p hp)]

private theorem max_signed_self (s : ℝ) : max 0 (max s (-s)) = |s| := by
  by_cases h : 0 ≤ s
  · rw [abs_of_nonneg h, max_eq_left (by linarith : -s ≤ s), max_eq_right h]
  · have hs : s ≤ 0 := le_of_not_ge h
    rw [abs_of_nonpos hs, max_eq_right (by linarith : s ≤ -s),
      max_eq_right (neg_nonneg.mpr hs)]

theorem finiteSourceMagnitude_tendsto (M p : ℕ) (hp : 0 < p) :
    Tendsto (finiteSourceMagnitude M p hp) atTop (𝓝 |source M p hp|) := by
  have h := (show Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0) from tendsto_const_nhds).max
    ((finiteSourceLower_tendsto M p hp).max (finiteSourceUpper_tendsto M p hp).neg)
  change Tendsto (fun K => max 0
    (max (finiteSourceLower M p hp K) (-finiteSourceUpper M p hp K))) _ _
  simpa only [max_signed_self] using h

/-- At each fixed budget, both complete signed sources are recovered as K grows. -/
def finiteSourceSquare (M K : ℕ) : ℝ :=
  (finiteSourceMagnitude M 2 (by omega) K)^2 +
    (finiteSourceMagnitude M 3 (by omega) K)^2

theorem finiteSourceSquare_le_sourceSquare (M K : ℕ) :
    finiteSourceSquare M K ≤ sourceSquare M :=
  add_le_add (finiteSourceMagnitude_sq_le M 2 (by omega) K)
    (finiteSourceMagnitude_sq_le M 3 (by omega) K)

theorem finiteSourceSquare_tendsto (M : ℕ) :
    Tendsto (finiteSourceSquare M) atTop (𝓝 (sourceSquare M)) := by
  change Tendsto (fun K => (finiteSourceMagnitude M 2 (by omega) K)^2 +
    (finiteSourceMagnitude M 3 (by omega) K)^2) _ _
  simpa only [sourceSquare, sq_abs] using
    ((finiteSourceMagnitude_tendsto M 2 (by omega)).pow 2).add
      ((finiteSourceMagnitude_tendsto M 3 (by omega)).pow 2)

/-- Unconditional finite-head lower certificate, also valid at zero trace. -/
theorem finiteSourceSquare_le_trace_gain (M K : ℕ) :
    finiteSourceSquare M K ≤ trace M * gain M := by
  have h2 := interscale_source_sq M 2 (by omega)
  have h3 := interscale_source_sq M 3 (by omega)
  have h := finiteSourceSquare_le_sourceSquare M K
  norm_num only [Nat.cast_ofNat] at h2 h3
  dsimp only [sourceSquare, trace] at h ⊢
  nlinarith

/-- Retain the previous certificate whenever its coarse head bound is better. -/
def combinedSourceSquare (M K : ℕ) : ℝ :=
  max (headSourceSquare M) (finiteSourceSquare M K)

theorem headSourceSquare_le_combined (M K : ℕ) :
    headSourceSquare M ≤ combinedSourceSquare M K := le_max_left _ _

theorem combinedSourceSquare_le_trace_gain (M K : ℕ) :
    combinedSourceSquare M K ≤ trace M * gain M :=
  max_le (headSourceSquare_le_trace_gain M) (finiteSourceSquare_le_trace_gain M K)

theorem combinedSourceSquare_tendsto (M : ℕ) :
    Tendsto (combinedSourceSquare M) atTop (𝓝 (sourceSquare M)) := by
  have h := (show Tendsto (fun _ : ℕ => headSourceSquare M) atTop
    (𝓝 (headSourceSquare M)) from tendsto_const_nhds).max (finiteSourceSquare_tendsto M)
  change Tendsto (fun K => max (headSourceSquare M) (finiteSourceSquare M K)) _ _
  simpa only [max_eq_right (headSourceSquare_le_sourceSquare M)] using h

theorem projected_error_ge_finiteSourceSquare (M K : ℕ) (ht : 0 < trace M) :
    finiteSourceSquare M K / trace M ≤
      ‖(budgetHilbert (2*M)).starProjection (error M)‖^2 := by
  rw [projected_error_norm_sq_eq_gain]
  apply (div_le_iff₀ ht).mpr
  simpa only [mul_comm] using finiteSourceSquare_le_trace_gain M K

/-- Finite heads detect precisely nonzero transported sources, with no uniform K. -/
theorem exists_positive_finiteSourceSquare_iff (M : ℕ) :
    (∃ K, 0 < finiteSourceSquare M K) ↔ 0 < sourceSquare M := by
  constructor
  · rintro ⟨K, hK⟩
    exact hK.trans_le (finiteSourceSquare_le_sourceSquare M K)
  · intro h
    obtain ⟨K, hK⟩ := Filter.Eventually.exists
      ((finiteSourceSquare_tendsto M).eventually (lt_mem_nhds h))
    exact ⟨K, hK⟩

/-- Earlier residual norm cannot be smaller than the current one. -/
theorem distance_le_norm_mul_earlier (M : ℕ) :
    distance M ≤ ‖error M‖ * ‖error (2*M/3)‖ := by
  have he := distance_antitone (show 2*M/3 ≤ M by omega)
  have hn : ‖error M‖ ≤ ‖error (2*M/3)‖ := by
    dsimp only [distance] at he
    nlinarith [norm_nonneg (error M), norm_nonneg (error (2*M/3))]
  dsimp only [distance]
  nlinarith [mul_le_mul_of_nonneg_left hn (norm_nonneg (error M))]

/-- An explicit cone where the original positive-part head certificate is zero.
This is a theorem about the actual residuals, but does not assert cone membership. -/
theorem headSourceSquare_eq_zero_of_head_cone (M : ℕ)
    (h1 : distance M ≤ hilbertSequence (error M) 1)
    (h2 : 0 ≤ hilbertSequence (error M) 2) : headSourceSquare M = 0 := by
  have hs2 : 1 < Real.sqrt 2 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hs3 : (3/2:ℝ) < Real.sqrt 3 :=
    (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hd := (distance_pos M).le
  have he := mul_le_mul_of_nonneg_left (distance_le_norm_mul_earlier M)
    (Real.sqrt_nonneg 3)
  have hb : binaryHeadLower M ≤ 0 := by
    dsimp only [binaryHeadLower]
    nlinarith [mul_nonneg (sub_nonneg.mpr hs2.le) hd]
  have ht : ternaryHeadLower M ≤ 0 := by
    dsimp only [ternaryHeadLower]
    nlinarith [mul_nonneg (sub_nonneg.mpr hs3.le) hd]
  simp only [headSourceSquare, max_eq_left hb, max_eq_left ht, zero_pow (by decide : 2 ≠ 0),
    zero_add]

/-- Any positive original certificate must escape that head cone. -/
theorem head_cone_escape_of_positive_certificate (M : ℕ) (h : 0 < headSourceSquare M) :
    hilbertSequence (error M) 1 < distance M ∨ hilbertSequence (error M) 2 < 0 := by
  by_contra hn
  simp only [not_or, not_lt] at hn
  rw [headSourceSquare_eq_zero_of_head_cone M hn.1 hn.2] at h
  exact (lt_irrefl 0) h

/-- In this cone no multiplier can rescue the original certificate at positive trace. -/
theorem head_certificate_impossible_in_cone (M : ℕ) (A : ℝ)
    (h1 : distance M ≤ hilbertSequence (error M) 1)
    (h2 : 0 ≤ hilbertSequence (error M) 2) (ht : 0 < trace M) :
    ¬ distance M * trace M ≤ A * headSourceSquare M := by
  rw [headSourceSquare_eq_zero_of_head_cone M h1 h2, mul_zero]
  exact not_le.mpr (mul_pos (distance_pos M) ht)

end RiemannResearch.RH.Pareto.CoupledResidual
