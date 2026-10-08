import RiemannResearch.RH.StepCorrectionComplete
import RiemannResearch.Analysis.PositiveNaturalCellIntegral
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Full continuum realization of the correction norm

The canonical Pareto step embedding is used literally. The initial cell is
retained, all positive cells are integrated, and all integer endpoint changes
are justified by their zero Lebesgue mass. The result applies to every sequence
with finite physical square energy, without boundedness or finite support.

Source: user-provided argument, `RH_CRT_Optimized_Gains_and_Uniform_Obstruction_20261007.md`,
for the full continuum correction-norm statement. The cell partition and
endpoint-null proof use Mathlib's Lebesgue integration framework.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace RiemannResearch.RH.StepCorrectionNorm
open Pareto
open RiemannResearch.Analysis.PositiveNaturalCellIntegral

/-- The actual corrected square density for the continuum measure `dx/x²`. -/
def continuumCorrectionDensity (f : ℕ → ℝ) (a x : ℝ) : ℝ :=
  (paretoStep f x - a * Int.fract x) ^ 2 / x ^ 2

theorem continuumCorrectionDensity_nonneg (f : ℕ → ℝ) (a x : ℝ) :
    0 ≤ continuumCorrectionDensity f a x := div_nonneg (sq_nonneg _) (sq_nonneg _)

private theorem continuum_cell_ae (f : ℕ → ℝ) (a : ℝ) (n : ℕ) :
    continuumCorrectionDensity f a =ᵐ[volume.restrict (Ioc ((n : ℝ) + 1) ((n : ℝ) + 2))]
      (fun x => (f (n + 1) - a * (x - ((n : ℝ) + 1))) ^ 2 / x ^ 2) := by
  filter_upwards [ae_restrict_mem (measurableSet_Ioc :
      MeasurableSet (Ioc ((n : ℝ) + 1) ((n : ℝ) + 2))),
    ae_restrict_of_ae (volume.ae_ne ((n : ℝ) + 2))] with x hx hxne
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hx0 : 0 ≤ x := by linarith [hx.1]
  have hfloor : ⌊x⌋₊ = n + 1 := by
    apply Nat.floor_eq_on_Ico
    simp only [Nat.cast_add, Nat.cast_one]
    exact ⟨le_of_lt hx.1, by linarith [lt_of_le_of_ne hx.2 hxne]⟩
  have hfract : Int.fract x = x - ((n : ℝ) + 1) := by
    rw [← Int.self_sub_floor, ← natCast_floor_eq_intCast_floor hx0, hfloor]
    simp
  simp only [continuumCorrectionDensity, paretoStep, hfloor, hfract]

private theorem continuum_cell_integrable (f : ℕ → ℝ) (a : ℝ) (n : ℕ) :
    IntegrableOn (continuumCorrectionDensity f a)
      (Ioc ((n : ℝ) + 1) ((n : ℝ) + 2)) := by
  have hc : ContinuousOn
      (fun x : ℝ => (f (n + 1) - a * (x - ((n : ℝ) + 1))) ^ 2 / x ^ 2)
      (Icc ((n : ℝ) + 1) ((n : ℝ) + 2)) := by
    apply ((continuousOn_const.sub
      (continuousOn_const.mul (continuousOn_id.sub continuousOn_const))).pow 2).div
      (continuousOn_id.pow 2)
    intro x hx
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hxpos : (0 : ℝ) < x := by linarith [hx.1]
    exact pow_ne_zero 2 (ne_of_gt hxpos)
  exact (hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self).congr
    (continuum_cell_ae f a n).symm

theorem continuum_cell_integral (f : ℕ → ℝ) (a : ℝ) (n : ℕ) :
    (∫ x in Ioc ((n : ℝ) + 1) ((n : ℝ) + 2), continuumCorrectionDensity f a x) =
      correctedCellEnergy n (f (n + 1)) a := by
  rw [integral_congr_ae (continuum_cell_ae f a n)]
  exact (intervalIntegral.integral_of_le (by linarith)).symm

private theorem continuum_initial_ae (f : ℕ → ℝ) (hf0 : f 0 = 0) (a : ℝ) :
    continuumCorrectionDensity f a =ᵐ[volume.restrict (Ioc 0 1)] (fun _ => a ^ 2) := by
  filter_upwards [ae_restrict_mem (measurableSet_Ioc : MeasurableSet (Ioc (0 : ℝ) 1)),
    ae_restrict_of_ae (volume.ae_ne (1 : ℝ))] with x hx hxne
  have hfloor : ⌊x⌋₊ = 0 := Nat.floor_eq_on_Ico 0 x
    ⟨by simpa using le_of_lt hx.1, by simpa using lt_of_le_of_ne hx.2 hxne⟩
  have hfract : Int.fract x = x := by
    rw [← Int.self_sub_floor, ← natCast_floor_eq_intCast_floor (le_of_lt hx.1), hfloor]
    simp
  simp only [continuumCorrectionDensity, paretoStep, hfloor, hf0, hfract]
  field_simp [ne_of_gt hx.1]
  <;> ring

private theorem continuum_initial_integrable (f : ℕ → ℝ) (hf0 : f 0 = 0) (a : ℝ) :
    IntegrableOn (continuumCorrectionDensity f a) (Ioc 0 1) := by
  have hc : IntegrableOn (fun _ : ℝ => a ^ 2) (Ioc 0 1) :=
    (continuousOn_const : ContinuousOn (fun _ : ℝ => a ^ 2) (Icc 0 1)).integrableOn_Icc
      |>.mono_set Ioc_subset_Icc_self
  exact hc.congr (continuum_initial_ae f hf0 a).symm

theorem continuum_initial_integral (f : ℕ → ℝ) (hf0 : f 0 = 0) (a : ℝ) :
    (∫ x in Ioc 0 1, continuumCorrectionDensity f a x) = a ^ 2 := by
  rw [integral_congr_ae (continuum_initial_ae f hf0 a)]
  simp

/-- Even without a finite-energy assumption, the complete nonnegative continuum
norm is exactly the first correction square and every physical cell energy. -/
theorem continuumCorrection_lintegral (f : ℕ → ℝ) (hf0 : f 0 = 0) (a : ℝ) :
    (∫⁻ x in Ioi 0, ENNReal.ofReal (continuumCorrectionDensity f a x)) =
      ENNReal.ofReal (a ^ 2) +
        ∑' n, ENNReal.ofReal (correctedCellEnergy n (f (n + 1)) a) := by
  rw [lintegral_Ioi_eq_head_add_tsum_cells]
  have hn := fun x => continuumCorrectionDensity_nonneg f a x
  have hhead := ofReal_integral_eq_lintegral_ofReal
    (continuum_initial_integrable f hf0 a) (Filter.Eventually.of_forall hn)
  rw [continuum_initial_integral f hf0 a] at hhead
  simp only [zero_add] at *
  rw [← hhead]
  congr 1
  apply tsum_congr
  intro n
  have hcell := ofReal_integral_eq_lintegral_ofReal
    (continuum_cell_integrable f a n) (Filter.Eventually.of_forall hn)
  rw [continuum_cell_integral f a n] at hcell
  simpa only [add_comm, add_left_comm, add_assoc, one_add_one_eq_two] using hcell.symm

/-- Finite physical step energy gives integrability on the complete continuum
ray, including the singular endpoint and the entire infinite tail. -/
theorem continuumCorrection_integrable (f : ℕ → ℝ) (hf0 : f 0 = 0)
    (hf : Summable (fun n => positiveWeight (n + 1) * (f (n + 1)) ^ 2)) (a : ℝ) :
    IntegrableOn (continuumCorrectionDensity f a) (Ioi 0) := by
  rw [← iUnion_nat_cells 0]
  apply integrableOn_iUnion_of_summable_integral_norm
  · intro n
    cases n with
    | zero => simpa using continuum_initial_integrable f hf0 a
    | succ n =>
      simpa only [zero_add, Nat.cast_add, Nat.cast_one, Nat.succ_eq_add_one,
        add_assoc, one_add_one_eq_two] using continuum_cell_integrable f a n
  · apply (summable_nat_add_iff 1).mp
    apply (correctedEnergy_summable hf a).congr
    intro n
    simp only [Nat.cast_add, Nat.cast_one, zero_add, add_assoc, one_add_one_eq_two]
    simp_rw [Real.norm_eq_abs, abs_of_nonneg (continuumCorrectionDensity_nonneg f a _)]
    exact (continuum_cell_integral f a n).symm

/-- Actual continuum integration realizes the complete corrected norm square. -/
theorem continuumCorrection_integral (f : ℕ → ℝ) (hf0 : f 0 = 0)
    (hf : Summable (fun n => positiveWeight (n + 1) * (f (n + 1)) ^ 2)) (a : ℝ) :
    (∫ x in Ioi 0, continuumCorrectionDensity f a x) =
      correctedEnergy (fun n => f (n + 1)) a := by
  have hsum := (hasSum_integral_Ioi_cells 0
    (continuumCorrection_integrable f hf0 hf a)).tsum_eq
  rw [← hsum]
  rw [Summable.tsum_eq_zero_add
    (hasSum_integral_Ioi_cells 0 (continuumCorrection_integrable f hf0 hf a)).summable]
  simp only [zero_add, Nat.cast_zero, Nat.cast_add, Nat.cast_one,
    add_assoc, one_add_one_eq_two]
  rw [continuum_initial_integral f hf0 a]
  unfold correctedEnergy
  congr 1
  apply tsum_congr
  intro n
  exact continuum_cell_integral f a n

/-- Full signed continuum correction-norm assembly for every finite-energy step. -/
theorem continuumCorrection_assembly (f : ℕ → ℝ) (hf0 : f 0 = 0)
    (hf : Summable (fun n => positiveWeight (n + 1) * (f (n + 1)) ^ 2)) (a : ℝ) :
    (∫ x in Ioi 0, continuumCorrectionDensity f a x) =
      stepEnergy (fun n => f (n + 1)) -
        2 * a * correctionSource (fun n => f (n + 1)) + a ^ 2 * residueEnergy := by
  rw [continuumCorrection_integral f hf0 hf a, correctedEnergy_assembly hf a]

/-- The complete orthogonal split is an identity of actual continuum integrals. -/
theorem continuumCorrection_orthogonal_split (f : ℕ → ℝ) (hf0 : f 0 = 0)
    (hf : Summable (fun n => positiveWeight (n + 1) * (f (n + 1)) ^ 2)) (a : ℝ) :
    (∫ x in Ioi 0, continuumCorrectionDensity f a x) =
      (∑' n, positiveWeight (n + 1) * (f (n + 1) - a * cellMean n) ^ 2) +
        a ^ 2 * residualEnergy := by
  rw [continuumCorrection_integral f hf0 hf a, correctedEnergy_orthogonal_split hf a]

/-- The complete raw fractional-part density is integrable on `(0,∞)`. -/
theorem fract_energy_integrable :
    IntegrableOn (fun x : ℝ => (Int.fract x) ^ 2 / x ^ 2) (Ioi 0) := by
  have hh : Summable (fun n : ℕ => positiveWeight (n + 1) * (0 : ℝ) ^ 2) := by
    simp
  have hi := continuumCorrection_integrable (fun _ => 0) rfl hh 1
  change IntegrableOn (fun x => continuumCorrectionDensity (fun _ => 0) 1 x) (Ioi 0) at hi
  simpa only [continuumCorrectionDensity, paretoStep, zero_sub, one_mul, neg_sq] using hi

/-- The literal continuum fractional-part norm includes the initial cell and
all positive cells of the complete residue series. -/
theorem fract_energy_integral :
    (∫ x in Ioi 0, (Int.fract x) ^ 2 / x ^ 2) = residueEnergy := by
  have hh : Summable (fun n : ℕ => positiveWeight (n + 1) * (0 : ℝ) ^ 2) := by
    simp
  simpa [continuumCorrectionDensity, paretoStep, stepEnergy, correctionSource] using
    continuumCorrection_assembly (fun _ => 0) rfl hh 1

/-- The complete continuum assembly for every vector of the canonical Hilbert
space, with no remaining analytic provider hypothesis. -/
theorem continuumCorrection_hilbert (f : ThresholdHilbert) (a : ℝ) :
    (∫ x in Ioi 0, continuumCorrectionDensity (hilbertSequence f) a x) =
      ‖f‖ ^ 2 - 2 * a * correctionSource (fun n => hilbertSequence f (n + 1)) +
        a ^ 2 * residueEnergy := by
  have hh : Summable (fun n => positiveWeight (n + 1) *
      (hilbertSequence f (n + 1)) ^ 2) := by
    simpa only [hilbertSequence_weighted_square] using hilbert_coordinate_square_summable f
  rw [continuumCorrection_integral (hilbertSequence f) (hilbertSequence_zero f) hh a,
    correctedEnergy_hilbert f a]

/-- The sharp transfer gap is the sum of the full charge square and the full
Cauchy gap, now for the literal continuum norm of every Hilbert-space vector. -/
theorem continuumCorrection_hilbert_transfer_gap (f : ThresholdHilbert) (a : ℝ) :
    residueEnergy * (∫ x in Ioi 0, continuumCorrectionDensity (hilbertSequence f) a x) -
        residualEnergy * ‖f‖ ^ 2 =
      (residueEnergy * a - correctionSource (fun n => hilbertSequence f (n + 1))) ^ 2 +
        (‖f‖ ^ 2 * projectionEnergy -
          correctionSource (fun n => hilbertSequence f (n + 1)) ^ 2) := by
  have hh : Summable (fun n => positiveWeight (n + 1) *
      (hilbertSequence f (n + 1)) ^ 2) := by
    simpa only [hilbertSequence_weighted_square] using hilbert_coordinate_square_summable f
  rw [continuumCorrection_integral (hilbertSequence f) (hilbertSequence_zero f) hh a,
    ← stepEnergy_hilbert f]
  exact correctedEnergy_transfer_gap hh a

/-- Sharp structural transfer on the full canonical Hilbert space. -/
theorem continuumCorrection_hilbert_transfer (f : ThresholdHilbert) (a : ℝ) :
    ‖f‖ ^ 2 ≤ (residueEnergy / residualEnergy) *
      (∫ x in Ioi 0, continuumCorrectionDensity (hilbertSequence f) a x) := by
  have hh : Summable (fun n => positiveWeight (n + 1) *
      (hilbertSequence f (n + 1)) ^ 2) := by
    simpa only [hilbertSequence_weighted_square] using hilbert_coordinate_square_summable f
  rw [continuumCorrection_integral (hilbertSequence f) (hilbertSequence_zero f) hh a,
    ← stepEnergy_hilbert f]
  exact correctedEnergy_transfer hh a

/-- The actual continuum transfer factor is minimal on the full canonical
Hilbert space, not merely on finite or bounded step sequences. -/
theorem continuumCorrection_hilbert_factor_minimal (K : ℝ)
    (hK : ∀ f : ThresholdHilbert, ∀ a : ℝ,
      ‖f‖ ^ 2 ≤ K *
        (∫ x in Ioi 0, continuumCorrectionDensity (hilbertSequence f) a x)) :
    residueEnergy / residualEnergy ≤ K := by
  apply correctionTransferFactor_minimal K
  intro h hh a
  let g : ℕ → ℝ
    | 0 => 0
    | n + 1 => h n
  have hg0 : g 0 = 0 := rfl
  have hgpos : ∀ n, g (n + 1) = h n := fun _ => rfl
  have hg : Summable (fun k => positiveWeight k * (g k) ^ 2) := by
    apply (summable_nat_add_iff 1).mp
    simpa only [hgpos] using hh
  obtain ⟨f, hf⟩ := (hilbertSequence_range g).mpr ⟨hg0, hg⟩
  have hnorm : ‖f‖ ^ 2 = stepEnergy h := by
    rw [← stepEnergy_hilbert f, hf]
  have hhg : Summable (fun n => positiveWeight (n + 1) * (g (n + 1)) ^ 2) := by
    simpa only [hgpos] using hh
  have hint : (∫ x in Ioi 0, continuumCorrectionDensity (hilbertSequence f) a x) =
      correctedEnergy h a := by
    rw [hf, continuumCorrection_integral g hg0 hhg a]
  simpa only [hnorm, hint] using hK f a

/-- The sharp transfer of norms, obtained from the complete actual continuum
square identity with its proved nonnegative factors. -/
theorem continuumCorrection_hilbert_norm_transfer (f : ThresholdHilbert) (a : ℝ) :
    ‖f‖ ≤ Real.sqrt (residueEnergy / residualEnergy) *
      Real.sqrt (∫ x in Ioi 0, continuumCorrectionDensity (hilbertSequence f) a x) := by
  have hfactor : 0 ≤ residueEnergy / residualEnergy :=
    div_nonneg (le_of_lt residueEnergy_pos) (by linarith [residualEnergy_ge_one])
  calc
    ‖f‖ = Real.sqrt (‖f‖ ^ 2) := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg f)]
    _ ≤ Real.sqrt ((residueEnergy / residualEnergy) *
        (∫ x in Ioi 0, continuumCorrectionDensity (hilbertSequence f) a x)) :=
      Real.sqrt_le_sqrt (continuumCorrection_hilbert_transfer f a)
    _ = _ := Real.sqrt_mul hfactor _

/-- Minimality of the sharp norm factor among nonnegative norm bounds. -/
theorem continuumCorrection_hilbert_norm_factor_minimal (K : ℝ) (hK0 : 0 ≤ K)
    (hK : ∀ f : ThresholdHilbert, ∀ a : ℝ,
      ‖f‖ ≤ K *
        Real.sqrt (∫ x in Ioi 0, continuumCorrectionDensity (hilbertSequence f) a x)) :
    Real.sqrt (residueEnergy / residualEnergy) ≤ K := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨hK0, continuumCorrection_hilbert_factor_minimal (K ^ 2) ?_⟩
  intro f a
  have he : 0 ≤ (∫ x in Ioi 0, continuumCorrectionDensity (hilbertSequence f) a x) :=
    integral_nonneg (fun x => continuumCorrectionDensity_nonneg (hilbertSequence f) a x)
  have hb : 0 ≤ K * Real.sqrt
      (∫ x in Ioi 0, continuumCorrectionDensity (hilbertSequence f) a x) :=
    mul_nonneg hK0 (Real.sqrt_nonneg _)
  have hs := (sq_le_sq₀ (norm_nonneg f) hb).mpr (hK f a)
  simpa only [mul_pow, Real.sq_sqrt he] using hs


end RiemannResearch.RH.StepCorrectionNorm
