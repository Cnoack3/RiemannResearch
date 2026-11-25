import RiemannResearch.RH.LegalTailMeanCapacityDilation
import RiemannResearch.RH.NymanContinuousSpace
import RiemannResearch.RH.ParetoNymanPointwise
import RiemannResearch.RH.ParetoResidueMean
import RiemannResearch.RH.ParetoUniformLaw
import RiemannResearch.RH.MultiRangeCompleteness
import RiemannResearch.RH.ArgumentDoublingGenerators
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Legal tail vectors on the rational Nyman mesh

J.-F. Burnol, *A note on Nyman's equivalent formulation of the Riemann
Hypothesis*, Theorem 1.2, https://arxiv.org/abs/math/9910055, supplies the
continuous generator convention and the external projection formula.
We transport the complete norm and the finite legal dictionary to rational
parameters. The continuous zero-product projection identity is a further
analytic theorem.
-/

noncomputable section
namespace RiemannResearch.RH.Pareto
open MeasureTheory Set ArithmeticCumulative
open scoped BigOperators ENNReal
open RiemannResearch.RH.Burnol.ContinuousNyman (realGenerator)

/-- Change of scale on the entire zero-head subspace. -/
theorem scaled_reciprocalFloor_norm_sq (m : ℕ) (hm : 0 < m) (f : ThresholdHilbert)
    (hf : ∀ k : ℕ, k < m → hilbertSequence f k = 0) :
    (∫⁻ u : ℝ in Ioc 0 1, ENNReal.ofReal ((hilbertSequence f ⌊(m : ℝ) / u⌋₊) ^ 2)) =
      ENNReal.ofReal ((m : ℝ) * ‖f‖ ^ 2) := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  let F := fun u : ℝ => ENNReal.ofReal ((hilbertSequence f ⌊(m : ℝ) / u⌋₊) ^ 2)
  have himage : (fun x : ℝ => (m : ℝ) * x) '' Ioc 0 1 = Ioc 0 (m : ℝ) := by
    ext u
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨mul_pos hmR hx.1, by simpa using mul_le_mul_of_nonneg_left hx.2 hmR.le⟩
    · intro hu
      exact ⟨u / m, ⟨div_pos hu.1 hmR, (div_le_one hmR).mpr hu.2⟩, by field_simp⟩
  have hsub := lintegral_image_eq_lintegral_abs_deriv_mul
    (s := Ioc (0 : ℝ) 1) measurableSet_Ioc
    (f := fun x : ℝ => (m : ℝ) * x)
    (fun x _ => (hasDerivAt_const_mul (x := x) (m : ℝ)).hasDerivWithinAt)
    (fun _ _ _ _ h => mul_left_cancel₀ hmR.ne' h) F
  rw [himage, abs_of_pos hmR] at hsub
  have hscale (x : ℝ) : F ((m : ℝ) * x) =
      ENNReal.ofReal ((hilbertSequence f (reciprocalFloor x)) ^ 2) := by
    dsimp [F, reciprocalFloor]
    rw [show (m : ℝ) / ((m : ℝ) * x) = 1 / x by
      simp [div_eq_mul_inv, mul_inv_rev, mul_left_comm, mul_comm, hmR.ne']]
  simp_rw [hscale] at hsub
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at hsub
  have hbase : (∫⁻ x : ℝ in Ioc 0 1, ENNReal.ofReal ((hilbertSequence f (reciprocalFloor x)) ^ 2)) =
      ENNReal.ofReal (‖f‖ ^ 2) := by
    change (∫⁻ x, ENNReal.ofReal ((hilbertSequence f (reciprocalFloor x)) ^ 2) ∂uniformUnit) = _
    rw [uniformUnit_lintegral_square, hilbert_norm_weighted_sq,
      ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg (positiveWeight_nonneg k) (sq_nonneg _))
        (hilbertSequence_square_summable f)] <;> rfl
  rw [hbase, ← ENNReal.ofReal_mul hmR.le] at hsub
  have hz : (∫⁻ u : ℝ in Ioc 1 (m : ℝ), F u) = 0 := by
    refine le_antisymm ?_ bot_le
    calc
      _ ≤ ∫⁻ _u : ℝ in Ioc 1 (m : ℝ), (0 : ℝ≥0∞) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
        have hu0 : 0 < u := zero_lt_one.trans hu.1
        have hk : ⌊(m : ℝ) / u⌋₊ < m := (Nat.floor_lt (div_nonneg hmR.le hu0.le)).mpr
          ((div_lt_iff₀ hu0).mpr (by nlinarith [mul_pos hmR (sub_pos.mpr hu.1)]))
        simp [F, hf _ hk]
      _ = 0 := by simp
  rw [← Ioc_union_Ioc_eq_Ioc (zero_le_one : (0 : ℝ)≤1) hm1,
    lintegral_union measurableSet_Ioc (disjoint_left.mpr fun _ h1 h2 => (not_lt_of_ge h1.2) h2.1),
    hz, add_zero] at hsub
  exact hsub

/-- Every rational mesh generator is the negative of the project's anchored
divisor direction, with the scale visible inside the physical floor. -/
theorem realGenerator_eq_neg_divisorAnchor (m d : ℕ) (hm : 0 < m) (hd : 0 < d)
    (u : ℝ) (hu : 0 < u) :
    realGenerator ((m : ℝ) / d) u = -divisorAnchorDirection m d ⌊(m : ℝ) / u⌋₊ := by
  have hmR : (m : ℝ) ≠ 0 := by positivity
  have hdR : (d : ℝ) ≠ 0 := by positivity
  have hx : 0 ≤ (m : ℝ) / u := by positivity
  have hd' := fract_div_sub_fract_div_eq_floor_mod ((m : ℝ) / u) hx d hd
  have hm' := fract_div_sub_fract_div_eq_floor_mod ((m : ℝ) / u) hx m hm
  rw [show ((m : ℝ) / u) / m = 1 / u by field_simp [hmR, hu.ne']] at hm'
  rw [show ((m : ℝ) / u) / d = ((m : ℝ) / d) / u by ring] at hd'
  unfold realGenerator divisorAnchorDirection residueFraction
  rw [← hd', ← hm']
  field_simp [hmR, hdR]
  ring

/-- Conversely every finite legal vector vanishing through a positive head
has one finite rational Nyman expansion valid on the whole positive half-line. -/
theorem legal_zero_head_exists_nyman_mesh {F : ℕ → ℝ} (Y : ℕ) (hY : 0 < Y)
    (hF : F ∈ legalSeedSpan (Ici 1)) (hh : ∀ n, 0 < n → n ≤ Y → F n = 0) :
    ∃ (s : Finset ℕ) (a : ℕ → ℝ), (∀ d ∈ s, Y < d) ∧
      ∀ u : ℝ, 0 < u → F ⌊((Y + 1 : ℕ) : ℝ) / u⌋₊ =
        ∑ d ∈ s, a d * realGenerator (((Y + 1 : ℕ) : ℝ) / d) u := by
  obtain ⟨v, c, hv, hc⟩ := legal_exists_normalized_synthesis hF
  obtain ⟨s, x, hs, hx⟩ := normalized_zero_head_range_representation Y hY v c hv
    (by simpa only [hc] using hh)
  refine ⟨s, fun d => -x d, hs, ?_⟩
  intro u hu
  rw [← hc, ← hx]
  unfold divisorRangeCorrection
  apply Finset.sum_congr rfl
  intro d hd
  rw [realGenerator_eq_neg_divisorAnchor _ _ (Nat.succ_pos _) (by have := hs d hd; omega) u hu]
  ring

/--
info: 'RiemannResearch.RH.Pareto.scaled_reciprocalFloor_norm_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms scaled_reciprocalFloor_norm_sq

/--
info: 'RiemannResearch.RH.Pareto.realGenerator_eq_neg_divisorAnchor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms realGenerator_eq_neg_divisorAnchor

/--
info: 'RiemannResearch.RH.Pareto.legal_zero_head_exists_nyman_mesh' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms legal_zero_head_exists_nyman_mesh

namespace PrimePowerSchur
open CoefficientStabilization FiniteHeadRepair

/-- The Hilbert-space trial realizing the rational generator r_d - (m/d) r_m. -/
theorem rational_residue_pair_mem_legalHeadKernel (m d : ℕ) (hm : 0 < m) (hmd : m ≤ d) :
    normalizedResidueHilbert d (hm.trans_le hmd) - ((m : ℝ) / d) • normalizedResidueHilbert m hm
      ∈ legalHeadKernel (m - 1) := by
  refine ⟨CoefficientStabilization.closedSpace.sub_mem (normalizedResidue_mem_closedSpace _ _)
    (CoefficientStabilization.closedSpace.smul_mem _ (normalizedResidue_mem_closedSpace _ _)), ?_⟩
  change headMap (m - 1) _ = 0
  ext i
  have hi : (i : ℕ) + 1 < m := by have := i.isLt; omega
  simp only [headMap_apply, hilbertSequence_sub, hilbertSequence_smul, Pi.sub_apply,
    Pi.smul_apply, Pi.zero_apply, normalizedResidueHilbert_sequence, residueFraction,
    Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt (hi.trans_le hmd), smul_eq_mul]
  have hmR : (m : ℝ) ≠ 0 := by positivity
  have hdR : (d : ℝ) ≠ 0 := by have := hm.trans_le hmd; positivity
  field_simp [hmR, hdR]
  ring

/--
info: 'RiemannResearch.RH.Pareto.PrimePowerSchur.rational_residue_pair_mem_legalHeadKernel' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms rational_residue_pair_mem_legalHeadKernel

/-- The signed mean of the actual rational test at scale m, including d = m. -/
theorem rational_residue_pair_scaled_mean (m d : ℕ) (hm : 0 < m) (hd : 0 < d) :
    (m : ℝ) * inner ℝ hilbertOne
        (normalizedResidueHilbert d hd - ((m : ℝ) / d) • normalizedResidueHilbert m hm) =
      ((m : ℝ) / d) * Real.log ((d : ℝ) / m) := by
  have hmean (n : ℕ) (hn : 0 < n) :
      inner ℝ (normalizedResidueHilbert n hn) hilbertOne = Real.log (n : ℝ) / n := by
    rw [normalizedResidueHilbert, real_inner_smul_left, hilbert_inner_one,
      hilbertSequence_digitHilbert]
    have he : digitSequence n 1 = residue n := by
      funext k
      simp [digitSequence, residue]
    rw [he, paretoMean_residue n hn]
    ring
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  conv_lhs => arg 2; rw [real_inner_comm]
  rw [inner_sub_left, real_inner_smul_left, hmean, hmean, Real.log_div hd0 hm0]
  field_simp [hd0, hm0]

/--
info: 'RiemannResearch.RH.Pareto.PrimePowerSchur.rational_residue_pair_scaled_mean' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms rational_residue_pair_scaled_mean

end PrimePowerSchur
end RiemannResearch.RH.Pareto
