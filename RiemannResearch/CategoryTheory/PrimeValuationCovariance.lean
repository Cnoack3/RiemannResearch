import RiemannResearch.CategoryTheory.OddConditionalUnit
import RiemannResearch.Analysis.NestedOrthogonalDecomposition
import RiemannResearch.RH.PrimeValuationIndependence
import RiemannResearch.RH.ParetoCoordinateEvaluation
import RiemannResearch.RH.QParetoEquivalence
import RiemannResearch.RH.ParetoProgressionDigamma
import RiemannResearch.RH.ParetoRamanujanGramCRT
import RiemannResearch.RH.PrimeSupportMeasureChange
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-! # Conditional Gram matrices at a prime valuation cutoff

The observed space consists of the physical profiles constant on each valuation
fibre. The squared residual of a finite packet trial retains every signed
covariance term. Weighting the physical Q inner product once by dP/dQ
preserves the raw parity observable and changes the conditional fit.
Source: the user's Q prime Parseval tower handoff and change of metric.
-/

noncomputable section
open scoped BigOperators
open RiemannResearch.RH RiemannResearch.RH.ZetaTwoHilbert
open RiemannResearch.RH.ZetaTwoProbability RiemannResearch.RH.ZetaTwoParitySignal
open RiemannResearch.RH.ZetaTwoParetoTransfer RiemannResearch.RH.QParetoEquivalence
open RiemannResearch.RH.Pareto RiemannResearch.RH.Pareto.PrimePowerSchur
open RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis
open RiemannResearch.CategoryTheory.OddConditionalUnit (B densityInner densityInner_eq_pareto)
open MeasureChange (qParity)

namespace RiemannResearch.CategoryTheory.PrimeValuationCovariance

/-- All revealed prime exponents agree on the two physical sites. -/
def sameFibre (cutoff : ℕ) (i j : ℕ+) : Prop :=
  ∀ p : ℕ, p.Prime → p ≤ cutoff → primeValuation p i = primeValuation p j

private def evaluation (i : ℕ+) : QHilbert →L[ℝ] ℝ :=
  (physicalEvaluationCLM ((i : ℕ) - 1)).comp paretoEquiv.toContinuousLinearMap

private theorem evaluation_apply (i : ℕ+) (x : QHilbert) :
    evaluation i x = qSequence x i := by
  change physicalEvaluationCLM ((i : ℕ)-1) (paretoEquiv x) = _
  rw [physicalEvaluationCLM_apply, paretoEquiv_apply, toPareto_sequence]
  congr 1
  have := i.pos
  omega

/-- The closed Q space of functions of the revealed valuations. -/
def observed (cutoff : ℕ) : Submodule ℝ QHilbert where
  carrier := {x | ∀ i j : ℕ+, sameFibre cutoff i j → evaluation i x = evaluation j x}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy i j h
    rw [map_add, map_add, hx i j h, hy i j h]
  smul_mem' := by
    intro a x hx i j h
    rw [map_smul, map_smul, hx i j h]

theorem mem_observed (cutoff : ℕ) (x : QHilbert) :
    x ∈ observed cutoff ↔ ∀ i j : ℕ+, sameFibre cutoff i j → qSequence x i = qSequence x j := by
  change (∀ i j : ℕ+, sameFibre cutoff i j → evaluation i x = evaluation j x) ↔ _
  simp only [evaluation_apply]

theorem observed_isClosed (cutoff : ℕ) : IsClosed (observed cutoff : Set QHilbert) := by
  change IsClosed {x : QHilbert | ∀ i j : ℕ+,
    sameFibre cutoff i j → evaluation i x = evaluation j x}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_eq (evaluation i).continuous (evaluation j).continuous

instance observed_projection (cutoff : ℕ) : (observed cutoff).HasOrthogonalProjection := by
  let : CompleteSpace (observed cutoff) := (observed_isClosed cutoff).completeSpace_coe
  exact Submodule.HasOrthogonalProjection.ofCompleteSpace _

theorem physical_parity_observed {cutoff : ℕ} (hB : 2 ≤ cutoff) : qParity ∈ observed cutoff := by
  have hOdd : qOdd ∈ observed cutoff := by
    apply (mem_observed _ _).2
    intro i j h
    have he : (i : ℕ).factorization 2 = (j : ℕ).factorization 2 := h 2 Nat.prime_two hB
    have hd : (2 ∣ (i : ℕ)) ↔ (2 ∣ (j : ℕ)) := by
      change (2 ^ 1 ∣ (i : ℕ)) ↔ (2 ^ 1 ∣ (j : ℕ))
      rw [Nat.prime_two.pow_dvd_iff_le_factorization i.pos.ne',
        Nat.prime_two.pow_dvd_iff_le_factorization j.pos.ne', he]
    simp only [qSequence_qOdd, hd]
  have hOne : qOne ∈ observed cutoff := by
    apply (mem_observed _ _).2
    intro i j _
    simp [qSequence_qOne, qOneSequence, i.pos.ne', j.pos.ne']
  rw [MeasureChange.qParity_eq_odd]
  exact (observed cutoff).sub_mem ((observed cutoff).smul_mem _ hOdd) hOne

/-- Complete signed covariance of two omitted valuation components. -/
def covariance (cutoff : ℕ) (x y : QHilbert) : ℝ :=
  inner ℝ (x - (observed cutoff).starProjection x) (y - (observed cutoff).starProjection y)

private theorem projection_gram {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : Submodule ℝ E) [S.HasOrthogonalProjection] (x y : E) :
    inner ℝ x y = inner ℝ (S.starProjection x) (S.starProjection y) +
      inner ℝ (x-S.starProjection x) (y-S.starProjection y) := by
  have hx : inner ℝ (x - S.starProjection x) (S.starProjection y) = 0 :=
    (real_inner_comm _ _).trans
      (S.sub_starProjection_mem_orthogonal x _ (S.starProjection_apply_mem y))
  have hy : inner ℝ (S.starProjection x) (y - S.starProjection y) = 0 :=
    S.sub_starProjection_mem_orthogonal y _ (S.starProjection_apply_mem x)
  simp only [inner_sub_left, inner_sub_right] at hx hy ⊢
  linarith only [hx, hy]

theorem gram_split (cutoff : ℕ) (x y : QHilbert) :
    inner ℝ x y = inner ℝ ((observed cutoff).starProjection x)
      ((observed cutoff).starProjection y) + covariance cutoff x y :=
  projection_gram (observed cutoff) x y

/-- Quadratic form of the entire residual matrix of a finite dictionary. -/
theorem finite_covariance_energy {ι : Type*} (s : Finset ι)
    (cutoff : ℕ) (c : ι → ℝ) (x : ι → QHilbert) :
    let m := ∑ i ∈ s, c i • x i
    ‖m - (observed cutoff).starProjection m‖ ^ 2 =
      ∑ i ∈ s, ∑ j ∈ s, c i * c j * covariance cutoff (x i) (x j) := by
  let R : QHilbert →L[ℝ] QHilbert :=
    ContinuousLinearMap.id ℝ QHilbert - (observed cutoff).starProjection
  change ‖R (∑ i ∈ s, c i • x i)‖ ^ 2 = _
  rw [map_sum]
  simp only [map_smul]
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [real_inner_smul_left, real_inner_smul_right, mul_assoc]
  rfl

/-- For a general target, variance is evaluated on the entire error. -/
theorem trial_error_split (cutoff : ℕ) (target trial : QHilbert) :
    let err := target - trial
    ‖err‖ ^ 2 = ‖(observed cutoff).starProjection err‖ ^ 2 + covariance cutoff err err := by
  simpa only [real_inner_self_eq_norm_sq] using gram_split cutoff (target-trial) (target-trial)

/-- When the target is raw centered parity, its omitted part is zero starting at two. -/
theorem physical_parity_error_split {cutoff : ℕ} (hB : 2 ≤ cutoff) (m : QHilbert) :
    ‖qParity - m‖ ^ 2 = ‖qParity - (observed cutoff).starProjection m‖ ^ 2 +
      covariance cutoff m m := by
  have h := trial_error_split cutoff qParity m
  have hp := (observed cutoff).starProjection_eq_self_iff.mpr (physical_parity_observed hB)
  dsimp only at h
  rw [map_sub, hp] at h
  have hcov : covariance cutoff (qParity-m) (qParity-m) = covariance cutoff m m := by
    unfold covariance
    rw [map_sub, hp, show qParity - m - (qParity - (observed cutoff).starProjection m) =
      -(m - (observed cutoff).starProjection m) by abel, inner_neg_left, inner_neg_right, neg_neg]
  rwa [hcov] at h

/-- The same measurable physical profiles with the Pareto Hilbert norm. -/
def densityObserved (cutoff : ℕ) : Submodule ℝ ThresholdHilbert :=
  (observed cutoff).comap paretoEquiv.symm.toLinearMap

instance densityObserved_projection (cutoff : ℕ) :
    (densityObserved cutoff).HasOrthogonalProjection := by
  have hc : IsClosed (densityObserved cutoff : Set ThresholdHilbert) :=
    (observed_isClosed cutoff).preimage paretoEquiv.symm.continuous
  let : CompleteSpace (densityObserved cutoff) := hc.completeSpace_coe
  exact Submodule.HasOrthogonalProjection.ofCompleteSpace _

/-- The conditional fit of a physical Q profile for the law with integration weight B. -/
def densityProjection (cutoff : ℕ) : QHilbert →L[ℝ] QHilbert :=
  paretoEquiv.symm.toContinuousLinearMap.comp
    ((densityObserved cutoff).starProjection.comp paretoEquiv.toContinuousLinearMap)

theorem densityProjection_apply (cutoff : ℕ) (x : QHilbert) :
    paretoEquiv (densityProjection cutoff x) =
      (densityObserved cutoff).starProjection (paretoEquiv x) :=
  paretoEquiv.apply_symm_apply _

theorem densityProjection_mem (cutoff : ℕ) (x : QHilbert) :
    densityProjection cutoff x ∈ observed cutoff :=
  (densityObserved cutoff).starProjection_apply_mem (paretoEquiv x)

private theorem physical_mem_densityObserved {cutoff : ℕ} {t : QHilbert}
    (ht : t ∈ observed cutoff) : paretoEquiv t ∈ densityObserved cutoff := by
  change paretoEquiv.symm (paretoEquiv t) ∈ observed cutoff
  rwa [paretoEquiv.symm_apply_apply]

/-- The weighted residual has zero moment against every revealed Q observable. -/
theorem densityResidual_moment {cutoff : ℕ} {t : QHilbert} (ht : t ∈ observed cutoff)
    (x : QHilbert) : inner ℝ t (B (x - densityProjection cutoff x)) = 0 := by
  change densityInner t (x - densityProjection cutoff x) = 0
  rw [densityInner_eq_pareto, map_sub, densityProjection_apply]
  exact (densityObserved cutoff).sub_starProjection_mem_orthogonal (paretoEquiv x) _
    (physical_mem_densityObserved ht)

/-- The native Q conditional projections of B times the weighted fit and B times the
original vector agree. This is the normal equation for conditional change of law. -/
theorem conditional_weighted_moment (cutoff : ℕ) (x : QHilbert) :
    (observed cutoff).starProjection (B (densityProjection cutoff x)) =
      (observed cutoff).starProjection (B x) := by
  have ho : B (x-densityProjection cutoff x) ∈ (observed cutoff)ᗮ :=
    fun _ ht => densityResidual_moment ht x
  have h := (observed cutoff).starProjection_apply_eq_zero_iff.mpr ho
  rw [map_sub, map_sub, sub_eq_zero] at h
  exact h.symm

/-- The omitted conditional covariance in the full-density pairing. -/
def densityCovariance (cutoff : ℕ) (x y : QHilbert) : ℝ :=
  densityInner (x - densityProjection cutoff x) (y - densityProjection cutoff y)

theorem density_gram_split (cutoff : ℕ) (x y : QHilbert) :
    densityInner x y = densityInner (densityProjection cutoff x) (densityProjection cutoff y) +
      densityCovariance cutoff x y := by
  simp only [densityCovariance, densityInner_eq_pareto, map_sub, densityProjection_apply]
  exact projection_gram (densityObserved cutoff) _ _

/-- Full dP/dQ-weighted Q cofactor mass at the valuation cutoff {2,3},
before normalizing inside the fibre with smooth part s. The cofactor class
is r modulo L, with r coprime to six in the period-60 application. -/
def densityCofactorMass (L s r : ℕ) : ℝ :=
  ∑' k : ℕ, let t := r + L*k
    (3/2 : ℝ) * positiveQWeight t *
      (zetaTwo * (s : ℝ) * (t : ℝ) / ((s : ℝ) * (t : ℝ) + 1))

theorem density_cofactor_progression (L s r : ℕ) (hs : 0 < s) (hr : 0 < r) :
    densityCofactorMass L s r = (3/2 : ℝ) * (s : ℝ)^2 * progressionWeight (s*L) (s*r) := by
  have hpoint (t : ℕ) (ht : 0 < t) :
      (3/2 : ℝ) * positiveQWeight t *
          (zetaTwo * (s : ℝ) * (t : ℝ) / ((s : ℝ) * (t : ℝ) + 1)) =
        (3/2 : ℝ) * (s : ℝ)^2 * positiveWeight (s*t) := by
    have hs' : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
    have ht' : (t : ℝ) ≠ 0 := by exact_mod_cast ht.ne'
    simp only [positiveQWeight, positiveWeight, Nat.cast_mul]
    field_simp [zetaTwo_pos.ne', hs', ht']
  rw [densityCofactorMass, progressionWeight, ← tsum_mul_left]
  apply tsum_congr
  intro k
  rw [show s*r+s*L*k = s*(r+L*k) by ring]
  exact hpoint _ (by omega)

/-- Exact shifted digamma difference for all twenty cofactor classes at period 60. -/
theorem density_cofactor_period60_digamma (s r : ℕ) (hs : 0 < s) (hr : 0 < r) (hrL : r ≤ 60) :
    densityCofactorMass 60 s r = (s : ℝ)/40 *
      ((Complex.digamma ((((r : ℝ) + (s : ℝ)⁻¹)/60 : ℝ) : ℂ)).re -
       (Complex.digamma (((r : ℝ)/60 : ℝ) : ℂ)).re) := by
  rw [density_cofactor_progression 60 s r hs hr,
    progressionWeight_eq_digamma (s*60) (s*r) (Nat.mul_pos hs (by decide))
      (Nat.mul_pos hs hr) (Nat.mul_le_mul_left s hrL)]
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  have hs' : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  have h₁ : ((s : ℝ)*(r : ℝ)+1)/((s : ℝ)*60) = ((r : ℝ)+(s : ℝ)⁻¹)/60 := by
    field_simp [hs']
  have h₀ : ((s : ℝ)*(r : ℝ))/((s : ℝ)*60) = (r : ℝ)/60 := by
    field_simp [hs']
  rw [h₁, h₀, ← mul_assoc]
  congr 1
  field_simp [hs']
  ring

/-- The observable Gram and the signed covariance recover the exact progression sum. -/
theorem density_packet_period_gram (cutoff L d e : ℕ) (hL : 0 < L) (hd : d ∣ L) (he : e ∣ L) :
    let x := paretoEquiv.symm (ramanujanPacketHilbert d)
    let y := paretoEquiv.symm (ramanujanPacketHilbert e)
    densityInner (densityProjection cutoff x) (densityProjection cutoff y) +
      densityCovariance cutoff x y =
      ∑ r : Fin L, progressionWeight L (r.val + 1) *
        (ramanujanPacket d (r.val + 1) * ramanujanPacket e (r.val + 1)) := by
  dsimp only
  rw [← density_gram_split, densityInner_eq_pareto, paretoEquiv.apply_symm_apply,
    paretoEquiv.apply_symm_apply]
  exact ramanujanPacketHilbert_inner_eq_crt d e L hL hd he

/-- Exactly the integers with smooth part s: divide by s and the cofactor
has no prime divisor through the cutoff. -/
theorem sameFibre_iff_rough_multiple (b : ℕ) (s n : ℕ+)
    (hs : ∀ p ∈ (s : ℕ).primeFactors, p ≤ b) :
    sameFibre b s n ↔ ∃ z : ℕ+, (n : ℕ) = (s : ℕ)*(z : ℕ) ∧
      ∀ p : ℕ, p.Prime → p ≤ b → ¬ p ∣ (z : ℕ) := by
  constructor
  · intro h
    have hd : (s : ℕ) ∣ (n : ℕ) := by
      apply (Nat.factorization_le_iff_dvd s.pos.ne' n.pos.ne').1
      intro p
      by_cases hp : p ∈ (s : ℕ).primeFactors
      · exact (h p (Nat.prime_of_mem_primeFactors hp) (hs p hp)).le
      · have hz : (s : ℕ).factorization p = 0 := by
          by_contra hne
          exact hp (Finsupp.mem_support_iff.mpr hne)
        simp [hz]
    obtain ⟨k, hk⟩ := hd
    have hk0 : k ≠ 0 := by
      intro h0
      apply n.pos.ne'
      simpa only [h0, mul_zero] using hk
    refine ⟨⟨k, Nat.pos_of_ne_zero hk0⟩, hk, ?_⟩
    intro p hp hb hpk
    have he := h p hp hb
    change (s : ℕ).factorization p = (n : ℕ).factorization p at he
    rw [hk, Nat.factorization_mul s.pos.ne' hk0, Finsupp.add_apply] at he
    have hpos := (hp.dvd_iff_one_le_factorization hk0).1 hpk
    omega
  · rintro ⟨z, hz, hr⟩ p hp hb
    change (s : ℕ).factorization p = (n : ℕ).factorization p
    rw [hz, Nat.factorization_mul s.pos.ne' z.pos.ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (hr p hp hb), add_zero]

/-- The indicator of the exact valuation fibre, zero at the Hilbert-space
dummy coordinate zero. -/
def fibreMark (b : ℕ) (s : ℕ+) (k : ℕ) : ℝ := by
  classical
  exact if h : 0 < k then if sameFibre b s ⟨k, h⟩ then 1 else 0 else 0

/-- The actual ambient Hilbert projection is the normalized physical Q mass
sum on each fibre. Every positive site lies on a fibre of positive mass. -/
theorem observed_fibre_mean (b : ℕ) (s : ℕ+) (x : QHilbert) :
    qSequence ((observed b).starProjection x) s =
      (∑' k, positiveQWeight k * fibreMark b s k * qSequence x k) /
      (∑' k, positiveQWeight k * fibreMark b s k) := by
  classical
  let f := fibreMark b s
  have hf (i : ℕ+) : f i = if sameFibre b s i then 1 else 0 := by
    rcases i with ⟨k, hk⟩
    by_cases h : sameFibre b s ⟨k, hk⟩ <;> simp [f, fibreMark, hk, h]
  have hf0 : f 0 = 0 := by simp [f, fibreMark]
  have hsumm := boundedQ_square_summable f 1 zero_le_one (fun k => by
    simp only [f, fibreMark]
    split_ifs <;> norm_num)
  let e := encodeQ f hsumm
  have he : qSequence e = f := qSequence_encodeQ _ _ hf0
  have hObs : e ∈ observed b := by
    apply (mem_observed _ _).2
    intro i j hij
    have hiff : sameFibre b s i ↔ sameFibre b s j := by
      constructor
      · intro h p hp hb
        exact (h p hp hb).trans (hij p hp hb)
      · intro h p hp hb
        exact (h p hp hb).trans (hij p hp hb).symm
    rw [he, hf i, hf j, if_congr hiff rfl rfl]
  let y := (observed b).starProjection x
  have hy := (mem_observed b y).1 ((observed b).starProjection_apply_mem x)
  have hv (k : ℕ) : positiveQWeight k * f k * qSequence y k =
      positiveQWeight k * f k * qSequence y s := by
    rcases k with _ | k
    · rw [hf0, mul_zero, zero_mul, zero_mul]
    · let i : ℕ+ := ⟨k+1, Nat.succ_pos _⟩
      change positiveQWeight i * f i * qSequence y i =
        positiveQWeight i * f i * qSequence y s
      rw [hf i]
      split_ifs with h
      · rw [hy s i h]
      · simp
  have hinner : inner ℝ e x = inner ℝ e y := by
    have ho : inner ℝ e (x-y) = 0 :=
      (observed b).sub_starProjection_mem_orthogonal x e hObs
    rwa [inner_sub_right, sub_eq_zero] at ho
  have hsum : Summable (fun k => positiveQWeight k * f k) := by
    apply Summable.of_nonneg_of_le _ _ positiveQWeight_summable
    · intro k
      simp only [f, fibreMark]
      split_ifs <;> simp [positiveQWeight_nonneg]
    · intro k
      simp only [f, fibreMark]
      split_ifs <;> simp [positiveQWeight_nonneg]
  have hpos : 0 < ∑' k, positiveQWeight k * f k := by
    refine hsum.tsum_pos ?_ (s : ℕ) ?_
    · intro k
      simp only [f, fibreMark]
      split_ifs <;> simp [positiveQWeight_nonneg]
    · have hself : sameFibre b s s := fun _ _ _ => rfl
      rw [hf s, if_pos hself, mul_one]
      unfold positiveQWeight
      have hz := zetaTwo_pos
      have hs : 0 < (s : ℝ) := by exact_mod_cast s.pos
      positivity
  rw [qInner_weighted, qInner_weighted, he] at hinner
  simp only [hv, tsum_mul_right] at hinner
  apply (eq_div_iff hpos.ne').2
  rw [mul_comm]
  exact hinner.symm

theorem observed_mono : Monotone observed := by
  intro a b hab x hx
  apply (mem_observed b x).2
  intro i j hij
  exact (mem_observed a x).1 hx i j (fun p hp ha => hij p hp (ha.trans hab))

private theorem nested_residual_gram {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {U V : Submodule ℝ E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hUV : U ≤ V) (x y : E) :
    inner ℝ (x-U.starProjection x) (y-U.starProjection y) -
      inner ℝ (x-V.starProjection x) (y-V.starProjection y) =
      inner ℝ (V.starProjection x-U.starProjection x) (V.starProjection y-U.starProjection y) := by
  have h := projection_gram U (V.starProjection x) (V.starProjection y)
  simp only [RiemannResearch.Analysis.NestedOrthogonalDecomposition.nested_projection_apply
    hUV] at h
  linarith only [h, projection_gram U x y, projection_gram V x y]

/-- The difference of two signed omitted covariances is the Gram entry of the
actual ambient valuation layer. This applies to two different packet inputs. -/
theorem covariance_layer {a b : ℕ} (hab : a ≤ b) (x y : QHilbert) :
    covariance a x y - covariance b x y =
      inner ℝ ((observed b).starProjection x - (observed a).starProjection x)
        ((observed b).starProjection y - (observed a).starProjection y) :=
  nested_residual_gram (observed_mono hab) x y

/-- The same polarized layer after refitting in the Pareto metric. -/
theorem density_covariance_layer {a b : ℕ} (hab : a ≤ b) (x y : QHilbert) :
    densityCovariance a x y - densityCovariance b x y =
      densityInner (densityProjection b x - densityProjection a x)
        (densityProjection b y - densityProjection a y) := by
  simp only [densityCovariance, densityInner_eq_pareto, map_sub, densityProjection_apply]
  have h : densityObserved a ≤ densityObserved b := Submodule.comap_mono (observed_mono hab)
  exact nested_residual_gram h _ _

/-- Joint Pareto mass of smooth part s and one rough residue r mod m, when m
contains every revealed prime and r is a unit there. The identity for the
progression itself holds for every positive r up to m. -/
theorem smooth_cofactor_progression_digamma (s m r : ℕ) (hs : 0 < s) (hm : 0 < m)
    (hr : 0 < r) (hrm : r ≤ m) :
    progressionWeight (s*m) (s*r) = 1 / ((s : ℝ)*(m : ℝ)) *
      ((Complex.digamma ((((r : ℝ)+(s : ℝ)⁻¹)/(m : ℝ) : ℝ) : ℂ)).re -
        (Complex.digamma (((r : ℝ)/(m : ℝ) : ℝ) : ℂ)).re) := by
  rw [progressionWeight_eq_digamma (s*m) (s*r) (Nat.mul_pos hs hm)
    (Nat.mul_pos hs hr) (Nat.mul_le_mul_left s hrm)]
  simp only [Nat.cast_mul]
  have hs' : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have h₁ : ((s : ℝ)*(r : ℝ)+1)/((s : ℝ)*(m : ℝ)) =
      ((r : ℝ)+(s : ℝ)⁻¹)/(m : ℝ) := by field_simp
  have h₀ : ((s : ℝ)*(r : ℝ))/((s : ℝ)*(m : ℝ)) = (r : ℝ)/(m : ℝ) := by field_simp
  rw [h₁, h₀]

theorem finite_density_covariance_energy {ι : Type*} (s : Finset ι)
    (cutoff : ℕ) (c : ι → ℝ) (x : ι → QHilbert) :
    let m := ∑ i ∈ s, c i • x i
    densityCovariance cutoff m m =
      ∑ i ∈ s, ∑ j ∈ s, c i * c j * densityCovariance cutoff (x i) (x j) := by
  let R : QHilbert →L[ℝ] QHilbert := ContinuousLinearMap.id ℝ QHilbert - densityProjection cutoff
  change inner ℝ (R (∑ i ∈ s, c i • x i)) (B (R (∑ i ∈ s, c i • x i))) = _
  simp only [map_sum, map_smul, sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [real_inner_smul_left, real_inner_smul_right, mul_assoc]
  rfl

/-- A revealed profile is fixed even after the density changes the fit. -/
theorem densityProjection_of_mem {cutoff : ℕ} {x : QHilbert} (hx : x ∈ observed cutoff) :
    densityProjection cutoff x = x := by
  apply paretoEquiv.injective
  rw [densityProjection_apply]
  exact (densityObserved cutoff).starProjection_eq_self_iff.mpr (physical_mem_densityObserved hx)

/-- With the full integration weight, raw parity still has exactly zero omitted component. -/
theorem density_parity_error_split {cutoff : ℕ} (h : 2 ≤ cutoff) (m : QHilbert) :
    densityInner (qParity-m) (qParity-m) =
      densityInner (qParity-densityProjection cutoff m) (qParity-densityProjection cutoff m) +
      densityCovariance cutoff m m := by
  have hp := densityProjection_of_mem (physical_parity_observed h)
  rw [density_gram_split cutoff (qParity-m) (qParity-m), map_sub, hp]
  congr 1
  unfold densityCovariance
  rw [map_sub, hp, show qParity - m - (qParity - densityProjection cutoff m) =
    -(m-densityProjection cutoff m) by abel]
  simp only [densityInner, map_neg, inner_neg_left, inner_neg_right, neg_neg]

/--
info: 'RiemannResearch.CategoryTheory.PrimeValuationCovariance.density_parity_error_split' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms density_parity_error_split

/--
info: 'RiemannResearch.CategoryTheory.PrimeValuationCovariance.density_cofactor_period60_digamma' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms density_cofactor_period60_digamma

end RiemannResearch.CategoryTheory.PrimeValuationCovariance
