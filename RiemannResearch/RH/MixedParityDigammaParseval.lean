import RiemannResearch.RH.CenteredMeanDigammaSection
import RiemannResearch.RH.MixedConductorHilbertBasis
import RiemannResearch.RH.ParetoRamanujanGramCRT
import RiemannResearch.RH.PhysicalHeadLayerIsometry
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

/-!
# Digamma recursion for the full mixed projection of parity

Gram–Schmidt in increasing mixed conductor order gives a triangular recursion.
Its scalar inputs are the rational-node digamma entries of the periodic packet
Gram. The sum of the squared computed parity coefficients is the physical
head Parseval sum. The signed input entries use the Pareto progression
series https://dlmf.nist.gov/5.7.E6 and recurrence https://dlmf.nist.gov/5.5.E2.
-/

noncomputable section
open InnerProductSpace
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis.DigammaParseval

open CenteredMeanSnake.DigammaSection

/-- Exact Pareto mass of a positive residue class, in rational digamma nodes. -/
def digammaWeight (L r : ℕ) : ℝ :=
  1 / (L : ℝ) * ((Complex.digamma ((((r : ℝ) + 1) / L : ℝ) : ℂ)).re -
    (Complex.digamma (((r : ℝ) / L : ℝ) : ℂ)).re)

private theorem digammaWeight_eq (L r : ℕ) (hL : 0 < L) (hr : 0 < r) (hrL : r ≤ L) :
    digammaWeight L r = progressionWeight L r :=
  (progressionWeight_eq_digamma L r hL hr hrL).symm

/-- Refinement of the rational digamma weights when the common period is multiplied by m. -/
theorem digammaWeight_refinement (L m r : ℕ) (hL : 0 < L) (hm : 0 < m)
    (hr : 0 < r) (hrL : r ≤ L) :
    digammaWeight L r = ∑ j : Fin m, digammaWeight (L * m) (r + L * j.val) := by
  rw [digammaWeight_eq L r hL hr hrL, progressionWeight_compatibility L m r hL hm]
  apply Finset.sum_congr rfl
  intro j _
  refine (digammaWeight_eq _ _ (Nat.mul_pos hL hm) (by omega) ?_).symm
  calc
    r + L * j.val ≤ L * j.val + L := by omega
    _ = L * (j.val + 1) := (Nat.mul_succ L j.val).symm
    _ ≤ L * m := Nat.mul_le_mul_left L j.isLt

theorem packetGramEntry_eq_weighted (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    packetGramEntry a b =
      ∑ r : Fin (a.lcm b), digammaWeight (a.lcm b) (r.val + 1) *
        (ramanujanPacket a (r.val + 1) * ramanujanPacket b (r.val + 1)) := by
  calc
    packetGramEntry a b = inner ℝ (ramanujanPacketHilbert a) (ramanujanPacketHilbert b) := by
      rw [packetGramEntry_eq _ _ ha hb, hilbert_inner_weighted,
        hilbertSequence_ramanujanPacketHilbert, hilbertSequence_ramanujanPacketHilbert]
    _ = _ := ramanujanPacketHilbert_inner_eq_lcm_digamma a b ha hb

/-- Signed mixed Fourier coefficient at a test packet of conductor a. -/
def modePair (q : Index) (a : ℕ) : ℝ :=
  inner ℝ (basis q : ThresholdHilbert) (ramanujanPacketHilbert a)

private abbrev orthogonalPacket (q : Index) := gramSchmidt ℝ packet q

private def scale (q : Index) : ℝ := ‖orthogonalPacket q‖

private theorem scale_pos (q : Index) : 0 < scale q :=
  norm_pos_iff.mpr (gramSchmidt_ne_zero q packet_independent)

private theorem basis_eq_scaled (q : Index) : basis q = (scale q)⁻¹ • orthogonalPacket q := by
  rw [basis_apply]
  rfl

private theorem scale_smul_basis (q : Index) : scale q • basis q = orthogonalPacket q := by
  rw [basis_eq_scaled, smul_smul, mul_inv_cancel₀ (scale_pos q).ne', one_smul]

private theorem packet_expansion (q : Index) :
    packet q = scale q • basis q + ∑ r ∈ Finset.Iio q, modePair r q.val • basis r := by
  rw [scale_smul_basis]
  refine (gramSchmidt_def'' ℝ packet q).trans (congrArg (_ + ·) (Finset.sum_congr rfl ?_))
  intro r _
  change (inner ℝ (orthogonalPacket r) (packet q) / scale r ^ 2) • orthogonalPacket r =
    inner ℝ (basis r) (packet q) • basis r
  rw [basis_eq_scaled, real_inner_smul_left, smul_smul]
  congr 1
  field_simp [(scale_pos r).ne']

private theorem diagonal_pair (q : Index) : modePair q q.val = scale q := by
  change inner ℝ (basis q) (packet q) = scale q
  rw [packet_expansion, inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
    basis.orthonormal.1 q, one_pow, mul_one, inner_sum]
  have hz : (∑ r ∈ Finset.Iio q, inner ℝ (basis q) (modePair r q.val • basis r)) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    rw [real_inner_smul_right, basis.orthonormal.2 (Finset.mem_Iio.mp hr).ne', mul_zero]
  rw [hz, add_zero]

private theorem cross_expansion (q : Index) (a : ℕ) (ha : 0 < a) :
    packetGramEntry q.val a = scale q * modePair q a +
      ∑ r ∈ Finset.Iio q, modePair r q.val * modePair r a := by
  calc
    packetGramEntry q.val a =
        inner ℝ (mixedClosure.subtype (packet q)) (ramanujanPacketHilbert a) := by
      change packetGramEntry q.val a =
        inner ℝ (ramanujanPacketHilbert q.val) (ramanujanPacketHilbert a)
      rw [packetGramEntry_eq _ _ (by have := q.property.1; omega) ha, hilbert_inner_weighted,
        hilbertSequence_ramanujanPacketHilbert, hilbertSequence_ramanujanPacketHilbert]
    _ = _ := by
      rw [packet_expansion q, map_add, map_smul, map_sum, inner_add_left, real_inner_smul_left,
        sum_inner]
      simp only [map_smul, real_inner_smul_left, modePair, Submodule.subtype_apply]

private theorem scale_sq (q : Index) :
    scale q ^ 2 = packetGramEntry q.val q.val - ∑ r ∈ Finset.Iio q, (modePair r q.val) ^ 2 := by
  have h := cross_expansion q q.val (by have := q.property.1; omega)
  rw [diagonal_pair] at h
  simp only [sq]
  linarith only [h]

/-- The new diagonal pivot is strictly positive for every mixed conductor. -/
theorem pivot_pos (q : Index) :
    0 < packetGramEntry q.val q.val - ∑ r ∈ Finset.Iio q, (modePair r q.val) ^ 2 := by
  rw [← scale_sq]
  exact sq_pos_of_pos (scale_pos q)

/-- The signed Cholesky recurrence for the Pareto Gram of the mixed packets. -/
theorem modePair_recurrence (q : Index) (a : ℕ) (ha : 0 < a) :
    modePair q a =
      (packetGramEntry q.val a - ∑ r ∈ Finset.Iio q, modePair r q.val * modePair r a) /
        Real.sqrt (packetGramEntry q.val q.val - ∑ r ∈ Finset.Iio q, (modePair r q.val) ^ 2) := by
  rw [← scale_sq, Real.sqrt_sq (scale_pos q).le]
  apply (eq_div_iff (scale_pos q).ne').mpr
  rw [mul_comm]
  linarith only [cross_expansion q a ha]

/-- A scalar recipe in earlier conductors, initialized solely by digamma Gram entries. -/
def digammaRow (q : Index) : ℕ → ℝ :=
  let prev (r : Finset.Iio q) : ℕ → ℝ := digammaRow r.val
  fun a => (packetGramEntry q.val a - ∑ r : Finset.Iio q, prev r q.val * prev r a) /
    Real.sqrt (packetGramEntry q.val q.val - ∑ r : Finset.Iio q, (prev r q.val) ^ 2)
termination_by q.val
decreasing_by exact (show r.val < q from Finset.mem_Iio.mp r.property)

theorem digammaRow_eq_modePair (q : Index) : ∀ a : ℕ, 0 < a → digammaRow q a = modePair q a := by
  induction q using (measure (fun q : Index => q.val)).wf.induction with
  | h q ih =>
    intro a ha
    have hq : 0 < q.val := by have := q.property.1; omega
    have hp (r : Finset.Iio q) (k : ℕ) (hk : 0 < k) : digammaRow r.val k = modePair r.val k :=
      ih r.val (show r.val < q from Finset.mem_Iio.mp r.property) k hk
    rw [digammaRow, modePair_recurrence q a ha]
    simp only [hp _ _ hq, hp _ _ ha]
    rw [Finset.sum_coe_sort (Finset.Iio q) (fun r => modePair r q.val * modePair r a),
      Finset.sum_coe_sort (Finset.Iio q) (fun r => (modePair r q.val) ^ 2)]

/-- The same triangular data compute every site value of the basis by taking F to be evaluation. -/
theorem basis_functional_recurrence (q : Index) (F : mixedClosure →ₗ[ℝ] ℝ) :
    F (basis q) =
      (F (packet q) - ∑ r ∈ Finset.Iio q, digammaRow r q.val * F (basis r)) /
        Real.sqrt (packetGramEntry q.val q.val - ∑ r ∈ Finset.Iio q, (digammaRow r q.val) ^ 2) := by
  have hq : 0 < q.val := by have := q.property.1; omega
  simp_rw [digammaRow_eq_modePair _ _ hq]
  rw [← scale_sq, Real.sqrt_sq (scale_pos q).le]
  apply (eq_div_iff (scale_pos q).ne').mpr
  have he := congrArg F (packet_expansion q)
  simp only [map_add, map_smul, map_sum, smul_eq_mul] at he
  rw [mul_comm]
  linarith only [he]

private theorem mixed_parity_coefficient (q : Index) :
    basis.repr (mixedClosure.orthogonalProjectionOnto (ramanujanPacketHilbert 2)) q =
      digammaRow q 2 := by
  rw [digammaRow_eq_modePair q 2 (by decide), HilbertBasis.repr_apply_apply]
  have h := mixedClosure.sub_starProjection_mem_orthogonal (ramanujanPacketHilbert 2)
    (basis q : ThresholdHilbert) (basis q).property
  rw [inner_sub_right, sub_eq_zero] at h
  exact h.symm

/-- A convergent series of nonnegative terms for the unnormalized mixed projection energy of J₂. -/
theorem hasSum_parity_energy :
    HasSum (fun q : Index => (digammaRow q 2) ^ 2)
      (‖mixedClosure.starProjection (ramanujanPacketHilbert 2)‖ ^ 2) := by
  let m := mixedClosure.orthogonalProjectionOnto (ramanujanPacketHilbert 2)
  change HasSum (fun q : Index => (digammaRow q 2) ^ 2) (‖m‖ ^ 2)
  have he (q : Index) : basis.repr m q = digammaRow q 2 := mixed_parity_coefficient q
  have hs := lp.hasSum_norm (by norm_num : 0 < (2 : ENNReal).toReal) (basis.repr m)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs, he,
    LinearIsometryEquiv.norm_map] using hs

/-- The norm itself is the square root of the scalar digamma Parseval series. -/
theorem parity_projection_norm :
    ‖mixedClosure.starProjection (ramanujanPacketHilbert 2)‖ =
      Real.sqrt (∑' q : Index, (digammaRow q 2) ^ 2) := by
  rw [hasSum_parity_energy.tsum_eq, Real.sqrt_sq (norm_nonneg _)]

/-- Each physical coefficient is the orthogonal change of basis of the signed digamma row. -/
theorem physical_head_coefficient (n : ℕ) :
    AffineHeadTower.headLayerIsometry
      (mixedClosure.orthogonalProjectionOnto (ramanujanPacketHilbert 2)) n =
        ∑' q : Index, inner ℝ (AffineHeadTower.unitHeadDirection n) (basis q) * digammaRow q 2 := by
  let m := mixedClosure.orthogonalProjectionOnto (ramanujanPacketHilbert 2)
  have hp (q : Index) : inner ℝ (basis q) m = digammaRow q 2 := by
    simpa only [HilbertBasis.repr_apply_apply] using mixed_parity_coefficient q
  rw [AffineHeadTower.headLayerIsometry, HilbertBasis.repr_apply_apply,
    AffineHeadTower.physicalHeadBasis_apply]
  simpa only [hp] using (basis.tsum_inner_mul_inner (AffineHeadTower.unitHeadDirection n) m).symm

theorem first_digamma_term :
    (digammaRow six 2) ^ 2 = (Real.log 2 - Real.pi / (2 * Real.sqrt 3)) ^ 2 /
      (Real.pi / Real.sqrt 3) := by
  rw [digammaRow_eq_modePair six 2 (by decide)]
  exact parity_six_coefficient_sq

/-- The next mixed conductor after six. -/
def ten : Index := ⟨10, by decide, by decide⟩

private theorem mixed_lt_ten {q : Index} (h : q.val < 10) : q = six := by
  have onlySix (k : ℕ) (hk : 1 < k) (hk' : k < 10) (hm : ¬ IsPrimePow k) : k = 6 := by
    interval_cases k
    · exact (hm Nat.prime_two.isPrimePow).elim
    · exact (hm Nat.prime_three.isPrimePow).elim
    · exact (hm (by decide)).elim
    · exact (hm (show Nat.Prime 5 by norm_num).isPrimePow).elim
    · rfl
    · exact (hm (show Nat.Prime 7 by norm_num).isPrimePow).elim
    · exact (hm (by decide)).elim
    · exact (hm (show IsPrimePow (3 ^ 2 : ℕ) from Nat.prime_three.isPrimePow.pow (by decide))).elim
  exact Subtype.ext (onlySix q.val q.property.1 h q.property.2)

private theorem before_six : Finset.Iio six = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro q h
  have hq : q.val < 6 := (Finset.mem_Iio.mp h : q < six)
  have he := mixed_lt_ten (q := q) (by omega)
  exact (Finset.mem_Iio.mp h).ne he

private theorem before_ten : Finset.Iio ten = {six} := by
  ext q
  rw [Finset.mem_Iio, Finset.mem_singleton]
  constructor
  · exact fun h => mixed_lt_ten h
  · rintro rfl
    decide

/-- The first two summands use periods six, ten and thirty. -/
theorem second_digamma_term :
    (digammaRow ten 2) ^ 2 =
      (packetGramEntry 10 2 -
        packetGramEntry 6 10 * packetGramEntry 6 2 / packetGramEntry 6 6) ^ 2 /
        (packetGramEntry 10 10 - (packetGramEntry 6 10) ^ 2 / packetGramEntry 6 6) := by
  have hsix : six.val = 6 := rfl
  have hten : ten.val = 10 := rfl
  have h6 (a : ℕ) (ha : 0 < a) :
      modePair six a = packetGramEntry 6 a / Real.sqrt (packetGramEntry 6 6) := by
    simpa only [before_six, Finset.sum_empty, sub_zero, hsix] using modePair_recurrence six a ha
  have hpos : 0 < packetGramEntry 6 6 := by
    simpa only [before_six, Finset.sum_empty, sub_zero, hsix] using pivot_pos six
  have hp : 0 < packetGramEntry 10 10 - (modePair six 10) ^ 2 := by
    simpa only [before_ten, Finset.sum_singleton, hten] using pivot_pos ten
  rw [digammaRow_eq_modePair ten 2 (by decide), modePair_recurrence ten 2 (by decide),
    before_ten, Finset.sum_singleton, Finset.sum_singleton]
  change ((_ - modePair six 10 * modePair six 2) /
    Real.sqrt (packetGramEntry 10 10 - (modePair six 10) ^ 2)) ^ 2 = _
  rw [div_pow, Real.sq_sqrt hp.le, h6 10 (by decide), h6 2 (by decide), div_mul_div_comm,
    ← sq, Real.sq_sqrt hpos.le, div_pow, Real.sq_sqrt hpos.le, hten]

/-- Change of orthonormal coordinates from the physical-head tower to the digamma series. -/
theorem physical_head_energy_eq_digamma_series :
    (∑' n : ℕ, (AffineHeadTower.headLayerIsometry
      (mixedClosure.orthogonalProjectionOnto (ramanujanPacketHilbert 2)) n) ^ 2) =
        ∑' q : Index, (digammaRow q 2) ^ 2 := by
  rw [AffineHeadTower.headLayer_parseval, hasSum_parity_energy.tsum_eq]
  rfl

/-- The exact open endpoint, expressed wholly in the scalar digamma coefficients. -/
theorem parity_endpoint_iff_one_mem :
    (∑' q : Index, (digammaRow q 2) ^ 2) = Real.log 2 - (Real.log 2) ^ 2 ↔
      hilbertOne ∈ CoefficientStabilization.closedSpace := by
  rw [hasSum_parity_energy.tsum_eq]
  exact full_capture_saturation_iff

end RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis.DigammaParseval
