import RiemannResearch.RH.AdjacentDigitCovariance
import RiemannResearch.RH.BaezDuarteNaturalApproximation
import RiemannResearch.RH.CenteredMeanQuotients
import RiemannResearch.RH.CenteredMeanSquarefreeConverse
import RiemannResearch.RH.DilationDensityLeakage
import RiemannResearch.RH.IntegratedRamanujanBasis
import RiemannResearch.RH.IntegratedRamanujanHilbert
import RiemannResearch.RH.MixedConductorDilation
import RiemannResearch.RH.MixedConductorRankOne
import RiemannResearch.RH.MixedReciprocalDensity
import RiemannResearch.RH.MobiusCoefficientStabilization
import RiemannResearch.RH.MobiusResidualFirstCoordinate
import RiemannResearch.RH.ParetoDensityDilation
import RiemannResearch.RH.ParetoPrimePackets
import RiemannResearch.RH.ParetoResidueDuality
import RiemannResearch.RH.PrimePowerRamanujanClosure
import RiemannResearch.RH.QDensityMetric
import RiemannResearch.RH.QDensityMetricInverse
import RiemannResearch.RH.QParetoEquivalence
import RiemannResearch.RH.ResidueClosureDensity
import RiemannResearch.RH.ThresholdHilbertMean
import RiemannResearch.RH.ThresholdHilbertSpace
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.ClosedSubmodule

/-!
# Pareto density tests from mixed packets and consecutive primes

Source: the user's question combining the orthogonal mixed/prime splitting with
density after adjoining the images of the residue space under the density multiplier.
The mixed reciprocal-density theorem separates vectors in the ambient mixed
complement. For two distinct primes the residue identity gives a quantitative
approximation to the constant, and orthogonal projection computes the remaining
legal residual and its signed scalar limit.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto.PrimePowerSchur.MixedPacketDensity
open CoefficientStabilization CenteredMeanSnake
open RiemannResearch.RH.ParetoDensityDilation RiemannResearch.RH.QDensityMetricInverse
open RiemannResearch.RH.ZetaTwoProbability

/-- A literal union of the legal subspace and its density image fills the
ambient Pareto space precisely under RH. -/
theorem riemannHypothesis_iff_union_eq_univ :
    RiemannHypothesis ↔ (closedSpace : Set ThresholdHilbert) ∪
      (closedSpace.map densityP.toLinearMap : Set ThresholdHilbert) = Set.univ := by
  have htop : RiemannHypothesis ↔ closedSpace = ⊤ :=
    (riemannHypothesis_iff_naturalApproximation.trans
      BaezDuarte.naturalApproximation_iff_one_mem).trans closedSpace_eq_top_iff_one_mem.symm
  rw [htop]
  constructor
  · intro h
    simp [h]
  · intro hu
    by_contra hV
    let T := closedSpace.map densityP.toLinearMap
    have hT : T ≠ ⊤ := by
      intro ht
      apply hV
      apply top_unique
      intro x _
      have hmem : densityP x ∈ T := by rw [ht]; trivial
      obtain ⟨y, hy, he⟩ := hmem
      change densityP y = densityP x at he
      have hQ : QDensityMetric.B (QParetoEquivalence.toQ y) =
          QDensityMetric.B (QParetoEquivalence.toQ x) := by
        apply QParetoEquivalence.paretoEquiv.injective
        simpa only [QParetoEquivalence.paretoEquiv_apply, ← densityP_toPareto,
          QParetoEquivalence.toPareto_toQ] using he
      have hyx : y = x := QParetoEquivalence.paretoEquiv.symm.injective
        (densityEquiv.injective hQ)
      exact hyx ▸ hy
    let family : Bool → Submodule ℝ ThresholdHilbert := fun b => if b then closedSpace else T
    have hproper (b : Bool) : family b ≠ ⊤ := by
      cases b
      · exact hT
      · exact hV
    obtain ⟨x, hx⟩ := Submodule.exists_forall_notMem_of_forall_ne_top family hproper
    have hcover : x ∈ (closedSpace : Set ThresholdHilbert) ∪
        (closedSpace.map densityP.toLinearMap : Set ThresholdHilbert) := by
      rw [hu]
      trivial
    exact hcover.elim (hx true) (hx false)

/-- Orthogonality to the original mixed packets reduces ambient separation to
one real pairing for each density-transformed mixed packet. -/
theorem eq_zero_iff_mixed_density_pairings {x : ThresholdHilbert} (hx : x ∈ mixedClosureᗮ) :
    x = 0 ↔ ∀ q : ℕ, 2 ≤ q → ¬ IsPrimePow q →
      inner ℝ x (densityP (ramanujanPacketHilbert q)) = 0 := by
  constructor
  · rintro rfl q _ _
    exact inner_zero_left _
  · intro h
    let F := (innerSL ℝ x).comp QParetoEquivalence.paretoEquiv.toContinuousLinearMap
    have hm : MixedReciprocalDensity.mixed ≤ F.ker := by
      intro v hv
      change inner ℝ x (QParetoEquivalence.paretoEquiv v) = 0
      exact (real_inner_comm _ _).trans (hx _ hv)
    have hb : MixedReciprocalDensity.mixed.map QDensityMetric.B.toLinearMap ≤ F.ker := by
      apply (MixedReciprocalDensity.mixed_image_le_iff QDensityMetric.B F.ker F.isClosed_ker).2
      intro q hq hmix
      change inner ℝ x (ZetaTwoParetoTransfer.toPareto
        (QDensityMetric.B (QParetoEquivalence.toQ (ramanujanPacketHilbert q)))) = 0
      rw [← densityP_toPareto, QParetoEquivalence.toPareto_toQ]
      exact h q hq hmix
    have htotal := Submodule.topologicalClosure_minimal _ (sup_le hm hb) F.isClosed_ker
    rw [MixedReciprocalDensity.mixed_augmented_dense] at htotal
    have hself := htotal (show QParetoEquivalence.paretoEquiv.symm x ∈ ⊤ from trivial)
    change inner ℝ x (QParetoEquivalence.paretoEquiv
      (QParetoEquivalence.paretoEquiv.symm x)) = 0 at hself
    rw [QParetoEquivalence.paretoEquiv.apply_symm_apply] at hself
    exact (inner_self_eq_zero (𝕜 := ℝ)).mp hself

/-- The projections of density-transformed mixed vectors are dense in the
orthogonal complement of every closed space containing the mixed subspace. -/
theorem projected_mixed_dense (S : Submodule ℝ ThresholdHilbert) [S.HasOrthogonalProjection]
    (hMS : mixedClosure ≤ S) :
    (mixedClosure.map (Sᗮ.starProjection.comp densityP).toLinearMap).topologicalClosure = Sᗮ := by
  let K := (mixedClosure.map (Sᗮ.starProjection.comp densityP).toLinearMap).topologicalClosure
  have hK : IsClosed (K : Set ThresholdHilbert) := Submodule.isClosed_topologicalClosure _
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal _ _ S.isClosed_orthogonal
    rintro _ ⟨m, _, rfl⟩
    exact Sᗮ.starProjection_apply_mem _
  · let F := Sᗮ.starProjection.comp QParetoEquivalence.paretoEquiv.toContinuousLinearMap
    let U := K.comap F.toLinearMap
    have hU : IsClosed (U : Set ZetaTwoHilbert.QHilbert) := hK.preimage F.continuous
    have hm : MixedReciprocalDensity.mixed ≤ U := by
      intro m hm
      have hmS : QParetoEquivalence.paretoEquiv m ∈ S := hMS hm
      change Sᗮ.starProjection (QParetoEquivalence.paretoEquiv m) ∈ K
      rw [Submodule.starProjection_orthogonal_val,
        Submodule.starProjection_eq_self_iff.mpr hmS, sub_self]
      exact K.zero_mem
    have hb : MixedReciprocalDensity.mixed.map QDensityMetric.B.toLinearMap ≤ U := by
      rintro _ ⟨m, hm, rfl⟩
      change Sᗮ.starProjection (ZetaTwoParetoTransfer.toPareto (QDensityMetric.B m)) ∈ K
      rw [← densityP_toPareto]
      exact Submodule.le_topologicalClosure _ ⟨ZetaTwoParetoTransfer.toPareto m, hm, rfl⟩
    have htotal := Submodule.topologicalClosure_minimal _ (sup_le hm hb) hU
    rw [MixedReciprocalDensity.mixed_augmented_dense] at htotal
    intro x hx
    have h := htotal (show QParetoEquivalence.paretoEquiv.symm x ∈ ⊤ from trivial)
    change Sᗮ.starProjection (QParetoEquivalence.paretoEquiv
      (QParetoEquivalence.paretoEquiv.symm x)) ∈ K at h
    simpa only [QParetoEquivalence.paretoEquiv.apply_symm_apply,
      Submodule.starProjection_eq_self_iff.mpr hx] using h

/-- Equality of the screened and ambient units is determined by their values
on the density transforms of the individual mixed packets. -/
theorem screened_eq_one_iff_mixed_density_pairings :
    normalizedScreenedTwo = hilbertOne ↔ ∀ q : ℕ, 2 ≤ q → ¬ IsPrimePow q →
      inner ℝ normalizedScreenedTwo (densityP (ramanujanPacketHilbert q)) =
        inner ℝ hilbertOne (densityP (ramanujanPacketHilbert q)) := by
  constructor
  · intro h q _ _
    rw [h]
  · intro h
    apply sub_eq_zero.mp
    apply (eq_zero_iff_mixed_density_pairings screenedTwo_sub_one_mem_orthogonals.2).2
    intro q hq hmix
    rw [inner_sub_left, h q hq hmix, sub_self]

/-- The physical value of a packet at the product of two distinct primes. -/
theorem semiprime_packet_sequence {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) (n : ℕ) :
    hilbertSequence (ramanujanPacketHilbert (p * q)) n =
      residue (p * q) n - residue p n - residue q n := by
  have hd : ¬ p ∣ q := fun h => ((Nat.dvd_prime hq).mp h).elim hp.ne_one hne
  rw [hilbertSequence_ramanujanPacketHilbert,
    ramanujanPacket_mul_prime_of_not_dvd p q n hp hq.one_lt hd,
    ramanujanPacket_prime_eq_residue q hq, residue_mul_floor]

/-- The complete Pareto error is supported on the tail starting at the smaller prime. -/
theorem semiprime_reciprocal_error_sq_le {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    ‖DP (ramanujanPacketHilbert (p * q)) + hilbertOne‖ ^ 2 ≤ 4 / ((min p q : ℕ) : ℝ) := by
  let e := DP (ramanujanPacketHilbert (p * q)) + hilbertOne
  have he (n : ℕ) (hn : 0 < n) : hilbertSequence e n =
      (((n % (p * q) : ℕ) : ℝ) - (n % p : ℕ) - (n % q : ℕ)) / (n : ℝ) + 1 := by
    simp only [e, hilbertSequence_add, Pi.add_apply, DP_physical,
      semiprime_packet_sequence hp hq hne, residue, hilbertOne_sequence, zeroAnchor,
      hn.ne', if_false]
  have hpoint (n : ℕ) : positiveWeight n * hilbertSequence e n ^ 2 ≤
      4 * (if min p q ≤ n then positiveWeight n else 0) := by
    by_cases hcut : min p q ≤ n
    · rw [if_pos hcut]
      have hn : 0 < n := (lt_min hp.pos hq.pos).trans_le hcut
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have hmod : n % p ≤ n % (p * q) := by rw [Nat.mod_mul]; omega
      have hlo : (0 : ℝ) ≤ hilbertSequence e n := by
        rw [he n hn]
        have h1 : ((n % p : ℕ) : ℝ) ≤ (n % (p * q) : ℕ) := by exact_mod_cast hmod
        have h2 : ((n % q : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.mod_le n q
        have hl : (-1 : ℝ) ≤ (((n % (p * q) : ℕ) : ℝ) - (n % p : ℕ) - (n % q : ℕ)) / (n : ℝ) :=
          (le_div_iff₀ hnR).2 (by linarith)
        linarith
      have hhi : hilbertSequence e n ≤ 2 := by
        rw [he n hn]
        have h1 : ((n % (p * q) : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.mod_le n (p * q)
        have h2 : (((n % (p * q) : ℕ) : ℝ) - (n % p : ℕ) - (n % q : ℕ)) / (n : ℝ) ≤ 1 :=
          (div_le_iff₀ hnR).2 (by
            linarith [Nat.cast_nonneg (α := ℝ) (n % p), Nat.cast_nonneg (α := ℝ) (n % q)])
        linarith
      have hs : hilbertSequence e n ^ 2 ≤ 4 := by nlinarith [mul_nonneg hlo (sub_nonneg.mpr hhi)]
      simpa only [mul_comm (positiveWeight n) 4] using
        mul_le_mul_of_nonneg_left hs (positiveWeight_nonneg n)
    · rw [if_neg hcut]
      have hz : hilbertSequence e n = 0 := by
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · exact hilbertSequence_zero e
        · have hh := lt_min_iff.mp (lt_of_not_ge hcut)
          have hprod := hh.1.trans_le (Nat.le_mul_of_pos_right p hq.pos)
          rw [he n hn, Nat.mod_eq_of_lt hprod, Nat.mod_eq_of_lt hh.1, Nat.mod_eq_of_lt hh.2]
          field_simp [ne_of_gt (show (0 : ℝ) < n by exact_mod_cast hn)]
          ring
      simp [hz]
  have h := Summable.tsum_le_tsum hpoint (hilbertSequence_square_summable e)
    ((AdjacentDigit.tailWeight_summable (min p q)).mul_left 4)
  rw [tsum_mul_left, AdjacentDigit.tailWeight_tsum _ (lt_min hp.pos hq.pos)] at h
  simpa only [e, ← hilbert_norm_weighted_sq, mul_one_div] using h

private theorem packet_mem_mixed {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    ramanujanPacketHilbert (p * q) ∈ mixedClosure :=
  mixedSpace_window_le_closure _ (mixed_packet_mul_of_coprime_mem_window hp.one_lt hq.one_lt
    ((Nat.coprime_primes hp hq).mpr hne) le_rfl)

private theorem smul_density (x : ThresholdHilbert) : zetaTwo • densityP x = x + DP x := by
  change zetaTwo • ((1 / zetaTwo) • (x + DP x)) = _
  simp only [smul_smul, one_div, mul_inv_cancel₀ zetaTwo_pos.ne', one_smul]

/-- Projecting a density image of a vector in the subspace removes its
identity component. The reciprocal component retains its sign and scale. -/
theorem projected_density_eq (S : Submodule ℝ ThresholdHilbert) [S.HasOrthogonalProjection]
    {x : ThresholdHilbert} (hx : x ∈ S) :
    (-zetaTwo) • Sᗮ.starProjection (densityP x) = -Sᗮ.starProjection (DP x) := by
  have hz : Sᗮ.starProjection x = 0 := by
    rw [Submodule.starProjection_orthogonal_val,
      Submodule.starProjection_eq_self_iff.mpr hx, sub_self]
  have hp := congrArg Sᗮ.starProjection (smul_density x)
  rw [map_smul, map_add, hz, zero_add] at hp
  rw [neg_smul, hp]

/-- The projected density approximation inherits the complete Pareto error bound. -/
theorem projected_error_sq_le (S : Submodule ℝ ThresholdHilbert) [S.HasOrthogonalProjection]
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (hJ : ramanujanPacketHilbert (p * q) ∈ S) :
    ‖(-zetaTwo) • Sᗮ.starProjection (densityP (ramanujanPacketHilbert (p * q))) -
      Sᗮ.starProjection hilbertOne‖ ^ 2 ≤ 4 / ((min p q : ℕ) : ℝ) := by
  set x := ramanujanPacketHilbert (p * q)
  have he : (-zetaTwo) • Sᗮ.starProjection (densityP x) - Sᗮ.starProjection hilbertOne =
      -Sᗮ.starProjection (DP x + hilbertOne) := by
    rw [projected_density_eq S hJ, map_add]
    abel
  rw [he, norm_neg]
  exact ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
    (Sᗮ.norm_starProjection_apply_le _)).trans (semiprime_reciprocal_error_sq_le hp hq hne)

/-- The exact signed residual pairing for one product of two distinct primes. -/
theorem residual_pairing_identity {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    ‖limitResidual‖ ^ 2 + zetaTwo * inner ℝ limitResidual
      (densityP (ramanujanPacketHilbert (p * q))) =
      inner ℝ limitResidual (DP (ramanujanPacketHilbert (p * q)) + hilbertOne) := by
  let x := ramanujanPacketHilbert (p * q)
  have hx : inner ℝ limitResidual x = 0 :=
    (real_inner_comm _ _).trans (limitResidual_mem_orthogonal x
      (mixedClosure_le_closedSpace (packet_mem_mixed hp hq hne)))
  have h := congrArg (fun y => inner ℝ limitResidual y) (smul_density x)
  change inner ℝ limitResidual (zetaTwo • densityP x) = inner ℝ limitResidual (x + DP x) at h
  rw [real_inner_smul_right, inner_add_right, hx, zero_add] at h
  change ‖limitResidual‖ ^ 2 + zetaTwo * inner ℝ limitResidual (densityP x) =
    inner ℝ limitResidual (DP x + hilbertOne)
  rw [h, inner_add_right, limitResidual_mean_and_screened_norm.1, add_comm]

/-- One nonnegative pairing gives a finite upper bound for the actual residual energy. -/
theorem residual_energy_le_of_nonnegative_pairing {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (hs : 0 ≤ inner ℝ limitResidual (densityP (ramanujanPacketHilbert (p * q)))) :
    ‖limitResidual‖ ^ 2 ≤ 4 / ((min p q : ℕ) : ℝ) := by
  let e := DP (ramanujanPacketHilbert (p * q)) + hilbertOne
  have he : ‖limitResidual‖ ^ 2 ≤ ‖limitResidual‖ * ‖e‖ := calc
    ‖limitResidual‖ ^ 2 ≤ inner ℝ limitResidual e := by
      change ‖limitResidual‖ ^ 2 ≤
        inner ℝ limitResidual (DP (ramanujanPacketHilbert (p * q)) + hilbertOne)
      rw [← residual_pairing_identity hp hq hne]
      exact le_add_of_nonneg_right (mul_nonneg zetaTwo_pos.le hs)
    _ ≤ ‖limitResidual‖ * ‖e‖ := real_inner_le_norm _ _
  have hnorm : ‖limitResidual‖ ≤ ‖e‖ := by
    by_contra! hlt
    have hpos : 0 < ‖limitResidual‖ := (norm_nonneg e).trans_lt hlt
    exact (not_le_of_gt (mul_lt_mul_of_pos_left hlt hpos)) (by simpa only [pow_two] using he)
  exact ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hnorm).trans
    (semiprime_reciprocal_error_sq_le hp hq hne)

local notation "nthPrime" => Nat.nth Nat.Prime

/-- The original integrated Ramanujan packet at the product of successive primes. -/
def consecutivePacket (j : ℕ) : ThresholdHilbert :=
  ramanujanPacketHilbert (nthPrime j * nthPrime (j + 1))

theorem consecutivePacket_mem_mixed (j : ℕ) : consecutivePacket j ∈ mixedClosure := by
  have hp := Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime j
  have hq := Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime (j + 1)
  have hlt := Nat.nth_strictMono Nat.infinite_setOfPred_prime (Nat.lt_succ_self j)
  exact packet_mem_mixed hp hq hlt.ne

/-- The reciprocals of these single mixed packets converge strongly to the negative constant. -/
theorem consecutive_reciprocal_tendsto :
    Tendsto (fun j => DP (consecutivePacket j)) atTop (𝓝 (-hilbertOne)) := by
  have hmono : StrictMono nthPrime := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  have hd : Tendsto (fun j => (nthPrime j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hmono.tendsto_atTop
  have hupper : Tendsto (fun j => (4 : ℝ) / (nthPrime j : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hd
  have hbound (j : ℕ) : ‖DP (consecutivePacket j) + hilbertOne‖ ^ 2 ≤ 4 / (nthPrime j : ℝ) := by
    have hlt := hmono (Nat.lt_succ_self j)
    simpa only [consecutivePacket, min_eq_left hlt.le] using
      semiprime_reciprocal_error_sq_le (Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime j)
        (Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime (j + 1)) hlt.ne
  have hsq := squeeze_zero (fun j => sq_nonneg ‖DP (consecutivePacket j) + hilbertOne‖)
    hbound hupper
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero, sub_neg_eq_add]
    using (Real.continuous_sqrt.continuousAt.tendsto.comp hsq)

/-- For every subspace containing these packets their density images approximate
the complementary part of the ambient constant, with the same normalization. -/
theorem projected_consecutive_tendsto (S : Submodule ℝ ThresholdHilbert) [S.HasOrthogonalProjection]
    (hs : ∀ j, consecutivePacket j ∈ S) :
    Tendsto (fun j => (-zetaTwo) • Sᗮ.starProjection (densityP (consecutivePacket j)))
      atTop (𝓝 (Sᗮ.starProjection hilbertOne)) := by
  simp_rw [projected_density_eq S (hs _)]
  have h := ((Sᗮ.starProjection.continuous.tendsto (-hilbertOne)).comp
    consecutive_reciprocal_tendsto).neg
  simpa only [Function.comp_def, map_neg, neg_neg] using h

/-- In the mixed quotient the limit is the ambient constant. In the legal quotient
it is exactly the Pareto residual of the constant. -/
theorem consecutive_projection_limits :
    Tendsto (fun j => (-zetaTwo) • mixedClosureᗮ.starProjection (densityP (consecutivePacket j)))
      atTop (𝓝 hilbertOne) ∧
    Tendsto (fun j => (-zetaTwo) • DilationDensityLeakage.leakage (consecutivePacket j))
      atTop (𝓝 limitResidual) := by
  constructor
  · simpa only [mixedOrthogonal_starProjection_one] using
      projected_consecutive_tendsto mixedClosure consecutivePacket_mem_mixed
  · simpa only [DilationDensityLeakage.leakage, ContinuousLinearMap.comp_apply,
      Submodule.starProjection_orthogonal_val, limitResidual, limitProjection] using
      projected_consecutive_tendsto closedSpace
        (fun j => mixedClosure_le_closedSpace (consecutivePacket_mem_mixed j))

/-- The signed pairing recovers the full squared residual norm. -/
theorem residual_pairing_tendsto :
    Tendsto (fun j => -zetaTwo * inner ℝ limitResidual (densityP (consecutivePacket j)))
      atTop (𝓝 (‖limitResidual‖ ^ 2)) := by
  have hpair (x : ThresholdHilbert) :
      inner ℝ limitResidual (DilationDensityLeakage.leakage x) =
        inner ℝ limitResidual (densityP x) := by
    change inner ℝ limitResidual (closedSpaceᗮ.starProjection (densityP x)) = _
    rw [Submodule.starProjection_orthogonal_val, inner_sub_right]
    have hz : inner ℝ limitResidual (closedSpace.starProjection (densityP x)) = 0 :=
      (real_inner_comm _ _).trans
        (limitResidual_mem_orthogonal _ (closedSpace.starProjection_apply_mem (densityP x)))
    rw [hz, sub_zero]
  have h := ((innerSL ℝ limitResidual).continuous.tendsto limitResidual).comp
    consecutive_projection_limits.2
  change Tendsto (fun j => inner ℝ limitResidual
    ((-zetaTwo) • DilationDensityLeakage.leakage (consecutivePacket j))) atTop
    (𝓝 (inner ℝ limitResidual limitResidual)) at h
  simpa only [real_inner_smul_right, hpair, real_inner_self_eq_norm_sq] using h

private theorem rh_iff_residual_zero :
    RiemannHypothesis ↔ limitResidual = 0 :=
  (riemannHypothesis_iff_naturalApproximation.trans
    BaezDuarte.naturalApproximation_iff_one_mem).trans
    (limitResidual_zero_iff_energy_zero.trans limitEnergy_zero_iff_mem).symm

/-- It suffices and is necessary to approximate the density images of this
one concrete sequence of mixed packets by legal vectors in the Pareto norm. -/
theorem riemannHypothesis_iff_consecutive_leakage_tendsto_zero :
    RiemannHypothesis ↔
      Tendsto (fun j => DilationDensityLeakage.leakage (consecutivePacket j)) atTop (𝓝 0) := by
  rw [rh_iff_residual_zero]
  have h := consecutive_projection_limits.2
  constructor
  · intro hd
    rw [hd] at h
    have hz : (-zetaTwo) ≠ 0 := neg_ne_zero.mpr zetaTwo_pos.ne'
    have ht := (tendsto_const_nhds (x := (-zetaTwo)⁻¹)).smul h
    simpa only [smul_zero, smul_smul, inv_mul_cancel₀ hz, one_smul] using ht
  · intro hz
    have ht := (tendsto_const_nhds (x := -zetaTwo)).smul hz
    apply tendsto_nhds_unique h
    simpa only [smul_zero] using ht

/-- RH is equivalent to a nonnegative residual pairing at arbitrarily late
successive-prime products. Providing these signs is the open arithmetic step. -/
theorem riemannHypothesis_iff_frequently_nonnegative_pairing :
    RiemannHypothesis ↔
      ∃ᶠ j in atTop, 0 ≤ inner ℝ limitResidual (densityP (consecutivePacket j)) := by
  rw [rh_iff_residual_zero]
  constructor
  · intro hd
    apply Filter.Eventually.frequently
    exact Eventually.of_forall (fun _ => by simp [hd])
  · intro hf
    by_contra hd
    have he : 0 < ‖limitResidual‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hd)
    have ht : ∀ᶠ j : ℕ in atTop,
        0 < -zetaTwo * inner ℝ limitResidual (densityP (consecutivePacket j)) :=
      residual_pairing_tendsto.eventually (Ioi_mem_nhds he)
    obtain ⟨j, hj, hj'⟩ := (hf.and_eventually ht).exists
    exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr zetaTwo_pos.le) hj)) hj'

#print axioms riemannHypothesis_iff_union_eq_univ
#print axioms residual_energy_le_of_nonnegative_pairing
#print axioms projected_mixed_dense
#print axioms screened_eq_one_iff_mixed_density_pairings
#print axioms semiprime_reciprocal_error_sq_le
#print axioms consecutive_projection_limits
#print axioms riemannHypothesis_iff_consecutive_leakage_tendsto_zero
#print axioms riemannHypothesis_iff_frequently_nonnegative_pairing

end RiemannResearch.RH.Pareto.PrimePowerSchur.MixedPacketDensity
