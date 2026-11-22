import RiemannResearch.RH.QDensityImageReconstruction
import RiemannResearch.RH.ZetaTwoAffineHeadTower
import RiemannResearch.RH.QReciprocalDensityClassification
import RiemannResearch.RH.QRamanujanFullSupport
import RiemannResearch.RH.ParetoPrimePackets
import Mathlib.Data.Nat.Prime.Infinite

/-!
# Reciprocal images of affine squarefree CRT packets

In repository notation B is dQ/dP and D = ζ(2) B - I is multiplication by
1/n. Adjoining a fresh prime to a squarefree packet changes its negative
only on a physical tail. After applying D that tail tends to zero in L²(Q).
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.SquarefreeAffineReciprocal

open Pareto ZetaTwoProbability ZetaTwoHilbert QRamanujanPackets QReciprocalMetric
open QDensityImageReconstruction

/-- Finite mixed squarefree packet combinations, indexed by composite squarefree conductors. -/
def mixedPackets : Submodule ℝ QHilbert :=
  Submodule.span ℝ {f | ∃ q : ℕ, 1 < q ∧ Squarefree q ∧ ¬ q.Prime ∧ f = qRamanujanPacket q}

def dampedMixed : Submodule ℝ QHilbert := (mixedPackets.map D.toLinearMap).topologicalClosure

/-- One fixed squarefree mean-one anchor. -/
def anchor : QHilbert := (Real.log 2)⁻¹ • qRamanujanPacket 2

private def envelope (q : ℕ) : ℝ :=
  ∑ d ∈ q.divisors, |(ArithmeticFunction.moebius (q/d) : ℝ)| * (d : ℝ)

private theorem envelope_nonneg (q : ℕ) : 0 ≤ envelope q := by unfold envelope; positivity

/-- The error is supported at n ≥ p and is pointwise bounded independently of p. -/
theorem fresh_packet_value (q p k : ℕ) (hq : 1 < q) (hp : p.Prime) (hnd : ¬p ∣ q) :
    qSequence (D (qRamanujanPacket (p*q) + qRamanujanPacket q)) k =
      ((p : ℝ) / (k : ℝ)) * ramanujanPacket q (k / p) := by
  rw [qSequence_D]
  change qSequenceLinear (qRamanujanPacket (p*q) + qRamanujanPacket q) k / _ = _
  rw [map_add]
  change (qSequence (qRamanujanPacket (p*q)) k + qSequence (qRamanujanPacket q) k) / _ = _
  rw [qSequence_qRamanujanPacket, qSequence_qRamanujanPacket,
    ramanujanPacket_mul_prime_of_not_dvd p q k hp hq hnd, sub_add_cancel]
  unfold dilation
  ring

private theorem packet_at_zero (q : ℕ) : ramanujanPacket q 0 = 0 := by
  rw [← qSequence_qRamanujanPacket]
  exact qSequence_zero _

theorem fresh_packet_bound (q p n : ℕ) (hq : 1 < q) (hp : p.Prime) (hnd : ¬p ∣ q)
    (hn : n < p) :
    ‖D (qRamanujanPacket (p*q) + qRamanujanPacket q)‖^2 ≤
      ((2 / zetaTwo) * (envelope q)^2) / ((n : ℝ) + 1) := by
  let e := D (qRamanujanPacket (p*q) + qRamanujanPacket q)
  have hh (k : ℕ) (hk : k < p) : qSequence e k = 0 := by
    rw [show e = _ from rfl, fresh_packet_value q p k hq hp hnd,
      Nat.div_eq_of_lt hk, packet_at_zero, mul_zero]
  have hA (k : ℕ) (hk : 0 < k) : |qSequence e k| ≤ envelope q := by
    by_cases hkp : k < p
    · rw [hh k hkp, abs_zero]; exact envelope_nonneg q
    · rw [show e = _ from rfl, fresh_packet_value q p k hq hp hnd, abs_mul,
        abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
      have hk' : (0 : ℝ) < k := by exact_mod_cast hk
      have hc : (p : ℝ) / k ≤ 1 := (div_le_one hk').2 (by exact_mod_cast le_of_not_gt hkp)
      exact (mul_le_mul_of_nonneg_right hc (abs_nonneg _)).trans
        (by simpa only [one_mul, envelope] using ramanujanPacket_abs_le q (k / p))
  have ht := ZetaTwoAffineHeadTower.bounded_test_tail e n (envelope q) (envelope_nonneg q) hA
  have hraw (i : ℕ) (hi : i < n) : e i = 0 := by
    have h := hh (i+1) (by omega)
    rw [qSequence_succ] at h
    exact (div_eq_zero_iff.mp h).resolve_right (Real.sqrt_pos.mpr (qWeight_pos _)).ne'
  have hs : ∑ i ∈ Finset.range n, (e i)^2 = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp [hraw i (Finset.mem_range.mp hi)]
  rw [hilbertTailShift_norm_sq, hs, sub_zero] at ht
  exact ht

private def fresh (q n : ℕ) : ℕ := (Nat.exists_infinite_primes (n+q+2)).choose

private theorem fresh_spec (q n : ℕ) : n+q+2 ≤ fresh q n ∧ (fresh q n).Prime :=
  (Nat.exists_infinite_primes (n+q+2)).choose_spec

/-- Every squarefree packet can be approximated after applying D by single
mixed squarefree packets, with the opposite sign. -/
theorem damped_packet_mem {q : ℕ} (hq : 1 < q) (hs : Squarefree q) :
    D (qRamanujanPacket q) ∈ dampedMixed := by
  let p := fresh q
  have hp (n : ℕ) : (p n).Prime := (fresh_spec q n).2
  have hbig (n : ℕ) : n+q+2 ≤ p n := (fresh_spec q n).1
  have hnd (n : ℕ) : ¬ p n ∣ q := fun h => by
    have hh := Nat.le_of_dvd (by omega : 0 < q) h
    have := hbig n
    omega
  have hm (n : ℕ) : qRamanujanPacket (p n * q) ∈ mixedPackets := by
    apply Submodule.subset_span
    have hprod : 1 < p n * q := hq.trans_le
      (by simpa only [one_mul] using Nat.mul_le_mul_right q (hp n).one_lt.le)
    refine ⟨p n * q, hprod, ?_, ?_, rfl⟩
    · exact (Nat.squarefree_mul ((hp n).coprime_iff_not_dvd.mpr (hnd n))).mpr
        ⟨(hp n).squarefree,hs⟩
    · exact Nat.not_prime_mul (by exact (hp n).ne_one) (by omega)
  have hlim : Tendsto (fun n => ‖D (qRamanujanPacket (p n*q) + qRamanujanPacket q)‖^2)
      atTop (𝓝 0) := by
    let c := 2 / zetaTwo * (envelope q)^2
    have hc : 0 ≤ c := mul_nonneg (div_nonneg (by norm_num) zetaTwo_pos.le) (sq_nonneg _)
    apply squeeze_zero' (Eventually.of_forall fun _ => sq_nonneg _) _
      (tendsto_const_div_atTop_nhds_zero_nat c)
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    exact (fresh_packet_bound q (p n) n hq (hp n) (hnd n) (by have := hbig n; omega)).trans
      (div_le_div_of_nonneg_left hc hn' (by linarith))
  have hnorm : Tendsto (fun n => ‖D (qRamanujanPacket (p n*q) + qRamanujanPacket q)‖)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hlim
  have hconv : Tendsto (fun n => -D (qRamanujanPacket (p n*q))) atTop
      (𝓝 (D (qRamanujanPacket q))) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have he (n : ℕ) : -D (qRamanujanPacket (p n*q)) - D (qRamanujanPacket q) =
        -(D (qRamanujanPacket (p n*q)) + D (qRamanujanPacket q)) := by abel
    simpa only [dist_eq_norm, he, norm_neg, map_add] using hnorm
  apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto hconv
  exact Eventually.of_forall fun n => dampedMixed.neg_mem
    (Submodule.le_topologicalClosure _ ⟨_, hm n, rfl⟩)

/-- The reciprocal closure of the mixed squarefree packets equals that of all
squarefree residues. -/
theorem dampedMixed_eq_squarefree :
    dampedMixed =
      (QReciprocalSpanObstruction.reciprocalSpan
        {k : ℕ | 2 ≤ k ∧ Squarefree k}).topologicalClosure := by
  apply le_antisymm
  · let K := (QReciprocalSpanObstruction.reciprocalSpan
        {k : ℕ | 2 ≤ k ∧ Squarefree k}).topologicalClosure
    have hinc : mixedPackets ≤ K.comap D.toLinearMap := by
      apply Submodule.span_le.mpr
      rintro _ ⟨q,_,hs,_,rfl⟩
      change D (qRamanujanPacket q) ∈ K
      rw [qRamanujanPacket, map_sum]
      apply K.sum_mem
      intro d hd
      rw [map_smul]
      apply K.smul_mem
      by_cases h1 : d = 1
      · simp [h1]
      · exact Submodule.le_topologicalClosure _ (Submodule.subset_span
          ⟨d,⟨by have := Nat.pos_of_mem_divisors hd; omega,
            hs.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)⟩,rfl⟩)
    apply Submodule.topologicalClosure_minimal _ _ (Submodule.isClosed_topologicalClosure _)
    rintro _ ⟨m,hm,rfl⟩
    exact hinc hm
  · apply Submodule.topologicalClosure_minimal _ _ (Submodule.isClosed_topologicalClosure _)
    apply Submodule.span_le.mpr
    rintro _ ⟨k,⟨hk,hs⟩,rfl⟩
    rw [qResidue_eq_divisor_packets k (by omega), map_smul, map_sum]
    apply dampedMixed.smul_mem
    apply dampedMixed.sum_mem
    intro q hq
    by_cases h1 : q = 1
    · simp [h1]
    · exact damped_packet_mem (by have := Nat.pos_of_mem_divisors hq; omega)
        (hs.squarefree_of_dvd (Nat.dvd_of_mem_divisors hq))

/-- The smoothed constant is in the closure of smoothed mixed squarefree packets. -/
theorem damped_target_mem : D qOne ∈ dampedMixed := by
  rw [dampedMixed_eq_squarefree]
  exact QReciprocalDensityClassification.D_one_mem_squarefree_reciprocalClosure

/-- Equivalently, finite mean-zero mixed corrections to the mean-one anchor
reach 1/n in the reciprocal norm. -/
theorem damped_affine_target : D (qOne - anchor) ∈ dampedMixed := by
  rw [map_sub, anchor, map_smul]
  exact dampedMixed.sub_mem damped_target_mem (dampedMixed.smul_mem _
    (damped_packet_mem (q := 2) (by decide) Nat.prime_two.squarefree))

/-- Equality of actual images under the injective reciprocal map reflects
equality of the original subspaces. -/
theorem exact_range_iff (S : Submodule ℝ QHilbert) :
    S.map D.toLinearMap = (⊤ : Submodule ℝ QHilbert).map D.toLinearMap ↔ S = ⊤ := by
  constructor
  · intro h
    apply top_unique
    intro x _
    have hx : D x ∈ S.map D.toLinearMap := by
      rw [h]
      exact ⟨x,Submodule.mem_top,rfl⟩
    obtain ⟨y,hy,he⟩ := hx
    exact QReciprocalTargetLift.D_injective he ▸ hy
  · rintro rfl
    rfl

/-- The unconditional equality for the full legal dictionary is one of closed images. -/
theorem full_closed_reciprocal_range :
    (QFullResidueProjection.closure.map D.toLinearMap).topologicalClosure = ⊤ := by
  apply top_unique
  rw [← QDensityClosureTransfer.full_D_map_dense]
  apply Submodule.topologicalClosure_mono
  exact Submodule.map_mono QFullResidueProjection.legalSpan.le_topologicalClosure

/-- A bound on the original affine trials lifts the smoothed convergence back to RH. -/
theorem rh_of_bounded_affine_lifts (C : ℝ) (F : ℕ → QHilbert)
    (hmem : ∀ n, F n - anchor ∈ mixedPackets)
    (hbound : ∀ n, ‖F n‖ ≤ C)
    (hlim : Tendsto (fun n => D (F n)) atTop (𝓝 (D qOne))) : RiemannHypothesis := by
  have hm : mixedPackets ≤ qSquarefreeCRTSpan := by
    apply Submodule.span_le.mpr
    rintro _ ⟨q,_,hs,_,rfl⟩
    exact QRamanujanFullSupport.packet_mem_squarefree q hs
  have ha : anchor ∈ qSquarefreeCRTSpan :=
    qSquarefreeCRTSpan.smul_mem _
      (QRamanujanFullSupport.packet_mem_squarefree 2 Nat.prime_two.squarefree)
  have hF (n : ℕ) : F n ∈ qSquarefreeCRTSpan.topologicalClosure := by
    apply qSquarefreeCRTSpan.le_topologicalClosure
    simpa only [sub_add_cancel] using qSquarefreeCRTSpan.add_mem (hm (hmem n)) ha
  exact rh_of_squarefree_image (squarefree_image_target_iff_q.mpr
    (QReciprocalTargetLift.mem_of_bounded_D_tendsto _ C F qOne hF hbound hlim).1)

#print axioms damped_affine_target
#print axioms rh_of_bounded_affine_lifts
end RiemannResearch.RH.SquarefreeAffineReciprocal
