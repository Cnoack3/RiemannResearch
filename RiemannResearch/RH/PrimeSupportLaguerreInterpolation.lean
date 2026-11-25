import RiemannResearch.RH.MixedConductorResonanceProduct
import RiemannResearch.Analysis.BoundedInterpolation
import RiemannResearch.Analysis.FiniteObservationApproximation
import RiemannResearch.RH.ParetoLaguerreCoordinates
import RiemannResearch.RH.RamanujanOrdinaryMomentsProof
import RiemannResearch.RH.RamanujanFiniteSpanBridge
import RiemannResearch.RH.ParetoBoundedInteraction
import RiemannResearch.RH.MixedCaptureLegalTrials
import RiemannResearch.RH.CenteredMeanSquarefreeConverse

/-!
# Exact finite Laguerre interpolation and the prime support of legal lifts

Distinct support sizes give a triangular interpolation matrix. A uniform bound on
complete norms of finite exact lifts characterizes membership in the legal closure.
A dictionary confined to one prime dilation orbit meets arbitrary finite targets,
but its exact unit-prefix costs escape every bound.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.RamanujanLaguerre
open CoefficientStabilization PrimePowerSchur RiemannResearch.Analysis

/-- A squarefree conductor at every Laguerre order, including the order-zero prime seed. -/
theorem exists_squarefree_laguerre_dictionary :
    ∃ d : ℕ → ℕ, ∀ j, 1 < d j ∧ Squarefree (d j) ∧ (d j).primeFactors.card = j + 1 := by
  classical
  have h (j : ℕ) : ∃ q : ℕ, 1 < q ∧ Squarefree q ∧ q.primeFactors.card = j + 1 := by
    cases j with
    | zero => exact ⟨2, by decide, Nat.prime_two.squarefree, by simp [Nat.prime_two.primeFactors]⟩
    | succ j => exact exists_squarefree_large_prime_support j
  exact ⟨fun j => Classical.choose (h j), fun j => Classical.choose_spec (h j)⟩

/-- Forward substitution on the actual arithmetic packets interpolates arbitrary finite data. -/
theorem laguerre_prefix_packet_interpolation
    (d : ℕ → ℕ) (hd : ∀ j, 1 < d j ∧ (d j).primeFactors.card = j+1)
    (a : ℕ → ℝ) (N : ℕ) :
    ∃ v : ThresholdHilbert,
      v ∈ Submodule.span ℝ {x : ThresholdHilbert | ∃ j < N, x = ramanujanPacketHilbert (d j)} ∧
      ∀ k < N, laguerreReadout k v = a k := by
  classical
  induction N with
  | zero =>
    exact ⟨0, Submodule.zero_mem _, fun k hk => (Nat.not_lt_zero k hk).elim⟩
  | succ N ih =>
    obtain ⟨v, hv, hread⟩ := ih
    let y := ramanujanPacketHilbert (d N)
    have hlevel : (d N).primeFactors.card - 1 = N := by rw [(hd N).2]; omega
    obtain ⟨hlow, hdiag⟩ := ramanujanLaguerreCancellationTarget (d N) (hd N).1
    rw [hlevel] at hlow hdiag
    have hresp (k : ℕ) : laguerreReadout k y = coefficient (ramanujanPacket (d N)) k := by
      rw [readout_coeff]
      simp only [y, hilbertSequence_ramanujanPacketHilbert]
    have hn : laguerreReadout N y ≠ 0 := by
      rw [hresp, hdiag]
      apply mul_ne_zero (pow_ne_zero _ (by norm_num))
      apply Finset.prod_ne_zero_iff.mpr
      intro p hp
      apply (Real.log_pos _).ne'
      exact_mod_cast (Nat.mem_primeFactors.mp hp).1.one_lt
    let c := (a N - laguerreReadout N v) / laguerreReadout N y
    let S := Submodule.span ℝ {x : ThresholdHilbert | ∃ j < N+1, x = ramanujanPacketHilbert (d j)}
    have hvS : v ∈ S := by
      apply Submodule.span_mono _ hv
      rintro x ⟨j, hj, he⟩
      exact ⟨j, Nat.lt_succ_of_lt hj, he⟩
    have hyS : y ∈ S := Submodule.subset_span ⟨N, Nat.lt_succ_self _, rfl⟩
    refine ⟨v + c • y, S.add_mem hvS (S.smul_mem _ hyS), ?_⟩
    intro k hk
    rw [map_add, map_smul, smul_eq_mul]
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hk | rfl
    · rw [hread k hk, hresp, hlow k hk, mul_zero, add_zero]
    · dsimp only [c]
      field_simp [hn]
      <;> ring

/-- The actual algebraic legal span consists of finite residue-packet combinations. -/
abbrev finiteLaguerreLegalSpan : Submodule ℝ ThresholdHilbert :=
  Submodule.span ℝ (Set.range residueAtom)

/-- One arithmetic dictionary serves every finite target, with a genuinely finite legal synthesis. -/
theorem exists_squarefree_dictionary_interpolating_all_prefixes :
    ∃ d : ℕ → ℕ, (∀ j, 1 < d j ∧ Squarefree (d j) ∧ (d j).primeFactors.card = j+1) ∧
      ∀ (a : ℕ → ℝ) (N : ℕ), ∃ v : ThresholdHilbert,
        v ∈ Submodule.span ℝ {x : ThresholdHilbert | ∃ j < N, x = ramanujanPacketHilbert (d j)} ∧
        v ∈ finiteLaguerreLegalSpan ∧ ∀ k < N, laguerreReadout k v = a k := by
  obtain ⟨d, hd⟩ := exists_squarefree_laguerre_dictionary
  refine ⟨d, hd, fun a N => ?_⟩
  obtain ⟨v, hv, ha⟩ :=
    laguerre_prefix_packet_interpolation d (fun j => ⟨(hd j).1, (hd j).2.2⟩) a N
  refine ⟨v, hv, ?_, ha⟩
  apply Submodule.span_le.mpr _ hv
  rintro w ⟨j, hj, rfl⟩
  rw [ramanujanPacketHilbert_eq_divisor_sum (d j) (hd j).1]
  apply finiteLaguerreLegalSpan.sum_mem
  intro e he
  apply finiteLaguerreLegalSpan.smul_mem
  unfold rawResidueAtom
  exact finiteLaguerreLegalSpan.smul_mem _ (Submodule.subset_span ⟨e-2, rfl⟩)

/-- Even legal lifts in the closed space itself suffice if their complete squared norms
share a uniform bound. -/
theorem screened_eq_one_of_bounded_legal_laguerre_prefixes {C : ℝ}
    (h : ∀ N : ℕ, ∃ v : ThresholdHilbert, v ∈ closedSpace ∧
      (∀ k ≤ N, laguerreReadout k v = laguerreReadout k hilbertOne) ∧ ‖v‖ ^ 2 ≤ C) :
    normalizedScreenedTwo = hilbertOne :=
  one_mem_closedSpace_iff_normalizedScreenedTwo.mp
    (BoundedInterpolation.mem_of_bounded_exact_interpolation closedSpace
      (Submodule.isClosed_topologicalClosure _) laguerreReadout
      (fun _ _ he => laguerreCoordinates_ext (fun k => congrFun he k)) hilbertOne C h)

/-- Uniform complete-norm control of exact Laguerre prefixes in the finite legal span
characterizes membership in its closure. The cost bound may depend on the target. -/
theorem mem_closedSpace_iff_bounded_finite_laguerre_prefixes (x : ThresholdHilbert) :
    x ∈ closedSpace ↔ ∃ C : ℝ, ∀ N : ℕ, ∃ v : ThresholdHilbert,
      v ∈ finiteLaguerreLegalSpan ∧ (∀ k ≤ N, laguerreReadout k v = laguerreReadout k x) ∧
        ‖v‖ ^ 2 ≤ C := by
  constructor
  · intro hx
    refine ⟨(‖x‖ + 1)^2, fun N => ?_⟩
    let T : ThresholdHilbert →L[ℝ] (Fin (N+1) → ℝ) :=
      ContinuousLinearMap.pi (fun i => laguerreReadout i.val)
    obtain ⟨v, hv, he, hdist⟩ :=
      exists_near_with_same_finite_observations finiteLaguerreLegalSpan T hx (by norm_num : (0:ℝ)<1)
    refine ⟨v, hv, fun k hk => ?_, ?_⟩
    · exact congrFun he (⟨k, Nat.lt_succ_of_le hk⟩ : Fin (N+1))
    · apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).2
      calc
        ‖v‖ = ‖(v-x)+x‖ := by rw [sub_add_cancel]
        _ ≤ ‖v-x‖ + ‖x‖ := norm_add_le _ _
        _ ≤ ‖x‖ + 1 := by rw [norm_sub_rev]; linarith
  · rintro ⟨C, hC⟩
    refine BoundedInterpolation.mem_of_bounded_exact_interpolation closedSpace
      (Submodule.isClosed_topologicalClosure _) laguerreReadout ?_ x C ?_
    · intro f g h
      exact laguerreCoordinates_ext (fun j => congrFun h j)
    · intro N
      obtain ⟨v, hv, hh, hb⟩ := hC N
      exact ⟨v, finiteLaguerreLegalSpan.le_topologicalClosure hv, hh, hb⟩

/-- The finite Laguerre lift criterion for the physical screened section. -/
theorem screened_eq_one_iff_bounded_finite_laguerre_prefixes :
    normalizedScreenedTwo = hilbertOne ↔ ∃ C : ℝ, ∀ N : ℕ, ∃ v : ThresholdHilbert,
      v ∈ finiteLaguerreLegalSpan ∧ (∀ k ≤ N, laguerreReadout k v = laguerreReadout k hilbertOne) ∧
        ‖v‖ ^ 2 ≤ C :=
  one_mem_closedSpace_iff_normalizedScreenedTwo.symm.trans
    (mem_closedSpace_iff_bounded_finite_laguerre_prefixes hilbertOne)

/-- A uniform bound on honest finite arithmetic lifts characterizes RH. -/
theorem bounded_finite_laguerre_prefixes_iff_riemannHypothesis :
    (∃ C : ℝ, ∀ N : ℕ, ∃ v : ThresholdHilbert,
      v ∈ finiteLaguerreLegalSpan ∧ (∀ k ≤ N, laguerreReadout k v = laguerreReadout k hilbertOne) ∧
        ‖v‖ ^ 2 ≤ C) ↔ RiemannHypothesis :=
  ⟨fun h => riemannHypothesis_of_normalizedScreenedTwo
      (screened_eq_one_iff_bounded_finite_laguerre_prefixes.mpr h),
    fun h => (mem_closedSpace_iff_bounded_finite_laguerre_prefixes hilbertOne).mp
      (BaezDuarte.naturalApproximation_iff_one_mem.mp (CenteredMeanSnake.riemannHypothesis_iff_naturalApproximation.mp h))⟩

end RiemannResearch.RH.Pareto.RamanujanLaguerre

noncomputable section
namespace RiemannResearch.RH.Pareto.RamanujanLaguerre

/-- At a fixed prime the entire closed integer-dilation span of its packet
eventually exceeds every energy budget for exact Laguerre interpolation.
This includes each packet whose conductor is divisible by the fixed prime. -/
theorem fixedPrime_laguerre_interpolation_norm_escape
    (p : ℕ) (hp : p.Prime) (C : ℝ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ f ∈ singleSeedDilationClosure (ramanujanPacketHilbert p),
      (∀ k ≤ n, laguerreReadout k f = laguerreReadout k hilbertOne) →
        C < ‖f‖ ^ 2 := by
  let K := singleSeedDilationClosure (ramanujanPacketHilbert p)
  have hclosed : IsClosed (K : Set ThresholdHilbert) :=
    (Submodule.span ℝ (singleSeedDilationSet (ramanujanPacketHilbert p))).isClosed_topologicalClosure
  have hs : (1 / 2 : ℝ) < (primePacketResonance p 1).re := by
    rw [primePacketResonance_re p hp.one_lt]
    norm_num
  have hnot : hilbertOne ∉ K :=
    hilbertOne_not_mem_singleSeedClosure_of_mellin _ _ hs
      (primePacketResonance_mellin_zero p hp 1 (by norm_num))
  have hsep : Function.Injective
      (fun f : ThresholdHilbert => fun k : ℕ => laguerreReadout k f) :=
    fun _ _ h => laguerreCoordinates_ext (fun k => congrFun h k)
  have hex : ∃ N : ℕ, ∀ f ∈ K,
      (∀ k ≤ N, laguerreReadout k f = laguerreReadout k hilbertOne) →
        C < ‖f‖ ^ 2 := by
    by_contra! h
    exact hnot (RiemannResearch.Analysis.BoundedInterpolation.mem_of_bounded_exact_interpolation
      K hclosed laguerreReadout hsep hilbertOne C h)
  obtain ⟨N, hN⟩ := hex
  exact ⟨N, fun n hn f hf hhead =>
    hN f hf (fun k hk => hhead k (hk.trans hn))⟩

end RiemannResearch.RH.Pareto.RamanujanLaguerre

namespace RiemannResearch.RH.Pareto.RamanujanLaguerre

/-- Every prescribed prime has a squarefree packet dictionary starting at that
prime which solves every finite Laguerre interpolation problem in its dilation span. -/
theorem fixedPrime_laguerre_prefix_solvable (p : ℕ) (hp : p.Prime) :
    ∃ d : ℕ → ℕ, d 0 = p ∧
      (∀ j, 1 < d j ∧ p ∣ d j ∧ Squarefree (d j) ∧ (d j).primeFactors.card = j + 1) ∧
      ∀ (a : ℕ → ℝ) (N : ℕ), ∃ v : ThresholdHilbert,
        v ∈ Submodule.span ℝ {x : ThresholdHilbert | ∃ j < N, x = ramanujanPacketHilbert (d j)} ∧
        v ∈ singleSeedDilationClosure (ramanujanPacketHilbert p) ∧
        ∀ k < N, laguerreReadout k v = a k := by
  classical
  have h (j : ℕ) : ∃ n : ℕ,
      1 < n ∧ p ∣ n ∧ Squarefree n ∧ n.primeFactors.card = j + 1 := by
    induction j with
    | zero =>
      exact ⟨p, hp.one_lt, dvd_refl _, hp.squarefree, by simp [hp.primeFactors]⟩
    | succ j ih =>
      obtain ⟨n, hn, hpn, hs, hc⟩ := ih
      obtain ⟨r, hrn, hr⟩ := Nat.exists_infinite_primes (n + 1)
      have hn0 : 0 < n := by omega
      have hrnd : ¬ r ∣ n := fun hd => by
        have := Nat.le_of_dvd hn0 hd
        omega
      have hrF : r ∉ n.primeFactors := fun hmem => hrnd (Nat.dvd_of_mem_primeFactors hmem)
      refine ⟨r * n, hn.trans_le (Nat.le_mul_of_pos_left n hr.pos),
        dvd_trans hpn (dvd_mul_left n r),
        (Nat.squarefree_mul (hr.coprime_iff_not_dvd.mpr hrnd)).mpr ⟨hr.squarefree, hs⟩, ?_⟩
      rw [Nat.primeFactors_mul hr.ne_zero hn0.ne', hr.primeFactors, Finset.singleton_union,
        Finset.card_insert_of_notMem hrF, hc]
  let d : ℕ → ℕ := fun j => if j = 0 then p else Classical.choose (h j)
  have hd (j : ℕ) : 1 < d j ∧ p ∣ d j ∧ Squarefree (d j) ∧
      (d j).primeFactors.card = j + 1 := by
    by_cases hj : j = 0
    · subst j
      simp only [d, if_pos rfl]
      exact ⟨hp.one_lt, dvd_refl _, hp.squarefree, by simp [hp.primeFactors]⟩
    · simpa only [d, if_neg hj] using Classical.choose_spec (h j)
  refine ⟨d, by simp [d], hd, fun a N => ?_⟩
  obtain ⟨v, hv, ha⟩ := laguerre_prefix_packet_interpolation d
    (fun j => ⟨(hd j).1, (hd j).2.2.2⟩) a N
  refine ⟨v, hv, ?_, ha⟩
  apply Submodule.span_le.mpr _ hv
  rintro w ⟨j, _, rfl⟩
  exact ramanujanPacketHilbert_mem_singleSeed_of_dvd p (d j) hp
    (Nat.zero_lt_one.trans (hd j).1) (hd j).2.1

/--
info: 'RiemannResearch.RH.Pareto.RamanujanLaguerre.exists_squarefree_dictionary_interpolating_all_prefixes' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_squarefree_dictionary_interpolating_all_prefixes

/--
info: 'RiemannResearch.RH.Pareto.RamanujanLaguerre.fixedPrime_laguerre_prefix_solvable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fixedPrime_laguerre_prefix_solvable

end RiemannResearch.RH.Pareto.RamanujanLaguerre
