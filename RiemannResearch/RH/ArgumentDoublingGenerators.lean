import RiemannResearch.RH.ArgumentDoublingClosure

/-!
# Argument doubling: exact norm, residue generators, and approximation obstructions

Source: user-provided
RH_Doubling_Generators_and_Hurwitz_Obstruction_2026-09-20(1).md,
Sections 1--4 (statements and proof strategy).
Bagchi, "On Nyman, Beurling and Baez-Duarte's Hilbert space reformulation
of the Riemann hypothesis", Theorem 1,
https://arxiv.org/abs/math/0607733, supports the weighted residue-space
terminology. Its equivalence is not introduced as an axiom here.

This file constructs the actual bounded even-sampling operator, proves its
exact norm two, computes its even and odd generator images, and identifies
invariance with closed-span membership of every odd carry indicator.
The finite-span obstruction at d = 3 is unconditional and does not pass to
the Hilbert closure. The continuous Mellin separator supplies the full
weighted squared-distance lower bound at a hypothetical right-half-plane zero.

Status: the norm, identities, membership equivalences, and obstruction
theorems are established. The final RH implication is a conditional research
reduction: membership of every odd carry remains Open. The source's Hurwitz
Taylor estimate, sufficiently-large-odd obstruction, unbounded-index criterion,
and RH-to-invariance converse are not formalized by this module.
-/

open scoped BigOperators Topology
open Filter
noncomputable section
namespace RiemannResearch.RH.Pareto
open RiemannResearch.RH.ArithmeticCumulative

theorem doubling_weight_identity (n : ℕ) :
    positiveWeight n = (4 - 2 / ((n : ℝ) + 1)) * positiveWeight (2 * n) := by
  by_cases hn : n = 0
  · subst n; norm_num [positiveWeight]
  · have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    unfold positiveWeight
    push_cast
    field_simp
    ring

theorem doubling_weight_bound (n : ℕ) :
    positiveWeight n ≤ 4 * positiveWeight (2 * n) := by
  rw [doubling_weight_identity]
  exact mul_le_mul_of_nonneg_right (sub_le_self _ (by positivity)) (positiveWeight_nonneg _)

private theorem even_tsum_le {g : ℕ → ℝ}
    (hg : Summable g) (h0 : ∀ n, 0 ≤ g n) :
    (∑' n, g (2 * n)) ≤ ∑' n, g n := by
  have hi : Function.Injective (fun n : ℕ => 2 * n) := by intro a b h; dsimp at h; omega
  have hs := hg.comp_injective hi
  have hb (N : ℕ) : (∑ n ∈ Finset.range N, g (2 * n)) ≤ ∑' n, g n := by
    calc
      _ = ∑ n ∈ (Finset.range N).image (fun k => 2 * k), g n := by
        rw [Finset.sum_image]
        intro a ha b hb hab
        exact hi hab
      _ ≤ _ := hg.sum_le_tsum _ (fun n _ => h0 n)
  exact le_of_tendsto hs.hasSum.tendsto_sum_nat (Eventually.of_forall hb)

theorem argumentDoubling_summable (f : ThresholdHilbert) :
    Summable (fun n => positiveWeight n * hilbertSequence f (2 * n) ^ 2) := by
  have hi : Function.Injective (fun n : ℕ => 2 * n) := by intro a b h; dsimp at h; omega
  have hs := (hilbertSequence_square_summable f).comp_injective hi
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (positiveWeight_nonneg _) (sq_nonneg _))
    (fun n => ?_) (hs.mul_left 4)
  simpa only [Function.comp_def, mul_assoc] using
    mul_le_mul_of_nonneg_right (doubling_weight_bound n)
      (sq_nonneg (hilbertSequence f (2 * n)))

def hilbertArgumentDoubling (f : ThresholdHilbert) : ThresholdHilbert :=
  sequenceHilbert (fun n => hilbertSequence f (2 * n)) (argumentDoubling_summable f)

@[simp] theorem hilbertArgumentDoubling_sequence (f : ThresholdHilbert) :
    hilbertSequence (hilbertArgumentDoubling f) = fun n => hilbertSequence f (2 * n) := by
  apply hilbertSequence_sequenceHilbert
  simp

def argumentDoublingLinear : ThresholdHilbert →ₗ[ℝ] ThresholdHilbert where
  toFun := hilbertArgumentDoubling
  map_add' f g := by
    apply hilbertSequence_injective
    simp only [hilbertArgumentDoubling_sequence, hilbertSequence_add]
    rfl
  map_smul' c f := by
    apply hilbertSequence_injective
    simp only [hilbertArgumentDoubling_sequence, hilbertSequence_smul]
    rfl

theorem hilbertArgumentDoubling_norm_sq_le (f : ThresholdHilbert) :
    ‖hilbertArgumentDoubling f‖ ^ 2 ≤ 4 * ‖f‖ ^ 2 := by
  rw [hilbert_norm_weighted_sq, hilbertArgumentDoubling_sequence,
    hilbert_norm_weighted_sq]
  have hi : Function.Injective (fun n : ℕ => 2 * n) := by intro a b h; dsimp at h; omega
  have hs := (hilbertSequence_square_summable f).comp_injective hi
  calc
    _ ≤ ∑' n, 4 * (positiveWeight (2 * n) * hilbertSequence f (2 * n) ^ 2) :=
      (argumentDoubling_summable f).tsum_le_tsum
        (fun n => by
          simpa only [mul_assoc] using
            mul_le_mul_of_nonneg_right (doubling_weight_bound n)
              (sq_nonneg (hilbertSequence f (2 * n)))) (hs.mul_left 4)
    _ = 4 * ∑' n, positiveWeight (2 * n) * hilbertSequence f (2 * n) ^ 2 :=
      hs.tsum_mul_left 4
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (even_tsum_le (hilbertSequence_square_summable f)
        (fun n => mul_nonneg (positiveWeight_nonneg _) (sq_nonneg _))) (by norm_num)

theorem hilbertArgumentDoubling_norm_le (f : ThresholdHilbert) :
    ‖hilbertArgumentDoubling f‖ ≤ 2 * ‖f‖ := by
  have h := hilbertArgumentDoubling_norm_sq_le f
  nlinarith [norm_nonneg (hilbertArgumentDoubling f), norm_nonneg f]

def argumentDoublingContinuous : ThresholdHilbert →L[ℝ] ThresholdHilbert :=
  argumentDoublingLinear.mkContinuous 2 hilbertArgumentDoubling_norm_le

@[simp] theorem argumentDoublingContinuous_apply (f : ThresholdHilbert) :
    argumentDoublingContinuous f = hilbertArgumentDoubling f := rfl

theorem residueFraction_double_even (q n : ℕ) (hq : 0 < q) :
    residueFraction (2 * q) (2 * n) = residueFraction q n := by
  simp only [residueFraction, Nat.mul_mod_mul_left, Nat.cast_mul, Nat.cast_ofNat]
  have hqR : (q : ℝ) ≠ 0 := by positivity
  field_simp

def doublingCarry (d n : ℕ) : ℝ :=
  if d ≤ 2 * (n % d) then 1 else 0

theorem residueFraction_double (d n : ℕ) (hd : 0 < d) :
    residueFraction d (2 * n) = 2 * residueFraction d n - doublingCarry d n := by
  have hr := Nat.mod_lt n hd
  have hm : (2 * n) % d = (2 * (n % d)) % d := by simp [Nat.mul_mod]
  have hdR : (d : ℝ) ≠ 0 := by positivity
  by_cases h : d ≤ 2 * (n % d)
  · have hb : 2 * (n % d) - d < d := by omega
    have he : (2 * n) % d = 2 * (n % d) - d := by
      rw [hm, Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt hb]
    simp only [residueFraction, he, doublingCarry, if_pos h,
      Nat.cast_sub h, Nat.cast_mul, Nat.cast_ofNat]
    field_simp
  · have he : (2 * n) % d = 2 * (n % d) := by
      rw [hm, Nat.mod_eq_of_lt (by omega)]
    simp only [residueFraction, he, doublingCarry, if_neg h,
      Nat.cast_mul, Nat.cast_ofNat, sub_zero]
    ring

theorem doublingCarry_odd (d n : ℕ) (hd : Odd d) :
    doublingCarry d n = if (d + 1) / 2 ≤ n % d then 1 else 0 := by
  rcases hd with ⟨k, hk⟩
  unfold doublingCarry
  have he : d ≤ 2 * (n % d) ↔ (d + 1) / 2 ≤ n % d := by omega
  simp only [he]


private theorem point_norm_sq (n : ℕ) :
    ‖paretoPointHilbert n‖ ^ 2 = positiveWeight (n + 1) := by
  rw [← real_inner_self_eq_norm_sq, inner_paretoPoint,
    hilbertGibbsPhysical_paretoPoint, positiveWeight_succ]
  simp

theorem hilbertArgumentDoubling_point (n : ℕ) :
    hilbertArgumentDoubling (paretoPointHilbert (2 * n + 1)) = paretoPointHilbert n := by
  apply hilbertSequence_injective
  rw [hilbertArgumentDoubling_sequence, hilbertSequence_paretoPoint,
    hilbertSequence_paretoPoint]
  funext k
  have he : 2 * k = 2 * n + 1 + 1 ↔ k = n + 1 := by omega
  simp only [paretoPointSequence, he]

theorem argumentDoublingContinuous_norm : ‖argumentDoublingContinuous‖ = 2 := by
  apply le_antisymm
  · exact argumentDoublingContinuous.opNorm_le_bound (by norm_num)
      hilbertArgumentDoubling_norm_le
  · have hb (n : ℕ) : 4 - 2 / ((n : ℝ) + 2) ≤ ‖argumentDoublingContinuous‖ ^ 2 := by
      have h := argumentDoublingContinuous.le_opNorm (paretoPointHilbert (2 * n + 1))
      have hsq := (sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr h
      rw [mul_pow, argumentDoublingContinuous_apply,
        hilbertArgumentDoubling_point, point_norm_sq, point_norm_sq] at hsq
      have hp : 0 < positiveWeight (2 * (n + 1)) := by
        unfold positiveWeight
        positivity
      have hw := doubling_weight_identity (n + 1)
      have hi : 2 * n + 1 + 1 = 2 * (n + 1) := by omega
      rw [hi] at hsq
      have hprod := hw.symm.le.trans hsq
      norm_num only [Nat.cast_add, Nat.cast_one, add_assoc] at hprod
      nlinarith
    have hd : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (2 : ℝ)))
    have hi := tendsto_inv_atTop_zero.comp hd
    have ht : Tendsto (fun n : ℕ => 4 - 2 / ((n : ℝ) + 2)) atTop (𝓝 4) := by
      simpa only [Function.comp_def, mul_zero, sub_zero, div_eq_mul_inv] using
        tendsto_const_nhds.sub (hi.const_mul 2)
    have h4 := le_of_tendsto ht (Eventually.of_forall hb)
    nlinarith [norm_nonneg argumentDoublingContinuous]

private theorem doublingCarry_square_summable (d : ℕ) :
    Summable (fun n => positiveWeight n * doublingCarry d n ^ 2) := by
  apply weighted_summable_of_bounded (C := 1)
  intro n
  unfold doublingCarry
  split_ifs <;> norm_num

def doublingCarryHilbert (d : ℕ) (_hd : 0 < d) : ThresholdHilbert :=
  sequenceHilbert (doublingCarry d) (doublingCarry_square_summable d)

@[simp] theorem doublingCarryHilbert_sequence (d : ℕ) (hd : 0 < d) :
    hilbertSequence (doublingCarryHilbert d hd) = doublingCarry d := by
  apply hilbertSequence_sequenceHilbert
  simp [doublingCarry, Nat.not_le.mpr hd]

theorem hilbertArgumentDoubling_residue_even (q : ℕ) (hq : 0 < q) :
    hilbertArgumentDoubling (normalizedResidueHilbert (2 * q) (by omega)) =
      normalizedResidueHilbert q hq := by
  apply hilbertSequence_injective
  rw [hilbertArgumentDoubling_sequence, normalizedResidueHilbert_sequence,
    normalizedResidueHilbert_sequence]
  funext n
  exact residueFraction_double_even q n hq

theorem hilbertArgumentDoubling_residue (d : ℕ) (hd : 0 < d) :
    hilbertArgumentDoubling (normalizedResidueHilbert d hd) =
      (2 : ℝ) • normalizedResidueHilbert d hd - doublingCarryHilbert d hd := by
  apply hilbertSequence_injective
  change hilbertSequence (hilbertArgumentDoubling _) = hilbertSequenceLinear (_ - _)
  rw [map_sub, map_smul]
  change hilbertSequence (hilbertArgumentDoubling _) =
    (2 : ℝ) • hilbertSequence (normalizedResidueHilbert d hd) -
      hilbertSequence (doublingCarryHilbert d hd)
  simp only [hilbertArgumentDoubling_sequence, normalizedResidueHilbert_sequence,
    doublingCarryHilbert_sequence]
  funext n
  exact residueFraction_double d n hd

namespace CoefficientStabilization

theorem normalizedResidue_mem_closedSpace (d : ℕ) (hd : 0 < d) :
    normalizedResidueHilbert d hd ∈ closedSpace :=
  (Submodule.span ℝ (Set.range residueAtom)).le_topologicalClosure
    (normalizedResidue_mem_atomSpan d hd)

theorem argumentDoublingInvariant_iff_operator :
    ArgumentDoublingInvariant ↔
      ∀ f : ThresholdHilbert, f ∈ closedSpace →
        hilbertArgumentDoubling f ∈ closedSpace := by
  constructor
  · intro h f hf
    obtain ⟨g, hg, he⟩ := h f hf
    have hga : g = hilbertArgumentDoubling f := by
      apply hilbertSequence_injective
      rw [hilbertArgumentDoubling_sequence]
      exact he
    rwa [← hga]
  · intro h f hf
    exact ⟨hilbertArgumentDoubling f, h f hf, hilbertArgumentDoubling_sequence f⟩

theorem argumentDoublingInvariant_iff_generators :
    ArgumentDoublingInvariant ↔
      ∀ d : ℕ, ∀ hd : 2 ≤ d,
        hilbertArgumentDoubling (normalizedResidueHilbert d (by omega)) ∈ closedSpace := by
  rw [argumentDoublingInvariant_iff_operator]
  constructor
  · intro h d hd
    exact h _ (normalizedResidue_mem_closedSpace _ _)
  · intro h f hf
    let T : Submodule ℝ ThresholdHilbert :=
      closedSpace.comap argumentDoublingContinuous.toLinearMap
    have hspan : Submodule.span ℝ (Set.range residueAtom) ≤ T := by
      apply Submodule.span_le.mpr
      rintro g ⟨i, rfl⟩
      exact h (i + 2) (by omega)
    have hclosed : IsClosed (T : Set ThresholdHilbert) :=
      (Submodule.isClosed_topologicalClosure _).preimage argumentDoublingContinuous.continuous
    exact ((Submodule.span ℝ (Set.range residueAtom)).topologicalClosure_minimal
      hspan hclosed) hf

theorem doubled_residue_mem_iff_carry (d : ℕ) (hd : 0 < d) :
    hilbertArgumentDoubling (normalizedResidueHilbert d hd) ∈ closedSpace ↔
      doublingCarryHilbert d hd ∈ closedSpace := by
  have hg := closedSpace.smul_mem (2 : ℝ) (normalizedResidue_mem_closedSpace d hd)
  rw [hilbertArgumentDoubling_residue]
  constructor
  · intro h
    have := closedSpace.sub_mem hg h
    simpa only [sub_sub_cancel] using this
  · intro h
    exact closedSpace.sub_mem hg h

theorem argumentDoublingInvariant_iff_odd_carry :
    ArgumentDoublingInvariant ↔
      ∀ d : ℕ, ∀ hd : 3 ≤ d, Odd d →
        doublingCarryHilbert d (by omega) ∈ closedSpace := by
  rw [argumentDoublingInvariant_iff_generators]
  constructor
  · intro h d hd ho
    exact (doubled_residue_mem_iff_carry d (by omega)).mp (h d (by omega))
  · intro h d hd
    rcases Nat.even_or_odd d with he | ho
    · rcases he with ⟨q, hq⟩
      have heq : d = 2 * q := by omega
      have hqpos : 0 < q := by omega
      clear hq
      subst d
      rw [hilbertArgumentDoubling_residue_even]
      exact normalizedResidue_mem_closedSpace q hqpos
    · exact (doubled_residue_mem_iff_carry d (by omega)).mpr (h d (by
        rcases ho with ⟨k, hk⟩
        omega) ho)

/-- Conditional research reduction: the odd carry membership is still Open. -/
theorem riemannHypothesis_of_odd_carry
    (h : ∀ d : ℕ, ∀ hd : 3 ≤ d, Odd d →
      doublingCarryHilbert d (by omega) ∈ closedSpace) : RiemannHypothesis :=
  riemannHypothesis_of_argumentDoubling (argumentDoublingInvariant_iff_odd_carry.mpr h)

theorem exists_odd_carry_not_mem_of_not_RH (h : ¬ RiemannHypothesis) :
    ∃ d : ℕ, ∃ hd : 3 ≤ d, Odd d ∧
      doublingCarryHilbert d (by omega) ∉ closedSpace := by
  classical
  by_contra hn
  apply h
  apply riemannHypothesis_of_odd_carry
  intro d hd ho
  by_contra hm
  exact hn ⟨d, hd, ho, hm⟩


private theorem residue_reflection_step (d : ℕ) (hd : 2 ≤ d)
    (L : ℕ) (hL : 3 ≤ L) (hdiv : d ∣ L) :
    residueFraction d (L - 1) - residueFraction d (L - 2) = residueFraction d 1 := by
  have hm (j : ℕ) (hj : 0 < j) (hjd : j ≤ d) :
      (L - j) % d = d - j := by
    obtain ⟨k, hk⟩ := hdiv
    have hkpos : 0 < k := by
      by_contra hn
      have hz : k = 0 := by omega
      simp only [hz, Nat.mul_zero] at hk
      omega
    have he : L - j = (k - 1) * d + (d - j) := by
      calc
        L - j = d * ((k - 1) + 1) - j := by rw [Nat.sub_add_cancel hkpos, hk]
        _ = d * (k - 1) + (d - j) := by
          rw [Nat.mul_add, Nat.mul_one, Nat.add_sub_assoc hjd]
        _ = _ := by rw [Nat.mul_comm d (k - 1)]
    rw [he]
    simp [Nat.add_mod, Nat.mod_eq_of_lt (show d - j < d by omega)]
  simp only [residueFraction, hm 1 (by omega) (by omega),
    hm 2 (by omega) hd, Nat.mod_eq_of_lt (show 1 < d by omega),
    Nat.cast_sub (show 1 ≤ d by omega), Nat.cast_sub hd, Nat.cast_one, Nat.cast_ofNat]
  ring

private theorem finiteSpan_reflection {f : ThresholdHilbert}
    (hf : f ∈ Submodule.span ℝ (Set.range residueAtom)) :
    ∃ P : ℕ, 0 < P ∧ ∀ L : ℕ, P ∣ L → 3 ≤ L →
      hilbertSequence f (L - 1) - hilbertSequence f (L - 2) = hilbertSequence f 1 := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨i, rfl⟩ := hf
    refine ⟨i + 2, by omega, ?_⟩
    intro L hdiv hL
    simp only [residueAtom, normalizedResidueHilbert_sequence]
    exact residue_reflection_step (i + 2) (by omega) L hL hdiv
  | zero =>
    refine ⟨1, by omega, ?_⟩
    intro L _ _
    have hz : hilbertSequence (0 : ThresholdHilbert) = (0 : ℕ → ℝ) :=
      hilbertSequenceLinear.map_zero
    rw [hz]
    norm_num
  | add x y hx hy ihx ihy =>
    obtain ⟨P, hP, hxp⟩ := ihx
    obtain ⟨Q, hQ, hyq⟩ := ihy
    refine ⟨P * Q, Nat.mul_pos hP hQ, ?_⟩
    intro L hdiv hL
    have hxL := hxp L (dvd_trans (show P ∣ P * Q from ⟨Q, rfl⟩) hdiv) hL
    have hyL := hyq L (dvd_trans (show Q ∣ P * Q from ⟨P, Nat.mul_comm _ _⟩) hdiv) hL
    simp only [hilbertSequence_add, Pi.add_apply]
    linarith
  | smul c x hx ih =>
    obtain ⟨P, hP, hxp⟩ := ih
    refine ⟨P, hP, ?_⟩
    intro L hdiv hL
    simp only [hilbertSequence_smul, Pi.smul_apply, smul_eq_mul]
    rw [← mul_sub, hxp L hdiv hL]

/-- A finite-span obstruction; this does not rule out membership in the closure. -/
theorem doubled_three_not_mem_finiteSpan :
    hilbertArgumentDoubling (normalizedResidueHilbert 3 (by omega)) ∉
      Submodule.span ℝ (Set.range residueAtom) := by
  intro hm
  obtain ⟨P, hP, hp⟩ := finiteSpan_reflection hm
  have h := hp (3 * P) ⟨3, by omega⟩ (by omega)
  rw [hilbertArgumentDoubling_sequence, normalizedResidueHilbert_sequence] at h
  have h1 : (2 * (3 * P - 1)) % 3 = 1 := by omega
  have h2 : (2 * (3 * P - 2)) % 3 = 2 := by omega
  norm_num [residueFraction, h1, h2] at h


/-- A continuous Mellin separator gives a lower bound in the original full norm. -/
theorem closedSpace_mellin_distance_sq_lower_bound
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) (f u : ThresholdHilbert) (hu : u ∈ closedSpace) :
    (2 * s.re - 1) * ‖paretoMellin f s‖ ^ 2 ≤ ‖f - u‖ ^ 2 := by
  have hu0 := paretoMellin_zero_on_legalClosure_of_zeta {n : ℕ | 0 < n}
    (fun _ hn => hn) s hs hs1 hz (closedSpace_le_legalClosure hu)
  have he : paretoMellin (f - u) s = paretoMellin f s := by
    change paretoMellinContinuous s hs (f - u) = _
    rw [map_sub]
    change paretoMellin f s - paretoMellin u s = _
    rw [hu0, sub_zero]
  have hb := paretoMellin_norm_sq_le (f - u) s hs
  rw [he] at hb
  have hd : 0 < 2 * s.re - 1 := by linarith
  simpa only [mul_comm] using (le_div_iff₀ hd).mp hb

/-- An explicit nonzero Mellin value obstructs membership of a doubled generator. -/
theorem doubled_residue_not_mem_of_mellin_ne_zero
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) (d : ℕ) (hd : 0 < d)
    (hL : paretoMellin (hilbertArgumentDoubling (normalizedResidueHilbert d hd)) s ≠ 0) :
    hilbertArgumentDoubling (normalizedResidueHilbert d hd) ∉ closedSpace := by
  intro hm
  exact hL (paretoMellin_zero_on_legalClosure_of_zeta {n : ℕ | 0 < n}
    (fun _ hn => hn) s hs hs1 hz (closedSpace_le_legalClosure hm))


end CoefficientStabilization
end RiemannResearch.RH.Pareto
