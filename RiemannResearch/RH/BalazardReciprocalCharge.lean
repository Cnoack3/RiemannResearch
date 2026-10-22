import RiemannResearch.RH.MobiusReciprocalChargeBridge
import RiemannResearch.RH.MobiusQuotientEnergy
import RiemannResearch.Analysis.WeakConvergenceDenseTests

/-!
# Balazard's reciprocal charge sum rule in the physical Pareto model

Source: Michel Balazard, arXiv:1812.04309, Propositions 6--7.
The explicit quotient-window bound, actual PNT, and finite reindexing are
provided in the imported modules. No uniform-bound or cancellation
hypothesis remains in the final statement.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto

theorem reciprocalChargeRiesz_norm_sq_le (N : ℕ) :
    ‖reciprocalChargeRiesz N‖ ^ 2 ≤ 42 := by
  rw [hilbert_norm_weighted_sq]
  rw [tsum_eq_sum (s := Finset.Icc 1 N) (by
    intro k hk
    by_cases hk0 : k = 0
    · simp [hk0]
    · have hkN : N < k := by
        have hn : ¬ (1 ≤ k ∧ k ≤ N) := by simpa only [Finset.mem_Icc] using hk
        omega
      rw [reciprocalChargeRiesz_sequence N k (Nat.pos_of_ne_zero hk0)]
      have hkS : N < k + 1 := by omega
      simp [Nat.div_eq_of_lt hkN, Nat.div_eq_of_lt hkS,
        mobiusReciprocalSum])]
  have he (k : ℕ) (hk : k ∈ Finset.Icc 1 N) :
      positiveWeight k * hilbertSequence (reciprocalChargeRiesz N) k ^ 2 =
        (k : ℝ) * ((k : ℝ) + 1) * mobiusQuotientKernel N k ^ 2 := by
    have hk0 : 0 < k := (Finset.mem_Icc.mp hk).1
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hk0
    have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
    rw [reciprocalChargeRiesz_sequence N k hk0]
    unfold positiveWeight
    change 1 / ((k : ℝ) * ((k : ℝ) + 1)) *
      ((k : ℝ) * ((k : ℝ) + 1) * mobiusQuotientKernel N k) ^ 2 = _
    field_simp
  rw [Finset.sum_congr rfl he]
  exact mobiusQuotientKernel_square_energy_le N

theorem reciprocalChargeRiesz_norm_le (N : ℕ) :
    ‖reciprocalChargeRiesz N‖ ≤ 7 := by
  nlinarith [reciprocalChargeRiesz_norm_sq_le N, norm_nonneg (reciprocalChargeRiesz N)]

theorem paretoPoint_span_dense :
    (Submodule.span ℝ (Set.range paretoPointHilbert)).topologicalClosure = ⊤ := by
  have ho : (Submodule.span ℝ (Set.range paretoPointHilbert))ᗮ = ⊥ := by
    apply le_antisymm
    · intro f hf
      change f = 0
      apply hilbertSequence_injective
      funext k
      cases k with
      | zero => simp
      | succ k =>
        have h := hf _ (Submodule.subset_span ⟨k, rfl⟩)
        rw [real_inner_comm, inner_paretoPoint, hilbertGibbsPhysical_eq] at h
        have hv := (mul_eq_zero.mp h).resolve_left (ne_of_gt (paretoWeight_pos k))
        simpa using hv
    · exact bot_le
  rw [← Submodule.orthogonal_orthogonal_eq_closure, ho]
  simp

theorem reciprocalChargeRiesz_weak_zero (f : ThresholdHilbert) :
    Tendsto (fun N => inner ℝ f (reciprocalChargeRiesz N)) atTop (𝓝 0) := by
  apply RiemannResearch.Analysis.tendsto_inner_zero_of_mem_closure_span
    (S := Set.range paretoPointHilbert) (C := 7) (by norm_num)
    (Eventually.of_forall reciprocalChargeRiesz_norm_le)
  · rintro y ⟨k, rfl⟩
    have hq := mobiusQuotientKernel_tendsto_zero (k + 1) (by omega)
    have he (N : ℕ) : inner ℝ (paretoPointHilbert k) (reciprocalChargeRiesz N) =
        paretoWeight k * (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1) *
          mobiusQuotientKernel N (k + 1)) := by
      rw [real_inner_comm, inner_paretoPoint, hilbertGibbsPhysical_eq,
        reciprocalChargeRiesz_sequence N (k + 1) (by omega)]
      rfl
    simpa only [he, mul_zero] using
      (hq.const_mul (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1))).const_mul (paretoWeight k)
  · rw [paretoPoint_span_dense]
    trivial

/-- Balazard Proposition 7, with the physical D_0 realization and ordered cutoffs. -/
theorem mobiusDifference_reciprocal_tendsto_zero (f : ThresholdHilbert) :
    Tendsto (fun N => ∑ m ∈ Finset.Icc 1 N,
      mobiusDifferenceCLM m f / (m : ℝ)) atTop (𝓝 0) := by
  have he (N : ℕ) : inner ℝ f (reciprocalChargeRiesz N) =
      ∑ m ∈ Finset.Icc 1 N, mobiusDifferenceCLM m f / (m : ℝ) := by
    rw [real_inner_comm, reciprocalChargeRiesz_inner]
  simpa only [he] using reciprocalChargeRiesz_weak_zero f

/-- Removing the first charge gives its exact compensating scalar limit. -/
theorem mobiusDifference_reciprocal_from_two_tendsto (f : ThresholdHilbert) :
    Tendsto (fun N => ∑ m ∈ Finset.Icc 2 N,
      mobiusDifferenceCLM m f / (m : ℝ)) atTop (𝓝 (-hilbertSequence f 1)) := by
  have hfirst : mobiusDifferenceCLM 1 f = hilbertSequence f 1 := by
    simp [mobiusDifferenceCLM_apply, mobiusDifference]
  have he (N : ℕ) (hN : 1 ≤ N) :
      (∑ m ∈ Finset.Icc 2 N, mobiusDifferenceCLM m f / (m : ℝ)) =
        (∑ m ∈ Finset.Icc 1 N, mobiusDifferenceCLM m f / (m : ℝ)) -
          hilbertSequence f 1 := by
    have hu : ({1} : Finset ℕ) ∪ Finset.Icc 2 N = Finset.Icc 1 N := by
      ext m
      simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_Icc]
      omega
    have hd : Disjoint ({1} : Finset ℕ) (Finset.Icc 2 N) := by simp
    rw [← hu, Finset.sum_union hd]
    simp only [Finset.sum_singleton, Nat.cast_one, div_one, hfirst]
    ring
  have ht := (mobiusDifference_reciprocal_tendsto_zero f).sub_const (hilbertSequence f 1)
  simp only [zero_sub] at ht
  exact ht.congr' (by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    exact (he N hN).symm)

end RiemannResearch.RH.Pareto
