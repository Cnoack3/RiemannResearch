/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.RootComponentExactHeadEnergy
import RiemannResearch.RH.TwoSeedHeadEnergyGeometry
import RiemannResearch.RH.DilationWaveletNoRiesz
import RiemannResearch.RH.DilationWaveletClosure

/-!
# Unconditional unboundedness of the arithmetic root projection

Source: continuation of the two-seed research, 14 September 2026. Adjacent
normalized binary wavelets at m = 6^(k+1) and m+1 are actual finite legal
vectors of norm one. The root projection keeps the first and kills the
second, while their full signed difference tends to zero. Each wavelet is a
two-generator combination; the difference uses four actual generators.

The construction vanishes below m. Hence the projection is unbounded even
on legal vectors with an arbitrary fixed zero head. No RH or approximation
of the constant is assumed, and every infinite tail remains in the norm.
-/

namespace RiemannResearch.RH.Pareto.RootComponentUnbounded

open scoped BigOperators Topology
open Filter TwoSeedThreshold RootComponentExactHeadEnergy

noncomputable section
attribute [local instance] Classical.propDecidable

private def rootProjectionLinear : (ℕ → ℝ) →ₗ[ℝ] (ℕ → ℝ) where
  toFun := roughComponentProjection 1
  map_add' := roughComponentProjection_add 1
  map_smul' := roughComponentProjection_smul 1

theorem rootProjection_dilation (a m : ℕ) (ha : a = 2 ∨ a = 3) (hm : 0 < m) :
    roughComponentProjection 1 (dilation m (residue a)) =
      if InRoughComponent 1 m then dilation m (residue a) else 0 := by
  have he : certificateGenerator a m = dilation m (residue a) := by
    funext n
    exact certificateGenerator_eq_dilation a m n
  funext n
  have h := roughComponentProjection_generator 1 a m n (by omega) (by decide) ha hm
  by_cases hx : InRoughComponent 1 m <;>
    simpa only [he, hx, ↓reduceIte, Pi.zero_apply] using h

/-- The two raw generators in one binary wavelet belong to the same
arithmetic component, so no endpoint is projected separately. -/
theorem rootProjection_binary_wavelet (m : ℕ) (hm : 0 < m) :
    roughComponentProjection 1 (dilationWaveletSequence 2 m) =
      if InRoughComponent 1 m then dilationWaveletSequence 2 m else 0 := by
  rw [dilationWaveletSequence_generator 2 m (by omega) hm]
  change rootProjectionLinear (_ - _) = _
  rw [map_sub]
  change roughComponentProjection 1 ((1 / (m : ℝ)) • dilation m (residue 2)) -
    roughComponentProjection 1 ((1 / ((2 * m : ℕ) : ℝ)) •
      dilation (2 * m) (residue 2)) = _
  rw [roughComponentProjection_smul, roughComponentProjection_smul,
    rootProjection_dilation 2 m (by simp) hm,
    rootProjection_dilation 2 (2 * m) (by simp) (by omega)]
  have hsame : InRoughComponent 1 (2 * m) ↔ InRoughComponent 1 m :=
    inRoughComponent_mul_iff 1 2 m (by omega) (by decide) (by decide)
  by_cases hx : InRoughComponent 1 m <;>
    simp [hsame, hx]

theorem normalizedBinaryWavelet_mem_legal (m : ℕ) (hm : 0 < m) :
    normalizedBinaryWavelet m hm ∈ hilbertLegalSubspace ({2, 3} : Set ℕ) := by
  unfold normalizedBinaryWavelet NormedSpace.normalize
  exact (hilbertLegalSubspace ({2, 3} : Set ℕ)).smul_mem _
    (dilationWaveletHilbert_mem_legal ({2, 3} : Set ℕ) 2 m (by simp) (by omega) hm)

theorem rootProjection_normalizedBinaryWavelet (m : ℕ) (hm : 0 < m) :
    roughComponentProjection 1 (hilbertSequence (normalizedBinaryWavelet m hm)) =
      if InRoughComponent 1 m then hilbertSequence (normalizedBinaryWavelet m hm) else 0 := by
  unfold normalizedBinaryWavelet NormedSpace.normalize
  simp only [hilbertSequence_smul, hilbertSequence_dilationWaveletHilbert,
    roughComponentProjection_smul]
  rw [rootProjection_binary_wavelet m hm]
  by_cases hx : InRoughComponent 1 m <;> simp [hx]

def rootScale (k : ℕ) : ℕ := 6 ^ (k + 1)

theorem rootScale_pos (k : ℕ) : 0 < rootScale k := by
  unfold rootScale
  positivity

theorem succ_le_rootScale (k : ℕ) : k + 1 ≤ rootScale k := by
  unfold rootScale
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [pow_succ]
    nlinarith

theorem rootScale_mem_root (k : ℕ) : InRoughComponent 1 (rootScale k) := by
  refine ⟨k, ?_⟩
  unfold smoothComponentVertices rootScale
  exact Finset.mem_image.mpr ⟨6 ^ (k + 1),
    Nat.mem_divisors.mpr ⟨dvd_refl _, by positivity⟩, by simp⟩

theorem rootScale_succ_coprime (k : ℕ) : Nat.Coprime (rootScale k + 1) 6 := by
  apply Nat.coprime_comm.mp
  change Nat.gcd 6 (6 ^ (k + 1) + 1) = 1
  rw [Nat.gcd_rec]
  norm_num [Nat.add_mod, Nat.pow_mod, pow_succ]

theorem rootScale_succ_not_mem_root (k : ℕ) :
    ¬ InRoughComponent 1 (rootScale k + 1) := by
  rintro ⟨L, hL⟩
  obtain ⟨d, hd, he⟩ := Finset.mem_image.mp hL
  have he' : d = rootScale k + 1 := by simpa only [one_mul] using he
  have hdiv : rootScale k + 1 ∣ 6 ^ (L + 1) := by
    rw [← he']
    exact Nat.dvd_of_mem_divisors hd
  have hcop : Nat.Coprime (rootScale k + 1) (6 ^ (L + 1)) := by
    simpa using (rootScale_succ_coprime k).pow 1 (L + 1)
  have hone : rootScale k + 1 = 1 := by
    calc
      rootScale k + 1 = Nat.gcd (rootScale k + 1) (6 ^ (L + 1)) :=
        (Nat.gcd_eq_left_iff_dvd.mpr hdiv).symm
      _ = 1 := hcop
  have hp := rootScale_pos k
  omega

/-- Four finite legal generators, including the signed mixed cancellation. -/
def cancellationPacket (k : ℕ) : ThresholdHilbert :=
  normalizedBinaryWavelet (rootScale k) (rootScale_pos k) -
    normalizedBinaryWavelet (rootScale k + 1) (by omega)

theorem cancellationPacket_mem_legal (k : ℕ) :
    cancellationPacket k ∈ hilbertLegalSubspace ({2, 3} : Set ℕ) :=
  (hilbertLegalSubspace ({2, 3} : Set ℕ)).sub_mem
    (normalizedBinaryWavelet_mem_legal _ (rootScale_pos k))
    (normalizedBinaryWavelet_mem_legal _ (by omega))

/-- The arithmetic projection is evaluated exactly on the entire packet. -/
theorem cancellationPacket_root (k : ℕ) :
    rootComponent (cancellationPacket k) (cancellationPacket_mem_legal k) =
      normalizedBinaryWavelet (rootScale k) (rootScale_pos k) := by
  apply hilbertSequence_injective
  rw [rootComponent_sequence]
  have hseq : hilbertSequence (cancellationPacket k) =
      hilbertSequence (normalizedBinaryWavelet (rootScale k) (rootScale_pos k)) -
        hilbertSequence (normalizedBinaryWavelet (rootScale k + 1) (by omega)) := by
    change hilbertSequenceLinear (_ - _) = _
    exact map_sub _ _ _
  rw [hseq]
  change rootProjectionLinear (_ - _) = _
  rw [map_sub]
  change roughComponentProjection 1
      (hilbertSequence (normalizedBinaryWavelet (rootScale k) (rootScale_pos k))) -
    roughComponentProjection 1
      (hilbertSequence (normalizedBinaryWavelet (rootScale k + 1) (by omega))) = _
  rw [rootProjection_normalizedBinaryWavelet, rootProjection_normalizedBinaryWavelet]
  simp [rootScale_mem_root, rootScale_succ_not_mem_root]

theorem cancellationPacket_root_norm (k : ℕ) :
    ‖rootComponent (cancellationPacket k) (cancellationPacket_mem_legal k)‖ = 1 := by
  rw [cancellationPacket_root, normalizedBinaryWavelet_norm]

/-- This is the complete normalized norm, not an absolute estimate for
vanishing unnormalized wavelets. It tends to zero while the projected norm
is exactly one. -/
theorem cancellationPacket_energy_tendsto_zero :
    Tendsto (fun k => ‖cancellationPacket k‖ ^ 2) atTop (𝓝 0) := by
  apply Analysis.NormalizedPairObstruction.tendsto_zero_of_cutoff_bound _ (64 / Real.pi)
    (fun _ => sq_nonneg _)
  intro k J hJ
  have hb := normalizedBinaryWavelet_nearby_bound (rootScale k) J (rootScale_pos k) hJ
  have hscale : (k : ℝ) + 1 ≤ (rootScale k : ℝ) := by
    exact_mod_cast succ_le_rootScale k
  have hden : (k : ℝ) + 1 ≤ (rootScale k : ℝ) + 1 := by linarith
  have hle := div_le_div_of_nonneg_left (Nat.cast_nonneg J)
    (by positivity : 0 < (k : ℝ) + 1) hden
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 64 / Real.pi)
  exact add_le_add hle le_rfl

theorem normalizedBinaryWavelet_head_zero (m : ℕ) (hm : 0 < m)
    (n : ℕ) (hn : n < m) : hilbertSequence (normalizedBinaryWavelet m hm) n = 0 := by
  unfold normalizedBinaryWavelet NormedSpace.normalize
  rw [hilbertSequence_smul, hilbertSequence_dilationWaveletHilbert]
  have hn2 : n < 2 * m := by omega
  simp [dilationWaveletSequence, digitSequence, Pi.smul_apply,
    Nat.div_eq_of_lt hn, Nat.div_eq_of_lt hn2]

theorem cancellationPacket_head_zero (k n : ℕ) (hn : n < rootScale k) :
    hilbertSequence (cancellationPacket k) n = 0 := by
  have hseq : hilbertSequence (cancellationPacket k) =
      hilbertSequence (normalizedBinaryWavelet (rootScale k) (rootScale_pos k)) -
        hilbertSequence (normalizedBinaryWavelet (rootScale k + 1) (by omega)) := by
    change hilbertSequenceLinear (_ - _) = _
    exact map_sub _ _ _
  rw [hseq]
  simp only [Pi.sub_apply]
  rw [normalizedBinaryWavelet_head_zero _ _ n hn,
    normalizedBinaryWavelet_head_zero _ _ n (by omega)]
  ring

/-- The bad component-projection packets are orthogonal to the actual
canonical optimizer whenever they lie beyond its prescribed head. -/
theorem closedMinimizer_orthogonal_packet (N k : ℕ) (hNk : N ≤ k) :
    inner ℝ (TwoSeedExactHeadEnergy.closedMinimizer N) (cancellationPacket k) = 0 := by
  apply TwoSeedExactHeadEnergy.closedMinimizer_orthogonal_zeroHead
  apply (TwoSeedExactHeadEnergy.zeroHeadLegal_mem_iff N _).mpr
  refine ⟨Submodule.le_topologicalClosure _ (cancellationPacket_mem_legal k), ?_⟩
  intro j hj
  apply cancellationPacket_head_zero
  have hs := succ_le_rootScale k
  omega

/-- The small packets are nearly flat legal directions, not a lower bound
on the canonical source energy. Their exact added cost is retained. -/
theorem closedMinimizer_packet_energy (N k : ℕ) (hNk : N ≤ k) (t : ℝ) :
    ‖TwoSeedExactHeadEnergy.closedMinimizer N + t • cancellationPacket k‖ ^ 2 =
      TwoSeedExactHeadEnergy.energy N + t ^ 2 * ‖cancellationPacket k‖ ^ 2 := by
  rw [RiemannResearch.LinearAlgebra.TwoChannelCancellation.norm_add_sq,
    real_inner_smul_right, closedMinimizer_orthogonal_packet N k hNk,
    mul_zero, mul_zero, add_zero, TwoSeedExactHeadEnergy.closedMinimizer_norm_sq,
    norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

/-- Every fixed-head tangent space already contains arbitrarily small full
vectors with root component of norm one. -/
theorem exists_small_legal_zero_head_with_unit_root (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : ThresholdHilbert, ∃ hf : f ∈ hilbertLegalSubspace ({2, 3} : Set ℕ),
      (∀ n, 0 < n → n ≤ N → hilbertSequence f n = 0) ∧
        ‖f‖ ^ 2 < ε ∧ ‖rootComponent f hf‖ = 1 := by
  have he := cancellationPacket_energy_tendsto_zero.eventually_lt_const hε
  obtain ⟨k, hkN, hkε⟩ := ((eventually_ge_atTop N).and he).exists
  refine ⟨cancellationPacket k, cancellationPacket_mem_legal k, ?_, hkε,
    cancellationPacket_root_norm k⟩
  intro n hn hnN
  apply cancellationPacket_head_zero
  have hs := succ_le_rootScale k
  omega

/-- There is no quadratic bound for the arithmetic projection, even on
vectors vanishing at every coordinate of an arbitrary fixed finite head. -/
theorem no_root_energy_bound_on_zero_head (N : ℕ) :
    ¬ ∃ C : ℝ, ∀ f : ThresholdHilbert,
      ∀ hf : f ∈ hilbertLegalSubspace ({2, 3} : Set ℕ),
      (∀ n, 0 < n → n ≤ N → hilbertSequence f n = 0) →
      ‖rootComponent f hf‖ ^ 2 ≤ C * ‖f‖ ^ 2 := by
  rintro ⟨C, hC⟩
  have ht : Tendsto (fun k => C * ‖cancellationPacket k‖ ^ 2) atTop (𝓝 0) := by
    simpa only [mul_zero] using cancellationPacket_energy_tendsto_zero.const_mul C
  obtain ⟨k, hkN, hk⟩ :=
    ((eventually_ge_atTop N).and (ht.eventually_lt_const (by norm_num : (0 : ℝ) < 1))).exists
  have hzero : ∀ n, 0 < n → n ≤ N → hilbertSequence (cancellationPacket k) n = 0 := by
    intro n hn hnN
    apply cancellationPacket_head_zero
    have hs := succ_le_rootScale k
    omega
  have hb := hC (cancellationPacket k) (cancellationPacket_mem_legal k) hzero
  rw [cancellationPacket_root_norm, one_pow] at hb
  exact not_lt_of_ge hb hk

/-- Unconditional failure of a continuous Hilbert extension of the actual
root projection on all finite legal vectors. -/
theorem rootProjection_no_continuous_extension :
    ¬ ∃ T : ThresholdHilbert →L[ℝ] ThresholdHilbert,
      ∀ f ∈ hilbertLegalSubspace ({2, 3} : Set ℕ),
        hilbertSequence (T f) = roughComponentProjection 1 (hilbertSequence f) := by
  rintro ⟨T, hT⟩
  apply no_root_energy_bound_on_zero_head 0
  refine ⟨‖T‖ ^ 2, ?_⟩
  intro f hf hzero
  have he : rootComponent f hf = T f := by
    apply hilbertSequence_injective
    rw [rootComponent_sequence, hT f hf]
  rw [he]
  have hb := T.le_opNorm f
  have hs := mul_self_le_mul_self (norm_nonneg (T f)) hb
  simpa only [← pow_two, mul_pow] using hs

theorem rootComponent_add (f g : ThresholdHilbert)
    (hf : f ∈ hilbertLegalSubspace ({2, 3} : Set ℕ))
    (hg : g ∈ hilbertLegalSubspace ({2, 3} : Set ℕ)) :
    rootComponent (f + g) ((hilbertLegalSubspace ({2, 3} : Set ℕ)).add_mem hf hg) =
      rootComponent f hf + rootComponent g hg := by
  apply hilbertSequence_injective
  rw [rootComponent_sequence]
  change rootProjectionLinear (hilbertSequenceLinear (f + g)) =
    hilbertSequenceLinear (rootComponent f hf + rootComponent g hg)
  rw [map_add, map_add, map_add]
  change roughComponentProjection 1 (hilbertSequence f) +
    roughComponentProjection 1 (hilbertSequence g) =
    hilbertSequence (rootComponent f hf) + hilbertSequence (rootComponent g hg)
  rw [rootComponent_sequence, rootComponent_sequence]

theorem rootComponent_smul (t : ℝ) (f : ThresholdHilbert)
    (hf : f ∈ hilbertLegalSubspace ({2, 3} : Set ℕ)) :
    rootComponent (t • f) ((hilbertLegalSubspace ({2, 3} : Set ℕ)).smul_mem t hf) =
      t • rootComponent f hf := by
  apply hilbertSequence_injective
  rw [rootComponent_sequence, hilbertSequence_smul, roughComponentProjection_smul,
    hilbertSequence_smul, rootComponent_sequence]

/-- Full-energy near-optimality alone gives no arithmetic component bound:
every neighborhood inside the same finite-head
fiber contains finite legal vectors with arbitrarily large root norm. -/
theorem exists_nearby_head_preserving_large_root
    (F : ThresholdHilbert) (hF : F ∈ hilbertLegalSubspace ({2, 3} : Set ℕ))
    (N : ℕ) {ε B : ℝ} (hε : 0 < ε) (hB : 0 < B) :
    ∃ G : ThresholdHilbert, ∃ hG : G ∈ hilbertLegalSubspace ({2, 3} : Set ℕ),
      (∀ n, 0 < n → n ≤ N → hilbertSequence G n = hilbertSequence F n) ∧
        ‖G - F‖ < ε ∧ B < ‖rootComponent G hG‖ := by
  let t : ℝ := B + ‖rootComponent F hF‖ + 1
  have ht : 0 < t := by dsimp [t]; positivity
  obtain ⟨h, hh, hzero, hsmall, hroot⟩ :=
    exists_small_legal_zero_head_with_unit_root N (sq_pos_of_pos (div_pos hε ht))
  let G : ThresholdHilbert := F + t • h
  have hG : G ∈ hilbertLegalSubspace ({2, 3} : Set ℕ) :=
    (hilbertLegalSubspace ({2, 3} : Set ℕ)).add_mem hF
      ((hilbertLegalSubspace ({2, 3} : Set ℕ)).smul_mem t hh)
  refine ⟨G, hG, ?_, ?_, ?_⟩
  · intro n hn hnN
    have he : hilbertSequence G = hilbertSequence F + t • hilbertSequence h := by
      change hilbertSequenceLinear (F + t • h) = _
      rw [map_add, map_smul]
      rfl
    rw [he]
    simp [hzero n hn hnN]
  · have he : G - F = t • h := by dsimp [G]; abel
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    have hn : ‖h‖ < ε / t := by
      nlinarith [norm_nonneg h, div_pos hε ht]
    have hm := (lt_div_iff₀ ht).mp hn
    nlinarith
  · have he : rootComponent G hG = rootComponent F hF + t • rootComponent h hh := by
      dsimp [G]
      rw [rootComponent_add F (t • h) hF
        ((hilbertLegalSubspace ({2, 3} : Set ℕ)).smul_mem t hh),
        rootComponent_smul t h hh]
    rw [he]
    have hr := norm_sub_norm_le (t • rootComponent h hh) (-rootComponent F hF)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht, hroot, mul_one,
      norm_neg, sub_neg_eq_add, add_comm (t • rootComponent h hh) (rootComponent F hF)] at hr
    dsimp [t] at hr
    linarith

end
end RiemannResearch.RH.Pareto.RootComponentUnbounded
