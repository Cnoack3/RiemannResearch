import RiemannResearch.RH.DyadicRegularizedNorm
import RiemannResearch.Analysis.AbelCoboundary

/-!
# An exact finite critical norm in the actual dyadic quotient

Source: user-provided September 10, 2026 dyadic-regularization ledger,
critical quotient provider (N5). The operator proof below develops the finite
norm and Gram identities needed by that provider.

Write T = T₂ and D = I - T T* / 2. We construct the genuinely convergent
series L(u) = Σ_j (T/2)^j u. On ker T*, it satisfies Q u = L(u)/2 and
‖Q u‖² = ‖u‖²/2. Consequently, if (T*)^N f = 0, then

  ‖Q f‖² = ‖D (Σ_{j<N} 2^(-j) (T*)^j f)‖² / 2.

The finite identity retains its exact terminal term without the nilpotence
hypothesis. All operators are the existing physical Hilbert operators. There
are no supplied projection, convergence, norm, or arithmetic estimates here.
This establishes a finite critical-norm provider, not the uniform arithmetic
norm bound, the full boundary fold theorem, or RH.
-/

namespace RiemannResearch.RH.Pareto

open scoped BigOperators
open RiemannResearch.Analysis.AbelCoboundary

noncomputable section

def dyadicHalfDilation : ThresholdHilbert →L[ℝ] ThresholdHilbert :=
  (1 / 2 : ℝ) • hilbertDilationContinuous 2 (by norm_num)

@[simp] theorem dyadicHalfDilation_apply (f : ThresholdHilbert) :
    dyadicHalfDilation f = (1 / 2 : ℝ) • hilbertDilation 2 (by norm_num) f := rfl

theorem dyadicHalfDilation_norm_sq (f : ThresholdHilbert) :
    ‖dyadicHalfDilation f‖ ^ 2 = (1 / 2 : ℝ) * ‖f‖ ^ 2 := by
  rw [dyadicHalfDilation_apply, norm_smul, Real.norm_eq_abs, mul_pow,
    hilbertDilation_norm_sq]
  norm_num
  ring

theorem dyadicHalfDilation_norm_le (f : ThresholdHilbert) :
    ‖dyadicHalfDilation f‖ ≤ (3 / 4 : ℝ) * ‖f‖ := by
  nlinarith [dyadicHalfDilation_norm_sq f, norm_nonneg (dyadicHalfDilation f),
    norm_nonneg f, sq_nonneg ‖f‖]

@[simp] theorem dyadicAdjoint_halfDilation (f : ThresholdHilbert) :
    hilbertDilationAdjoint 2 (by norm_num) (dyadicHalfDilation f) = f := by
  rw [dyadicHalfDilation_apply, map_smul, hilbertDilationAdjoint_dilation, smul_smul]
  norm_num

theorem dyadicHalfDilation_orbit_norm_le (u : ThresholdHilbert) (j : ℕ) :
    ‖orbit dyadicHalfDilation u j‖ ≤ (3 / 4 : ℝ) ^ j * ‖u‖ := by
  induction j with
  | zero => simp only [orbit_zero, pow_zero, one_mul, le_refl]
  | succ j ih =>
      calc
        _ ≤ (3 / 4 : ℝ) * ‖orbit dyadicHalfDilation u j‖ :=
          dyadicHalfDilation_norm_le _
        _ ≤ (3 / 4 : ℝ) * ((3 / 4 : ℝ) ^ j * ‖u‖) :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (3 / 4 : ℝ) ^ (j + 1) * ‖u‖ := by rw [pow_succ]; ring

/-- The eigenvector construction has actual norm-convergent series. -/
theorem dyadicKernelLift_summable (u : ThresholdHilbert) :
    Summable (orbit dyadicHalfDilation u) := by
  have hg := (summable_geometric_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 3 / 4) (by norm_num : (3 / 4 : ℝ) < 1)).mul_right ‖u‖
  exact (Summable.of_nonneg_of_le (fun j => norm_nonneg _)
    (fun j => dyadicHalfDilation_orbit_norm_le u j) hg).of_norm

def dyadicKernelLift (u : ThresholdHilbert) : ThresholdHilbert :=
  ∑' j : ℕ, orbit dyadicHalfDilation u j

theorem dyadicKernelLift_eq (u : ThresholdHilbert) :
    dyadicKernelLift u = u + dyadicHalfDilation (dyadicKernelLift u) := by
  calc
    _ = orbit dyadicHalfDilation u 0 +
        ∑' j : ℕ, orbit dyadicHalfDilation u (j + 1) :=
      (dyadicKernelLift_summable u).tsum_eq_zero_add
    _ = u + dyadicHalfDilation (dyadicKernelLift u) := by
      rw [dyadicKernelLift, dyadicHalfDilation.map_tsum (dyadicKernelLift_summable u)]
      rfl

theorem dyadicKernelLift_fixed (u : ThresholdHilbert)
    (hu : hilbertDilationAdjoint 2 (by norm_num) u = 0) :
    hilbertDilationAdjoint 2 (by norm_num) (dyadicKernelLift u) =
      dyadicKernelLift u := by
  have h := congrArg (hilbertDilationAdjoint 2 (by norm_num)) (dyadicKernelLift_eq u)
  simpa only [map_add, hu, dyadicAdjoint_halfDilation, zero_add] using h

/-- Exact reconstruction of the actual quotient projection on the adjoint kernel. -/
theorem dyadicQuotientProjection_eq_half_kernelLift (u : ThresholdHilbert)
    (hu : hilbertDilationAdjoint 2 (by norm_num) u = 0) :
    dyadicQuotientProjection u = (1 / 2 : ℝ) • dyadicKernelLift u := by
  have hq : dyadicQuotientProjection (dyadicKernelLift u) = dyadicKernelLift u :=
    dyadicQuotientProjection_eq_self
      ((mem_dyadicQuotientSubspace_iff _).mpr (dyadicKernelLift_fixed u hu))
  have h := congrArg dyadicQuotientProjection (dyadicKernelLift_eq u)
  rw [map_add, dyadicHalfDilation_apply, map_smul,
    dyadicQuotientProjection_dilation_two, hq] at h
  calc
    _ = dyadicKernelLift u - (1 / 2 : ℝ) • dyadicKernelLift u :=
      eq_sub_iff_add_eq.mpr h.symm
    _ = (1 / 2 : ℝ) • dyadicKernelLift u := by module

theorem dyadicKernelLift_norm_sq (u : ThresholdHilbert)
    (hu : hilbertDilationAdjoint 2 (by norm_num) u = 0) :
    ‖dyadicKernelLift u‖ ^ 2 = 2 * ‖u‖ ^ 2 := by
  have hi : inner ℝ u (hilbertDilation 2 (by norm_num) (dyadicKernelLift u)) = 0 := by
    calc
      _ = inner ℝ (hilbertDilation 2 (by norm_num) (dyadicKernelLift u)) u :=
        real_inner_comm _ _
      _ = inner ℝ (dyadicKernelLift u) (hilbertDilationAdjoint 2 (by norm_num) u) :=
        (ContinuousLinearMap.adjoint_inner_right
          (hilbertDilationContinuous 2 (by norm_num)) (dyadicKernelLift u) u).symm
      _ = 0 := by rw [hu]; simp
  have hs : inner ℝ u (dyadicHalfDilation (dyadicKernelLift u)) = 0 := by
    rw [dyadicHalfDilation_apply, real_inner_smul_right, hi, mul_zero]
  have he := norm_add_sq_real u (dyadicHalfDilation (dyadicKernelLift u))
  rw [← dyadicKernelLift_eq u, hs, dyadicHalfDilation_norm_sq] at he
  nlinarith

/-- The critical factor 1/2 is proved for the physical projection. -/
theorem dyadicQuotientProjection_kernel_norm_sq (u : ThresholdHilbert)
    (hu : hilbertDilationAdjoint 2 (by norm_num) u = 0) :
    ‖dyadicQuotientProjection u‖ ^ 2 = (1 / 2 : ℝ) * ‖u‖ ^ 2 := by
  rw [dyadicQuotientProjection_eq_half_kernelLift u hu, norm_smul,
    Real.norm_eq_abs, mul_pow, dyadicKernelLift_norm_sq u hu]
  norm_num
  ring

theorem dyadicQuotientProjection_kernel_inner (u v : ThresholdHilbert)
    (hu : hilbertDilationAdjoint 2 (by norm_num) u = 0)
    (hv : hilbertDilationAdjoint 2 (by norm_num) v = 0) :
    inner ℝ (dyadicQuotientProjection u) (dyadicQuotientProjection v) =
      (1 / 2 : ℝ) * inner ℝ u v := by
  have huv : hilbertDilationAdjoint 2 (by norm_num) (u + v) = 0 := by
    rw [map_add, hu, hv, zero_add]
  have h := dyadicQuotientProjection_kernel_norm_sq (u + v) huv
  rw [map_add, norm_add_sq_real, norm_add_sq_real,
    dyadicQuotientProjection_kernel_norm_sq u hu,
    dyadicQuotientProjection_kernel_norm_sq v hv] at h
  linarith

/-- The genuine complementary block projection D = I - T₂ T₂* / 2. -/
def dyadicKernelDefect : ThresholdHilbert →L[ℝ] ThresholdHilbert :=
  ContinuousLinearMap.id ℝ ThresholdHilbert - hilbertBlockProjection 2 (by norm_num)

@[simp] theorem dyadicKernelDefect_apply (f : ThresholdHilbert) :
    dyadicKernelDefect f = f - hilbertBlockProjection 2 (by norm_num) f := rfl

@[simp] theorem dyadicKernelDefect_adjoint_zero (f : ThresholdHilbert) :
    hilbertDilationAdjoint 2 (by norm_num) (dyadicKernelDefect f) = 0 := by
  rw [dyadicKernelDefect_apply, map_sub, hilbertBlockProjection_apply,
    map_smul, hilbertDilationAdjoint_dilation, smul_smul]
  norm_num

theorem dyadicQuotientProjection_kernelDefect (f : ThresholdHilbert) :
    dyadicQuotientProjection (dyadicKernelDefect f) =
      dyadicQuotientProjection f -
        (1 / 2 : ℝ) • dyadicQuotientProjection (hilbertDilationAdjoint 2 (by norm_num) f) := by
  rw [dyadicKernelDefect_apply, map_sub, hilbertBlockProjection_apply,
    map_smul, dyadicQuotientProjection_dilation_two]
  norm_num

def dyadicAdjointPacket (N : ℕ) (f : ThresholdHilbert) : ThresholdHilbert :=
  ∑ j ∈ Finset.range N,
    (1 / 2 : ℝ) ^ j • orbit (hilbertDilationAdjoint 2 (by norm_num)) f j

/-- Exact finite critical reconstruction, retaining the complete terminal term. -/
theorem dyadicQuotientProjection_kernelDefect_packet (N : ℕ) (f : ThresholdHilbert) :
    dyadicQuotientProjection (dyadicKernelDefect (dyadicAdjointPacket N f)) =
      dyadicQuotientProjection f - (1 / 2 : ℝ) ^ N •
        dyadicQuotientProjection (orbit (hilbertDilationAdjoint 2 (by norm_num)) f N) := by
  simp only [dyadicAdjointPacket, map_sum, map_smul, dyadicQuotientProjection_kernelDefect]
  simpa only [orbit_zero, orbit_succ] using
    finite_discounted (1 / 2 : ℝ)
      (fun j => dyadicQuotientProjection (orbit (hilbertDilationAdjoint 2 (by norm_num)) f j)) N

/-- Unconditional exact critical norm whenever the displayed physical adjoint
iterate vanishes; no boundary-norm or arbitrary-projection premise is supplied. -/
theorem dyadicQuotientProjection_norm_sq_of_adjoint_nilpotent
    (N : ℕ) (f : ThresholdHilbert)
    (hf : orbit (hilbertDilationAdjoint 2 (by norm_num)) f N = 0) :
    ‖dyadicQuotientProjection f‖ ^ 2 =
      (1 / 2 : ℝ) * ‖dyadicKernelDefect (dyadicAdjointPacket N f)‖ ^ 2 := by
  have h := dyadicQuotientProjection_kernelDefect_packet N f
  rw [hf, map_zero, smul_zero, sub_zero] at h
  rw [← h]
  exact dyadicQuotientProjection_kernel_norm_sq _ (dyadicKernelDefect_adjoint_zero _)

/-- Exact finite Gram entries follow from the same physical construction. -/
theorem dyadicQuotientProjection_inner_of_adjoint_nilpotent
    (N M : ℕ) (f g : ThresholdHilbert)
    (hf : orbit (hilbertDilationAdjoint 2 (by norm_num)) f N = 0)
    (hg : orbit (hilbertDilationAdjoint 2 (by norm_num)) g M = 0) :
    inner ℝ (dyadicQuotientProjection f) (dyadicQuotientProjection g) =
      (1 / 2 : ℝ) * inner ℝ (dyadicKernelDefect (dyadicAdjointPacket N f))
        (dyadicKernelDefect (dyadicAdjointPacket M g)) := by
  have h1 := dyadicQuotientProjection_kernelDefect_packet N f
  have h2 := dyadicQuotientProjection_kernelDefect_packet M g
  rw [hf, map_zero, smul_zero, sub_zero] at h1
  rw [hg, map_zero, smul_zero, sub_zero] at h2
  rw [← h1, ← h2]
  exact dyadicQuotientProjection_kernel_inner _ _
    (dyadicKernelDefect_adjoint_zero _) (dyadicKernelDefect_adjoint_zero _)

/-- Exact physical pairing of every dyadic adjoint iterate. -/
theorem dyadicAdjointOrbit_inner (N : ℕ) (f g : ThresholdHilbert) :
    inner ℝ g (orbit (hilbertDilationAdjoint 2 (by norm_num)) f N) =
      inner ℝ (hilbertDilation (2 ^ N) (by positivity) g) f := by
  induction N generalizing g with
  | zero => simp only [orbit_zero, pow_zero, hilbertDilation_one]
  | succ N ih =>
      calc
        _ = inner ℝ (hilbertDilation 2 (by norm_num) g)
            (orbit (hilbertDilationAdjoint 2 (by norm_num)) f N) :=
          ContinuousLinearMap.adjoint_inner_right
            (hilbertDilationContinuous 2 (by norm_num)) g _
        _ = inner ℝ (hilbertDilation (2 ^ N) (by positivity)
            (hilbertDilation 2 (by norm_num) g)) f := ih _
        _ = _ := by simp only [hilbertDilation_comp, pow_succ]

/-- A physical support cutoff supplies the terminal-vanishing hypothesis;
no abstract nilpotence provider is needed for finite supported vectors. -/
theorem dyadicAdjointOrbit_eq_zero_of_support
    (N : ℕ) (f : ThresholdHilbert)
    (hf : ∀ k : ℕ, 2 ^ N ≤ k → hilbertSequence f k = 0) :
    orbit (hilbertDilationAdjoint 2 (by norm_num)) f N = 0 := by
  apply hilbertSequence_injective
  change hilbertSequenceLinear (orbit (hilbertDilationAdjoint 2 (by norm_num)) f N) =
    hilbertSequenceLinear 0
  rw [map_zero]
  funext k
  change hilbertSequence (orbit (hilbertDilationAdjoint 2 (by norm_num)) f N) k = 0
  by_cases hk : k = 0
  · subst k
    exact hilbertSequence_zero _
  · have hkp : 0 < k := Nat.pos_of_ne_zero hk
    have he := dyadicAdjointOrbit_inner N f (hilbertAtom k hkp)
    rw [hilbertAtom_inner, hilbertDilation_hilbertAtom_inner] at he
    have hsum : (∑ n ∈ Finset.Ico (2 ^ N * k) (2 ^ N * (k + 1)),
        positiveWeight n * hilbertSequence f n) = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      have hb : 2 ^ N ≤ n :=
        (Nat.le_mul_of_pos_right (2 ^ N) hkp).trans (Finset.mem_Ico.mp hn).1
      rw [hf n hb, mul_zero]
    rw [hsum, mul_zero] at he
    have hw : positiveWeight k ≠ 0 := by unfold positiveWeight; positivity
    exact (mul_eq_zero.mp he).resolve_left hw

/-- The critical quotient norm is an exact finite expression for every
physical sequence supported below 2^N. -/
theorem dyadicQuotientProjection_norm_sq_of_support
    (N : ℕ) (f : ThresholdHilbert)
    (hf : ∀ k : ℕ, 2 ^ N ≤ k → hilbertSequence f k = 0) :
    ‖dyadicQuotientProjection f‖ ^ 2 =
      (1 / 2 : ℝ) * ‖dyadicKernelDefect (dyadicAdjointPacket N f)‖ ^ 2 :=
  dyadicQuotientProjection_norm_sq_of_adjoint_nilpotent N f
    (dyadicAdjointOrbit_eq_zero_of_support N f hf)

/-- The complete mixed Gram entry has the same finite critical realization. -/
theorem dyadicQuotientProjection_inner_of_support
    (N M : ℕ) (f g : ThresholdHilbert)
    (hf : ∀ k : ℕ, 2 ^ N ≤ k → hilbertSequence f k = 0)
    (hg : ∀ k : ℕ, 2 ^ M ≤ k → hilbertSequence g k = 0) :
    inner ℝ (dyadicQuotientProjection f) (dyadicQuotientProjection g) =
      (1 / 2 : ℝ) * inner ℝ (dyadicKernelDefect (dyadicAdjointPacket N f))
        (dyadicKernelDefect (dyadicAdjointPacket M g)) :=
  dyadicQuotientProjection_inner_of_adjoint_nilpotent N M f g
    (dyadicAdjointOrbit_eq_zero_of_support N f hf)
    (dyadicAdjointOrbit_eq_zero_of_support M g hg)

end
end RiemannResearch.RH.Pareto
