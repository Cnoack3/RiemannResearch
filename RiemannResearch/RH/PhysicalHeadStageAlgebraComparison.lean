import RiemannResearch.RH.PhysicalHeadStageAlgebra
import RiemannResearch.RH.PhysicalHeadSectionGrowth

/-!
# Ordinary and unit-preserving comparison of physical head algebras

For deeper and shallower physical stages, inclusion preserves the Pareto
mean. Its multiplicative error is the displacement of the two canonical
least-norm lifts times the two means. Subtracting the mean times this
displacement gives a unital algebra embedding. Its existence is unconditional.
Multiplicativity of all the ordinary adjacent inclusions is equivalent to RH.
-/

noncomputable section

namespace RiemannResearch.RH.Pareto.PrimePowerSchur.PhysicalHeadStageAlgebra

open CoefficientStabilization CenteredMeanSnake.PhysicalHeadSections AffineHeadTower
open scoped RiemannResearch.RH.Pareto.PrimePowerSchur.PhysicalHeadStageAlgebra

private theorem compactHead_nested {N K : ℕ} (h : N ≤ K) (x : ThresholdHilbert) :
    compactHead N (compactHead K x) = compactHead N x := by
  apply hilbertSequence_injective
  funext j
  by_cases hj : j ≤ N
  · simp only [compactHead_sequence, if_pos hj, if_pos (hj.trans h)]
  · simp only [compactHead_sequence, if_neg hj]

theorem headCompatible_antitone : Antitone headCompatible := by
  intro N K h v hv
  apply (mem_headCompatible_iff N v).mpr
  have he := (mem_headCompatible_iff K v).mp hv
  rw [← compactHead_smul] at he ⊢
  calc
    compactHead N (v : ThresholdHilbert) = compactHead N (compactHead K v.val) :=
      (compactHead_nested h v.val).symm
    _ = compactHead N (compactHead K (legalPacketMean v • hilbertOne)) := congrArg _ he
    _ = _ := compactHead_nested h _

/-- Literal inclusion of a deeper stage into a shallower stage. -/
def stageInclusion {N K : ℕ} (h : N ≤ K) : headCompatible K →ₗ[ℝ] headCompatible N :=
  Submodule.inclusion (headCompatible_antitone h)

@[simp] theorem stageInclusion_mean {N K : ℕ} (h : N ≤ K) (x : headCompatible K) :
    stageMean N (stageInclusion h x) = stageMean K x := rfl

theorem stageInclusion_injective {N K : ℕ} (h : N ≤ K) :
    Function.Injective (stageInclusion h) :=
  fun _ _ hxy => Subtype.ext (congrArg (fun z : headCompatible N => z.val) hxy)

/-- The ordinary inclusion carries the deeper unit to this translate of the shallower unit. -/
def displacement {N K : ℕ} (h : N ≤ K) : headCompatible N :=
  stageInclusion h (stageUnit K) - stageUnit N

@[simp] theorem displacement_mean {N K : ℕ} (h : N ≤ K) : stageMean N (displacement h) = 0 := by
  simp only [displacement, map_sub, stageInclusion_mean, stageUnit_mean, sub_self]

theorem displacement_val {N K : ℕ} (h : N ≤ K) :
    ((displacement h).val : ThresholdHilbert) = patch K - patch N := rfl

theorem displacement_orthogonal_deeper {N K : ℕ} (h : N ≤ K) :
    ((displacement h).val : ThresholdHilbert) ∈ (kernel K)ᗮ := by
  rw [displacement_val]
  intro x hx
  rw [inner_sub_right, (patch_spec K).2 x hx, (patch_spec N).2 x (kernel_antitone h hx), sub_self]

theorem displacement_norm_sq {N K : ℕ} (h : N ≤ K) :
    ‖displacement h‖ ^ 2 = ‖patch K‖ ^ 2 - ‖patch N‖ ^ 2 := by
  change ‖patch K - patch N‖ ^ 2 = _
  linarith only [patch_norm_sq_between h]

theorem adjacent_displacement_norm_sq (N : ℕ) :
    ‖displacement (Nat.le_succ N)‖ ^ 2 = stepEnergy N := by
  rw [displacement_norm_sq]
  linarith only [patch_norm_sq_step N]

/-- The multiplicative error of the ordinary inclusion, with its sign. -/
theorem inclusion_mul_defect {N K : ℕ} (h : N ≤ K) (x y : headCompatible K) :
    stageInclusion h x * stageInclusion h y - stageInclusion h (x * y) =
      (stageMean K x * stageMean K y) • displacement h := by
  rw [mul_def N, mul_def K]
  simp only [stageProduct, map_sub, map_add, map_smul, stageInclusion_mean, displacement, smul_sub]
  abel

theorem inclusion_unit_defect {N K : ℕ} (h : N ≤ K) :
    stageInclusion h (stageUnit K) * stageInclusion h (stageUnit K) -
      stageInclusion h (stageUnit K * stageUnit K) = displacement h := by
  simpa only [stageUnit_mean, one_mul, one_smul] using
    inclusion_mul_defect h (stageUnit K) (stageUnit K)

/-- The unit-adjusted linear inclusion. On the mean kernel it is the ordinary inclusion. -/
def transportLinear {N K : ℕ} (h : N ≤ K) : headCompatible K →ₗ[ℝ] headCompatible N :=
  stageInclusion h - (stageMean K).toLinearMap.smulRight (displacement h)

theorem transportLinear_apply {N K : ℕ} (h : N ≤ K) (x : headCompatible K) :
    transportLinear h x = stageInclusion h x - stageMean K x • displacement h := rfl

@[simp] theorem transportLinear_mean {N K : ℕ} (h : N ≤ K) (x : headCompatible K) :
    stageMean N (transportLinear h x) = stageMean K x := by
  simp only [transportLinear_apply, map_sub, stageInclusion_mean, map_smul,
    displacement_mean, smul_zero, sub_zero]

theorem transportLinear_unit {N K : ℕ} (h : N ≤ K) :
    transportLinear h (stageUnit K) = stageUnit N := by
  rw [transportLinear_apply, stageUnit_mean, one_smul, displacement]
  abel

theorem transportLinear_mul {N K : ℕ} (h : N ≤ K) (x y : headCompatible K) :
    transportLinear h (x * y) = transportLinear h x * transportLinear h y := by
  rw [mul_def K, mul_def N]
  simp only [stageProduct, map_sub, map_add, map_smul, transportLinear_mean, transportLinear_unit]

/-- The canonical unital algebra homomorphism from a deeper stage into a shallower one. -/
def stageAlgebraTransport {N K : ℕ} (h : N ≤ K) :
    headCompatible K →ₐ[ℝ] headCompatible N :=
  AlgHom.ofLinearMap (transportLinear h) (transportLinear_unit h) (transportLinear_mul h)

theorem stageAlgebraTransport_apply {N K : ℕ} (h : N ≤ K) (x : headCompatible K) :
    stageAlgebraTransport h x = stageInclusion h x - stageMean K x • displacement h := rfl

theorem stageAlgebraTransport_injective {N K : ℕ} (h : N ≤ K) :
    Function.Injective (stageAlgebraTransport h) := by
  intro x y hxy
  change transportLinear h x = transportLinear h y at hxy
  have hm := congrArg (stageMean N) hxy
  simp only [transportLinear_mean] at hm
  rw [transportLinear_apply, transportLinear_apply, hm] at hxy
  apply stageInclusion_injective h
  simpa only [sub_add_cancel] using congrArg (fun z => z + stageMean K y • displacement h) hxy

theorem stageAlgebraTransport_on_kernel {N K : ℕ} (h : N ≤ K) (x : (stageMean K).ker) :
    stageAlgebraTransport h x.val = stageInclusion h x.val := by
  rw [stageAlgebraTransport_apply, show stageMean K x.val = 0 from x.property, zero_smul, sub_zero]

theorem stageInclusion_comp_apply {N K J : ℕ} (h : N ≤ K) (h' : K ≤ J)
    (x : headCompatible J) :
    stageInclusion h (stageInclusion h' x) = stageInclusion (h.trans h') x := rfl

/-- Changes of the canonical scalar section telescope under ordinary inclusion. -/
theorem displacement_cocycle {N K J : ℕ} (h : N ≤ K) (h' : K ≤ J) :
    displacement (h.trans h') = stageInclusion h (displacement h') + displacement h := by
  simp only [displacement, map_sub, stageInclusion_comp_apply]
  abel

theorem stageAlgebraTransport_refl (N : ℕ) (x : headCompatible N) :
    stageAlgebraTransport (le_refl N) x = x := by
  have hd : displacement (le_refl N) = 0 := by
    change stageUnit N - stageUnit N = 0
    exact sub_self _
  calc
    stageAlgebraTransport (le_refl N) x = stageInclusion (le_refl N) x := by
      rw [stageAlgebraTransport_apply, hd, smul_zero, sub_zero]
    _ = x := rfl

/-- Unital comparison is transitive even when the ordinary inclusions move the unit. -/
theorem stageAlgebraTransport_comp_apply {N K J : ℕ} (h : N ≤ K) (h' : K ≤ J)
    (x : headCompatible J) :
    stageAlgebraTransport h (stageAlgebraTransport h' x) =
      stageAlgebraTransport (h.trans h') x := by
  have hm : stageMean K (stageAlgebraTransport h' x) = stageMean J x := transportLinear_mean h' x
  rw [stageAlgebraTransport_apply h, hm, stageAlgebraTransport_apply h',
    stageAlgebraTransport_apply (h.trans h'), map_sub, map_smul, stageInclusion_comp_apply,
    displacement_cocycle h h', smul_add]
  abel

/-- Testing both arguments on the stage unit detects any failure of multiplicativity. -/
theorem stageInclusion_multiplicative_iff {N K : ℕ} (h : N ≤ K) :
    (∀ x y : headCompatible K,
      stageInclusion h (x * y) = stageInclusion h x * stageInclusion h y) ↔
    displacement h = 0 := by
  constructor
  · intro hm
    have he := inclusion_unit_defect h
    rw [hm, sub_self] at he
    exact he.symm
  · intro hd x y
    have he := inclusion_mul_defect h x y
    rw [hd, smul_zero] at he
    exact (sub_eq_zero.mp he).symm

/-- All ordinary adjacent inclusions preserve the product exactly if and only if RH holds. -/
theorem adjacent_stageInclusion_multiplicative_iff_rh :
    (∀ N : ℕ, ∀ x y : headCompatible (N + 1),
      stageInclusion (Nat.le_succ N) (x * y) =
        stageInclusion (Nat.le_succ N) x * stageInclusion (Nat.le_succ N) y) ↔
    RiemannHypothesis := by
  constructor
  · intro hm
    have hcost : stepEnergy = fun _ => 0 := by
      funext N
      rw [← adjacent_displacement_norm_sq, (stageInclusion_multiplicative_iff _).mp (hm N),
        norm_zero, zero_pow (by decide : 2 ≠ 0)]
    apply riemannHypothesis_of_summable_steps
    rw [hcost]
    exact summable_zero
  · intro hRH N
    apply (stageInclusion_multiplicative_iff _).mpr
    apply norm_eq_zero.mp
    have he := displacement_norm_sq (Nat.le_succ N)
    change ‖displacement (Nat.le_succ N)‖ ^ 2 =
      PhysicalHeadSectionGrowth.kappa (N + 1) ^ 2 - PhysicalHeadSectionGrowth.kappa N ^ 2 at he
    rw [PhysicalHeadSectionGrowth.kappa_eq_one_of_rh hRH,
      PhysicalHeadSectionGrowth.kappa_eq_one_of_rh hRH, sub_self] at he
    nlinarith [norm_nonneg (displacement (Nat.le_succ N))]

end RiemannResearch.RH.Pareto.PrimePowerSchur.PhysicalHeadStageAlgebra
