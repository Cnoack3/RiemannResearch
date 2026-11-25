import RiemannResearch.RH.PhysicalHeadSnakeSections
import RiemannResearch.RH.MixedConductorSquareZero
import RiemannResearch.RH.ParetoAffineHeadTower
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # The split square-zero real algebra on a physical-head stage

The unit is the canonical least-norm section at the specified physical cutoff.
The augmentation is its original continuous Pareto mean, and the square-zero
ideal consists of the mean-zero legal vectors whose head vanishes.
-/

noncomputable section
namespace RiemannResearch.RH.Pareto.PrimePowerSchur.PhysicalHeadStageAlgebra
open CoefficientStabilization CenteredMeanSnake.PhysicalHeadSections

/-- The least-norm affine head patch regarded as a head-compatible legal vector. -/
def stageUnit (N : ℕ) : headCompatible N := by
  have hp := (AffineHeadTower.patch_spec N).1
  let v : closedSpace := ⟨AffineHeadTower.patch N, hp.1⟩
  have hh : MatchesUnitHead N v := by
    apply (matchesUnitHead_iff_sequence N v).mpr
    intro k hk hkN
    cases k with
    | zero => omega
    | succ i => simpa only [physicalEvaluationCLM_apply] using hp.2.2 i (by omega)
  have hm : legalPacketMean v = 1 := hp.2.1
  exact ⟨v, (mem_headCompatible_iff N v).mpr (by rw [hm, one_smul]; exact hh)⟩

@[simp] theorem stageUnit_val (N : ℕ) :
    ((stageUnit N).val : ThresholdHilbert) = AffineHeadTower.patch N := rfl

@[simp] theorem stageUnit_mean (N : ℕ) : stageMean N (stageUnit N) = 1 :=
  (AffineHeadTower.patch_spec N).1.2.1

/-- Square-zero multiplication with the orthogonal stage section as unit. -/
def stageProduct (N : ℕ) (x y : headCompatible N) : headCompatible N :=
  stageMean N x • y + stageMean N y • x - (stageMean N x * stageMean N y) • stageUnit N

theorem stageProduct_val (N : ℕ) (x y : headCompatible N) :
    (stageProduct N x y).val = LegalMeanAlgebra.mulWith (stageUnit N).val x.val y.val := rfl

@[simp] theorem mean_stageProduct (N : ℕ) (x y : headCompatible N) :
    stageMean N (stageProduct N x y) = stageMean N x * stageMean N y :=
  LegalMeanAlgebra.mean_mulWith (stageUnit_mean N) x.val y.val

private theorem product_comm (N : ℕ) (x y : headCompatible N) :
    stageProduct N x y = stageProduct N y x :=
  Subtype.ext (LegalMeanAlgebra.mulWith_comm _ _ _)

private theorem product_right_smul (N : ℕ) (a : ℝ) (x y : headCompatible N) :
    stageProduct N x (a • y) = a • stageProduct N x y :=
  Subtype.ext (LegalMeanAlgebra.mulWith_smul _ _ _ _)

/-- The existing stage additive group with the multiplication of its canonical section. -/
scoped instance stageCommRing (N : ℕ) : CommRing (headCompatible N) where
  __ := (inferInstance : AddCommGroup (headCompatible N))
  one := stageUnit N
  mul := stageProduct N
  mul_assoc x y z := Subtype.ext (LegalMeanAlgebra.mulWith_assoc (stageUnit_mean N) x.val y.val z.val)
  mul_comm := product_comm N
  one_mul x := Subtype.ext (LegalMeanAlgebra.mulWith_unit (stageUnit_mean N) x.val)
  mul_one x := (product_comm N x _).trans (Subtype.ext (LegalMeanAlgebra.mulWith_unit (stageUnit_mean N) x.val))
  left_distrib x y z := Subtype.ext (LegalMeanAlgebra.mulWith_add _ x.val y.val z.val)
  right_distrib x y z := by
    change stageProduct N (x+y) z = stageProduct N x z + stageProduct N y z
    rw [product_comm N (x+y), product_comm N x z, product_comm N y z]
    exact Subtype.ext (LegalMeanAlgebra.mulWith_add _ z.val x.val y.val)
  mul_zero x := Subtype.ext (LegalMeanAlgebra.mulWith_zero _ x.val)
  zero_mul x := (product_comm N _ x).trans (Subtype.ext (LegalMeanAlgebra.mulWith_zero _ x.val))

theorem mul_def (N : ℕ) (x y : headCompatible N) : x * y = stageProduct N x y := rfl

theorem one_def (N : ℕ) : (1 : headCompatible N) = stageUnit N := rfl

@[simp] theorem stageMean_mul (N : ℕ) (x y : headCompatible N) :
    stageMean N (x*y) = stageMean N x * stageMean N y := mean_stageProduct N x y

/-- The real algebra structure uses the original scalar multiplication. -/
scoped instance stageAlgebra (N : ℕ) : Algebra ℝ (headCompatible N) :=
  Algebra.ofModule
    (fun a x y => by rw [mul_comm, mul_def, product_right_smul, ← mul_def, mul_comm y x])
    (product_right_smul N)

@[simp] theorem algebraMap_apply (N : ℕ) (a : ℝ) :
    algebraMap ℝ (headCompatible N) a = a • stageUnit N := rfl

/-- The algebra section is the scalar right inverse in the centered head complex. -/
theorem algebraMap_eq_stageSection (N : ℕ) (a : ℝ) :
    algebraMap ℝ (headCompatible N) a = stageSection N (stageUnit N) a := rfl

/-- The original scalar observation is the augmentation of the stage algebra. -/
def augmentation (N : ℕ) : headCompatible N →ₐ[ℝ] ℝ :=
  AlgHom.ofLinearMap (stageMean N).toLinearMap (stageUnit_mean N) (mean_stageProduct N)

@[simp] theorem augmentation_apply (N : ℕ) (x : headCompatible N) :
    augmentation N x = stageMean N x := rfl

/-- The ideal of mean-zero, zero-head legal vectors. -/
def stageIdeal (N : ℕ) : Ideal (headCompatible N) := RingHom.ker (augmentation N)

theorem mem_stageIdeal_iff (N : ℕ) (x : headCompatible N) :
    x ∈ stageIdeal N ↔ (x.val : ThresholdHilbert) ∈ mixedClosure ∧
      compactHead N (x.val : ThresholdHilbert) = 0 :=
  mem_stageMean_ker_iff N x

theorem mul_eq_zero_of_mem (N : ℕ) {x y : headCompatible N}
    (hx : x ∈ stageIdeal N) (hy : y ∈ stageIdeal N) : x*y = 0 := by
  change stageMean N x = 0 at hx
  change stageMean N y = 0 at hy
  simp [mul_def, stageProduct, hx, hy]

theorem stageIdeal_sq (N : ℕ) : (stageIdeal N)^2 = ⊥ := by
  simp only [pow_two, eq_bot_iff, Ideal.mul_le, Ideal.mem_bot]
  exact fun _ hx _ hy => mul_eq_zero_of_mem N hx hy

/-- The mixed coordinate of a stage vector under the orthogonal splitting. -/
def mixedCoordinate (N : ℕ) : headCompatible N →L[ℝ] (stageMean N).ker :=
  (ContinuousLinearMap.id ℝ (headCompatible N) -
    (stageMean N).smulRight (stageUnit N)).codRestrict _ fun x => by
      change stageMean N (x - stageMean N x • stageUnit N) = 0
      rw [map_sub, map_smul, stageUnit_mean, smul_eq_mul, mul_one, sub_self]

theorem mixedCoordinate_val (N : ℕ) (x : headCompatible N) :
    (mixedCoordinate N x).val = x - stageMean N x • stageUnit N := rfl

@[simp] theorem mixedCoordinate_unit (N : ℕ) : mixedCoordinate N (stageUnit N) = 0 := by
  apply Subtype.ext
  change (mixedCoordinate N (stageUnit N)).val = 0
  rw [mixedCoordinate_val, stageUnit_mean, one_smul, sub_self]

@[simp] theorem mixedCoordinate_kernel (N : ℕ) (k : (stageMean N).ker) :
    mixedCoordinate N k.val = k := by
  apply Subtype.ext
  rw [mixedCoordinate_val, show stageMean N k.val = 0 from k.property, zero_smul, sub_zero]

/-- Algebra coordinates consist of the Pareto mean and the centered kernel vector.
Their inverse adds the actual canonical scalar section to its mixed coordinate. -/
def coordinates (N : ℕ) : headCompatible N ≃ₐ[ℝ] TrivSqZeroExt ℝ (stageMean N).ker where
  toFun x := (stageMean N x, mixedCoordinate N x)
  invFun z := z.snd.val + z.fst • stageUnit N
  left_inv x := by
    change (mixedCoordinate N x).val + stageMean N x • stageUnit N = x
    rw [mixedCoordinate_val, sub_add_cancel]
  right_inv z := by
    apply TrivSqZeroExt.ext
    · change stageMean N (z.snd.val + z.fst • stageUnit N) = z.fst
      rw [map_add, map_smul, stageUnit_mean, show stageMean N z.snd.val = 0 from z.snd.property,
        smul_eq_mul, mul_one, zero_add]
    · change mixedCoordinate N (z.snd.val + z.fst • stageUnit N) = z.snd
      rw [map_add, map_smul, mixedCoordinate_kernel, mixedCoordinate_unit, smul_zero, add_zero]
  map_add' x y := TrivSqZeroExt.ext (map_add (stageMean N) x y) (map_add (mixedCoordinate N) x y)
  map_mul' x y := by
    apply TrivSqZeroExt.ext
    · exact mean_stageProduct N x y
    · change mixedCoordinate N (stageProduct N x y) =
        stageMean N x • mixedCoordinate N y + MulOpposite.op (stageMean N y) • mixedCoordinate N x
      simp only [stageProduct, map_sub, map_add, map_smul, mixedCoordinate_unit, smul_zero,
        sub_zero, op_smul_eq_smul]
  commutes' a := by
    rw [algebraMap_apply]
    apply TrivSqZeroExt.ext
    · change stageMean N (a • stageUnit N) = a
      rw [map_smul, stageUnit_mean, smul_eq_mul, mul_one]
    · change mixedCoordinate N (a • stageUnit N) = 0
      rw [map_smul, mixedCoordinate_unit, smul_zero]

end RiemannResearch.RH.Pareto.PrimePowerSchur.PhysicalHeadStageAlgebra
