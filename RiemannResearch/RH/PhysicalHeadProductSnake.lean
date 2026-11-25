import RiemannResearch.RH.PhysicalHeadAlgebraSnake
import Mathlib.Algebra.Module.SnakeLemma
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The snake on countable products of physical head mean sequences

Use the algebraic product of the stage rows. Each vertical difference is the
next entry transported by ordinary inclusion minus the current entry. Its
cokernel on the mixed kernels uses the algebraic range. The connecting map on
constant scalars takes one to the class of all adjacent unit displacements.
This difference-map description of a countable derived inverse limit is the
one in the Stacks Project, Tag 07KV (Derived limits).
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.Pareto.PrimePowerSchur.PhysicalHeadStageAlgebra

open CenteredMeanSnake.PhysicalHeadSections

abbrev KernelSeq := (n : ℕ) → (stageMean n).ker
abbrev StageSeq := (n : ℕ) → headCompatible n

/-- Successive difference after genuine inclusion of physical-stage kernels. -/
def kernelDiff : KernelSeq →ₗ[ℝ] KernelSeq :=
  LinearMap.pi fun n : ℕ =>
    (kernelInclusion (Nat.le_succ n)).comp
      (LinearMap.proj (n + 1) : KernelSeq →ₗ[ℝ] (stageMean (n + 1)).ker) -
      (LinearMap.proj n : KernelSeq →ₗ[ℝ] (stageMean n).ker)

/-- Successive difference after genuine inclusion of physical stages. -/
def stageDiff : StageSeq →ₗ[ℝ] StageSeq :=
  LinearMap.pi fun n : ℕ =>
    (stageInclusion (Nat.le_succ n)).comp
      (LinearMap.proj (n + 1) : StageSeq →ₗ[ℝ] headCompatible (n + 1)) -
      (LinearMap.proj n : StageSeq →ₗ[ℝ] headCompatible n)

/-- Successive difference on scalar sequences. -/
def scalarDiff : (ℕ → ℝ) →ₗ[ℝ] (ℕ → ℝ) :=
  LinearMap.pi fun n : ℕ => (LinearMap.proj (n + 1) : (ℕ → ℝ) →ₗ[ℝ] ℝ) -
    (LinearMap.proj n : (ℕ → ℝ) →ₗ[ℝ] ℝ)

/-- Constant scalars form the kernel of the scalar difference. -/
def constantScalar : ℝ →ₗ[ℝ] (ℕ → ℝ) := LinearMap.pi fun _ => LinearMap.id

private theorem constantScalar_exact : Function.Exact constantScalar scalarDiff := by
  intro s
  constructor
  · intro hs
    refine ⟨s 0, ?_⟩
    funext n
    change s 0 = s n
    induction n with
    | zero => rfl
    | succ n ih =>
      have hstep := congrFun hs n
      change s (n + 1) - s n = 0 at hstep
      exact ih.trans (sub_eq_zero.mp hstep).symm
  · rintro ⟨a, rfl⟩
    funext n
    exact sub_self a

/-- Stagewise kernel inclusion. -/
def productInclusion : KernelSeq →ₗ[ℝ] StageSeq :=
  LinearMap.pi fun n => (stageMean n).ker.subtype.comp (LinearMap.proj n)

/-- Stagewise scalar augmentation. -/
def productMean : StageSeq →ₗ[ℝ] (ℕ → ℝ) :=
  LinearMap.pi fun n => (stageMean n).toLinearMap.comp (LinearMap.proj n)

private theorem productRow_exact : Function.Exact productInclusion productMean := by
  intro x
  constructor
  · intro hx
    exact ⟨fun n => ⟨x n, congrFun hx n⟩, rfl⟩
  · rintro ⟨w, rfl⟩
    funext n
    exact (w n).property

private theorem product_left_square :
    productInclusion.comp kernelDiff = stageDiff.comp productInclusion := by
  apply LinearMap.ext
  intro x
  funext n
  rfl

private theorem product_right_square :
    productMean.comp stageDiff = scalarDiff.comp productMean := by
  apply LinearMap.ext
  intro x
  funext n
  change stageMean n (stageInclusion (Nat.le_succ n) (x (n + 1)) - x n) =
    stageMean (n + 1) (x (n + 1)) - stageMean n (x n)
  rw [map_sub, stageInclusion_mean]

private def productLift (s : ℕ → ℝ) : StageSeq := fun n => s n • stageUnit n
private def productRetraction (x : StageSeq) : KernelSeq := fun n => mixedCoordinate n (x n)

private theorem productLift_right : productMean ∘ productLift = id := by
  funext s n
  change stageMean n (s n • stageUnit n) = s n
  rw [map_smul, stageUnit_mean, smul_eq_mul, mul_one]

private theorem productRetraction_left : productRetraction ∘ productInclusion = id := by
  funext w n
  exact mixedCoordinate_kernel n (w n)

/-- Algebraic cokernel of the kernel difference, the countable derived-limit model. -/
abbrev KernelCokernel := KernelSeq ⧸ LinearMap.range kernelDiff

/-- The coordinatewise displacements of canonical mean sections. -/
def unitCarries : KernelSeq := fun n => unitCarry (Nat.le_succ n)

/-- The actual Mathlib snake on the two product rows with vertical difference maps. -/
def productSnake : ℝ →ₗ[ℝ] KernelCokernel :=
  SnakeLemma.δ kernelDiff stageDiff scalarDiff
    productInclusion productMean productRow_exact productInclusion productMean productRow_exact
    product_left_square product_right_square productLift productLift_right
    productRetraction productRetraction_left constantScalar constantScalar_exact
    (LinearMap.range kernelDiff).mkQ (fun _ => Submodule.Quotient.mk_eq_zero _)

theorem productSnake_one :
    productSnake 1 = (LinearMap.range kernelDiff).mkQ unitCarries := by
  change (LinearMap.range kernelDiff).mkQ
    (productRetraction (stageDiff (productLift (constantScalar 1)))) = _
  apply congrArg (LinearMap.range kernelDiff).mkQ
  funext n
  change mixedCoordinate n (stageInclusion (Nat.le_succ n) ((1 : ℝ) • stageUnit (n + 1)) -
    (1 : ℝ) • stageUnit n) = unitCarry (Nat.le_succ n)
  simp only [one_smul]
  exact mixedCoordinate_kernel n (unitCarry (Nat.le_succ n))

theorem productSnake_apply (a : ℝ) :
    productSnake a = a • (LinearMap.range kernelDiff).mkQ unitCarries := by
  rw [← productSnake_one, ← map_smul, smul_eq_mul, mul_one]

/-- Coboundaries are exactly compatible choices of a mean-one stage section. -/
theorem productSnake_one_eq_zero_iff_coherent :
    productSnake 1 = 0 ↔ ∃ x : StageSeq,
      stageDiff x = 0 ∧ ∀ n, stageMean n (x n) = 1 := by
  rw [productSnake_one]
  change (Submodule.Quotient.mk unitCarries : KernelCokernel) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨w, hw⟩
    let x : StageSeq := fun n => stageUnit n - (w n).val
    refine ⟨x, ?_, fun n => ?_⟩
    · funext n
      have hw' := congrArg (fun a : (stageMean n).ker => a.val) (congrFun hw n)
      change stageInclusion (Nat.le_succ n) (w (n + 1)).val - (w n).val =
        displacement (Nat.le_succ n) at hw'
      change stageInclusion (Nat.le_succ n) (stageUnit (n + 1) - (w (n + 1)).val) -
        (stageUnit n - (w n).val) = 0
      calc
        _ = displacement (Nat.le_succ n) -
            (stageInclusion (Nat.le_succ n) (w (n + 1)).val - (w n).val) := by
              rw [map_sub, displacement]
              abel
        _ = 0 := by rw [hw', sub_self]
    · change stageMean n (stageUnit n - (w n).val) = 1
      rw [map_sub, stageUnit_mean, show stageMean n (w n).val = 0 from (w n).property, sub_zero]
  · rintro ⟨x, hx, hm⟩
    let w : KernelSeq := fun n =>
      ⟨stageUnit n - x n, by
        change stageMean n (stageUnit n - x n) = 0
        rw [map_sub, stageUnit_mean, hm, sub_self]⟩
    refine ⟨w, ?_⟩
    funext n
    apply Subtype.ext
    have hx' := congrFun hx n
    change stageInclusion (Nat.le_succ n) (x (n + 1)) - x n = 0 at hx'
    change stageInclusion (Nat.le_succ n) (stageUnit (n + 1) - x (n + 1)) -
      (stageUnit n - x n) = displacement (Nat.le_succ n)
    rw [map_sub, sub_eq_zero.mp hx', displacement]
    abel

/-- Evaluation at level zero of the coherent scalar mean. -/
def coherentMean : stageDiff.ker →ₗ[ℝ] ℝ :=
  (LinearMap.proj 0 : (ℕ → ℝ) →ₗ[ℝ] ℝ).comp (productMean.comp stageDiff.ker.subtype)

private theorem stageKernel_exact : Function.Exact stageDiff.ker.subtype stageDiff := by
  intro x
  constructor
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨v, rfl⟩
    exact v.property

private theorem coherentMean_square :
    productMean.comp stageDiff.ker.subtype = constantScalar.comp coherentMean := by
  apply LinearMap.ext
  intro x
  have hs : scalarDiff (productMean x.val) = 0 := by
    calc
      _ = productMean (stageDiff x.val) :=
        (congrArg (fun f : StageSeq →ₗ[ℝ] (ℕ → ℝ) => f x.val) product_right_square).symm
      _ = 0 := by rw [show stageDiff x.val = 0 from x.property, map_zero]
  obtain ⟨c, hc⟩ := (constantScalar_exact _).mp hs
  funext n
  exact (congrFun hc n).symm.trans (congrFun hc 0)

/-- Exactness at the coherent scalars. -/
theorem coherentMean_productSnake_exact : Function.Exact coherentMean productSnake :=
  SnakeLemma.exact_δ_right kernelDiff stageDiff scalarDiff
    productInclusion productMean productRow_exact productInclusion productMean productRow_exact
    product_left_square product_right_square productLift productLift_right
    productRetraction productRetraction_left stageDiff.ker.subtype stageKernel_exact
    constantScalar constantScalar_exact (LinearMap.range kernelDiff).mkQ
    (fun _ => Submodule.Quotient.mk_eq_zero _) coherentMean coherentMean_square
    (fun _ _ h => congrFun h 0)

abbrev StageCokernel := StageSeq ⧸ LinearMap.range stageDiff

/-- The map of first derived limits induced by the stagewise kernel inclusions. -/
def cokernelInclusion : KernelCokernel →ₗ[ℝ] StageCokernel :=
  (LinearMap.range kernelDiff).liftQ ((LinearMap.range stageDiff).mkQ.comp productInclusion) (by
    rintro x ⟨w, rfl⟩
    change (Submodule.Quotient.mk (productInclusion (kernelDiff w)) : StageCokernel) = 0
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact ⟨productInclusion w,
      (congrArg (fun f : KernelSeq →ₗ[ℝ] StageSeq => f w) product_left_square).symm⟩)

/-- Exactness identifies the line removed on passing from the mixed to the legal-stage cokernel. -/
theorem productSnake_cokernelInclusion_exact : Function.Exact productSnake cokernelInclusion :=
  SnakeLemma.exact_δ_left kernelDiff stageDiff scalarDiff
    productInclusion productMean productRow_exact productInclusion productMean productRow_exact
    product_left_square product_right_square productLift productLift_right
    productRetraction productRetraction_left constantScalar constantScalar_exact
    (LinearMap.range kernelDiff).mkQ (fun _ => Submodule.Quotient.mk_eq_zero _)
    (LinearMap.range stageDiff).mkQ (fun _ => Submodule.Quotient.mk_eq_zero _)
    cokernelInclusion (by ext w; rfl) (LinearMap.range kernelDiff).mkQ_surjective

private theorem scalarDiff_surjective : Function.Surjective scalarDiff := by
  intro x
  refine ⟨fun n => ∑ i ∈ Finset.range n, x i, funext fun n => ?_⟩
  change (∑ i ∈ Finset.range (n + 1), x i) - (∑ i ∈ Finset.range n, x i) = x n
  rw [Finset.sum_range_succ, add_sub_cancel_left]

/-- Every class of legal stages comes from a class of mixed stages. -/
theorem cokernelInclusion_surjective : Function.Surjective cokernelInclusion := by
  intro z
  obtain ⟨x, rfl⟩ := (LinearMap.range stageDiff).mkQ_surjective z
  obtain ⟨s, hs⟩ := scalarDiff_surjective (productMean x)
  let t := productLift s
  have ht : productMean t = s := congrFun productLift_right s
  have hz : productMean (x - stageDiff t) = 0 := by
    rw [map_sub, show productMean (stageDiff t) = scalarDiff (productMean t) from
      congrArg (fun f : StageSeq →ₗ[ℝ] (ℕ → ℝ) => f t) product_right_square, ht, hs, sub_self]
  obtain ⟨w, hw⟩ := (productRow_exact _).mp hz
  refine ⟨(LinearMap.range kernelDiff).mkQ w, ?_⟩
  change (LinearMap.range stageDiff).mkQ (productInclusion w) = _
  rw [hw, map_sub, show (LinearMap.range stageDiff).mkQ (stageDiff t) = 0 from
    (Submodule.Quotient.mk_eq_zero _).mpr ⟨t, rfl⟩, sub_zero]

theorem cokernelInclusion_ker_eq_boundary_line :
    cokernelInclusion.ker = Submodule.span ℝ {productSnake 1} := by
  ext x
  change cokernelInclusion x = 0 ↔ _
  rw [productSnake_cokernelInclusion_exact x, Submodule.mem_span_singleton]
  have h (a : ℝ) : productSnake a = a • productSnake 1 := by
    simpa only [smul_eq_mul, mul_one] using productSnake.map_smul a (1 : ℝ)
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, (h t).symm.trans ht⟩
  · rintro ⟨t, ht⟩
    exact ⟨t, (h t).trans ht⟩

/-- The legal-stage derived limit is the quotient by the image of the one scalar boundary. -/
def stageCokernelEquiv :
    (KernelCokernel ⧸ Submodule.span ℝ {productSnake 1}) ≃ₗ[ℝ] StageCokernel :=
  (Submodule.quotEquivOfEq _ _ cokernelInclusion_ker_eq_boundary_line.symm).trans
    (cokernelInclusion.quotKerEquivOfSurjective cokernelInclusion_surjective)

end RiemannResearch.RH.Pareto.PrimePowerSchur.PhysicalHeadStageAlgebra
