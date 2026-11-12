import RiemannResearch.NumberTheory.ProfiniteGeneralizedCRT
import RiemannResearch.NumberTheory.ProfiniteCRT
import Mathlib.Topology.Algebra.Ring.Basic

/-!
# Universal properties of infinite Chinese remainder theory

Compatible all-modulus homomorphisms and arbitrary p-adic homomorphisms
have unique lifts to the existing profinite integer model. Continuity is
proved from the respective coordinate maps. See Wilkes, Profinite Groups
and Group Cohomology, Section 2.2; no Hilbert density follows from this result.
-/

namespace RiemannResearch.NumberTheory.GeneralizedCRT
variable {R : Type*} [Ring R]

/-- The inverse-limit universal property for compatible ring homomorphisms. -/
def compatibleLift (f : (n : PositiveModulus) → R →+* ZMod n.val)
    (hf : ∀ (m n : PositiveModulus) (h : m.val ∣ n.val) (x : R),
      ZMod.castHom h (ZMod m.val) (f n x) = f m x) :
    R →+* ProfiniteInt where
  toFun x := ⟨fun n => f n x, fun m n h => hf m n h x⟩
  map_zero' := Subtype.ext (funext fun n => (f n).map_zero)
  map_one' := Subtype.ext (funext fun n => (f n).map_one)
  map_add' x y := Subtype.ext (funext fun n => (f n).map_add x y)
  map_mul' x y := Subtype.ext (funext fun n => (f n).map_mul x y)

@[simp] theorem reduce_compatibleLift
    (f : (n : PositiveModulus) → R →+* ZMod n.val) (hf : ∀ (m n : PositiveModulus) (h : m.val ∣ n.val) (x : R),
      ZMod.castHom h (ZMod m.val) (f n x) = f m x) (n : PositiveModulus) :
    (reduce n).comp (compatibleLift f hf) = f n := rfl

theorem compatibleLift_unique
    (f : (n : PositiveModulus) → R →+* ZMod n.val) (hf : ∀ (m n : PositiveModulus) (h : m.val ∣ n.val) (x : R),
      ZMod.castHom h (ZMod m.val) (f n x) = f m x)
    (g : R →+* ProfiniteInt)
    (hg : ∀ n, (reduce n).comp g = f n) : g = compatibleLift f hf := by
  apply RingHom.ext
  intro x
  apply Subtype.ext
  funext n
  exact DFunLike.congr_fun (hg n) x

theorem continuous_compatibleLift [TopologicalSpace R]
    (f : (n : PositiveModulus) → R →+* ZMod n.val) (hf : ∀ (m n : PositiveModulus) (h : m.val ∣ n.val) (x : R),
      ZMod.castHom h (ZMod m.val) (f n x) = f m x)
    (hc : ∀ n, Continuous (f n)) : Continuous (compatibleLift f hf) := by
  exact (continuous_pi (fun n => hc n)).subtype_mk _

theorem existsUnique_continuous_lift [TopologicalSpace R]
    (f : (n : PositiveModulus) → R →+* ZMod n.val) (hf : ∀ (m n : PositiveModulus) (h : m.val ∣ n.val) (x : R),
      ZMod.castHom h (ZMod m.val) (f n x) = f m x)
    (hc : ∀ n, Continuous (f n)) :
    ∃! g : R →+* ProfiniteInt,
      Continuous g ∧ ∀ n, (reduce n).comp g = f n := by
  refine ⟨compatibleLift f hf, ⟨continuous_compatibleLift f hf hc,
    fun _ => rfl⟩, ?_⟩
  intro g hg
  exact compatibleLift_unique f hf g hg.2

/-- Naturality under precomposition, the categorical compatibility needed to
transport arithmetic parameter spaces through the inverse limit. -/
theorem compatibleLift_comp {A : Type*} [Ring A]
    (f : (n : PositiveModulus) → R →+* ZMod n.val) (hf : ∀ (m n : PositiveModulus) (h : m.val ∣ n.val) (x : R),
      ZMod.castHom h (ZMod m.val) (f n x) = f m x) (u : A →+* R) :
    (compatibleLift f hf).comp u =
      compatibleLift (fun n => (f n).comp u)
        (fun m n h x => hf m n h (u x)) := rfl


local instance (p : Nat.Primes) : Fact p.val.Prime := ⟨p.property⟩

/-- The product version of the same universal property. -/
noncomputable def padicFamilyLift
    (f : (p : Nat.Primes) → R →+* PadicInt p.val) : R →+* ProfiniteInt :=
  profinitePadicEquiv.symm.toRingHom.comp
    { toFun := fun x p => f p x
      map_zero' := funext fun p => (f p).map_zero
      map_one' := funext fun p => (f p).map_one
      map_add' := fun x y => funext fun p => (f p).map_add x y
      map_mul' := fun x y => funext fun p => (f p).map_mul x y }

@[simp] theorem padicProjection_familyLift
    (f : (p : Nat.Primes) → R →+* PadicInt p.val) (p : Nat.Primes) (x : R) :
    padicProjection p (padicFamilyLift f x) = f p x := by
  change profinitePadicEquiv (profinitePadicEquiv.symm (fun p => f p x)) p = _
  rw [profinitePadicEquiv.apply_symm_apply]

theorem padicFamilyLift_unique
    (f : (p : Nat.Primes) → R →+* PadicInt p.val) (g : R →+* ProfiniteInt)
    (hg : ∀ p x, padicProjection p (g x) = f p x) : g = padicFamilyLift f := by
  apply RingHom.ext
  intro x
  apply profinitePadicEquiv.injective
  funext p
  exact (hg p x).trans (padicProjection_familyLift f p x).symm

theorem continuous_padicFamilyLift [TopologicalSpace R]
    (f : (p : Nat.Primes) → R →+* PadicInt p.val)
    (hc : ∀ p, Continuous (f p)) : Continuous (padicFamilyLift f) :=
  isTopologicalRingCRT_profinitePadicEquiv.2.comp (continuous_pi fun p => hc p)

end RiemannResearch.NumberTheory.GeneralizedCRT
