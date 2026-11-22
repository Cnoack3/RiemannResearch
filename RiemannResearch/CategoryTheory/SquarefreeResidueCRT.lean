import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.ZMod.QuotientRing

/-!
# The residue diagram of squarefree conductors

A finite set of primes determines a squarefree conductor. Reduction to a
divisor restricts its prime coordinates. The CRT equivalences intertwine
these maps and exhibit each residue ring as a categorical product.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

namespace RiemannResearch.SquarefreeResidueCRT

/-- The inclusion poset of finite sets of distinct primes. -/
abbrev PrimeFamily := {s : Finset ℕ // ∀ p ∈ s, Nat.Prime p}

def conductor (S : PrimeFamily) : ℕ := ∏ p : S.val, p.val

def primeSupport (q : ℕ) : PrimeFamily :=
  ⟨q.primeFactors, fun _ hp => Nat.prime_of_mem_primeFactors hp⟩

theorem conductor_eq_prod (S : PrimeFamily) : conductor S = ∏ p ∈ S.val, p := by
  exact Finset.prod_attach S.val id

theorem primeFactors_conductor (S : PrimeFamily) : (conductor S).primeFactors = S.val := by
  rw [conductor_eq_prod]
  exact Nat.primeFactors_prod S.property

theorem conductor_primeSupport {q : ℕ} (hq : Squarefree q) : conductor (primeSupport q) = q :=
  (conductor_eq_prod _).trans (Nat.prod_primeFactors_of_squarefree hq)

theorem conductor_squarefree (S : PrimeFamily) : Squarefree (conductor S) := by
  rw [conductor_eq_prod]
  obtain ⟨s, hs⟩ := S
  change Squarefree (∏ p ∈ s, p)
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
    have hprime := hs p (Finset.mem_insert_self p s)
    have hs' : ∀ k ∈ s, Nat.Prime k := fun k hk => hs k (Finset.mem_insert_of_mem hk)
    have hn : ∏ k ∈ s, k ≠ 0 := Finset.prod_ne_zero_iff.2 fun k hk => (hs' k hk).ne_zero
    have hc : p.Coprime (∏ k ∈ s, k) := hprime.coprime_iff_not_dvd.2 fun hd => hp <| by
      rw [← Nat.primeFactors_prod hs']
      exact (Nat.mem_primeFactors_of_ne_zero hn).2 ⟨hprime, hd⟩
    rw [Finset.prod_insert hp, Nat.squarefree_mul hc]
    exact ⟨hprime.squarefree, ih hs'⟩

theorem conductor_dvd {S T : PrimeFamily} (h : S ≤ T) : conductor S ∣ conductor T := by
  rw [conductor_eq_prod, conductor_eq_prod]
  exact Finset.prod_dvd_prod_of_subset _ _ _ h

/-- One finite residue field at each prime of the conductor. -/
abbrev Coordinates (S : PrimeFamily) := (p : S.val) → ZMod p.val

private theorem pairwise (S : PrimeFamily) :
    Pairwise fun i j : S.val => Nat.Coprime i.val j.val :=
  fun i j h => (Nat.coprime_primes (S.property _ i.property) (S.property _ j.property)).2
    (fun he => h (Subtype.ext he))

def crtEquiv (S : PrimeFamily) : ZMod (conductor S) ≃+* Coordinates S :=
  ZMod.prodEquivPi (fun p : S.val => p.val) (pairwise S)

theorem crtEquiv_apply (S : PrimeFamily) (x : ZMod (conductor S)) (p : S.val) :
    crtEquiv S x p =
      ZMod.castHom (Finset.dvd_prod_of_mem (fun i : S.val => i.val) (Finset.mem_univ p)) _ x :=
  ZMod.prodEquivPi_apply _ _ _ _

def squarefreeEquiv (q : ℕ) (hq : Squarefree q) :
    ZMod q ≃+* ((p : q.primeFactors) → ZMod p.val) :=
  (ZMod.ringEquivCongr (conductor_primeSupport hq).symm).trans (crtEquiv (primeSupport q))

def restrictCoordinates {S T : PrimeFamily} (h : S ≤ T) : Coordinates T →+* Coordinates S where
  toFun x p := x ⟨p.val, h p.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- A prime-set inclusion gives reduction in the reverse direction. -/
def residueFunctor : PrimeFamilyᵒᵖ ⥤ CommRingCat where
  obj S := CommRingCat.of (ZMod (conductor S.unop))
  map f := CommRingCat.ofHom (ZMod.castHom (conductor_dvd (leOfHom f.unop)) _)
  map_id _ := CommRingCat.hom_ext (RingHom.ext_zmod _ _)
  map_comp _ _ := CommRingCat.hom_ext (RingHom.ext_zmod _ _)

def coordinateFunctor : PrimeFamilyᵒᵖ ⥤ CommRingCat where
  obj S := CommRingCat.of (Coordinates S.unop)
  map f := CommRingCat.ofHom (restrictCoordinates (leOfHom f.unop))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- CRT is a natural isomorphism for all subfamilies, including the empty one. -/
def crtIso : residueFunctor ≅ coordinateFunctor :=
  NatIso.ofComponents (fun S => (crtEquiv S.unop).toCommRingCatIso) (by
    intro S T f
    exact CommRingCat.hom_ext (RingHom.ext_zmod _ _))

/-- The product cone has the residue ring itself as its vertex. -/
def primeFan (S : PrimeFamily) : Fan (fun p : S.val => CommRingCat.of (ZMod p.val)) :=
  Fan.mk (CommRingCat.of (ZMod (conductor S))) fun p =>
    CommRingCat.ofHom ((Pi.evalRingHom _ p).comp (crtEquiv S).toRingHom)

private def glue (S : PrimeFamily) (s : Fan (fun p : S.val => CommRingCat.of (ZMod p.val))) :
    s.pt ⟶ (primeFan S).pt :=
  CommRingCat.ofHom ((crtEquiv S).symm.toRingHom.comp (RingHom.pi fun p => (s.proj p).hom))

private theorem glue_proj (S : PrimeFamily) (s : Fan (fun p : S.val => CommRingCat.of (ZMod p.val)))
    (p : S.val) : glue S s ≫ (primeFan S).proj p = s.proj p := by
  apply ConcreteCategory.hom_ext
  intro x
  exact congrFun ((crtEquiv S).apply_symm_apply fun j => s.proj j x) p

/-- Maps into the squarefree residue ring are uniquely determined by their prime coordinates. -/
def primeFanIsLimit (S : PrimeFamily) : IsLimit (primeFan S) :=
  Fan.IsLimit.mk _ (glue S) (glue_proj S) (by
    intro s m hm
    apply ConcreteCategory.hom_ext
    intro x
    apply (crtEquiv S).injective
    funext p
    exact (ConcreteCategory.congr_hom (hm p) x).trans
      (ConcreteCategory.congr_hom (glue_proj S s p) x).symm)

end RiemannResearch.SquarefreeResidueCRT
