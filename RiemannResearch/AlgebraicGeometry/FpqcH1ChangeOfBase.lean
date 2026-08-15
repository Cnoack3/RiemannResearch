import RiemannResearch.AlgebraicGeometry.FpqcH1Functoriality

namespace RiemannResearch.AlgebraicGeometry

open CategoryTheory

universe uC vC uD vD uI wG u v

noncomputable section

/-! ## Different-site fixed-cover H¹ -/

namespace PresheafH1

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable (F : D ⥤ C)
variable {G : Cᵒᵖ ⥤ GrpCat.{wG}}
variable {H : Dᵒᵖ ⥤ GrpCat.{wG}}
variable (η : F.op ⋙ G ⟶ H)
variable {I : Type uI}
variable {U : I → C} {V : I → D}
variable (p : ∀ i, F.obj (V i) ⟶ U i)

def changeBaseOneCochain
    (γ : PresheafOfGroups.OneCochain G U) :
    PresheafOfGroups.OneCochain H V where
  ev i j T a b :=
    (η.app (Opposite.op T)).hom
      (γ.ev i j (F.map a ≫ p i) (F.map b ≫ p j))
  ev_precomp := by
    intro i j T T' φ a b
    rw [naturality_apply η φ.op]
    change
      (η.app (Opposite.op T)).hom
          ((G.map (F.map φ).op).hom
            (γ.ev i j (F.map a ≫ p i) (F.map b ≫ p j))) =
        (η.app (Opposite.op T)).hom
          (γ.ev i j (F.map (φ ≫ a) ≫ p i) (F.map (φ ≫ b) ≫ p j))
    apply congrArg (η.app (Opposite.op T)).hom
    rw [γ.ev_precomp]
    simp only [F.map_comp, Category.assoc]

def changeBaseOneCocycle
    (γ : PresheafOfGroups.OneCocycle G U) :
    PresheafOfGroups.OneCocycle H V where
  toOneCochain := changeBaseOneCochain F η p γ.toOneCochain
  ev_trans := by
    intro i j k T a b c
    change
      (η.app (Opposite.op T)).hom
          (γ.ev i j (F.map a ≫ p i) (F.map b ≫ p j)) *
        (η.app (Opposite.op T)).hom
          (γ.ev j k (F.map b ≫ p j) (F.map c ≫ p k)) =
      (η.app (Opposite.op T)).hom
          (γ.ev i k (F.map a ≫ p i) (F.map c ≫ p k))
    rw [← map_mul, γ.ev_trans]

def changeBaseZeroCochain
    (α : PresheafOfGroups.ZeroCochain G U) :
    PresheafOfGroups.ZeroCochain H V :=
  fun i =>
    (η.app (Opposite.op (V i))).hom
      ((G.map (p i).op).hom (α i))

theorem changeBase_oneCohomologyRelation
    {γ₁ γ₂ : PresheafOfGroups.OneCocycle G U}
    {α : PresheafOfGroups.ZeroCochain G U}
    (h : PresheafOfGroups.OneCohomologyRelation
      γ₁.toOneCochain γ₂.toOneCochain α) :
    PresheafOfGroups.OneCohomologyRelation
      (changeBaseOneCocycle F η p γ₁).toOneCochain
      (changeBaseOneCocycle F η p γ₂).toOneCochain
      (changeBaseZeroCochain F η p α) := by
  intro i j T a b
  change
    (H.map a.op).hom
        ((η.app (Opposite.op (V i))).hom ((G.map (p i).op).hom (α i))) *
      (η.app (Opposite.op T)).hom
        (γ₁.ev i j (F.map a ≫ p i) (F.map b ≫ p j)) =
    (η.app (Opposite.op T)).hom
        (γ₂.ev i j (F.map a ≫ p i) (F.map b ≫ p j)) *
      (H.map b.op).hom
        ((η.app (Opposite.op (V j))).hom ((G.map (p j).op).hom (α j)))
  rw [naturality_apply η a.op, naturality_apply η b.op]
  rw [← map_mul, ← map_mul]
  apply congrArg (η.app (Opposite.op T)).hom
  simpa [Functor.comp_map, Functor.op_map, ← ConcreteCategory.comp_apply,
    ← G.map_comp, ← op_comp, Category.assoc] using
    h i j (F.map a ≫ p i) (F.map b ≫ p j)

theorem changeBase_isCohomologous
    {γ₁ γ₂ : PresheafOfGroups.OneCocycle G U}
    (h : γ₁.IsCohomologous γ₂) :
    (changeBaseOneCocycle F η p γ₁).IsCohomologous
      (changeBaseOneCocycle F η p γ₂) := by
  rcases h with ⟨α, hα⟩
  exact ⟨changeBaseZeroCochain F η p α,
    changeBase_oneCohomologyRelation F η p hα⟩

def changeBase :
    PresheafOfGroups.H1 G U → PresheafOfGroups.H1 H V :=
  Quot.lift
    (fun γ => (changeBaseOneCocycle F η p γ).class)
    (fun _ _ h => (changeBase_isCohomologous F η p h).class_eq)

@[simp] theorem changeBase_class
    (γ : PresheafOfGroups.OneCocycle G U) :
    changeBase F η p γ.class =
      (changeBaseOneCocycle F η p γ).class :=
  rfl

@[simp] theorem changeBase_one :
    changeBase F η p (1 : PresheafOfGroups.H1 G U) =
      (1 : PresheafOfGroups.H1 H V) := by
  change
    (changeBaseOneCocycle F η p
      (1 : PresheafOfGroups.OneCocycle G U)).class =
      (1 : PresheafOfGroups.OneCocycle H V).class
  apply congrArg PresheafOfGroups.OneCocycle.class
  apply cocycle_ext
  apply PresheafOfGroups.OneCochain.ext
  funext i j T a b
  exact MonoidHom.map_one (η.app (Opposite.op T)).hom

end PresheafH1

/-! ## Minimal quotient descent interface -/

structure FpqcH1ChangeOfBaseData
    (R A S B : CommRingCat.{u})
    [HopfAlgebra R A] [HopfAlgebra S B] where
  mapCover : {I : Type v} → FpqcCover R I → FpqcCover S I
  mapRefinement :
    {I J : Type v} → {U : FpqcCover R I} → {V : FpqcCover R J} →
      V.Refinement U → (mapCover V).Refinement (mapCover U)
  mapH1 :
    {I : Type v} → (U : FpqcCover R I) →
      FpqcCechH1 R A U → FpqcCechH1 S B (mapCover U)
  mapH1_pullback :
    ∀ {I J : Type v} {U : FpqcCover R I} {V : FpqcCover R J}
      (r : V.Refinement U) (ξ : FpqcCechH1 R A U),
      mapH1 V (r.pullbackH1 ξ) =
        (mapRefinement r).pullbackH1 (mapH1 U ξ)
  mapH1_neutral :
    ∀ {I : Type v} (U : FpqcCover R I),
      mapH1 U (FpqcCechH1.neutral R A U) =
        FpqcCechH1.neutral S B (mapCover U)

namespace FpqcH1ChangeOfBaseData

variable {R A S B : CommRingCat.{u}}
variable [HopfAlgebra R A] [HopfAlgebra S B]
variable (D : FpqcH1ChangeOfBaseData.{u, v} R A S B)

def mapRepresentative
    (a : FpqcH1Representative.{u, v} R A) :
    FpqcH1Representative.{u, v} S B where
  I := a.I
  cover := D.mapCover a.cover
  value := D.mapH1 a.cover a.value

theorem mapRepresentative_equivalent
    {a b : FpqcH1Representative.{u, v} R A}
    (h : FpqcH1Representative.Equivalent R A a b) :
    FpqcH1Representative.Equivalent S B
      (D.mapRepresentative a) (D.mapRepresentative b) := by
  rcases h with ⟨K, W, ra, rb, hab⟩
  refine ⟨K, D.mapCover W, D.mapRefinement ra, D.mapRefinement rb, ?_⟩
  change
    (D.mapRefinement ra).pullbackH1 (D.mapH1 a.cover a.value) =
      (D.mapRefinement rb).pullbackH1 (D.mapH1 b.cover b.value)
  rw [← D.mapH1_pullback ra a.value, ← D.mapH1_pullback rb b.value, hab]

def toFun : FpqcH1.{u, v} R A → FpqcH1.{u, v} S B :=
  Quotient.map D.mapRepresentative
    (fun _ _ h => D.mapRepresentative_equivalent h)

@[simp] theorem toFun_classOf
    {I : Type v} (U : FpqcCover R I) (ξ : FpqcCechH1 R A U) :
    D.toFun (FpqcH1.classOf R A U ξ) =
      FpqcH1.classOf S B (D.mapCover U) (D.mapH1 U ξ) :=
  rfl

@[simp] theorem toFun_neutral :
    D.toFun (FpqcH1.neutral R A) = FpqcH1.neutral S B := by
  rw [FpqcH1.neutral, D.toFun_classOf, D.mapH1_neutral]
  exact FpqcH1.classOf_neutral S B
    (D.mapCover (FpqcH1.trivialCover R))

end FpqcH1ChangeOfBaseData

/-! ## Geometric data producing the quotient interface -/

structure FpqcH1GeometricChangeOfBaseData
    (R A S B : CommRingCat.{u})
    [HopfAlgebra R A] [HopfAlgebra S B] where
  restrict :
    Over (_root_.AlgebraicGeometry.Spec S) ⥤
      Over (_root_.AlgebraicGeometry.Spec R)
  coefficient :
    restrict.op ⋙ affineGroupPresheaf R A ⟶ affineGroupPresheaf S B
  mapCover : {I : Type v} → FpqcCover R I → FpqcCover S I
  coverProjection :
    {I : Type v} → (U : FpqcCover R I) → ∀ i,
      restrict.obj ((mapCover U).obj i) ⟶ U.obj i
  mapRefinementHom :
    {I J : Type v} → {U : FpqcCover R I} → {V : FpqcCover R J} →
      (r : V.Refinement U) → ∀ j,
        (mapCover V).obj j ⟶ (mapCover U).obj (r.index j)
  mapRefinementHom_projection :
    ∀ {I J : Type v} {U : FpqcCover R I} {V : FpqcCover R J}
      (r : V.Refinement U) (j : J),
      restrict.map (mapRefinementHom r j) ≫
          coverProjection U (r.index j) =
        coverProjection V j ≫ r.hom j

namespace FpqcH1GeometricChangeOfBaseData

variable {R A S B : CommRingCat.{u}}
variable [HopfAlgebra R A] [HopfAlgebra S B]
variable (D : FpqcH1GeometricChangeOfBaseData.{u, v} R A S B)

def mapRefinement
    {I J : Type v} {U : FpqcCover R I} {V : FpqcCover R J}
    (r : V.Refinement U) :
    (D.mapCover V).Refinement (D.mapCover U) where
  index := r.index
  hom := D.mapRefinementHom r

def mapH1 {I : Type v} (U : FpqcCover R I) :
    FpqcCechH1 R A U → FpqcCechH1 S B (D.mapCover U) :=
  PresheafH1.changeBase D.restrict D.coefficient (D.coverProjection U)

theorem mapH1_pullback
    {I J : Type v} {U : FpqcCover R I} {V : FpqcCover R J}
    (r : V.Refinement U) (ξ : FpqcCechH1 R A U) :
    D.mapH1 V (r.pullbackH1 ξ) =
      (D.mapRefinement r).pullbackH1 (D.mapH1 U ξ) := by
  refine Quot.inductionOn ξ ?_
  intro γ
  change
    (PresheafH1.changeBaseOneCocycle D.restrict D.coefficient
      (D.coverProjection V) (r.pullbackOneCocycle γ)).class =
    ((D.mapRefinement r).pullbackOneCocycle
      (PresheafH1.changeBaseOneCocycle D.restrict D.coefficient
        (D.coverProjection U) γ)).class
  apply congrArg PresheafOfGroups.OneCocycle.class
  apply PresheafH1.cocycle_ext
  apply PresheafOfGroups.OneCochain.ext
  funext j k T a b
  change
    (D.coefficient.app (Opposite.op T)).hom
      (γ.ev (r.index j) (r.index k)
        (D.restrict.map a ≫ D.coverProjection V j ≫ r.hom j)
        (D.restrict.map b ≫ D.coverProjection V k ≫ r.hom k)) =
    (D.coefficient.app (Opposite.op T)).hom
      (γ.ev (r.index j) (r.index k)
        (D.restrict.map (a ≫ D.mapRefinementHom r j) ≫
          D.coverProjection U (r.index j))
        (D.restrict.map (b ≫ D.mapRefinementHom r k) ≫
          D.coverProjection U (r.index k)))
  apply congrArg (D.coefficient.app (Opposite.op T)).hom
  simp only [D.restrict.map_comp, Category.assoc,
    D.mapRefinementHom_projection]

@[simp] theorem mapH1_neutral
    {I : Type v} (U : FpqcCover R I) :
    D.mapH1 U (FpqcCechH1.neutral R A U) =
      FpqcCechH1.neutral S B (D.mapCover U) := by
  exact PresheafH1.changeBase_one D.restrict D.coefficient
    (D.coverProjection U)

def toChangeOfBaseData : FpqcH1ChangeOfBaseData.{u, v} R A S B where
  mapCover := D.mapCover
  mapRefinement := D.mapRefinement
  mapH1 := D.mapH1
  mapH1_pullback := D.mapH1_pullback
  mapH1_neutral := D.mapH1_neutral

end FpqcH1GeometricChangeOfBaseData

end

end RiemannResearch.AlgebraicGeometry
