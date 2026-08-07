/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.GaloisCohomology.NonabelianH1

/-!
# Local-gauge transporters for nonabelian one-cocycles

Let a group Γ act by automorphisms on a group G, and let a be a
nonabelian one-cocycle. Suppose a family of subgroups H i generates Γ
and u i is a gauge trivializing the restriction of a to H i.

The transition from gauge j to gauge i is u i * (u j)⁻¹.

This module proves that transitions are fixed on pairwise overlaps and satisfy
the expected composition law. Its main theorem says that a is a global
coboundary exactly when the transitions can be written using corrections
c i fixed by the corresponding subgroups:

u i * (u j)⁻¹ = c i * (c j)⁻¹.

This is the abstract transporter/gluing criterion used by the full-Weyl EVIII
descent program. It does **not** prove that the required fixed corrections
exist in the E₈ application; that is the remaining geometric factorization
problem.
-/

universe u v w

namespace RiemannResearch.GaloisCohomology
namespace NonabelianCocycle

variable {Γ : Type u} {G : Type v} {I : Type w}
variable [Group Γ] [Group G] [MulDistribMulAction Γ G]

/-- Every nonabelian one-cocycle takes the identity to the identity. -/
@[simp]
theorem map_one (a : NonabelianCocycle Γ G) : a 1 = 1 := by
  have h := congrArg (fun x : G => (a 1)⁻¹ * x) (a.map_mul' 1 1)
  simpa [mul_assoc] using h.symm

/-- The subgroup on which a cocycle agrees with the coboundary having
global gauge b. -/
def agreementSubgroup (a : NonabelianCocycle Γ G) (b : G) : Subgroup Γ where
  carrier := {σ | a σ = b⁻¹ * (σ • b)}
  one_mem' := by simp
  mul_mem' := by
    intro σ τ hσ hτ
    calc
      a (σ * τ) = a σ * (σ • a τ) := a.map_mul' σ τ
      _ = (b⁻¹ * (σ • b)) * (σ • (b⁻¹ * (τ • b))) := by rw [hσ, hτ]
      _ = b⁻¹ * ((σ * τ) • b) := by
        simp [smul_mul', mul_smul, mul_assoc]
  inv_mem' := by
    intro σ hσ
    have hleft : a σ⁻¹ * (σ⁻¹ • a σ) = 1 := by
      calc
        a σ⁻¹ * (σ⁻¹ • a σ) = a (σ⁻¹ * σ) := (a.map_mul' σ⁻¹ σ).symm
        _ = 1 := by simp
    have hright :
        (b⁻¹ * (σ⁻¹ • b)) * (σ⁻¹ • a σ) = 1 := by
      rw [hσ]
      simp [smul_mul', mul_assoc]
    exact mul_right_cancel (hleft.trans hright.symm)

/-- Pointwise fixedness of an element of G under a subgroup of Γ. -/
def IsFixedBy (H : Subgroup Γ) (x : G) : Prop :=
  ∀ σ, σ ∈ H → σ • x = x

/-- The element x is a gauge trivializing a on H. -/
def IsLocalGauge
    (a : NonabelianCocycle Γ G) (H : Subgroup Γ) (x : G) : Prop :=
  ∀ σ, σ ∈ H → a σ = x⁻¹ * (σ • x)

/-- Transition from local gauge j to local gauge i. -/
def transition (u : I → G) (i j : I) : G :=
  u i * (u j)⁻¹

/-- A local gauge has trivial self-transition. -/
@[simp]
theorem transition_self (u : I → G) (i : I) :
    transition u i i = 1 := by
  simp [transition]

/-- Reversing a transition takes its inverse. -/
theorem transition_inv (u : I → G) (i j : I) :
    (transition u i j)⁻¹ = transition u j i := by
  simp [transition]

/-- Transitions compose on triple overlaps. -/
theorem transition_mul (u : I → G) (i j k : I) :
    transition u i j * transition u j k = transition u i k := by
  simp [transition, mul_assoc]

/-- Left changes of local gauge act on transitions on the left and right. -/
theorem transition_left_mul (u c : I → G) (i j : I) :
    transition (fun k => c k * u k) i j =
      c i * transition u i j * (c j)⁻¹ := by
  simp [transition, mul_assoc]

/-- Two local gauges of one cocycle have an ordinarily fixed transition on
their subgroup overlap. -/
theorem transition_fixed_on_inf
    (a : NonabelianCocycle Γ G) (H : I → Subgroup Γ) (u : I → G)
    (hlocal : ∀ i, a.IsLocalGauge (H i) (u i))
    (i j : I) :
    IsFixedBy (H i ⊓ H j) (transition u i j) := by
  intro σ hσ
  have hi := hlocal i σ hσ.1
  have hj := hlocal j σ hσ.2
  have heq : (u i)⁻¹ * (σ • u i) = (u j)⁻¹ * (σ • u j) :=
    hi.symm.trans hj
  have h := congrArg
    (fun x : G => u i * x * (σ • u j)⁻¹) heq
  have h' : (σ • u i) * (σ • u j)⁻¹ = u i * (u j)⁻¹ := by
    simpa [mul_assoc] using h
  simpa [transition, smul_mul'] using h'

/-- If a cocycle agrees with one global gauge on a generating family of
subgroups, then that gauge trivializes the cocycle globally. -/
theorem eq_trivial_gauge_of_generating_family
    (a : NonabelianCocycle Γ G) (b : G) (H : I → Subgroup Γ)
    (hgen : (⨆ i, H i) = ⊤)
    (hagrees : ∀ i, H i ≤ agreementSubgroup a b) :
    a = trivial.gauge b := by
  have hall : (⊤ : Subgroup Γ) ≤ agreementSubgroup a b := by
    rw [← hgen]
    exact iSup_le hagrees
  ext σ
  have hσ := hall (show σ ∈ (⊤ : Subgroup Γ) by simp)
  change a σ = b⁻¹ * (σ • b) at hσ
  simpa [trivial, gauge] using hσ

/-- **Generating-family transporter criterion.**

Let the subgroups H i generate Γ, and let u i trivialize a
nonabelian cocycle a on H i. Then a is a global coboundary if and
only if there are corrections c i, fixed by H i, whose transition
system equals that of the local gauges.

In the full-Weyl EVIII application, H i are the preimages of the 135
D₈ stabilizers. This theorem proves the exact gluing criterion, but it does
not supply the E₈-specific fixed corrections.
-/
theorem isCoboundary_iff_exists_fixedGaugeCorrections
    [Nonempty I]
    (a : NonabelianCocycle Γ G)
    (H : I → Subgroup Γ) (u : I → G)
    (hgen : (⨆ i, H i) = ⊤)
    (hlocal : ∀ i, a.IsLocalGauge (H i) (u i)) :
    a.IsCoboundary ↔
      ∃ c : I → G,
        (∀ i, IsFixedBy (H i) (c i)) ∧
        (∀ i j, transition u i j = transition c i j) := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨fun i => u i * b⁻¹, ?_, ?_⟩
    · intro i σ hσ
      have hbσ : a σ = b⁻¹ * (σ • b) := by
        rw [hb]
        simp [trivial, gauge]
      have heq : (u i)⁻¹ * (σ • u i) = b⁻¹ * (σ • b) :=
        (hlocal i σ hσ).symm.trans hbσ
      have h := congrArg
        (fun x : G => u i * x * (σ • b)⁻¹) heq
      have h' : (σ • u i) * (σ • b)⁻¹ = u i * b⁻¹ := by
        simpa [mul_assoc] using h
      simpa [IsFixedBy, smul_mul'] using h'
    · intro i j
      simp [transition, mul_assoc]
  · rintro ⟨c, hfixed, htransition⟩
    let i₀ : I := Classical.choice (inferInstance : Nonempty I)
    let b : G := (c i₀)⁻¹ * u i₀
    have hbi (i : I) : (c i)⁻¹ * u i = b := by
      have h := congrArg
        (fun x : G => (c i)⁻¹ * x * u i₀) (htransition i i₀)
      simpa [transition, b, mul_assoc] using h
    have hui (i : I) : u i = c i * b := by
      calc
        u i = c i * ((c i)⁻¹ * u i) := by simp
        _ = c i * b := by rw [hbi i]
    have hagrees : ∀ i, H i ≤ agreementSubgroup a b := by
      intro i σ hσ
      change a σ = b⁻¹ * (σ • b)
      calc
        a σ = (u i)⁻¹ * (σ • u i) := hlocal i σ hσ
        _ = b⁻¹ * (σ • b) := by
          rw [hui i]
          simp [smul_mul', hfixed i σ hσ, mul_assoc]
    refine ⟨b, ?_⟩
    exact eq_trivial_gauge_of_generating_family a b H hgen hagrees

/-- **Anchored generating-family transporter criterion.**

Choose one local gauge as an anchor. Global neutrality is equivalent to the
existence of a single element `c₀` such that, for every index `i`, translating
`c₀` by the transition from `i₀` to `i` is fixed by `H i`.

The condition at `i = i₀` says that `c₀` itself is fixed by `H i₀`. Every
other correction is then forced to be
`transition u i i₀ * c₀`; the transition identities make all pairwise
factorization equations automatic.

For the full-Weyl E₈ application with the 135 `D₈` stabilizers, this reduces
the unresolved correction system to one anchor element and 135 fixedness
conditions. It does not assert that such an E₈-valued anchor exists.
-/
theorem isCoboundary_iff_exists_anchoredFixedGaugeCorrection
    (a : NonabelianCocycle Γ G)
    (H : I → Subgroup Γ) (u : I → G) (i₀ : I)
    (hgen : (⨆ i, H i) = ⊤)
    (hlocal : ∀ i, a.IsLocalGauge (H i) (u i)) :
    a.IsCoboundary ↔
      ∃ c₀ : G,
        ∀ i, IsFixedBy (H i) (transition u i i₀ * c₀) := by
  let _ : Nonempty I := ⟨i₀⟩
  constructor
  · intro ha
    obtain ⟨c, hfixed, htransition⟩ :=
      (isCoboundary_iff_exists_fixedGaugeCorrections a H u hgen hlocal).mp ha
    refine ⟨c i₀, ?_⟩
    intro i
    rw [htransition i i₀]
    simpa [transition] using hfixed i
  · rintro ⟨c₀, hc⟩
    apply
      (isCoboundary_iff_exists_fixedGaugeCorrections a H u hgen hlocal).mpr
    refine ⟨fun i => transition u i i₀ * c₀, hc, ?_⟩
    intro i j
    simp [transition, mul_assoc]

end NonabelianCocycle
end RiemannResearch.GaloisCohomology
