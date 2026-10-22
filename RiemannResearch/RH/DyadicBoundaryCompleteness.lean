import RiemannResearch.RH.DyadicStepBoundary

/-!
# Completeness of the actual projected dyadic boundaries

Source: user-provided `DyadicRegularizedVerificationContinuation20260910.md`,
September 10, 2026; completed quotient boundary coordinates.

The constant and projected two-coordinate boundaries detect every dyadic
quotient vector. The proof uses the exact signed odd-step recurrence and
recovers physical coordinates from consecutive integer-step pairings.
No arithmetic Gram estimate, Mobius cancellation, or RH assumption is used.
-/

namespace RiemannResearch.RH.Pareto
noncomputable section

/-- The physical constant and all projected finite Haar details. -/
def dyadicBoundarySpan : Submodule ℝ ThresholdHilbert :=
  Submodule.span ℝ {g | g = hilbertOne ∨
    ∃ l : ℕ, ∃ hl : 0 < l,
      g = dyadicQuotientProjection (dyadicStepBoundary l hl)}

/-- The odd/even refinement recursion transfers vanishing of the boundary
pairings and mean into vanishing of every projected integer-step pairing. -/
theorem dyadicProjectedStep_inner_zero_of_boundaries
    (f : ThresholdHilbert) (hmean : inner ℝ hilbertOne f = 0)
    (hbound : ∀ l (hl : 0 < l),
      inner ℝ (dyadicQuotientProjection (dyadicStepBoundary l hl)) f = 0)
    (m : ℕ) (hm : 0 < m) : inner ℝ (dyadicProjectedStep m hm) f = 0 := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases h1 : m = 1
    · subst m
      simpa only [dyadicProjectedStep_one] using hmean
    have hm2 : 2 ≤ m := by omega
    have hl : 0 < m / 2 := Nat.div_pos_iff.mpr ⟨by norm_num, hm2⟩
    have hmod := Nat.mod_lt m (by norm_num : 0 < 2)
    have hdecomp := Nat.mod_add_div m 2
    by_cases he : m % 2 = 0
    · have hmform : m = 2 * (m / 2) := by omega
      have hsmall : m / 2 < m := by omega
      have hv : dyadicProjectedStep m hm = dyadicProjectedStep (m / 2) hl := by
        simpa only [← hmform] using dyadicProjectedStep_double (m / 2) hl
      rw [hv]
      exact ih (m / 2) hsmall hl
    · have hmform : m = 2 * (m / 2) + 1 := by omega
      have hsmall : m / 2 < m := by omega
      have hsmall' : m / 2 + 1 < m := by omega
      have hv : dyadicProjectedStep m hm =
          dyadicQuotientProjection (dyadicStepBoundary (m / 2) hl) +
            (1 / 2 : ℝ) • (dyadicProjectedStep (m / 2) hl +
              dyadicProjectedStep (m / 2 + 1) (by positivity)) := by
        simpa only [← hmform] using dyadicProjectedStep_odd_recurrence (m / 2) hl
      rw [hv, inner_add_left, real_inner_smul_left, inner_add_left,
        hbound (m / 2) hl, ih (m / 2) hsmall hl,
        ih (m / 2 + 1) hsmall' (by positivity)]
      norm_num

/-- No undetected quotient component remains after all boundary and mean
coordinates vanish. This is the unconditional completeness endpoint. -/
theorem dyadicQuotientProjection_eq_zero_of_boundary_inner
    (f : ThresholdHilbert) (hmean : inner ℝ hilbertOne f = 0)
    (hbound : ∀ l (hl : 0 < l),
      inner ℝ (dyadicQuotientProjection (dyadicStepBoundary l hl)) f = 0) :
    dyadicQuotientProjection f = 0 := by
  have hpair (d : ℕ) (hd : 0 < d) :
      inner ℝ (hilbertDilation d hd hilbertOne) (dyadicQuotientProjection f) = 0 := by
    have h := dyadicProjectedStep_inner_zero_of_boundaries f hmean hbound d hd
    change inner ℝ (dyadicQuotientProjection (hilbertDilation d hd hilbertOne)) f = 0 at h
    rwa [dyadicQuotientProjection_inner] at h
  apply hilbertSequence_injective
  change hilbertSequenceLinear (dyadicQuotientProjection f) = hilbertSequenceLinear 0
  rw [map_zero]
  funext k
  change hilbertSequence (dyadicQuotientProjection f) k = 0
  by_cases hk : k = 0
  · subst k
    simp
  · have hkp : 0 < k := Nat.pos_of_ne_zero hk
    have ha := hilbertAtom_inner k hkp (dyadicQuotientProjection f)
    rw [hilbertAtom, hilbertTail, hilbertTail, inner_sub_left,
      real_inner_smul_left, real_inner_smul_left,
      hpair k hkp, hpair (k + 1) (by omega)] at ha
    have hw : positiveWeight k ≠ 0 := by unfold positiveWeight; positivity
    apply (mul_eq_zero.mp (show positiveWeight k *
      hilbertSequence (dyadicQuotientProjection f) k = 0 by
        simpa using ha.symm)).resolve_left hw

theorem dyadicQuotient_eq_zero_of_boundary_inner
    (f : ThresholdHilbert) (hf : f ∈ dyadicQuotientSubspace)
    (hmean : inner ℝ hilbertOne f = 0)
    (hbound : ∀ l (hl : 0 < l),
      inner ℝ (dyadicQuotientProjection (dyadicStepBoundary l hl)) f = 0) :
    f = 0 := by
  have hfix : dyadicQuotientProjection f = f :=
    Submodule.starProjection_eq_self_iff.mpr hf
  rw [← hfix]
  exact dyadicQuotientProjection_eq_zero_of_boundary_inner f hmean hbound

/-- Equality of all actual boundary coordinates and the mean determines the
quotient vector exactly, with no missing orthogonal summand. -/
theorem dyadicQuotientProjection_eq_of_boundary_inner
    (f g : ThresholdHilbert)
    (hmean : inner ℝ hilbertOne f = inner ℝ hilbertOne g)
    (hbound : ∀ l (hl : 0 < l),
      inner ℝ (dyadicQuotientProjection (dyadicStepBoundary l hl)) f =
        inner ℝ (dyadicQuotientProjection (dyadicStepBoundary l hl)) g) :
    dyadicQuotientProjection f = dyadicQuotientProjection g := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply dyadicQuotientProjection_eq_zero_of_boundary_inner
  · rw [inner_sub_right, hmean, sub_self]
  · intro l hl
    rw [inner_sub_right, hbound l hl, sub_self]

theorem dyadicBoundarySpan_le_quotient : dyadicBoundarySpan ≤ dyadicQuotientSubspace := by
  apply Submodule.span_le.mpr
  rintro g (rfl | ⟨l, hl, rfl⟩)
  · rw [← dyadicQuotientProjection_one]
    exact dyadicQuotientProjection_mem _
  · exact dyadicQuotientProjection_mem _

/-- The constant and the projected weighted dyadic boundary family span the
whole completed quotient densely. This supplies actual boundary completeness. -/
theorem dyadicBoundarySpan_closure_eq_quotient :
    dyadicBoundarySpan.topologicalClosure = dyadicQuotientSubspace := by
  apply le_antisymm
  · exact dyadicBoundarySpan.topologicalClosure_minimal
      dyadicBoundarySpan_le_quotient (Submodule.isClosed_orthogonal _)
  · intro f hf
    rw [← Submodule.orthogonal_orthogonal_eq_closure]
    apply (Submodule.mem_orthogonal _ _).mpr
    intro g hg
    have hmean : inner ℝ hilbertOne g = 0 :=
      (Submodule.mem_orthogonal _ _).mp hg hilbertOne
        (Submodule.subset_span (Or.inl rfl))
    have hbound (l : ℕ) (hl : 0 < l) :
        inner ℝ (dyadicQuotientProjection (dyadicStepBoundary l hl)) g = 0 :=
      (Submodule.mem_orthogonal _ _).mp hg _
        (Submodule.subset_span (Or.inr ⟨l, hl, rfl⟩))
    have hQg := dyadicQuotientProjection_eq_zero_of_boundary_inner g hmean hbound
    have hfix : dyadicQuotientProjection f = f :=
      Submodule.starProjection_eq_self_iff.mpr hf
    rw [← hfix, ← dyadicQuotientProjection_inner, hQg, inner_zero_left]

end
end RiemannResearch.RH.Pareto
