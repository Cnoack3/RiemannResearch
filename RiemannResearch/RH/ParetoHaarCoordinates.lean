import RiemannResearch.RH.ParetoPacketCoordinates

/-!
# A complete Haar coordinate isometry for the actual Pareto Hilbert space

Source: user-provided argument, RH_CRT_Packet_Research_2026-09-09.md,
Section 7. The extra `none` index is the constant coordinate; `some n`
is the paper's h_(n+1). Mean-zero vectors have exactly zero `none` coordinate.
This uses a proved complete orthonormal family and Mathlib's HilbertBasis
construction, so the coordinate norm and reconstruction are not assumptions.
-/

namespace RiemannResearch.RH.Pareto
noncomputable section

def paretoHaarFamily : Option ℕ → ThresholdHilbert
  | none => hilbertOne
  | some n => tailBasisHilbert n

theorem paretoHaarFamily_orthonormal : Orthonormal ℝ paretoHaarFamily := by
  apply orthonormal_iff_ite.mpr
  intro i j
  cases i with
  | none =>
      cases j with
      | none => simp [paretoHaarFamily, real_inner_self_eq_norm_sq, hilbertOne_norm_sq]
      | some j =>
          change inner ℝ hilbertOne (tailBasisHilbert j) = 0
          rw [real_inner_comm, tailBasis_inner_one]
  | some i =>
      cases j with
      | none => simp [paretoHaarFamily, tailBasis_inner_one]
      | some j => simp [paretoHaarFamily, tailBasis_inner]

theorem paretoHaarFamily_total :
    (⊤ : Submodule ℝ ThresholdHilbert) ≤
      (Submodule.span ℝ (Set.range paretoHaarFamily)).topologicalClosure := by
  have ho : (Submodule.span ℝ (Set.range paretoHaarFamily))ᗮ = ⊥ := by
    apply le_antisymm
    · intro f hf
      have he : f = 0 := by
        apply tailBasis_total
        · rw [real_inner_comm]
          exact hf hilbertOne (Submodule.subset_span ⟨none, rfl⟩)
        · intro n
          rw [real_inner_comm]
          exact hf (tailBasisHilbert n) (Submodule.subset_span ⟨some n, rfl⟩)
      simpa [he]
    · exact bot_le
  rw [← Submodule.orthogonal_orthogonal_eq_closure, ho]
  intro f _hf
  change ∀ g ∈ (⊥ : Submodule ℝ ThresholdHilbert), inner ℝ g f = 0
  intro g hg
  have hg0 : g = 0 := hg
  simp [hg0]

/-- An actual complete Hilbert basis, including the constant coordinate. -/
def paretoHaarBasis : HilbertBasis (Option ℕ) ℝ ThresholdHilbert :=
  HilbertBasis.mk paretoHaarFamily_orthonormal paretoHaarFamily_total

@[simp] theorem paretoHaarBasis_apply (i : Option ℕ) :
    paretoHaarBasis i = paretoHaarFamily i := by
  exact congrFun (HilbertBasis.coe_mk paretoHaarFamily_orthonormal
    paretoHaarFamily_total) i

/-- The complete coordinate isometry. In particular, it preserves the full
infinite norm and has an inverse on all square-summable coordinate vectors. -/
def paretoHaarCoordinates :
    ThresholdHilbert ≃ₗᵢ[ℝ] lp (fun _ : Option ℕ => ℝ) 2 :=
  paretoHaarBasis.repr

theorem paretoHaarCoordinates_none (f : ThresholdHilbert) :
    paretoHaarCoordinates f none = inner ℝ f hilbertOne := by
  rw [paretoHaarCoordinates, HilbertBasis.repr_apply_apply, paretoHaarBasis_apply]
  exact real_inner_comm _ _

theorem paretoHaarCoordinates_some (f : ThresholdHilbert) (n : ℕ) :
    paretoHaarCoordinates f (some n) = inner ℝ f (tailBasisHilbert n) := by
  rw [paretoHaarCoordinates, HilbertBasis.repr_apply_apply, paretoHaarBasis_apply]
  exact real_inner_comm _ _

theorem paretoHaarCoordinates_norm (f : ThresholdHilbert) :
    ‖paretoHaarCoordinates f‖ = ‖f‖ := paretoHaarCoordinates.norm_map f

theorem paretoHaarCoordinates_mean_zero (f : ThresholdHilbert)
    (hmean : inner ℝ f hilbertOne = 0) : paretoHaarCoordinates f none = 0 := by
  rw [paretoHaarCoordinates_none, hmean]

/-- Exact coordinate reconstruction, including the complete infinite tail. -/
theorem paretoHaarCoordinates_reconstruct (f : ThresholdHilbert) :
    paretoHaarCoordinates.symm (paretoHaarCoordinates f) = f :=
  paretoHaarCoordinates.symm_apply_apply f

/-- Every square-summable family with zero constant coordinate reconstructs
an actual mean-zero Pareto vector. -/
theorem paretoHaarCoordinates_inverse_mean_zero
    (x : lp (fun _ : Option ℕ => ℝ) 2) (hx : x none = 0) :
    inner ℝ (paretoHaarCoordinates.symm x) hilbertOne = 0 := by
  rw [← paretoHaarCoordinates_none, paretoHaarCoordinates.apply_symm_apply, hx]

/-- Formula (31), in a bundled complete coordinate space. The extra constant
coordinate of the error is exactly zero by the preceding theorem. -/
theorem paretoHaarCoordinates_mean_one_energy (F : ThresholdHilbert)
    (hmean : inner ℝ F hilbertOne = 1) :
    ‖F‖ ^ 2 = 1 + ‖paretoHaarCoordinates (F - hilbertOne)‖ ^ 2 := by
  rw [paretoHaarCoordinates_norm]
  exact pareto_mean_one_norm_sq F hmean

end
end RiemannResearch.RH.Pareto
