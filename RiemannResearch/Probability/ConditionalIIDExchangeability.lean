import RiemannResearch.Probability.ConditionalIIDUniformModel

/-!
# Exchangeability of the entire conditional iid mixture

Source: user-provided `Conditional_IID_Cesaro_Mathematical_Completion_2026-09-17.md`,
Section 2. Infinite coordinate permutations preserve every product fiber and
therefore the actual joint law of the latent endpoint and the whole sequence.
-/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace RiemannResearch.Probability.ConditionalIID

def permutePath (π : Equiv.Perm ℕ) (x : Path) : Path := fun i => x (π i)

theorem permutePath_measurable (π : Equiv.Perm ℕ) : Measurable (permutePath π) :=
  measurable_pi_lambda _ (fun i => measurable_pi_apply (π i))

/-- Every fiber is invariant under arbitrary permutations of the infinite coordinate set. -/
theorem pathLaw_map_permutePath (k : ℕ) (π : Equiv.Perm ℕ) :
    Measure.map (permutePath π) (pathLaw k) = pathLaw k := by
  have he : permutePath π =
      (MeasurableEquiv.piCongrLeft (fun _ : ℕ => ℕ) π.symm : Path → Path) := by
    ext x i
    have h := Equiv.piCongrLeft_apply_apply (fun _ : ℕ => ℕ) π.symm x (π i)
    simpa only [permutePath, MeasurableEquiv.coe_piCongrLeft,
      Equiv.symm_apply_apply] using h.symm
  rw [he]
  exact Measure.infinitePi_map_piCongrLeft (fun _ : ℕ => uniformLaw k) π.symm

def permuteRows (π : Equiv.Perm ℕ) (ω : Omega) : Omega := (ω.1, permutePath π ω.2)

theorem permuteRows_measurable (π : Equiv.Perm ℕ) : Measurable (permuteRows π) :=
  measurable_fst.prodMk ((permutePath_measurable π).comp measurable_snd)

@[simp] theorem endpoint_permuteRows (π : Equiv.Perm ℕ) (ω : Omega) :
    endpoint (permuteRows π ω) = endpoint ω := rfl

@[simp] theorem coordinate_permuteRows (π : Equiv.Perm ℕ) (i : ℕ) (ω : Omega) :
    coordinate i (permuteRows π ω) = coordinate (π i) ω := rfl

/-- Exchangeability as equality of the full measures, with the latent variable retained. -/
theorem probability_map_permuteRows (π : Equiv.Perm ℕ) :
    Measure.map (permuteRows π) probability = probability := by
  ext s hs
  rw [Measure.map_apply (permuteRows_measurable π) hs,
    probability, Measure.compProd_apply (hs.preimage (permuteRows_measurable π)),
    Measure.compProd_apply hs]
  apply lintegral_congr
  intro k
  change pathLaw k ((permutePath π) ⁻¹' (Prod.mk k ⁻¹' s)) =
    pathLaw k (Prod.mk k ⁻¹' s)
  have hm : Measurable (Prod.mk k : Path → Omega) := measurable_const.prodMk measurable_id
  have hsec : MeasurableSet (Prod.mk k ⁻¹' s) := hs.preimage hm
  calc
    _ = (Measure.map (permutePath π) (pathLaw k)) (Prod.mk k ⁻¹' s) :=
      (Measure.map_apply (permutePath_measurable π) hsec).symm
    _ = _ := congrArg (fun μ : Measure Path => μ (Prod.mk k ⁻¹' s))
      (pathLaw_map_permutePath k π)

theorem permuteRows_measurePreserving (π : Equiv.Perm ℕ) :
    MeasurePreserving (permuteRows π) probability probability :=
  ⟨permuteRows_measurable π, probability_map_permuteRows π⟩

end RiemannResearch.Probability.ConditionalIID
