import RiemannResearch.Analysis.NestedOrthogonalDecomposition
import RiemannResearch.RH.FiniteAtomCarryCRT
import RiemannResearch.RH.UniversalAtomCarryPresentation
import RiemannResearch.RH.ParetoNormalizedResidueHilbert
import RiemannResearch.RH.MobiusCoefficientStabilization
import RiemannResearch.RH.QFullResidueProjection
import RiemannResearch.RH.ZetaTwoHilbertSpace

/-!
# Physical prime-power and projected mixed-carry spaces

Source: the user-provided atom/carry CRT argument, §§14.5–14.6.
Evaluate signed carry expressions using the actual Pareto and Q sequence maps.
The orthogonal splitting uses every positive prime-power depth.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.PhysicalPrimePowerCarryProjection

open RiemannResearch.NumberTheory.PrimePowerCRT
open RiemannResearch.Analysis.NestedOrthogonalDecomposition
open UniversalAtomCarry (Atom Certificate)
open ArithmeticCumulative (residueFraction)

abbrev PrimePowerConductor := {d : ℕ // 1 < d ∧ d.primeFactors.card = 1}
abbrev MixedConductor := {d : ℕ // 1 < d ∧ d.primeFactors.card ≠ 1}

theorem primePowerConductor_iff (d : ℕ) :
    (1 < d ∧ d.primeFactors.card = 1) ↔ ∃ p k : ℕ, p.Prime ∧ 0 < k ∧ d = p ^ k := by
  by_cases hd : d = 0
  · subst d
    constructor
    · rintro ⟨h, _⟩
      omega
    · rintro ⟨p, k, hp, _, heq⟩
      exact False.elim ((ne_of_gt (pow_pos hp.pos k)) heq.symm)
  · have hself : d ∈ d.divisors := Nat.mem_divisors.mpr ⟨dvd_refl _, hd⟩
    simpa only [FiniteAtomCarryCRT.primeConductors, Finset.mem_filter, hself, true_and]
      using FiniteAtomCarryCRT.mem_primeConductors_iff d d

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (g : ℕ → H)

/-- A signed certificate realized by its finite Hilbert expression. -/
def certifiedVector (c : Certificate) : H :=
  (∑ i, (c.coeff i : ℝ) • g (c.input i)) - g c.output

/-- The canonical prime-power expression with the output atom subtracted. -/
def canonicalVector (d : ℕ) : H :=
  (∑ p ∈ d.primeFactors, (coefficient d p : ℝ) • g (modulus d p)) - g d

theorem evaluate_certified (ev : H →ₗ[ℝ] (ℕ → ℝ))
    (hg : ∀ d, 0 < d → ev (g d) = residueFraction d) (c : Certificate) :
    ev (certifiedVector g c) = c.carry := by
  funext n
  rw [certifiedVector, map_sub, map_sum, Pi.sub_apply, Finset.sum_apply, c.carry_eq]
  simp only [map_smul, Pi.smul_apply, smul_eq_mul,
    hg c.output (Nat.zero_lt_of_lt c.output_gt_one)]
  apply congrArg (· - residueFraction c.output n)
  apply Finset.sum_congr rfl
  intro i _
  rw [hg (c.input i) (Nat.zero_lt_of_lt (c.input_gt_one i))]

theorem evaluate_canonical (ev : H →ₗ[ℝ] (ℕ → ℝ))
    (hg : ∀ d, 0 < d → ev (g d) = residueFraction d) (d : ℕ) (hd : 0 < d) :
    ev (canonicalVector g d) = fun n => (canonicalCarry d n : ℝ) := by
  funext n
  rw [canonicalVector, map_sub, map_sum, Pi.sub_apply, Finset.sum_apply, hg d hd]
  simp only [map_smul, Pi.smul_apply, smul_eq_mul, hg _ (modulus_pos d _)]
  linarith [atom_reconstruction d hd n]

abbrev fullClosure : Submodule ℝ H :=
  (Submodule.span ℝ (Set.range (fun d : Atom => g d.val))).topologicalClosure

abbrev powerClosure : Submodule ℝ H :=
  (Submodule.span ℝ (Set.range (fun d : PrimePowerConductor => g d.val))).topologicalClosure

theorem powerClosure_le_full : powerClosure g ≤ fullClosure g := by
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_le.mpr
  rintro _ ⟨d, rfl⟩
  exact Submodule.subset_span ⟨⟨d.val, d.property.1⟩, rfl⟩

variable [CompleteSpace H]

theorem projected_power (d : PrimePowerConductor) :
    (powerClosure g)ᗮ.starProjection (g d.val) = 0 :=
  Submodule.starProjection_orthogonal_apply_eq_zero
    ((Submodule.span ℝ _).le_topologicalClosure (Submodule.subset_span ⟨d, rfl⟩))

theorem projected_canonical (d : ℕ) :
    (powerClosure g)ᗮ.starProjection (canonicalVector g d) =
      -((powerClosure g)ᗮ.starProjection (g d)) := by
  have hsum : (∑ p ∈ d.primeFactors, (coefficient d p : ℝ) • g (modulus d p)) ∈
      powerClosure g := by
    apply (powerClosure g).sum_mem
    intro p hp
    apply (powerClosure g).smul_mem
    have hprime := (Nat.mem_primeFactors.mp hp).1
    have he : 0 < d.factorization p :=
      hprime.factorization_pos_of_dvd (Nat.mem_primeFactors.mp hp).2.2
        (Nat.mem_primeFactors.mp hp).2.1
    have hlabel := (primePowerConductor_iff (modulus d p)).2 ⟨p, _, hprime, he, rfl⟩
    exact (Submodule.span ℝ _).le_topologicalClosure
      (Submodule.subset_span ⟨⟨modulus d p, hlabel⟩, rfl⟩)
  rw [canonicalVector, map_sub, Submodule.starProjection_orthogonal_apply_eq_zero hsum, zero_sub]

/-- Only canonical mixed conductors index this projected span. -/
abbrev projectedMixedSpan : Submodule ℝ H :=
  Submodule.span ℝ (Set.range (fun d : MixedConductor =>
    (powerClosure g)ᗮ.starProjection (canonicalVector g d.val)))

theorem complement_eq_closed_mixed :
    fullClosure g ⊓ (powerClosure g)ᗮ = (projectedMixedSpan g).topologicalClosure := by
  let : (fullClosure g ⊓ (powerClosure g)ᗮ).HasOrthogonalProjection :=
    carry_hasOrthogonalProjection (powerClosure_le_full g)
  rw [carry_eq_closure_projected_generators (powerClosure_le_full g)
    (Set.range (fun d : Atom => g d.val)) rfl]
  congr 1
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨d, rfl⟩, rfl⟩
    change (powerClosure g)ᗮ.starProjection (g d.val) ∈ projectedMixedSpan g
    by_cases hp : d.val.primeFactors.card = 1
    · rw [projected_power g (⟨d.val, d.property, hp⟩ : PrimePowerConductor)]
      exact (projectedMixedSpan g).zero_mem
    · have hc : (powerClosure g)ᗮ.starProjection (canonicalVector g d.val) ∈
          projectedMixedSpan g :=
        Submodule.subset_span ⟨⟨d.val, d.property, hp⟩, rfl⟩
      simpa only [projected_canonical, neg_neg] using (projectedMixedSpan g).neg_mem hc
  · apply Submodule.span_le.mpr
    rintro _ ⟨d, rfl⟩
    change (powerClosure g)ᗮ.starProjection (canonicalVector g d.val) ∈
      Submodule.span ℝ ((powerClosure g)ᗮ.starProjection '' Set.range (fun a : Atom => g a.val))
    rw [projected_canonical]
    apply (Submodule.span ℝ _).neg_mem
    exact Submodule.subset_span ⟨g d.val, ⟨⟨d.val, d.property.1⟩, rfl⟩, rfl⟩

theorem orthogonal_decomposition :
    fullClosure g = powerClosure g ⊔ (projectedMixedSpan g).topologicalClosure ∧
    ∀ w ∈ powerClosure g, ∀ z ∈ (projectedMixedSpan g).topologicalClosure,
      inner ℝ w z = 0 := by
  rw [← complement_eq_closed_mixed]
  exact ⟨(prime_sup_carry (powerClosure_le_full g)).symm,
    fun _ hw _ hz => prime_carry_inner_eq_zero hw hz⟩

/-- The Pareto normalized residue, extended at the unused conductor zero. -/
def pAtom (d : ℕ) : Pareto.ThresholdHilbert :=
  if hd : 0 < d then Pareto.normalizedResidueHilbert d hd else 0

theorem pAtom_sequence (d : ℕ) (hd : 0 < d) :
    Pareto.hilbertSequenceLinear (pAtom d) = residueFraction d := by
  change Pareto.hilbertSequence (pAtom d) = _
  rw [pAtom, dif_pos hd, Pareto.normalizedResidueHilbert_sequence]

/-- Both physical decodings agree with the same literal signed floor. -/
theorem physical_certified_floors (c : Certificate) :
    Pareto.hilbertSequence (certifiedVector pAtom c) = c.carry ∧
    ZetaTwoHilbert.qSequence (certifiedVector ZetaTwoHilbert.qResidue c) = c.carry :=
  ⟨evaluate_certified pAtom _ pAtom_sequence c,
    evaluate_certified ZetaTwoHilbert.qResidue ZetaTwoHilbert.qSequenceLinear
      (fun d _ => ZetaTwoHilbert.qSequence_qResidue d) c⟩

theorem physical_canonical_floors (d : ℕ) (hd : 0 < d) :
    Pareto.hilbertSequence (canonicalVector pAtom d) = (fun n => (canonicalCarry d n : ℝ)) ∧
    ZetaTwoHilbert.qSequence (canonicalVector ZetaTwoHilbert.qResidue d) =
      (fun n => (canonicalCarry d n : ℝ)) :=
  ⟨evaluate_canonical pAtom _ pAtom_sequence d hd,
    evaluate_canonical ZetaTwoHilbert.qResidue ZetaTwoHilbert.qSequenceLinear
      (fun m _ => ZetaTwoHilbert.qSequence_qResidue m) d hd⟩

/-- In either physical norm, removing the prime-power projection of a canonical
carry gives the negative of the mixed atom with its prime-power projection removed. -/
theorem physical_projected_canonical (d : MixedConductor) :
    (canonicalVector pAtom d.val -
      (powerClosure pAtom).starProjection (canonicalVector pAtom d.val) =
      -(pAtom d.val - (powerClosure pAtom).starProjection (pAtom d.val))) ∧
    (canonicalVector ZetaTwoHilbert.qResidue d.val -
      (powerClosure ZetaTwoHilbert.qResidue).starProjection
        (canonicalVector ZetaTwoHilbert.qResidue d.val) =
      -(ZetaTwoHilbert.qResidue d.val -
        (powerClosure ZetaTwoHilbert.qResidue).starProjection
          (ZetaTwoHilbert.qResidue d.val))) := by
  simpa only [Submodule.starProjection_orthogonal_val] using
    And.intro (projected_canonical pAtom d.val) (projected_canonical ZetaTwoHilbert.qResidue d.val)

omit [CompleteSpace H] in
private theorem fullClosure_eq_shift :
    fullClosure g = (Submodule.span ℝ (Set.range (fun i : ℕ => g (i + 2)))).topologicalClosure := by
  have he : Set.range (fun d : Atom => g d.val) = Set.range (fun i : ℕ => g (i + 2)) := by
    ext x
    constructor
    · rintro ⟨d, rfl⟩
      refine ⟨d.val - 2, ?_⟩
      change g (d.val - 2 + 2) = g d.val
      rw [Nat.sub_add_cancel d.property]
    · rintro ⟨i, rfl⟩
      exact ⟨⟨i + 2, by omega⟩, rfl⟩
  unfold fullClosure
  rw [he]

/-- The two full spans are the existing physical legal spaces. -/
theorem physical_full_closures :
    fullClosure pAtom = Pareto.CoefficientStabilization.closedSpace ∧
    fullClosure ZetaTwoHilbert.qResidue = QFullResidueProjection.closure := by
  constructor
  · rw [fullClosure_eq_shift]
    have he : (fun i : ℕ => pAtom (i + 2)) = Pareto.CoefficientStabilization.residueAtom := by
      funext i
      simp only [pAtom, dif_pos (show 0 < i + 2 by omega),
        Pareto.CoefficientStabilization.residueAtom]
    rw [he]
    rfl
  · exact fullClosure_eq_shift ZetaTwoHilbert.qResidue

/-- Full prime-power Pareto and Q orthogonal decompositions, with their own projections. -/
theorem physical_decompositions :
    (Pareto.CoefficientStabilization.closedSpace =
      powerClosure pAtom ⊔ (projectedMixedSpan pAtom).topologicalClosure) ∧
    (QFullResidueProjection.closure = powerClosure ZetaTwoHilbert.qResidue ⊔
      (projectedMixedSpan ZetaTwoHilbert.qResidue).topologicalClosure) :=
  ⟨physical_full_closures.1.symm.trans (orthogonal_decomposition pAtom).1,
    physical_full_closures.2.symm.trans (orthogonal_decomposition ZetaTwoHilbert.qResidue).1⟩

end RiemannResearch.RH.PhysicalPrimePowerCarryProjection
