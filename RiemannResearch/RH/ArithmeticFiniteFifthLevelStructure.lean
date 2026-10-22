import RiemannResearch.RH.ArithmeticFiniteCertificateInfrastructure
import RiemannResearch.RH.ArithmeticFiniteFifthLevelEnclosures

/-!
# Exact fifth-level grid and reflection structure

The width-1/256 sample matrix, native unnormalized Haar endpoint triples,
root-first reflection coordinates, and coefficient indexing are identified
without dependent-index expansion in the scalar interval checker.

Source: user-provided FifthLevel_Paper_Recon_v47.md and the RH continuation
program support the certificate architecture and candidate rational data.
All identities and inequalities below are formally proved. These fixed-level
results do not establish all-level positivity, completed-Weil positivity, or RH.
-/

open scoped BigOperators
namespace RiemannResearch.RH
open RiemannResearch.RH.PrimeGapCurvature
noncomputable section

def fifthLevelDistance (i j : Fin 33) : Fin 33 :=
  ⟨if i.val ≤ j.val then j.val-i.val else i.val-j.val,by split_ifs <;> omega⟩

def fifthLevelValueMatrix (p : Fin 33 → ℝ) : Matrix (Fin 33) (Fin 33) ℝ :=
  fun i j => p (fifthLevelDistance i j)

def fifthLevelValueHaar (p : Fin 33 → ℝ) :
    Matrix (FiniteDyadicHaarIndex 5) (FiniteDyadicHaarIndex 5) ℝ :=
  -((finiteDyadicHaarEndpointJumps 5).transpose * fifthLevelValueMatrix p *
      finiteDyadicHaarEndpointJumps 5)

def fifthLevelOddPick : Fin 16 → FiniteDyadicHaarIndex 5 :=
  ![⟨0,0⟩,⟨1,0⟩,⟨2,0⟩,⟨2,1⟩,⟨3,0⟩,⟨3,1⟩,⟨3,2⟩,⟨3,3⟩,
    ⟨4,0⟩,⟨4,1⟩,⟨4,2⟩,⟨4,3⟩,⟨4,4⟩,⟨4,5⟩,⟨4,6⟩,⟨4,7⟩]

def fifthLevelEvenPick (i : Fin 15) : FiniteDyadicHaarIndex 5 :=
  finiteDyadicHaarReflectionPick 4 (some (fourthLevelIndex i))

def fifthLevelOddWeight (i : Fin 16) : ℝ := if i = 0 then 1/2 else 1

def fifthLevelOddBlock (p : Fin 33 → ℝ) : Matrix (Fin 16) (Fin 16) ℝ :=
  involutionOddBlock (finiteDyadicHaarReflect 5) fifthLevelOddPick fifthLevelOddWeight
    (fifthLevelValueHaar p)

def fifthLevelEvenBlock (p : Fin 33 → ℝ) : Matrix (Fin 15) (Fin 15) ℝ :=
  involutionEvenBlock (finiteDyadicHaarReflect 5) fifthLevelEvenPick (fifthLevelValueHaar p)


/-- Root-first exact reindexing of the native reflection orbits. -/
def fifthLevelOddIndex : Fin 16 → Option (FiniteDyadicHaarIndex 4) :=
  Fin.cases none (fun j => some (fourthLevelIndex j))

theorem fifthLevelOddIndex_bijective : Function.Bijective fifthLevelOddIndex := by
  constructor
  · intro i
    refine Fin.cases ?_ (fun a => ?_) i <;> intro j <;>
      refine Fin.cases ?_ (fun b => ?_) j <;> intro h
    · rfl
    · change none = some (fourthLevelIndex b) at h
      contradiction
    · change some (fourthLevelIndex a) = none at h
      contradiction
    · change some (fourthLevelIndex a) = some (fourthLevelIndex b) at h
      exact congrArg Fin.succ (fourthLevelIndex_injective (Option.some.inj h))
  · intro j
    cases j with
    | none => exact ⟨0,rfl⟩
    | some j =>
      obtain ⟨i,rfl⟩ := fourthLevelIndex_surjective j
      exact ⟨i.succ,rfl⟩

def fifthLevelOddIndexEquiv : Fin 16 ≃ Option (FiniteDyadicHaarIndex 4) :=
  Equiv.ofBijective fifthLevelOddIndex fifthLevelOddIndex_bijective

theorem fifthLevelOddIndex_root (i : Fin 16) :
    fifthLevelOddIndex i = none ↔ i = 0 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [fifthLevelOddIndex]
  · simp [fifthLevelOddIndex]

theorem fifthLevelOddPick_eq (i : Fin 16) :
    fifthLevelOddPick i = finiteDyadicHaarReflectionPick 4 (fifthLevelOddIndex i) := by
  fin_cases i <;> rfl

theorem fifthLevelOddWeight_eq (i : Fin 16) :
    fifthLevelOddWeight i = reflectionOrbitWeight (fifthLevelOddIndex i) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp [fifthLevelOddWeight, fifthLevelOddIndex, reflectionOrbitWeight]

theorem fifthLevelDistance_symm (i j : Fin 33) :
    fifthLevelDistance i j = fifthLevelDistance j i := by
  apply Fin.ext
  dsimp only [fifthLevelDistance]
  split_ifs <;> omega

theorem fifthLevelDistance_reflect (i j : Fin 33) :
    fifthLevelDistance i.rev j.rev = fifthLevelDistance i j := by
  apply Fin.ext
  have hi := i.isLt
  have hj := j.isLt
  simp only [fifthLevelDistance, Fin.val_rev]
  split_ifs <;> omega

theorem fifthLevelDistance_grid (i j : Fin 33) :
    |finiteDyadicGridEndpoint (1/16) 5 i - finiteDyadicGridEndpoint (1/16) 5 j| =
      (fifthLevelDistance i j).val / (256:ℝ) := by
  change |(-(1/16:ℝ) + (2*(1/16)/(2^5))*i.val) -
      (-(1/16:ℝ) + (2*(1/16)/(2^5))*j.val)| = _
  dsimp only [fifthLevelDistance]
  split_ifs with h
  · rw [Nat.cast_sub h, abs_of_nonpos]
    · ring
    · norm_num
      exact h
  · have h' : j.val ≤ i.val := by omega
    rw [Nat.cast_sub h', abs_of_nonneg]
    · ring
    · norm_num
      exact h'

theorem fifthLevelValueMatrix_eq_primitive :
    fifthLevelValueMatrix fifthLevelSamples =
      endpointPrimitiveMatrix (fun t => fourthLevelPrimitive (5373/2000) |t|)
        (finiteDyadicGridEndpoint (1/16) 5) := by
  ext i j
  simp only [fifthLevelValueMatrix, fifthLevelSamples,
    endpointPrimitiveMatrix, fifthLevelDistance_grid]

theorem fifthLevelValueHaar_eq_arithmetic :
    fifthLevelValueHaar fifthLevelSamples =
      arithmeticFiniteHaarModel (5373/2000) (1/16) 5 2 5 := by
  rw [arithmeticFiniteHaarModel_fiveModes_jumps]
  exact congrArg (fun F => -((finiteDyadicHaarEndpointJumps 5).transpose * F *
    finiteDyadicHaarEndpointJumps 5)) fifthLevelValueMatrix_eq_primitive

theorem fifthLevelOddBlock_eq_arithmetic (i j : Fin 16) :
    fifthLevelOddBlock fifthLevelSamples i j =
      arithmeticFiniteOddBlock (5373/2000) (1/16) 4
        (fifthLevelOddIndexEquiv i) (fifthLevelOddIndexEquiv j) := by
  simp only [fifthLevelOddBlock, arithmeticFiniteOddBlock, involutionOddBlock,
    fifthLevelValueHaar_eq_arithmetic, fifthLevelOddPick_eq, fifthLevelOddWeight_eq]
  rfl

theorem fifthLevelEvenBlock_eq_arithmetic (i j : Fin 15) :
    fifthLevelEvenBlock fifthLevelSamples i j =
      arithmeticFiniteEvenBlock (5373/2000) (1/16) 4
        (fourthLevelIndexEquiv i) (fourthLevelIndexEquiv j) := by
  simp only [fifthLevelEvenBlock, arithmeticFiniteEvenBlock, involutionEvenBlock,
    fifthLevelValueHaar_eq_arithmetic, fifthLevelEvenPick]
  rfl

def fifthLevelOddLeft : Fin 16 → Fin 33 :=
  ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩,⟨8,by decide⟩,⟨0,by decide⟩,⟨4,by decide⟩,⟨8,by decide⟩,⟨12,by decide⟩,⟨0,by decide⟩,⟨2,by decide⟩,⟨4,by decide⟩,⟨6,by decide⟩,⟨8,by decide⟩,⟨10,by decide⟩,⟨12,by decide⟩,⟨14,by decide⟩]

theorem fifthLevelOddPick_left (i : Fin 16) :
    finiteDyadicHaarLeftEndpoint 5 (fifthLevelOddPick i) = fifthLevelOddLeft i := by
  fin_cases i <;> rfl

def fifthLevelOddMid : Fin 16 → Fin 33 :=
  ![⟨16,by decide⟩,⟨8,by decide⟩,⟨4,by decide⟩,⟨12,by decide⟩,⟨2,by decide⟩,⟨6,by decide⟩,⟨10,by decide⟩,⟨14,by decide⟩,⟨1,by decide⟩,⟨3,by decide⟩,⟨5,by decide⟩,⟨7,by decide⟩,⟨9,by decide⟩,⟨11,by decide⟩,⟨13,by decide⟩,⟨15,by decide⟩]

theorem fifthLevelOddPick_mid (i : Fin 16) :
    finiteDyadicHaarMidEndpoint 5 (fifthLevelOddPick i) = fifthLevelOddMid i := by
  fin_cases i <;> rfl

def fifthLevelOddRight : Fin 16 → Fin 33 :=
  ![⟨32,by decide⟩,⟨16,by decide⟩,⟨8,by decide⟩,⟨16,by decide⟩,⟨4,by decide⟩,⟨8,by decide⟩,⟨12,by decide⟩,⟨16,by decide⟩,⟨2,by decide⟩,⟨4,by decide⟩,⟨6,by decide⟩,⟨8,by decide⟩,⟨10,by decide⟩,⟨12,by decide⟩,⟨14,by decide⟩,⟨16,by decide⟩]

theorem fifthLevelOddPick_right (i : Fin 16) :
    finiteDyadicHaarRightEndpoint 5 (fifthLevelOddPick i) = fifthLevelOddRight i := by
  fin_cases i <;> rfl

theorem fifthLevelEvenPick_eq (i : Fin 15) :
    fifthLevelEvenPick i = fifthLevelOddPick i.succ := by
  fin_cases i <;> rfl

/-- Nine-term evaluation after the native endpoint indices have been normalized. -/
def fifthLevelJumpEntry (p : Fin 33 → ℝ) (a b d e f g : Fin 33) : ℝ :=
  -(p (fifthLevelDistance a e)-2*p (fifthLevelDistance a f)+p (fifthLevelDistance a g) -
    2*p (fifthLevelDistance b e)+4*p (fifthLevelDistance b f)-2*p (fifthLevelDistance b g) +
    p (fifthLevelDistance d e)-2*p (fifthLevelDistance d f)+p (fifthLevelDistance d g))

theorem fifthLevelValueHaar_entry (p : Fin 33 → ℝ) (i j : FiniteDyadicHaarIndex 5) :
    fifthLevelValueHaar p i j =
      fifthLevelJumpEntry p
        (finiteDyadicHaarLeftEndpoint 5 i) (finiteDyadicHaarMidEndpoint 5 i)
        (finiteDyadicHaarRightEndpoint 5 i) (finiteDyadicHaarLeftEndpoint 5 j)
        (finiteDyadicHaarMidEndpoint 5 j) (finiteDyadicHaarRightEndpoint 5 j) := by
  simp only [fifthLevelValueHaar, Matrix.neg_apply, finiteDyadicHaarEndpointJumps,
    threePointJumps_congruence, fifthLevelValueMatrix, fifthLevelJumpEntry]

theorem fifthLevelOddBlock_entry (p : Fin 33 → ℝ) (i j : Fin 16) :
    fifthLevelOddBlock p i j =
      2*fifthLevelOddWeight i*fifthLevelOddWeight j *
        (fifthLevelJumpEntry p (fifthLevelOddLeft i) (fifthLevelOddMid i)
          (fifthLevelOddRight i) (fifthLevelOddLeft j) (fifthLevelOddMid j) (fifthLevelOddRight j) +
         fifthLevelJumpEntry p (fifthLevelOddLeft i) (fifthLevelOddMid i)
          (fifthLevelOddRight i) (fifthLevelOddRight j).rev (fifthLevelOddMid j).rev
          (fifthLevelOddLeft j).rev) := by
  simp only [fifthLevelOddBlock, involutionOddBlock, fifthLevelValueHaar_entry,
    finiteDyadicHaarReflect_left, finiteDyadicHaarReflect_mid, finiteDyadicHaarReflect_right,
    fifthLevelOddPick_left, fifthLevelOddPick_mid, fifthLevelOddPick_right]

theorem fifthLevelEvenBlock_entry (p : Fin 33 → ℝ) (i j : Fin 15) :
    fifthLevelEvenBlock p i j =
      2 * (fifthLevelJumpEntry p (fifthLevelOddLeft i.succ) (fifthLevelOddMid i.succ)
          (fifthLevelOddRight i.succ) (fifthLevelOddLeft j.succ) (fifthLevelOddMid j.succ)
          (fifthLevelOddRight j.succ) -
         fifthLevelJumpEntry p (fifthLevelOddLeft i.succ) (fifthLevelOddMid i.succ)
          (fifthLevelOddRight i.succ) (fifthLevelOddRight j.succ).rev (fifthLevelOddMid j.succ).rev
          (fifthLevelOddLeft j.succ).rev) := by
  simp only [fifthLevelEvenBlock, involutionEvenBlock, fifthLevelEvenPick_eq,
    fifthLevelValueHaar_entry,
    finiteDyadicHaarReflect_left, finiteDyadicHaarReflect_mid, finiteDyadicHaarReflect_right,
    fifthLevelOddPick_left, fifthLevelOddPick_mid, fifthLevelOddPick_right]

theorem fifthLevelValueHaar_reflect (p : Fin 33 → ℝ) (i j : FiniteDyadicHaarIndex 5) :
    fifthLevelValueHaar p (finiteDyadicHaarReflect 5 i) (finiteDyadicHaarReflect 5 j) =
      fifthLevelValueHaar p i j := by
  simp only [fifthLevelValueHaar, Matrix.neg_apply]
  congr 1
  apply finiteDyadicHaarEndpointJumps_congruence_reflect
  intro r s
  simp only [fifthLevelValueMatrix, fifthLevelDistance_reflect]

theorem fifthLevelValueHaar_symm (p : Fin 33 → ℝ) (i j : FiniteDyadicHaarIndex 5) :
    fifthLevelValueHaar p i j = fifthLevelValueHaar p j i := by
  simp only [fifthLevelValueHaar_entry, fifthLevelJumpEntry]
  simp only [fifthLevelDistance_symm]
  ring

theorem fifthLevelValueHaar_cross (p : Fin 33 → ℝ) (i j : FiniteDyadicHaarIndex 5) :
    fifthLevelValueHaar p i (finiteDyadicHaarReflect 5 j) =
      fifthLevelValueHaar p j (finiteDyadicHaarReflect 5 i) := by
  rw [fifthLevelValueHaar_symm]
  simpa only [finiteDyadicHaarReflect_involutive 5 i] using
    fifthLevelValueHaar_reflect p j (finiteDyadicHaarReflect 5 i)

theorem fifthLevelOddBlock_symm (p : Fin 33 → ℝ) (i j : Fin 16) :
    fifthLevelOddBlock p i j = fifthLevelOddBlock p j i := by
  simp only [fifthLevelOddBlock, involutionOddBlock]
  rw [fifthLevelValueHaar_symm p (fifthLevelOddPick i) (fifthLevelOddPick j),
    fifthLevelValueHaar_cross]
  ring

theorem fifthLevelEvenBlock_symm (p : Fin 33 → ℝ) (i j : Fin 15) :
    fifthLevelEvenBlock p i j = fifthLevelEvenBlock p j i := by
  simp only [fifthLevelEvenBlock, involutionEvenBlock]
  rw [fifthLevelValueHaar_symm p (fifthLevelEvenPick i) (fifthLevelEvenPick j),
    fifthLevelValueHaar_cross]

theorem fifthLevelOddBlock_isHermitian (p : Fin 33 → ℝ) :
    (fifthLevelOddBlock p).IsHermitian := by
  apply Matrix.isHermitian_iff_isSymm.mpr
  ext i j
  exact fifthLevelOddBlock_symm p j i

theorem fifthLevelEvenBlock_isHermitian (p : Fin 33 → ℝ) :
    (fifthLevelEvenBlock p).IsHermitian := by
  apply Matrix.isHermitian_iff_isSymm.mpr
  ext i j
  exact fifthLevelEvenBlock_symm p j i

end
end RiemannResearch.RH
