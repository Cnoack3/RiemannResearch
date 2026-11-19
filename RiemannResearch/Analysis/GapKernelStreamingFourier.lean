/-
Copyright (c) 2026 RiemannResearch contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.GapKernelFourierRecurrence

/-! # A single-pass integer trace for the Fourier coefficient recurrence -/

namespace RiemannResearch.Analysis.GapKernelFourierRecurrence
open GapKernelPolynomial GapKernelObjective

private def driftRow (k : ℕ) : List ℤ → List ℤ
  | [] => []
  | a :: p => ((k+1 : ℕ) * p.headD 0 - a : ℤ) :: driftRow (k+1) p

private theorem driftRow_eq (k : ℕ) (p : List ℤ) :
    add (indexed (k+1) p.tail) (scale (-1) p) = driftRow k p := by
  induction p generalizing k with
  | nil => rfl
  | cons a p ih =>
    cases p with
    | nil => simp [List.tail, indexed, scale, add, driftRow]
    | cons b p =>
      change ((k+1 : ℕ) * b + (-1)*a : ℤ) ::
          add (indexed (k+1+1) p) (scale (-1) (b :: p)) =
        ((k+1 : ℕ) * b-a : ℤ) :: driftRow (k+1) (b :: p)
      rw [show add (indexed (k+1+1) p) (scale (-1) (b :: p)) = _ from ih (k+1)]
      congr 1
      ring

private theorem drift_eq_row (p : List ℤ) : drift p = driftRow 0 p := driftRow_eq 0 p

private def combineRow (k : ℕ) (prev : ℤ) : List ℤ → List ℤ
  | [] => [2*prev]
  | a :: p => (2*prev-(2*(k : ℤ)+1)*a) :: combineRow (k+1) a p

private theorem combineRow_eq (k : ℕ) (prev : ℤ) (p : List ℤ) :
    add (scale (-1) p) ((-2*((k : ℤ)*p.headD 0-prev)) :: scale (-2) (driftRow k p)) =
      combineRow k prev p := by
  induction p generalizing k prev with
  | nil => simp [scale, add, driftRow, combineRow]
  | cons a p ih =>
    change ((-1)*a + (-2)*((k : ℤ)*a-prev)) ::
        add (scale (-1) p) ((-2)*(((k+1 : ℕ) : ℤ)*p.headD 0-a) ::
          scale (-2) (driftRow (k+1) p)) =
      (2*prev-(2*(k : ℤ)+1)*a) :: combineRow (k+1) a p
    rw [ih]
    congr 1
    ring

private def rowStep (p : List ℤ) := combineRow 0 0 (driftRow 0 p)

private theorem doubleStep_eq_rowStep (p : List ℤ) : doubleStep p = rowStep p := by
  unfold doubleStep rowStep
  rw [drift_eq_row p, drift_eq_row]
  simpa using combineRow_eq 0 0 (driftRow 0 p)

private def localStep (k : ℕ) (prev : ℤ) : List ℤ → List ℤ
  | [] => [-2*prev]
  | a :: p => ((4*(k : ℤ)+1)*a-((k : ℤ)+1)*(2*(k : ℤ)+1)*p.headD 0-2*prev) ::
      localStep (k+1) a p

private theorem localStep_eq (k : ℕ) (prev : ℤ) (p : List ℤ) :
    combineRow k ((k : ℤ)*p.headD 0-prev) (driftRow k p) = localStep k prev p := by
  induction p generalizing k prev with
  | nil => simp [combineRow, driftRow, localStep]
  | cons a p ih =>
    change (2*((k : ℤ)*a-prev)-(2*(k : ℤ)+1)*(((k+1 : ℕ) : ℤ)*p.headD 0-a)) ::
        combineRow (k+1) (((k+1 : ℕ) : ℤ)*p.headD 0-a) (driftRow (k+1) p) =
      ((4*(k : ℤ)+1)*a-((k : ℤ)+1)*(2*(k : ℤ)+1)*p.headD 0-2*prev) ::
        localStep (k+1) a p
    rw [ih]
    congr 1
    push_cast
    ring


private def checkCoefficients (k : ℕ) (prev initial : ℤ) : List ℤ → List ℤ → Bool
  | [], [z] => decide (initial-2*prev = z)
  | a :: p, z :: q =>
    decide (initial + ((4*(k : ℤ)+1)*a-((k : ℤ)+1)*(2*(k : ℤ)+1)*p.headD 0-2*prev) = z) &&
      checkCoefficients (k+1) a 0 p q
  | _, _ => false

private theorem add_zero_localStep (k : ℕ) (prev : ℤ) (p : List ℤ) :
    add [0] (localStep k prev p) = localStep k prev p := by
  cases p <;> simp [localStep, add]

private theorem checkCoefficients_sound (k : ℕ) (prev initial : ℤ) (p q : List ℤ)
    (h : checkCoefficients k prev initial p q = true) :
    add [initial] (localStep k prev p) = q := by
  induction p generalizing k prev initial q with
  | nil =>
    cases q with
    | nil => simp [checkCoefficients] at h
    | cons z q =>
      cases q with
      | nil =>
        simp only [checkCoefficients, decide_eq_true_eq] at h
        simp [localStep, add, ← h, sub_eq_add_neg]
      | cons => simp [checkCoefficients] at h
  | cons a p ih =>
    cases q with
    | nil => simp [checkCoefficients] at h
    | cons z q =>
      simp only [checkCoefficients, Bool.and_eq_true, decide_eq_true_eq] at h
      have tail := ih (k+1) a 0 q h.2
      rw [add_zero_localStep] at tail
      simp only [localStep, add, h.1, tail]


def proposeRow (z : ℤ) (p : List ℤ) : List ℤ := add [z] (rowStep p)

def checkNewRow (z : ℤ) (p q : List ℤ) : Bool := checkCoefficients 0 0 z p q

theorem checked_doubleStep {z : ℤ} {p q : List ℤ} (h : checkNewRow z p q = true) :
    add [z] (doubleStep p) = q := by
  rw [doubleStep_eq_rowStep]
  have he : rowStep p = localStep 0 0 p := by simpa [rowStep] using localStep_eq 0 0 p
  rw [he]
  exact checkCoefficients_sound 0 0 z p q h

/-- The last proposed row after inserting descending physical coefficients. -/
def advanceTrace (len : ℕ) (base : List ℤ) : List ℤ → List ℤ
  | [] => base
  | a :: p => advanceTrace (len+1) (proposeRow ((2 : ℤ)^(len+1)*a) base) p

end RiemannResearch.Analysis.GapKernelFourierRecurrence
