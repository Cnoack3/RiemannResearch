/-
Copyright (c) 2026 RiemannResearch contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.LamzouriGap285DataCache
import RiemannResearch.Analysis.GapKernelStreamingFourier

/-! Shared checkpoints for eight independent blocks of the Fourier recurrence. -/
namespace RiemannResearch.Analysis.LamzouriGapKernel285.FourierBlocks
open GapKernelFourierRecurrence GapKernelPolynomial

set_option maxRecDepth 120000
set_option maxHeartbeats 0

def cut (i : ℕ) : ℕ := min (36*i) 286
def entryAt (n : ℕ) : ℤ := physicalData.reverse.getD n 0

def inputAt : ℕ → List ℤ
  | 0 => []
  | n+1 => entryAt n :: inputAt n

private theorem inputAt_length (n : ℕ) : (inputAt n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [inputAt, ih]

private def checkpoints : List (List ℤ) := eval% (List.range 9).map fun i =>
  advanceTrace 0 [] (physicalData.reverse.take (cut i))
def checkpoint (i : ℕ) : List ℤ := checkpoints.getD i []

def scalarAt (n : ℕ) : ℤ := (2 : ℤ)^(n+1)*entryAt n

def propose (n : ℕ) (p : List ℤ) := proposeRow (scalarAt n) p

def Step (i : ℕ) : Prop :=
  transport (inputAt (cut i)) = checkpoint i → transport (inputAt (cut (i+1))) = checkpoint (i+1)

theorem oneStep (n : ℕ) (p q : List ℤ) (hc : checkNewRow (scalarAt n) p q = true)
    (h : transport (inputAt n) = p) : transport (inputAt (n+1)) = q := by
  rw [inputAt, transport, inputAt_length, h]
  exact checked_doubleStep hc

end RiemannResearch.Analysis.LamzouriGapKernel285.FourierBlocks
