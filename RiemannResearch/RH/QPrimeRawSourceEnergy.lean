/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QPrimeJumpEnergyIdentity
import RiemannResearch.RH.QCountableJumpEnergy

/-!
# Unconditional complete raw-source prime-resampling energy

Source: the user's prime-resampling agenda. The generic countable symmetric
flow estimate is instantiated with the actual arithmetic prime kernel and
its proved full exit-rate envelope. No kernel or rate hypothesis remains.
-/

noncomputable section
open scoped ENNReal
namespace RiemannResearch.RH.QCountableJumpEnergy
open ZetaTwoHilbert QShiftedReciprocal PrimeResampling

/-- The actual full prime-resampling raw-source energy costs at most 1/32
of its input Q energy. In particular, the infinite form is finite. -/
theorem rawSourceDirichletEnergy_le (f : QHilbert) :
    dirichletEnergy (qWeightedSequence (B f)) ≤ ENNReal.ofReal (‖f‖ ^ 2 / 32) :=
  countableRawSourceJumpEnergy_le primeFlow f primeFlow_symm primeFlow_row_bound

theorem rawSourceDirichletEnergy_ne_top (f : QHilbert) :
    dirichletEnergy (qWeightedSequence (B f)) ≠ ⊤ :=
  countableRawSourceJumpEnergy_ne_top primeFlow f primeFlow_symm primeFlow_row_bound

end RiemannResearch.RH.QCountableJumpEnergy
