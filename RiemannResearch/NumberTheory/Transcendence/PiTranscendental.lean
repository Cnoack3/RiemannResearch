/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import RiemannResearch.NumberTheory.Transcendence.MonicRootSums
import RiemannResearch.NumberTheory.Transcendence.SubsetSumEsymm


/-!
# Transcendence of the physical constant π

Source: Trevor Morris, `gotrevor/lean-formalizations`,
https://github.com/gotrevor/lean-formalizations/blob/bad0e21a37874f09f45072dad6225de55742e6c5/src/LeanFormalizations/NumberTheory/Transcendence/PiTranscendental.lean.
The cited source supplies both statements and proof bodies. This adaptation
uses the RiemannResearch namespace and focused imports. Its concrete RH
consumer is the exact physical minimum in `ArithmeticMinimumTranscendence`.
-/

namespace RiemannResearch.NumberTheory.Transcendence

/-- Lindemann's transcendence theorem for the actual real constant π. -/
theorem transcendental_pi : Transcendental ℚ Real.pi :=
  transcendental_pi_of_subsetSumEsymm
    (fun n θ G hG hr j => subsetSum_esymm_rational n θ G hG hr j)

end RiemannResearch.NumberTheory.Transcendence
