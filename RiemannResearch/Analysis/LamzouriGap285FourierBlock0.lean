/-
Copyright (c) 2026 RiemannResearch contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.LamzouriGap285FourierStages

namespace RiemannResearch.Analysis.LamzouriGapKernel285.FourierBlocks
open GapKernelFourierRecurrence

set_option maxRecDepth 120000
set_option maxHeartbeats 0
private def r1 : List ℤ := eval% propose 0 (checkpoint 0)
private def r2 : List ℤ := eval% propose 1 r1
private def r3 : List ℤ := eval% propose 2 r2
private def r4 : List ℤ := eval% propose 3 r3
private def r5 : List ℤ := eval% propose 4 r4
private def r6 : List ℤ := eval% propose 5 r5
private def r7 : List ℤ := eval% propose 6 r6
private def r8 : List ℤ := eval% propose 7 r7
private def r9 : List ℤ := eval% propose 8 r8
private def r10 : List ℤ := eval% propose 9 r9
private def r11 : List ℤ := eval% propose 10 r10
private def r12 : List ℤ := eval% propose 11 r11
private def r13 : List ℤ := eval% propose 12 r12
private def r14 : List ℤ := eval% propose 13 r13
private def r15 : List ℤ := eval% propose 14 r14
private def r16 : List ℤ := eval% propose 15 r15
private def r17 : List ℤ := eval% propose 16 r16
private def r18 : List ℤ := eval% propose 17 r17
private def r19 : List ℤ := eval% propose 18 r18
private def r20 : List ℤ := eval% propose 19 r19
private def r21 : List ℤ := eval% propose 20 r20
private def r22 : List ℤ := eval% propose 21 r21
private def r23 : List ℤ := eval% propose 22 r22
private def r24 : List ℤ := eval% propose 23 r23
private def r25 : List ℤ := eval% propose 24 r24
private def r26 : List ℤ := eval% propose 25 r25
private def r27 : List ℤ := eval% propose 26 r26
private def r28 : List ℤ := eval% propose 27 r27
private def r29 : List ℤ := eval% propose 28 r28
private def r30 : List ℤ := eval% propose 29 r29
private def r31 : List ℤ := eval% propose 30 r30
private def r32 : List ℤ := eval% propose 31 r31
private def r33 : List ℤ := eval% propose 32 r32
private def r34 : List ℤ := eval% propose 33 r33
private def r35 : List ℤ := eval% propose 34 r34

private def next0 := oneStep 0 (checkpoint 0) r1 (by decide +kernel)
private def next1 := oneStep 1 r1 r2 (by decide +kernel)
private def next2 := oneStep 2 r2 r3 (by decide +kernel)
private def next3 := oneStep 3 r3 r4 (by decide +kernel)
private def next4 := oneStep 4 r4 r5 (by decide +kernel)
private def next5 := oneStep 5 r5 r6 (by decide +kernel)
private def next6 := oneStep 6 r6 r7 (by decide +kernel)
private def next7 := oneStep 7 r7 r8 (by decide +kernel)
private def next8 := oneStep 8 r8 r9 (by decide +kernel)
private def next9 := oneStep 9 r9 r10 (by decide +kernel)
private def next10 := oneStep 10 r10 r11 (by decide +kernel)
private def next11 := oneStep 11 r11 r12 (by decide +kernel)
private def next12 := oneStep 12 r12 r13 (by decide +kernel)
private def next13 := oneStep 13 r13 r14 (by decide +kernel)
private def next14 := oneStep 14 r14 r15 (by decide +kernel)
private def next15 := oneStep 15 r15 r16 (by decide +kernel)
private def next16 := oneStep 16 r16 r17 (by decide +kernel)
private def next17 := oneStep 17 r17 r18 (by decide +kernel)
private def next18 := oneStep 18 r18 r19 (by decide +kernel)
private def next19 := oneStep 19 r19 r20 (by decide +kernel)
private def next20 := oneStep 20 r20 r21 (by decide +kernel)
private def next21 := oneStep 21 r21 r22 (by decide +kernel)
private def next22 := oneStep 22 r22 r23 (by decide +kernel)
private def next23 := oneStep 23 r23 r24 (by decide +kernel)
private def next24 := oneStep 24 r24 r25 (by decide +kernel)
private def next25 := oneStep 25 r25 r26 (by decide +kernel)
private def next26 := oneStep 26 r26 r27 (by decide +kernel)
private def next27 := oneStep 27 r27 r28 (by decide +kernel)
private def next28 := oneStep 28 r28 r29 (by decide +kernel)
private def next29 := oneStep 29 r29 r30 (by decide +kernel)
private def next30 := oneStep 30 r30 r31 (by decide +kernel)
private def next31 := oneStep 31 r31 r32 (by decide +kernel)
private def next32 := oneStep 32 r32 r33 (by decide +kernel)
private def next33 := oneStep 33 r33 r34 (by decide +kernel)
private def next34 := oneStep 34 r34 r35 (by decide +kernel)
private def next35 := oneStep 35 r35 (checkpoint 1) (by decide +kernel)

theorem checked0 : Step 0 := by
  intro h
  have h1 := next0 h
  have h2 := next1 h1
  have h3 := next2 h2
  have h4 := next3 h3
  have h5 := next4 h4
  have h6 := next5 h5
  have h7 := next6 h6
  have h8 := next7 h7
  have h9 := next8 h8
  have h10 := next9 h9
  have h11 := next10 h10
  have h12 := next11 h11
  have h13 := next12 h12
  have h14 := next13 h13
  have h15 := next14 h14
  have h16 := next15 h15
  have h17 := next16 h16
  have h18 := next17 h17
  have h19 := next18 h18
  have h20 := next19 h19
  have h21 := next20 h20
  have h22 := next21 h21
  have h23 := next22 h22
  have h24 := next23 h23
  have h25 := next24 h24
  have h26 := next25 h25
  have h27 := next26 h26
  have h28 := next27 h27
  have h29 := next28 h28
  have h30 := next29 h29
  have h31 := next30 h30
  have h32 := next31 h31
  have h33 := next32 h32
  have h34 := next33 h33
  have h35 := next34 h34
  have h36 := next35 h35
  exact h36

end RiemannResearch.Analysis.LamzouriGapKernel285.FourierBlocks
