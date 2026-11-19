/-
Copyright (c) 2026 RiemannResearch contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.LamzouriGap285FourierStages

namespace RiemannResearch.Analysis.LamzouriGapKernel285.FourierBlocks
open GapKernelFourierRecurrence

set_option maxRecDepth 120000
set_option maxHeartbeats 0
private def r37 : List ℤ := eval% propose 36 (checkpoint 1)
private def r38 : List ℤ := eval% propose 37 r37
private def r39 : List ℤ := eval% propose 38 r38
private def r40 : List ℤ := eval% propose 39 r39
private def r41 : List ℤ := eval% propose 40 r40
private def r42 : List ℤ := eval% propose 41 r41
private def r43 : List ℤ := eval% propose 42 r42
private def r44 : List ℤ := eval% propose 43 r43
private def r45 : List ℤ := eval% propose 44 r44
private def r46 : List ℤ := eval% propose 45 r45
private def r47 : List ℤ := eval% propose 46 r46
private def r48 : List ℤ := eval% propose 47 r47
private def r49 : List ℤ := eval% propose 48 r48
private def r50 : List ℤ := eval% propose 49 r49
private def r51 : List ℤ := eval% propose 50 r50
private def r52 : List ℤ := eval% propose 51 r51
private def r53 : List ℤ := eval% propose 52 r52
private def r54 : List ℤ := eval% propose 53 r53
private def r55 : List ℤ := eval% propose 54 r54
private def r56 : List ℤ := eval% propose 55 r55
private def r57 : List ℤ := eval% propose 56 r56
private def r58 : List ℤ := eval% propose 57 r57
private def r59 : List ℤ := eval% propose 58 r58
private def r60 : List ℤ := eval% propose 59 r59
private def r61 : List ℤ := eval% propose 60 r60
private def r62 : List ℤ := eval% propose 61 r61
private def r63 : List ℤ := eval% propose 62 r62
private def r64 : List ℤ := eval% propose 63 r63
private def r65 : List ℤ := eval% propose 64 r64
private def r66 : List ℤ := eval% propose 65 r65
private def r67 : List ℤ := eval% propose 66 r66
private def r68 : List ℤ := eval% propose 67 r67
private def r69 : List ℤ := eval% propose 68 r68
private def r70 : List ℤ := eval% propose 69 r69
private def r71 : List ℤ := eval% propose 70 r70

private def next36 := oneStep 36 (checkpoint 1) r37 (by decide +kernel)
private def next37 := oneStep 37 r37 r38 (by decide +kernel)
private def next38 := oneStep 38 r38 r39 (by decide +kernel)
private def next39 := oneStep 39 r39 r40 (by decide +kernel)
private def next40 := oneStep 40 r40 r41 (by decide +kernel)
private def next41 := oneStep 41 r41 r42 (by decide +kernel)
private def next42 := oneStep 42 r42 r43 (by decide +kernel)
private def next43 := oneStep 43 r43 r44 (by decide +kernel)
private def next44 := oneStep 44 r44 r45 (by decide +kernel)
private def next45 := oneStep 45 r45 r46 (by decide +kernel)
private def next46 := oneStep 46 r46 r47 (by decide +kernel)
private def next47 := oneStep 47 r47 r48 (by decide +kernel)
private def next48 := oneStep 48 r48 r49 (by decide +kernel)
private def next49 := oneStep 49 r49 r50 (by decide +kernel)
private def next50 := oneStep 50 r50 r51 (by decide +kernel)
private def next51 := oneStep 51 r51 r52 (by decide +kernel)
private def next52 := oneStep 52 r52 r53 (by decide +kernel)
private def next53 := oneStep 53 r53 r54 (by decide +kernel)
private def next54 := oneStep 54 r54 r55 (by decide +kernel)
private def next55 := oneStep 55 r55 r56 (by decide +kernel)
private def next56 := oneStep 56 r56 r57 (by decide +kernel)
private def next57 := oneStep 57 r57 r58 (by decide +kernel)
private def next58 := oneStep 58 r58 r59 (by decide +kernel)
private def next59 := oneStep 59 r59 r60 (by decide +kernel)
private def next60 := oneStep 60 r60 r61 (by decide +kernel)
private def next61 := oneStep 61 r61 r62 (by decide +kernel)
private def next62 := oneStep 62 r62 r63 (by decide +kernel)
private def next63 := oneStep 63 r63 r64 (by decide +kernel)
private def next64 := oneStep 64 r64 r65 (by decide +kernel)
private def next65 := oneStep 65 r65 r66 (by decide +kernel)
private def next66 := oneStep 66 r66 r67 (by decide +kernel)
private def next67 := oneStep 67 r67 r68 (by decide +kernel)
private def next68 := oneStep 68 r68 r69 (by decide +kernel)
private def next69 := oneStep 69 r69 r70 (by decide +kernel)
private def next70 := oneStep 70 r70 r71 (by decide +kernel)
private def next71 := oneStep 71 r71 (checkpoint 2) (by decide +kernel)

theorem checked1 : Step 1 := by
  intro h
  have h37 := next36 h
  have h38 := next37 h37
  have h39 := next38 h38
  have h40 := next39 h39
  have h41 := next40 h40
  have h42 := next41 h41
  have h43 := next42 h42
  have h44 := next43 h43
  have h45 := next44 h44
  have h46 := next45 h45
  have h47 := next46 h46
  have h48 := next47 h47
  have h49 := next48 h48
  have h50 := next49 h49
  have h51 := next50 h50
  have h52 := next51 h51
  have h53 := next52 h52
  have h54 := next53 h53
  have h55 := next54 h54
  have h56 := next55 h55
  have h57 := next56 h56
  have h58 := next57 h57
  have h59 := next58 h58
  have h60 := next59 h59
  have h61 := next60 h60
  have h62 := next61 h61
  have h63 := next62 h62
  have h64 := next63 h63
  have h65 := next64 h64
  have h66 := next65 h65
  have h67 := next66 h66
  have h68 := next67 h67
  have h69 := next68 h68
  have h70 := next69 h69
  have h71 := next70 h70
  have h72 := next71 h71
  exact h72

end RiemannResearch.Analysis.LamzouriGapKernel285.FourierBlocks
