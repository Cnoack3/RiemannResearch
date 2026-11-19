/-
Copyright (c) 2026 RiemannResearch contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.LamzouriGap285FourierStages

namespace RiemannResearch.Analysis.LamzouriGapKernel285.FourierBlocks
open GapKernelFourierRecurrence

set_option maxRecDepth 120000
set_option maxHeartbeats 0
private def r73 : List ℤ := eval% propose 72 (checkpoint 2)
private def r74 : List ℤ := eval% propose 73 r73
private def r75 : List ℤ := eval% propose 74 r74
private def r76 : List ℤ := eval% propose 75 r75
private def r77 : List ℤ := eval% propose 76 r76
private def r78 : List ℤ := eval% propose 77 r77
private def r79 : List ℤ := eval% propose 78 r78
private def r80 : List ℤ := eval% propose 79 r79
private def r81 : List ℤ := eval% propose 80 r80
private def r82 : List ℤ := eval% propose 81 r81
private def r83 : List ℤ := eval% propose 82 r82
private def r84 : List ℤ := eval% propose 83 r83
private def r85 : List ℤ := eval% propose 84 r84
private def r86 : List ℤ := eval% propose 85 r85
private def r87 : List ℤ := eval% propose 86 r86
private def r88 : List ℤ := eval% propose 87 r87
private def r89 : List ℤ := eval% propose 88 r88
private def r90 : List ℤ := eval% propose 89 r89
private def r91 : List ℤ := eval% propose 90 r90
private def r92 : List ℤ := eval% propose 91 r91
private def r93 : List ℤ := eval% propose 92 r92
private def r94 : List ℤ := eval% propose 93 r93
private def r95 : List ℤ := eval% propose 94 r94
private def r96 : List ℤ := eval% propose 95 r95
private def r97 : List ℤ := eval% propose 96 r96
private def r98 : List ℤ := eval% propose 97 r97
private def r99 : List ℤ := eval% propose 98 r98
private def r100 : List ℤ := eval% propose 99 r99
private def r101 : List ℤ := eval% propose 100 r100
private def r102 : List ℤ := eval% propose 101 r101
private def r103 : List ℤ := eval% propose 102 r102
private def r104 : List ℤ := eval% propose 103 r103
private def r105 : List ℤ := eval% propose 104 r104
private def r106 : List ℤ := eval% propose 105 r105
private def r107 : List ℤ := eval% propose 106 r106

private def next72 := oneStep 72 (checkpoint 2) r73 (by decide +kernel)
private def next73 := oneStep 73 r73 r74 (by decide +kernel)
private def next74 := oneStep 74 r74 r75 (by decide +kernel)
private def next75 := oneStep 75 r75 r76 (by decide +kernel)
private def next76 := oneStep 76 r76 r77 (by decide +kernel)
private def next77 := oneStep 77 r77 r78 (by decide +kernel)
private def next78 := oneStep 78 r78 r79 (by decide +kernel)
private def next79 := oneStep 79 r79 r80 (by decide +kernel)
private def next80 := oneStep 80 r80 r81 (by decide +kernel)
private def next81 := oneStep 81 r81 r82 (by decide +kernel)
private def next82 := oneStep 82 r82 r83 (by decide +kernel)
private def next83 := oneStep 83 r83 r84 (by decide +kernel)
private def next84 := oneStep 84 r84 r85 (by decide +kernel)
private def next85 := oneStep 85 r85 r86 (by decide +kernel)
private def next86 := oneStep 86 r86 r87 (by decide +kernel)
private def next87 := oneStep 87 r87 r88 (by decide +kernel)
private def next88 := oneStep 88 r88 r89 (by decide +kernel)
private def next89 := oneStep 89 r89 r90 (by decide +kernel)
private def next90 := oneStep 90 r90 r91 (by decide +kernel)
private def next91 := oneStep 91 r91 r92 (by decide +kernel)
private def next92 := oneStep 92 r92 r93 (by decide +kernel)
private def next93 := oneStep 93 r93 r94 (by decide +kernel)
private def next94 := oneStep 94 r94 r95 (by decide +kernel)
private def next95 := oneStep 95 r95 r96 (by decide +kernel)
private def next96 := oneStep 96 r96 r97 (by decide +kernel)
private def next97 := oneStep 97 r97 r98 (by decide +kernel)
private def next98 := oneStep 98 r98 r99 (by decide +kernel)
private def next99 := oneStep 99 r99 r100 (by decide +kernel)
private def next100 := oneStep 100 r100 r101 (by decide +kernel)
private def next101 := oneStep 101 r101 r102 (by decide +kernel)
private def next102 := oneStep 102 r102 r103 (by decide +kernel)
private def next103 := oneStep 103 r103 r104 (by decide +kernel)
private def next104 := oneStep 104 r104 r105 (by decide +kernel)
private def next105 := oneStep 105 r105 r106 (by decide +kernel)
private def next106 := oneStep 106 r106 r107 (by decide +kernel)
private def next107 := oneStep 107 r107 (checkpoint 3) (by decide +kernel)

theorem checked2 : Step 2 := by
  intro h
  have h73 := next72 h
  have h74 := next73 h73
  have h75 := next74 h74
  have h76 := next75 h75
  have h77 := next76 h76
  have h78 := next77 h77
  have h79 := next78 h78
  have h80 := next79 h79
  have h81 := next80 h80
  have h82 := next81 h81
  have h83 := next82 h82
  have h84 := next83 h83
  have h85 := next84 h84
  have h86 := next85 h85
  have h87 := next86 h86
  have h88 := next87 h87
  have h89 := next88 h88
  have h90 := next89 h89
  have h91 := next90 h90
  have h92 := next91 h91
  have h93 := next92 h92
  have h94 := next93 h93
  have h95 := next94 h94
  have h96 := next95 h95
  have h97 := next96 h96
  have h98 := next97 h97
  have h99 := next98 h98
  have h100 := next99 h99
  have h101 := next100 h100
  have h102 := next101 h101
  have h103 := next102 h102
  have h104 := next103 h103
  have h105 := next104 h104
  have h106 := next105 h105
  have h107 := next106 h106
  have h108 := next107 h107
  exact h108

end RiemannResearch.Analysis.LamzouriGapKernel285.FourierBlocks
