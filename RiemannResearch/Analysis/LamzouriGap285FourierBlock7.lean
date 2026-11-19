/-
Copyright (c) 2026 RiemannResearch contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.LamzouriGap285FourierStages

namespace RiemannResearch.Analysis.LamzouriGapKernel285.FourierBlocks
open GapKernelFourierRecurrence

set_option maxRecDepth 120000
set_option maxHeartbeats 0
private def r253 : List ℤ := eval% propose 252 (checkpoint 7)
private def r254 : List ℤ := eval% propose 253 r253
private def r255 : List ℤ := eval% propose 254 r254
private def r256 : List ℤ := eval% propose 255 r255
private def r257 : List ℤ := eval% propose 256 r256
private def r258 : List ℤ := eval% propose 257 r257
private def r259 : List ℤ := eval% propose 258 r258
private def r260 : List ℤ := eval% propose 259 r259
private def r261 : List ℤ := eval% propose 260 r260
private def r262 : List ℤ := eval% propose 261 r261
private def r263 : List ℤ := eval% propose 262 r262
private def r264 : List ℤ := eval% propose 263 r263
private def r265 : List ℤ := eval% propose 264 r264
private def r266 : List ℤ := eval% propose 265 r265
private def r267 : List ℤ := eval% propose 266 r266
private def r268 : List ℤ := eval% propose 267 r267
private def r269 : List ℤ := eval% propose 268 r268
private def r270 : List ℤ := eval% propose 269 r269
private def r271 : List ℤ := eval% propose 270 r270
private def r272 : List ℤ := eval% propose 271 r271
private def r273 : List ℤ := eval% propose 272 r272
private def r274 : List ℤ := eval% propose 273 r273
private def r275 : List ℤ := eval% propose 274 r274
private def r276 : List ℤ := eval% propose 275 r275
private def r277 : List ℤ := eval% propose 276 r276
private def r278 : List ℤ := eval% propose 277 r277
private def r279 : List ℤ := eval% propose 278 r278
private def r280 : List ℤ := eval% propose 279 r279
private def r281 : List ℤ := eval% propose 280 r280
private def r282 : List ℤ := eval% propose 281 r281
private def r283 : List ℤ := eval% propose 282 r282
private def r284 : List ℤ := eval% propose 283 r283
private def r285 : List ℤ := eval% propose 284 r284

private def next252 := oneStep 252 (checkpoint 7) r253 (by decide +kernel)
private def next253 := oneStep 253 r253 r254 (by decide +kernel)
private def next254 := oneStep 254 r254 r255 (by decide +kernel)
private def next255 := oneStep 255 r255 r256 (by decide +kernel)
private def next256 := oneStep 256 r256 r257 (by decide +kernel)
private def next257 := oneStep 257 r257 r258 (by decide +kernel)
private def next258 := oneStep 258 r258 r259 (by decide +kernel)
private def next259 := oneStep 259 r259 r260 (by decide +kernel)
private def next260 := oneStep 260 r260 r261 (by decide +kernel)
private def next261 := oneStep 261 r261 r262 (by decide +kernel)
private def next262 := oneStep 262 r262 r263 (by decide +kernel)
private def next263 := oneStep 263 r263 r264 (by decide +kernel)
private def next264 := oneStep 264 r264 r265 (by decide +kernel)
private def next265 := oneStep 265 r265 r266 (by decide +kernel)
private def next266 := oneStep 266 r266 r267 (by decide +kernel)
private def next267 := oneStep 267 r267 r268 (by decide +kernel)
private def next268 := oneStep 268 r268 r269 (by decide +kernel)
private def next269 := oneStep 269 r269 r270 (by decide +kernel)
private def next270 := oneStep 270 r270 r271 (by decide +kernel)
private def next271 := oneStep 271 r271 r272 (by decide +kernel)
private def next272 := oneStep 272 r272 r273 (by decide +kernel)
private def next273 := oneStep 273 r273 r274 (by decide +kernel)
private def next274 := oneStep 274 r274 r275 (by decide +kernel)
private def next275 := oneStep 275 r275 r276 (by decide +kernel)
private def next276 := oneStep 276 r276 r277 (by decide +kernel)
private def next277 := oneStep 277 r277 r278 (by decide +kernel)
private def next278 := oneStep 278 r278 r279 (by decide +kernel)
private def next279 := oneStep 279 r279 r280 (by decide +kernel)
private def next280 := oneStep 280 r280 r281 (by decide +kernel)
private def next281 := oneStep 281 r281 r282 (by decide +kernel)
private def next282 := oneStep 282 r282 r283 (by decide +kernel)
private def next283 := oneStep 283 r283 r284 (by decide +kernel)
private def next284 := oneStep 284 r284 r285 (by decide +kernel)
private def next285 := oneStep 285 r285 (checkpoint 8) (by decide +kernel)

theorem checked7 : Step 7 := by
  intro h
  have h253 := next252 h
  have h254 := next253 h253
  have h255 := next254 h254
  have h256 := next255 h255
  have h257 := next256 h256
  have h258 := next257 h257
  have h259 := next258 h258
  have h260 := next259 h259
  have h261 := next260 h260
  have h262 := next261 h261
  have h263 := next262 h262
  have h264 := next263 h263
  have h265 := next264 h264
  have h266 := next265 h265
  have h267 := next266 h266
  have h268 := next267 h267
  have h269 := next268 h268
  have h270 := next269 h269
  have h271 := next270 h270
  have h272 := next271 h271
  have h273 := next272 h272
  have h274 := next273 h273
  have h275 := next274 h274
  have h276 := next275 h275
  have h277 := next276 h276
  have h278 := next277 h277
  have h279 := next278 h278
  have h280 := next279 h279
  have h281 := next280 h280
  have h282 := next281 h281
  have h283 := next282 h282
  have h284 := next283 h283
  have h285 := next284 h284
  have h286 := next285 h285
  exact h286

end RiemannResearch.Analysis.LamzouriGapKernel285.FourierBlocks
