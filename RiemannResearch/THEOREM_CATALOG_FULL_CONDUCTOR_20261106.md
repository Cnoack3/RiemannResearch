# Full-conductor dilation and projection audit, November 2026

## Established finite and Hilbert identities

Module: `RiemannResearch/RH/QFloorDilationEnergy.lean`.
The following additions concern the actual inverse-square Q space and every
integer dilation m > 1, without a squarefree assumption.

- `qBlockWeight_lt`: each positive quotient block has mass strictly below Q(k)/m.
- `qBlockDefect_pos`: every positive block defect is strictly positive.
- `qBlockDefect_energy_summable`: the complete nonnegative energy defect is summable.
- `floorDilation_norm_sq_lt`: for nonzero f, ||T_m f||_Q^2 < ||f||_Q^2/m.
- `floorDilation_sharp_equality_iff`: equality in that bound iff f = 0.

These strengthen the existing weak upper estimate and exact defect identity.
They do not supply a uniform constant smaller than 1/m. They do not imply
that legal approximation error vanishes.

Source: user-requested full-conductor research audit; direct strict
inverse-square block comparison. No mathematical priority claim is made.
The initial coherent snippet passed server job
`job_mU_yRm8NjQrXSTs_Lxa0DDUDlUQRKfHl` (31.249 seconds);
the final source is subject to the required publication checkpoint.

## Paper results, not new Lean certifications

The accompanying full-conductor manuscript develops exact P/Q Gram equations,
integrated Ramanujan changes of basis, full p-adic CRT, Q divisor Parseval, and
Mertens exact-head transfer for the full matched displacement.

In particular, the paper establishes:
RH iff liminf_m m dist_Q(d g_m,V)/(1+log m)^k < infinity, for each fixed k >= 0.
The argument uses localized residue pairing, the full exact-head correction,
and the actual full-family witness. Formalization of that proof is Open.

## Open obligations

- Formalize the full-family localized residue and product-distance proof.
- Supply the named RH-to-natural-approximation provider wherever still explicit.
- Prove an actual quantitative regularity or tail bound for the full displacement.
- Do not substitute the squarefree displacement in these full-family statements.
