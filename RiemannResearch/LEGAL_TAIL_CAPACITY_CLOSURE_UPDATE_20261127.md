# Legal tail-mean capacity closure update

## Kernel-checked progress

The continuous Nyman generator is represented in the actual complex
`Lp ℂ 2 (volume.restrict (Set.Ioc 0 1))` space.  The following declarations
are proved in `RH/NymanContinuousSpace.lean`:

- `generatorFunction_ae_tendsto`: for nonzero limiting parameter, pointwise
  convergence holds away from the countable set of floor discontinuities;
- `generatorFunction_unifIntegrable_of_abs_le`: a bounded parameter family
  is uniformly integrable at exponent two;
- `tendsto_generator` and `continuousAt_generator`: parameter convergence
  gives convergence of the actual L2 generators;
- `generator_mem_rationalClosedSpace`: every generator with parameter in
  `(0,1)` belongs to the rational-parameter closed span;
- `rationalClosedSpace_eq_closedSpace`: the rational-parameter closed span
  is exactly Burnol's full continuous Nyman closed space.

The density argument uses rational approximation inside `(0,1)); it does not
assume the Riemann hypothesis or a zero-free half-plane.

## Exact symbolic check

On a reciprocal cell where `floor (a/t) = n` and `floor (1/t) = k`,
Wolfram exact simplification gives

`FractionalPart[a/t] - a FractionalPart[1/t] = a*k - n`.

This is the cellwise identity underlying the rational residue transport.  It
does not by itself give a uniform capacity gain.

## Remaining obligation

The analytic rational-density step is now closed.  The next missing theorem is
the rescaled discrete identification: prove that the cofinal (equivalently,
factorial) union of the transported legal zero-head stages has closed span equal
to the rational Nyman span.  After that, one still needs either Burnol's genuine
multiplicity-sensitive zero-product projection equality in Lean (confluent
Mellin derivative jets for repeated zeros), or an independent arithmetic
rational/coprime witness estimate forcing the limiting deficit to vanish.
No unconditional positive relative gain is currently proved, and saturation
remains open.

## Factorial rescaling update (2026-11-28)

The factorial parameter-space identification is now kernel checked:

- `scaleMeshParameters m` is the exact set of ratios `m / d` with `m < d`;
- `factorialMeshParameters_eq_rationalParameters` proves that the union of
  these meshes at scales `(n + 1)!` is exactly the rational part of `(0,1)`;
- `factorialMeshClosedSpace_eq_closedSpace` proves that the closed span of
  their continuous generators is Burnol's full continuous Nyman space.

For a reduced rational `a / b` in `(0,1)`, the proof takes a factorial
`m` divisible by `a`, sets `d = b * (m / a)`, and verifies exactly that
`m / d = a / b` and `m < d`. Wolfram independently simplified both
identities under `0 < a < b` and `a ∣ m`.

This closes the cofinal parameter-space span. It does **not** yet construct an
isometric linear transport from the completed discrete legal head kernel onto
the corresponding continuous mesh space. The finite dictionary in
`LegalTailNymanMesh.lean` supplies both algebraic directions, but continuity
and surjectivity on the completed stage remain the operator-level obligation.
The multiplicity-sensitive Burnol projection equality and a quantitative
arithmetic estimate excluding a positive limiting deficit also remain open.
