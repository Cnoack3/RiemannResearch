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
