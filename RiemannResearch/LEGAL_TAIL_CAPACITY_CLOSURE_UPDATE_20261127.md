# Legal tail-mean capacity closure update

**Current status, November 28.** The completed legal stages, their strong limit,
and the continuous Nyman projection now have exact Lean identifications. The
physical weak-* limit has mass \(1-C_*\) at zero. The fixed-window arithmetic
criterion and the remaining Hardy-space evaluation are described in the final section.

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

## Remaining obligation at the November 27 checkpoint

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

## Physical weak-* compactness and triangular meshes (Christian Noack, 2026-11-28)

Write \(m=K+1\), \(e_K=t_K-v_K\), \(\Delta_m=1-C_K\), and \(C_*=\sup_K C_K\).
The mass \(m\|e_K\|^2=\Delta_m\) on the physical sites \(1/j\) defines the
positive functional \(\nu_m\) on \(C([0,1],\mathbb R)\).

* All \(\nu_m\) belong to the weak-* compact dual unit ball. Along every
  integer scale, \(\nu_m\to(1-C_*)\delta_0\) weak-*. A constant test recovers
  the missing mass. For the piecewise-linear triangular hats at \(i/N\),
  \(m\ge N\) gives zero weight at nodes \(i\ge2\) and the first two coefficients
  sum to exactly \(\Delta_m\). The first interior hat has weight at most
  \(N\Delta_m/m\). See `physicalTailEnergy_weakStar_compact`,
  `physicalTailEnergy_weakStar_tendsto` and `physicalTailEnergy_first_hat_pair`.
* The separate triangular array of generator parameters is
  \(T_N=\{a/b:1\le a<b\le N\}\). Each finite row has legal witnesses at
  the single physical stage \(N!\); the rows are nested and exhaust all
  rationals in \((0,1)\). See `triangularMeshRow_legal_witness` and
  `triangularMesh_closedSpan`.
* The normalized reciprocal-cell map takes the completed legal stage onto
  its real mesh, including \(m=1\). The fixed-head repair supplies the reverse
  inclusion. The real stage projection of one is the actual optimizer \(p_m\).
  In the common coordinate there is a strong limit \(p\) with
  \(\|p-p_m\|_2^2=C_*-C_{m-1}\) at every stage. The common-coordinate squared
  residual densities converge in total variation, with the explicit bound
  in `commonTailResidual_energy_variation`.
* Embedding the real optimizers into complex \(L^2\) and testing the limit
  on the triangular rational rows gives
  \(C_*=\|P_{\mathcal N}\mathbf1\|_2^2\) for Burnol's continuous space.
  See `normalizedLegalTailMeanCapacity_iSup_eq_nymanProjection`.
* The signed block average is the actual dilation adjoint \(D_m^*e_K\).
  If \(B_m(N)\) is its first \(N\) weighted negative parts and \(B_m(\infty)\)
  the complete sum, the parity witness and the signed dyadic correlation give
  \[
    B_m(\infty)\ge(1-1/\sqrt2)\Delta_m\ge(4/27)\Delta_m^2,\qquad
    B_m(N)\ge(1-1/\sqrt2)\Delta_m-\sqrt{\Delta_m/(N+1)} .
  \]
  For \(0<\varepsilon\le\Delta_m\) and \(N+1\ge64/\varepsilon\), some
  block among the first \(N\) overshoots one by at least \(\Delta_m/8\).
  Also \(B_m(N)\le(\sqrt{\Delta_m}-\Delta_m)/2\). The separate trial benchmark
  uses two conductors with the exact entries from `ResidueSmallGram`.
  See `tailBlockResidual_first_identity`, `tailBlockOvershoot_exists_block`
  and `twoGeneratorMesh_energy`.

**Open arithmetic step.** Establish
\(\liminf_{n\to\infty} B_{(n+1)!}(N)=0\) for every fixed \(N\ge1\).
The equivalence with RH is `fixedBlock_liminf_zero_iff_RH`. The upper
bound above still permits a positive limiting deficit. The continuous
multiplicity-sensitive Hardy projection product also remains open in Lean.

## GUE comparison in absolute ordered pairs

Let \(M=N(0,T)\), let \(m_\rho\) be analytic multiplicity, and let \(D_T\)
count ordered pairs of occurrences of different complex roots at the same
ordinate. The full horizontal diagonal is \(\sum_{\rho}m_\rho^2+D_T\).
At the bandwidth in `distinctRootGaussianPrecision`, define \(S_T\) by
subtracting the analytic diagonal and \(M G(a)\) from the full reconstructed
Gaussian power in count units, where
\[
G(a)=\int_{\mathbb R}e^{-a x^2}\bigl(1-\operatorname{sinc}^2(\pi x)\bigr)\,dx .
\]
The capacity and Gaussian comparison theorems use the original occurrence
labels, including analytic repeats. The deterministic bandwidth uses \(M\)
and the least positive unfolded gap capped at one. At that bandwidth each of
the unequal-height contribution and \(M G(a)\) lies in \([0,1/8]\).
The signed reconstruction costs at most \(1/4\), so \(|S_T-D_T|\le3/8\)
and \(\lfloor S_T+1/2\rfloor=D_T\). The signed integral is recorded in
`calibratedSineRootExcess_eq_landau_integral`.

For one right zero \(\rho=\beta+i\gamma\) of positive height, put
\(d_\rho=(2\beta-1)/|\rho|^2\). Every legal scale satisfies
\(B_m(N)\ge d_\rho/8\) as soon as \(N+1\ge64/d_\rho\). Every nonempty
cutoff \(T>1\) containing that zero satisfies \(S_T\ge2m_\rho^2-3/8\).

**Open arithmetic estimate.** Prove \(S_T<1\) for arbitrarily large \(T\).
The checked equivalence is `fixedBlock_liminf_zero_iff_calibrated_sine_excess`.
The GUE two-point law supplies the model term \(G(a)\). A bounded number of
ordered collisions has vanishing weight after division by \(M\), whereas
this estimate is in absolute ordered pairs.
