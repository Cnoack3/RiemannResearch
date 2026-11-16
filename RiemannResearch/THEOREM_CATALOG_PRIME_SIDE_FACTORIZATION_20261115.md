# Prime-side Weil factorization: formal results and revised agenda

Date: 2026-11-15.
Development base: `ac85bee98c61d52bb7865e010acab73ee988360a`.

Continuation (2026-11-16): [actual damped prime operator and revised agenda](THEOREM_CATALOG_DAMPED_PRIME_OPERATOR_20261116.md).
The synthesis, exact support projection, and nuclear prime operator for sigma > 1
are now formalized. Analytic-only status statements below record the earlier
checkpoint; the continuation gives the current status and remaining obligations.

## Sources and scope

The selected Drive file was [v_prime_side_factorization.pdf](https://drive.google.com/file/d/1q6RheCrn_nIDz3B8JZRs0Vuv4nr1h19p/view).
The comparison source was [v_prime_side_factorization_A_F_audited.pdf](https://drive.google.com/file/d/1eJugqY5pLGGUG9RsfjLQlsj7sWa7fAjl/view),
especially Theorems 11.6--11.8 and Tracks C--F.
Their V is the arithmetic prime-power coordinate space; it must not be
identified without proof with the closed residue-generator space called V
elsewhere in this repository.

No RH proof or unconditional positive factorization is claimed.
The new declarations have no unresolved RH-specific hypotheses hidden as axioms.
The cutoff-factorization theorem is a conditional research reduction whose
pointwise approximation hypotheses remain open.

## Kernel-checked development

A single coherent snippet containing all 22 new theorems passed Bazel /
BuildBuddy in job `job_kKD-v1ZTGALdFQ1MwZO8SmpqL-K2ON7x`.
Server verification duration: 31.593 seconds (not workspace setup or polling).
Build invocation:
https://app.buildbuddy.io/invocation/bae1f646-5c60-47fc-b1ca-a56f376bd04b

All four saved modules compiled with their own imports in Bazel job
`job_2KRn1WXOi2lDSl939fhIZYflNsAN8Ij_` (101.516 server seconds).
An exact `#guard_msgs` axiom audit passed in job
`job_lcDQR69pTrk6k6SmNUMXSTJDVgw5G26I`: both the actual RH reduction
and off-line defect theorem depend only on `propext`,
`Classical.choice`, and `Quot.sound`. Their stated local hypotheses
remain part of their types.

This is development evidence. Publication is separately gated by a full
`//:RiemannResearch` checkpoint including the integrated source.

### Exact signed energy

Module: `Analysis/FiniteTranslationEnergy.lean`.
Namespace: `RiemannResearch.Analysis.FiniteTranslationEnergy`.

| Declaration | Exact content |
|---|---|
| `signed_energy_identity` | Signed correlation equals weighted displacement squares minus the full scalar counterterm. |
| `signed_energy_lower_bound` | Lower bound by minus twice total weight times squared norm. |
| `polar_signed_identity` | The polar cross term is half the difference of sum/difference norm squares. |
| `completed_signed_identity` | Full finite signed identity retaining polar, archimedean, displacement, and negative scalar sectors. |
| `cosineSymbol_zero` | The symbol at zero is exactly minus twice total weight. |
| `cosineSymbol_lower_bound` | This value is a global minimum of the finite symbol for nonnegative weights. |
| `scalar_repair_iff` | A constant b makes the finite symbol nonnegative exactly when b is at least twice total weight. |
| `repair_at_zero` | Every pointwise nonconstant repair must pay the full deficit at zero. |
| `nonneg_of_approximate_squares` | Pointwise convergence of values and vanishing signed errors suffices for a nonnegative limit. |

For a finite set S, weights c_i, and maps preserving the norm of x, the exact identity is

```math
-2\sum_{i\in S}c_i\operatorname{Re}\langle x,U_ix\rangle
=\sum_{i\in S}c_i\|x-U_ix\|^2
 -2\left(\sum_{i\in S}c_i\right)\|x\|^2.
```

The algebra does not need linearity or surjectivity of the maps. The scalar
symbol results are pointwise results about a real function; this module does
not separately formalize its realization as an L2 Fourier multiplier.
The completed identity treats the two gamma-sector values as explicit real
inputs. Identification with convergent gamma integrals is an analytic bridge,
not an implicit assumption of the algebra.

### Actual prime weights and finite windows

Module: `RH/WeilPrimeCutoffFactorization.lean`.
Namespace: `RiemannResearch.RH.WeilPrimeCutoff`.

The definitions reuse the repository's actual
`primePowerWeight n = vonMangoldt n / sqrt n`.
The cutoff convention is n < N, not n <= N.

| Declaration | Content |
|---|---|
| `primeSymbol_lower_bound` | Exact lower bound -2 C_N for the actual prime symbol. |
| `primeSymbol_zero` | Equality at frequency zero. |
| `primeSymbol_scalar_repair_iff` | Exact necessary and sufficient scalar correction b >= 2 C_N, at every cutoff, without PNT. |
| `kernelTerm_eq_zero_of_cutoff` | A support bound proves every omitted prime term is zero. |
| `primeKernel_eq_cutoff` | The infinite series equals the finite sum at the explicit cutoff. |
| `kernelTerm_summable` | Summability is proved by finite support, not default-value tsum behavior. |
| `finite_window_stabilization` | All entries on any specified finite shift window stabilize together. |

If C(u)=0 for |u|>B and |x_i-x_j|<=D throughout the window, then any
N>exp(D+B) gives the exact infinite prime kernel on that window.
For the PDF's autocorrelation support B=2r this recovers its exp(D+2r)
bound. The Lean statement is stronger in allowing arbitrary complex kernels,
arbitrary finite shift sets, with the actual von Mangoldt weights.
It does not claim uniform convergence as D and B grow.

### Singular auxiliary sectors

Module: `Analysis/RangeSchurComplement.lean`.
Namespace: `RiemannResearch.Analysis.RangeSchurComplement`.

The four theorems `complete_square`, `minimizing_value`,
`reduced_le_block`, and `block_nonneg_iff` hold in real inner-product
spaces. For symmetric D and a range solution D(Sx)=Cx they prove

```math
\langle x,Bx\rangle+2\langle Cx,y\rangle+\langle y,Dy\rangle
=\langle x,Bx\rangle-\langle Cx,Sx\rangle
 +\langle y+Sx,D(y+Sx)\rangle.
```

When D is nonnegative, block positivity is equivalent to nonnegativity
of the reduced form. The minimum is attained at y=-Sx.
This improves the PDF's hypothesis D>=delta I>0: no inverse, finite
dimension, completeness, or uniform positive lower bound is required.
Singularity of the auxiliary sector therefore does not provide a way around
the positivity obligation when the range equation is solvable.

### Actual Weil test functions and the factorization obstruction

Module: `RH/WeilApproximateFactorization.lean`.
Namespace: `RiemannResearch.RH.SignedWeilCorrelation`.

`riemannHypothesis_of_cutoff_gram_limit` proves RH from

```math
A_n(f)=\|R_n f\|^2+E_n(f),\qquad
A_n(f)\longrightarrow \operatorname{Re}W(f,f),\qquad E_n(f)\longrightarrow0
```

for every `SmoothSuperexponentialDecay` test f in the existing repository
criterion. Only scalar pointwise convergence is required. The maps R_n
need not be linear for this implication. Constructing them from prime data
with these properties is still open. Positivity just on a fixed finite
prime-power window does not supply the displayed hypotheses.

`off_line_forces_factorization_defect` proves the stronger falsification
statement: given any actual off-line zero rho of analytic multiplicity m,
and any family R_n into any seminormed additive group, there is one smooth
superexponentially decaying test f such that, for every n,

```math
\operatorname{Re}W(f,f)-\|R_n f\|^2=-2m-\|R_n f\|^2,
\qquad
\left|\operatorname{Re}W(f,f)-\|R_n f\|^2\right|\ge 2m.
```

The witness is fixed across the entire family. There is no simplicity
assumption and no synthetic-zero substitution. This uses the repository's
proved `exists_smooth_negative_weil_of_off_line` and actual Weil converse.
It is an implication under the hypothetical existence of an off-line zero,
not a claim that such a zero exists.

## Analytic improvement of the Schatten threshold (not yet Lean-formalized)

The PDF gives trace class for the damped prime sector only for sigma>3/2.
A support-projection argument improves the sufficient threshold to sigma>1.
Here is the full argument, retained for formalization.

Let phi be compactly supported in [-r,r], let m run over prime powers, and set

```math
J_\sigma e_m=\sqrt{\Lambda(m)}m^{-\sigma}\phi(\,\cdot-\log m).
```

For sigma>1/2 this is Hilbert--Schmidt because
sum_m Lambda(m)m^(-2 sigma)<infinity. Its range is supported in
[log 2-r,infinity). For a=log n let P_n project onto coordinates
m>=2n exp(-2r). Support separation gives exactly

```math
J_\sigma^*\tau_aJ_\sigma=J_\sigma^*\tau_aJ_\sigma P_n.
```

Thus, by the Hilbert--Schmidt product inequality,

```math
\|J_\sigma^*\tau_{\log n}J_\sigma\|_1
\le \|J_\sigma\|_2\|J_\sigma P_n\|_2
\le C_{\phi,\sigma}\,
n^{1/2-\sigma}\sqrt{1+\log n}.
```

For the last step, use Lambda(m)<=log m and the elementary tail estimate
sum_{m>=Y} log(m)m^(-2 sigma)
=O_sigma(Y^(1-2 sigma)(1+log Y)); finitely many small n are absorbed
into the constant. Consequently the two-sided prime series converges
absolutely in trace norm for sigma>1, since

```math
\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}
\|J_\sigma^*\tau_{\log n}J_\sigma\|_1
\le C\sum_{n\ge2}\Lambda(n)n^{-\sigma}\sqrt{1+\log n}<\infty.
```

No PNT is needed for this sufficient bound. The trace-norm limit agrees
with the finite-core prime form by the already established local finiteness.
Together with the PDF's archimedean estimate and the two polar vectors,
this gives trace class for the *separated completed damped form* when
sigma>1, without establishing its positivity.

A limitation is also explicit. For a real nonnegative nonzero bump phi,
its correlation C is nonnegative and

```math
\kappa_{\rm prime}(d)\sim
-e^{d/2}\int e^{u/2}C(u)\,du\quad(d\longrightarrow+\infty)
```

by PNT and partial summation on the fixed support window. The coefficient
is strictly positive. A fixed column of the damped prime matrix then has
squared entries comparable to Lambda(m)m^(1-2 sigma). Their sum diverges
for sigma<=1. In this case the raw prime matrix has no bounded extension
on the coordinate l2 space at or below 1. This is an informal analytic
obstruction, not a new Lean theorem. It does not cover polar-free signed
bumps, for which the leading coefficient can vanish.

The revised F2 objective should therefore distinguish the raw separated
prime sector from the completed or polar-cancelled sector. Pushing a raw
nonnegative-bump prime operator to sigma>1/2 is impossible in this setting.

## Research agenda after this checkpoint

| Track | Established here | Remaining obligation |
|---|---|---|
| A: domains | Exact finite identities avoid global operator-domain claims. | Formalize the closure of J_phi and the fixed-support closed-form domain. |
| B: kernels | Actual prime kernel is summable and exactly stabilized on each fixed finite window. | Prove the complete translated kernel identity and the synthesis-density bridge needed for all admissible tests. |
| C: auxiliary sector | Exact minimization and positivity equivalence, including singular D with a range solution. | Construct a genuinely nonnegative block from arithmetic data; reduced positivity cannot be assumed. |
| D: falsification | An actual off-line zero forces one fixed test with a persistent defect >=2m for every candidate family. | Build interval-certified prime-side numerical matrices with all pole and gamma terms and rigorous tails. |
| E: limits | Pointwise scalar convergence suffices to transfer approximate squares to RH. | Produce A_n,R_n,E_n on the full supported test class, with both stated pointwise limits. |
| F2: Schatten | Analytic support-projection proof improves trace class to sigma>1; not formalized. | Formalize the tail projection, the HS product estimate and trace-norm series; investigate completed-sector cancellation below 1. |
| F4: compensation | The finite prime symbol requires exactly 2 C_N of scalar compensation. | Control the actual gamma/polar compensation on the same tests without discarding signed terms. |
| F5: Galerkin | Explicit exact stabilization at N>exp(D+2r). | Uniform estimates as window diameter/support/dimension grow together. |

Priority order: (1) formalize the sigma>1 trace-norm argument;
(2) implement the actual completed damped kernel and polar cancellation;
(3) obtain an estimate for the retained signed remainder on every test;
(4) apply `riemannHypothesis_of_cutoff_gram_limit` only after its providers
are proved. The full positive-factorization construction remains open.

## Literature and computation checks

- Connes--Consani, [Weil positivity and trace formula, the archimedean
  place](https://arxiv.org/abs/2006.13771): operator compression and the
  archimedean case provide background, not a proof of full Weil positivity.
- Suzuki, [On the Hilbert space derived from the Weil
  distribution](https://arxiv.org/abs/2301.00421): the relevant global Hilbert
  space is constructed under RH.
- Suzuki, [Weil's quadratic form via the screw
  function](https://arxiv.org/html/2606.09096v3), September 2026 revision:
  unconditional localized operator results coexist with a conjectural
  global spectral-limit target.
- Suzuki, [Spectral convergence associated with Weil's quadratic
  form](https://arxiv.org/abs/2610.32704), October 23, 2026:
  its spectral convergence theorem assumes RH. It cannot be imported as
  an unconditional provider for the present missing positivity step.

Wolfram independently returned zero for the cosine-counterterm,
scalar Schur-completion, and polar-square algebraic residuals. It also
returned C_N/(2 sqrt N) approximately 0.8448101, 0.9567116, and 0.9873303
at inclusive cutoffs 100, 1000, 10000, consistent with the PDF's numerical
check. These numerical values are exploratory evidence only, not inputs
to any Lean proof. The log-power tail integral was symbolically checked.
