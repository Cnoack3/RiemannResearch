# Infinite CRT continuity of the displacement — 4 November 2026

## Status

**The requested unconditional continuous extension of the actual displacement
has not been proved.** The new files formalize the infinite-CRT extension
mechanism, its exact missing hypothesis, and an obstruction to obtaining that
hypothesis from the shifted reciprocal operator.

This is an RH-relevant investigation. The existing theorem
`QSquarefreeCRTRegularity.riemannHypothesis_of_crt_extension` already proves
that the desired extension would imply Mathlib's RiemannHypothesis.
No new arithmetic assumption is silently inserted.

## The actual CRT space and universal extension property

Let X = product over primes p of Z/pZ with its product topology, and
iota(n) = (n mod p)_p. This is the squarefree congruence completion.
It is not the full profinite completion product_p Z_p.

`NumberTheory/PrimeResidueTopology.lean` proves:

- `finite_crt_large`: every finite residue prescription has a positive integer
  representative beyond any given bound.
- `exists_cofinal_crt_sequence`: every x in X is the limit of iota(a_j)
  for a sequence a_j > j tending to infinity ordinarily.
- `dense_positive_integers`: the positive integer image is dense.
- `continuous_extension_unique`: agreement on positive integers determines
  a real continuous map on X uniquely.
- `positiveCongruenceUniformity`: the uniformity on positive integers induced
  from the product of the discrete uniformities on Z/pZ.
- `exists_unique_extension_of_uniformContinuous` and
  `exists_extension_iff_uniformContinuous`: a map from these positive integers
  into any complete Hausdorff uniform space extends uniquely and continuously
  to X exactly when it is uniformly continuous for this congruence uniformity.

The source topology is explicitly the congruence topology, not the default
discrete topology on the natural numbers. The extension proof uses Mathlib's
uniformly continuous extension along a dense uniform inducing map.

This is the universal extension property needed for this question. The module
does not additionally package a categorical `IsLimit` object for an inverse
system of quotient rings.

## Exact arithmetic obligation for d

Set d = f_Q - f_P, r = 1 - Pi 1, where Pi is the Q-orthogonal projection to V.
The new application file is `RH/QSquarefreeCRTContinuity.lean`.

The theorem `crt_extension_iff_congruence_uniform_continuity` proves that d
extends continuously exactly when the following holds:

For every epsilon > 0, there is a finite set S of primes such that, for all
positive n,m agreeing modulo every p in S,
|d(n) - d(m)| < epsilon.

`crt_extension_iff_uniformContinuous` identifies this with the precise
uniform-space premise of the general extension theorem.
**Open:** prove this premise for the actual displacement.

There is a strictly weaker-looking sufficient estimate:
for one fixed positive modulus M, find C in R such that
|d(n) - d(m)| <= C whenever n,m >= 1 and n mod M = m mod M.

`crt_extension_iff_modular_oscillation` proves equivalence between this condition
and existence of the extension, for every fixed M > 0. Its proof uses the
general lemma `NumberTheory.ModularOscillation.bounded_of_modular_oscillation`:
the finitely many representatives M,...,2M-1 give the explicit global bound

|a(n)| <= max(C + sum_(r<M) |a(r+M)|, 0), n >= 1.

For d, the repository's bounded-displacement rigidity theorem then gives r=0.
**Open:** provide this bound for even one fixed modulus. The theorem does not
supply the bound.

`displacement_continuous_extension_eq_zero` proves that any extension of d
would necessarily be the zero function on the entire product.

The contrapositive `unbounded_modular_oscillation_of_residual_ne_zero` is exact:
if r != 0, then for every M > 0 and every C there are positive n,m with the
same residue modulo M and |d(n)-d(m)| > C.

## Why the Schur/resolvent construction does not automatically preserve continuity

For each fixed n, the factorial sequence n+k! tends to infinity ordinarily,
but its CRT image tends to iota(n). This is
`factorial_shift_cofinal` and `factorial_shift_tendsto`.

Thus if a(n) has an ordinary limit L and is the trace of a continuous map F
on X, then F(iota(n))=L for every n:
`continuous_trace_limit_constant`.

The existing theorem `ZetaTwoHilbert.qSequence_div_nat_tendsto_zero` gives
f(n)/n -> 0 for every f in QHilbert. The new theorem
`B_physical_tendsto_zero` therefore proves Bf(n)=f(n)/(n+1) -> 0.

Combining these facts yields the unconditional checked theorem

**Bf has a continuous CRT extension if and only if f=0.**

Its Lean name is `continuous_crt_extension_B_iff`. In particular B1(n)=1/(n+1)
has no continuous extension. Consequently B cannot be assumed to preserve
CRT-continuous functions, even though it is a positive bounded Hilbert operator.

This does not refute the desired extension of d. In the exact identity
d = Pi B(r+d), the projection Pi is applied after B; we have not proved that
Pi preserves physical decay, boundedness, or CRT continuity.

## Finite approximants

`finite_displacement_unbounded_eventually` proves that if r != 0, then for
every real C, eventually every finite displacement approximant d_j has some
physical value satisfying |d_j(n)| > C.

Proof: bounded-displacement rigidity supplies a fixed site with |d(n)| > C,
and Hilbert convergence implies convergence at that site.

Thus Hilbert convergence of finite CRT approximants does not itself provide
the supremum or congruence estimates needed for extension. The already checked
centered-resolvent error estimate remains a Hilbert-norm estimate.

## Sources and provenance

- Mathlib, finite Chinese remainder theorem:
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/ChineseRemainder.html.
- Mathlib, uniform extension along dense uniform inducing maps:
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/UniformSpace/UniformEmbedding.html.
- Bourbaki, *General Topology*, and I. M. James, *Topologies and Uniformities*,
  cited by Mathlib's completion construction:
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/UniformSpace/Completion.html.
  These support the extension mechanism and its uniform-continuity hypothesis.
- T. Tao, *An Epsilon of Room I* (AMS, 2010), Exercise 1.10.28; author's
  corresponding Notes 12, Exercise 47:
  https://terrytao.wordpress.com/2009/03/02/245b-notes-12-continuous-functions-on-locally-compact-hausdorff-spaces/.
  This supports uniform approximation of an already continuous function on a
  compact product by finite-coordinate functions; it does not establish
  continuity of an arbitrary Hilbert-space limit.
- B. Bagchi (2006), *On Nyman, Beurling and Baez-Duarte's Hilbert space
  reformulation of the Riemann hypothesis*:
  https://arxiv.org/abs/math/0607733.
  The RH bridge is inherited from the repository, not newly assumed here.

The elementary finite-representative and factorial-recurrence arguments are
standard consequences assembled for this investigation; no novelty claim is made.

## Verification record

The coherent topology, B-obstruction, and modular-oscillation candidate passed
job `job_c_Pwuw0ePn-P-dgclUgCXfXT0GYjt_ww`, exit 0, server-reported 6.347 seconds.
The real-valued universal extension candidate passed
`job_Zpbqp70DCVXodLA8m6IOh0OieU4LaoAD`, exit 0, 3.430 seconds.
The saved three-module application and eight axiom reports passed
`job_AdkqZdLE5Lrifz3R5956tg5cdJhXHCDk`, exit 0, 15.069 seconds.
The principal reports contain only propext, Classical.choice, and Quot.sound.

The general-target extension theorem passed
`job_ngo8ZwIXADOPO6irMKH_HcaQ3Vm4xOl0`, exit 0, 3.443 seconds, with only the
same three standard foundations. The publication checkpoint is reported with
the delivered commit. A final checkpoint validates the aggregate
project and all changed modules before publication; an isolated snippet is
not presented as that project validation.

All verification jobs were serialized, and polling observed the server's
30-second minimum. Workspace-opening duration was not instrumented separately.
Reported verification durations are server measurements, not total request,
research, or polling time. No provider of the Open displacement-continuity
premise was obtained.
