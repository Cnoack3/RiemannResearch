# Displacement regularity and the actual projection — 4 November 2026

## Status

The continuous extension and physical boundedness of the actual displacement
remain **Open**. This continuation proves arithmetic recurrence, an explicit
closed-projection formula, a pointwise-order obstruction, and a CRT blow-up
alternative. It does not prove RH or assert that the displacement is nonzero.

All symbols below use physical coordinates on positive integers. Set
Q(n)=1/(zeta(2)n^2), P(n)=1/(n(n+1)), and let V be the closed real span of
g_s(n)=(n mod s)/s for squarefree s>=2. Equivalent P and Q norms give the same
physical closed span, but different orthogonal projections.

Write Pi for the Q-orthogonal projection to V, f_Q=Pi(1), f_P for the
P-orthogonal projection of 1, r=1-f_Q, d=f_Q-f_P, and r_P=r+d.
The operator B is multiplication by 1/(n+1). The index-zero physical value is
defined to be zero in Lean and has Q weight zero.

## Exact projection and the remaining estimate

Pi is the unique least-squares minimizer:
Pi f is in V and f-Pi f is orthogonal to V in the Q inner product.
It is self-adjoint, idempotent, and a contraction in Q norm. The equations
for d are
```
d = Pi B r_P = Pi B(r+d),
<v,d>_Q = <v,B r_P>_Q  for every v in V.
```
These are global weighted normal equations, not coordinatewise averaging.

Let E_n be the Riesz vector for evaluation f -> f(n), so that
E_n(m)=1_{m=n}/Q(n), for positive n. Define K_n=Pi E_n.
The new module RH/QSquarefreeClosedKernel.lean proves
```
(Pi f)(n) = <f,K_n>_Q
          = sum_(m>=1) Q(m) f(m) K_n(m).
```
The complete infinite sum is retained. Its absolute convergence follows from
the existing weighted Hilbert product summability theorem.

RH/QSquarefreeDisplacementRegularity.lean proves
```
d(n) = sum_(m>=1) Q(m) (r(m)+d(m))/(m+1) K_n(m)
     = <r_P,B K_n>_Q,
|d(n)| <= ||r_P||_Q ||B K_n||_Q.
```
Thus one concrete sufficient target is
```
exists C, forall n, ||B K_n||_Q <= C.
```
This is an **Open** operator estimate, stronger than the cancellation-sensitive
bound on the actual pairings <r_P,B K_n>. The theorem
residual_zero_of_smoothed_kernel_bound proves this premise implies r=0.
It does not supply the premise. Proving merely an n-dependent bound does not
close the argument.

A second precise sufficient property is that Pi sends every physical c0
vector in QHilbert to a bounded physical sequence. The theorem
residual_zero_of_projection_preserves_c0_bound proves this would force r=0.
Only its application to the particular input B r_P is necessary.

Conversely, projected_decay_unbounded_of_residual_ne_zero proves that if r!=0,
then the particular vector B r_P tends to zero ordinarily while Pi(B r_P)
is unbounded. This identifies exactly where decay would be lost.

## Arithmetic recurrence outside the Hilbert norm

For Delta f(n)=f(n)-f(n-1), the new theorem
displacement_difference_radical proves, for every n>=2,
```
Delta d(n) = Delta d(rad(n)).
```
This follows from the squarefree legality constraint and d in V, using the
existing bridge from the optimizer closure to the literal closed squarefree
span. Equivalently,
```
d(n) = d(n-1) + d(rad(n)) - d(rad(n)-1).
```
The strengthened specialization displacement_difference_squarefree_power gives
Delta d(s^k)=Delta d(s) for every squarefree s>=2 and k>=1, including all
prime powers. This is a genuine arithmetic relation, but at squarefree n it
is tautological and it does not bound accumulated increments.

Existing checked results also give:
- d(n)/n -> 0.
- d belongs to V and is the Hilbert limit of finite legal periodic sequences.
- The centered resolvent has error at most 3^(-j)||d||_Q.
- If r!=0, N||tail_N d||_Q^2 -> infinity.

Fixed-site convergence does not give a uniform bound across all n: evaluation
at n has norm 1/sqrt(Q(n))=sqrt(zeta(2))*n. In particular, the Hilbert error
estimate becomes a physical error estimate with a factor growing linearly
in the site n.

## Pi is not a conditional-expectation operator

RH/QSquarefreeProjectionOrder.lean proves unconditionally that Pi is **not
positive in the pointwise order**.

The explicit legal vector v=g_2-g_3 has values
```
n       1      2      3      4
v(n)    1/6   -2/3   1/2   -1/3
|v(n)|  1/6    2/3   1/2    1/3.
```
Every legal vector satisfies f(4)-f(3)-f(2)+f(1)=0, whereas |v| gives -2/3.
Therefore |v| is not in V.

If Pi preserved nonnegative functions, Pi(|v|+v)>=0 and Pi(|v|-v)>=0 would
give Pi|v|>=|v|. Monotonicity of the weighted square norm, together with the
exact orthogonal Pythagorean remainder, would then force Pi|v|=|v|, a
contradiction. This argument is checked in
qAbs_mem_of_positive_projection and projection_not_physically_positive.

This does not contradict Hilbert operator positivity:
<f,Pi f>_Q=||Pi f||_Q^2>=0. Pointwise order preservation is a different property.
In particular Pi cannot be conditional expectation onto a sigma algebra, which
does preserve nonnegative functions. Failure of positivity alone does not prove
failure of boundedness or CRT continuity for d.

The CRT product topology also does not change Q into Haar measure. Its physical
pushforward is countably atomic. V is a closed linear span of legal atoms,
not automatically the algebra of all cylinder functions.

## Categorical CRT

NumberTheory/PrimeResidueTopology.lean now constructs positiveCRTCompletion
as a Mathlib AbstractCompletion of positive integers with their squarefree
congruence uniformity, and positiveCRTCompletionEquiv as the canonical uniform
equivalence
```
Completion(N_positive, squarefree congruence uniformity)
  ≃ᵤ product_(p prime) ZMod p.
```
This uses the already proved dense uniform-inducing embedding. The abstract
completion is exactly the universal object for extending uniformly continuous
maps into complete Hausdorff uniform spaces. Mathlib packages the general
categorical statement as completionFunctor left adjoint to the forgetful
functor, UniformSpaceCat.adj.

In ordinary categorical language, finite CRT also identifies this product with
the inverse limit of Z/MZ over squarefree moduli M. This continuation packages
the completion and its canonical equivalence; it does **not** construct a
separate categorical IsLimit cone for that inverse system.

This space is the squarefree completion, not the full profinite integers
product_p Z_p. The universal property cannot create uniform continuity of d.

## What failure of regularity would imply

For this particular d, existing checked rigidity gives
```
d=0 <=> r=0 <=> physical boundedness of d
          <=> continuous extension of d to the CRT product.
```
The new theorem displacement_crt_blowup_of_ne_zero gives the stronger geometric
consequence:
```
d != 0 implies exists positive integers a_j and x in the CRT product such that
  iota(a_j) -> x,   |d(a_j)| -> infinity.
```
It chooses arbitrarily large values and extracts a convergent CRT subsequence
by compactness and first countability. The limiting x need not be an embedded
integer.

The existing modular theorem additionally says that for every M>=1 and every
real C there are n,m>=1 congruent modulo M with |d(n)-d(m)|>C.
This does not assert that every residue class is unbounded, that every embedded
integer is a discontinuity, or that every factorial-shift sequence causes blow-up.

Not having proved the bound is not evidence of its failure. If actual failure
were proved, it would force d!=0 and r!=0. With Bagchi's published reverse
squarefree criterion this would imply failure of RH. The inspected Lean bridge
formalizes r=0 -> RH; the reverse analytic provider RH -> r=0 is not supplied
by this work. No kernel-checked negation of RH is claimed.

## Sources

- Bhaskar Bagchi (2006), On Nyman, Beurling and Baez-Duarte's Hilbert space
  reformulation of the Riemann hypothesis, Remark 8 (squarefree criterion),
  and discussion after Theorem 1 (equivalent weights):
  https://arxiv.org/abs/math/0607733
- Mathlib projection theorem, used for exact normal equations and remainders:
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/Projection/Submodule.html
- Mathlib AbstractCompletion and canonical comparison:
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/UniformSpace/AbstractCompletion.html
- Mathlib categorical completion adjunction:
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Category/UniformSpace.html
- Mathlib compact sequential extraction:
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Sequences.html
- T. Tao, An Epsilon of Room I (AMS, 2010), Exercise 1.10.28, supports
  finite-coordinate approximation of already continuous compact-product functions:
  https://terrytao.wordpress.com/2009/03/02/245b-notes-12-continuous-functions-on-locally-compact-hausdorff-spaces/

The arithmetic assembly and the explicit absolute-value example were developed
for this investigation. No novelty claim is made. Wolfram independently returned
the four rational values and -2/3; this diagnostic is not substituted for Lean.

## Verification

The combined preliminary candidate passed job
job_SgdhZWklBYC-4b5SFh9ntTQrWxKzCg4A, exit 0, reported 7.436 seconds.
The saved modules and seven principal axiom checks passed
job_6mh9IAPhVmAcQmCX8IYiA_HnUkcFvvOv, exit 0, reported 20.039 seconds.
All seven reports contain only propext, Classical.choice, and Quot.sound.
Substantive hypotheses of conditional reductions remain explicitly Open;
axiom reports do not discharge hypotheses in theorem types.

The final publication checkpoint separately validates the project scope
reported by the server before pushing. The delivered response records that
checkpoint and exact commit. Workspace-opening and user-facing polling delays
were not separately instrumented and are not counted as proof-checking time.
