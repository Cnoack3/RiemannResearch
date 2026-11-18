# Displacement, Schur operators, and CRT regularity — 4 November 2026

## Result and status

The existing theorem `riemannHypothesis_of_displacement_prime_products`
already proves the conditional implication from legal prime products to
Mathlib's `RiemannHypothesis`. This continuation constructs the actual
Neumann inverse and Schur operator, formalizes several sufficient regularity
conditions, and checks a finite obstruction to an operator-algebra-only proof.
It does **not** prove the prime-product premise unconditionally.

The [CRT carry Schur and zeta trace continuation](THEOREM_CATALOG_CRT_CARRY_SCHUR_TRACE_20261117.md) records the physical prime blocks, sharpened source reductions and determinant obstruction.

All concrete Hilbert operators below are real. The finite matrix-algebra
generation theorem holds over every characteristic-zero field, including C.
No full complex classification of the infinite operator algebra is claimed.

## Setting

For n>=1, Q(n)=1/(zeta(2)n^2), P(n)=1/(n(n+1)), and
g_m(n)=(n mod m)/m. Let V be the Q-closed real linear span of the
squarefree g_m, m>=2, and let Pi be its Q-orthogonal projection.
Set r=1-Pi(1), d=f_Q-f_P, Bf(n)=f(n)/(n+1), and N=I-Pi.
The physical sequence is represented in Lean by `qSequence`; its value at
the artificial site zero is zero and is not an additional physical datum.

The metric change is
`<f,g>_P = zeta(2) (<f,g>_Q - <f,Bg>_Q)`.
The inherited normal equation is `d=Pi Br+Pi Bd`.

## 1. What d is: an actual bounded inverse and a unique variational correction

Module: `RH/QSquarefreeSchurOperator.lean`.

Define A=Pi B Pi, R=sum_{j>=0} A^j, and L=R Pi B.
The checked operator norm estimate ||A||<=1/2 proves convergence in operator
norm. Both identities R(I-A)=I and (I-A)R=I are formalized. The actual displacement is

\[
d=R\,\Pi Br=Lr.
\]

The response Lx belongs to V and satisfies Pi B(x+Lx)=Lx.
Thus this is a constructed solution of the normal equation, not an assumed
inverse or an extra RH hypothesis.

Define the actual Schur operator
\[
K=NB(N+LN)=NBN+NBR\Pi BN.
\]
On V-perp this is the usual D+C^* R C expression, where C=Pi BN
and D=NBN; I-K is the Schur complement of I-B.
The formal module uses the displayed bounded compositions directly.

Checked declarations include:
- `compressedB_powers_summable`, `inverseCompression_mul`,
  `mul_inverseCompression`, `displacement_eq_inverseCompression`;
- `response_mem`, `response_normal`, `response_residual`;
- `schurOperator_residual`: Kr equals the existing witness B(r+d)-d;
- `schur_energy_exact`, `schur_energy_lower`, `schur_faithful`;
- `schur_variational_identity`, `schur_variational_gap`,
  `response_unique_maximizer`.

For x in V-perp and z=Lx the complete identity is
\[
\langle x,Kx\rangle
=\langle x,Bx\rangle+\|z\|^2-\langle z,Bz\rangle.
\]
The legal four-site certificate improves its lower bound to
\[
\langle x,Kx\rangle
\ge \langle x,Bx\rangle+\frac{1017}{2000}\|z\|^2.
\]
The form is faithful on V-perp: zero quadratic form implies x=0.

For every y in V, with Phi_x(y)=<x+y,B(x+y)>-||y||^2,
\[
\Phi_x(y)=\langle x,Kx\rangle-
 \left(\|y-z\|^2-\langle y-z,B(y-z)\rangle\right).
\]
The complete remainder is at least (1017/2000)||y-z||^2.
Consequently z is the unique maximizer. In particular **d is this unique
variational response for x=r**. No remainder has been discarded.

The checked bilinear identity and `schur_symmetric_on_normal` establish
symmetry on V-perp. In addition, `inverseCompression_mem_closed_algebra`
and `schurOperator_mem_closed_algebra` place R and K in **every closed
unital real operator subalgebra containing Pi and B**. These are actual
closure-of-series arguments. This connects the construction to the generated
operator algebra without assuming physical boundedness or a complex
classification theorem.

Source for the block-elimination/shorted-operator framework:
W. N. Anderson and G. E. Trapp, *Shorted Operators. II* (1975),
https://doi.org/10.1137/0128007.
The concrete squarefree application is a derivation using repository theorems;
the source is not claimed to prove this RH premise.

## 2. Several formal sufficient conditions

Module: `RH/QSquarefreeCRTRegularity.lean`, together with the Schur module.

| Route | Exact remaining condition | Checked conclusion |
|---|---|---|
| Compact CRT extension | The physical d is the restriction of a continuous real function on X=product_p Z/pZ | r=0, every d g_p is legal, RH |
| Schur witness regularity | A common C bounds all physical values of Kr | r=0 and every d g_p is legal |
| CRT extension of the witness | Kr extends continuously to the same compact X | every d g_p is legal |
| Centered resolvent | All centered resolvent approximants are bounded by one common physical constant | every d g_p is legal |
| Cofinal finite projections | Along J_j -> infinity, finite Q/P displacements have one common physical bound on 0<=n<=H_j, where H_j -> infinity | every d g_p is legal and RH |

Each condition in the middle column is **Open** for the actual arithmetic
objects. None is supplied by Hilbert norm convergence or by the C-star
algebra structure.

The CRT space is constructed as the product of actual finite prime residue
rings. Its compactness is checked using Mathlib's product compactness.
The physical embedding is n -> (n mod p)_p. The theorem
`residual_zero_iff_crt_extension` proves the exact equivalence
r=0 iff d has such a continuous extension. This is a reformulation of the
missing regularity, not a proof of its existence.

The centered resolvent is inherited from
`QSquarefreeDisplacementResolvent`:
s_0=0, s_{j+1}=(4/3)b+F(s_j), with
F(x)=(4/3)Pi(Bx-x/4), b=Pi Br, and ||F x||<=||x||/3.
Its exact remainder and bound ||d-s_j||<=3^{-j}||d|| were already proved.
The new `centered_resolvent_tendsto` assembles the full norm limit, and
`prime_products_of_bounded_centered_resolvent` isolates the uniform
physical bound still needed to conclude legality.

The cofinal finite-head theorem permits *independent* cofinal stage and
head sequences J,H. It weakens the inherited requirement to control every
stage N through the whole head n<=N.
The inherited `finiteDisplacement_tendsto` supplies convergence.
The new `riemannHypothesis_of_cofinal_finite_heads` keeps the common
constant as an explicit hypothesis.

Published background for the compact CRT route:
T. Tao, *An Epsilon of Room, I* (AMS, 2010), Theorem 1.10.18
and Exercise 1.10.28:
https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf.
Finite-coordinate continuous functions uniformly approximate continuous
functions on a compact product. This does not supply a continuous extension
of an arbitrary L2(Q) function, or turn the legal linear span into an algebra.
Only compactness and continuous-function boundedness are needed for the
formal extension criterion here.

The underlying RH closure criterion is from B. Bagchi (2006),
*On Nyman, Beurling and Baez-Duarte's Hilbert space reformulation of the
Riemann hypothesis*, including Remark 4 on squarefree indices:
https://arxiv.org/abs/math/0607733.
Its repository formalization is inherited, not newly re-proved in this work.

## 3. Why irreducibility alone does not finish the argument

Module: `Analysis/SchurDisplacementCountermodel.lean`.

Take
\[
\Pi=\begin{pmatrix}1&0\\0&0\end{pmatrix},\qquad
B=\begin{pmatrix}1/4&1/8\\1/8&1/4\end{pmatrix}.
\]
The model has a positive strict contraction B, with eigenvalues 1/8 and 3/8.
Lean checks exact square identities for its quadratic form and contraction
gap. It also proves:
- `matrix_decomposition`: every 2x2 matrix is an explicit linear combination
  of Pi, I-Pi, Pi B(I-Pi), and (I-Pi)B Pi;
- `algebra_eq_top_of_contains`: the generators give the full matrix algebra;
- `joint_commutant_scalar`: their common commutant consists of scalars.

For target (1,1) and legal space the first axis, the ordinary best coefficient
is 1 and the (I-B)-metric best coefficient is 5/6:
\[
E_{I-B}(t)=35/48+(3/4)(t-5/6)^2.
\]
Thus d=(1/6,0) is nonzero and still satisfies the displacement normal equation.
The Schur completion is
\[
\langle(y,x),B(y,x)\rangle-y^2
=(13/48)x^2-(3/4)(y-x/6)^2.
\]
Wolfram confirmed these exact rational computations; Lean provides the
formal proof. This example does not have the squarefree arithmetic
annihilator identities and is not a counterexample to any arithmetic RH
criterion. It blocks only a proposed deduction from the general operator
structure alone.

Published operator-algebra background:
M. Rieffel, *C-star Algebras* (Spring 2008), notes by T. Johnson-Freyd,
sections 15.1-15.2, https://categorified.net/CstarAlgebras.pdf.
An irreducible C-star algebra containing a nonzero compact operator contains
all compact operators. That structural theorem does not establish
prime-product membership of this particular arithmetic vector.

## Research obligations

1. **Open, most concrete:** bound the matched finite Q/P displacements on a
   cofinal family of slowly growing heads, with a constant independent of
   stage and site. Exact Gram systems plus certified tails may supply
   candidate inequalities; finite numerical stability alone is insufficient.
2. **Open:** prove a physical endpoint estimate for the particular response
   R Pi Br, or for the witness Kr. General operator norm estimates have
   already been supplied and do not provide this estimate.
3. **Open:** construct continuous CRT extensions through a uniform finite-
   cylinder approximation or another explicit regularity argument. L2
   cylinder density alone cannot supply the extension.
4. **Open:** derive vanishing of the prime-product leakage using additional
   arithmetic relations. Global preservation of V by all prime multipliers
   is unavailable; the existing g_2 g_3 obstruction rules it out.
5. The full infinite-dimensional complex C-star classification and
   compactness of the newly bundled K are not formalized in these additions.

## Verification evidence

Successful isolated Lean jobs:
- Schur inverse and energy:
  `job_SEWox3XCApxW4wm1VoVeWJQwIzSSfzZX` — 8.112 reported seconds.
- Compact CRT and bounded resolvent criteria:
  `job_YXwrmjG6qEAwr1i6LwKHrZMLjM2Gycnj` — 15.149 reported seconds.
- Improved variational remainder and cofinal finite heads:
  `job_0zcxf5gX-jKOHRSQ4AN3N2UqWLZTVBdP` — 14.022 reported seconds.
- Full-algebra countermodel:
  `job_1_ZwnOOhNO9hDTl938a4w4tkuJEC-K5O` — 4.105 reported seconds.

- Closed-algebra membership and Schur symmetry:
  `job_ZOxhyVeFKnhHmp-pZ1lxk8UaKZMfIWBT` — 6.865 reported seconds.

The successful main declarations' axiom reports contain only
propext, Classical.choice, and Quot.sound.
This is independent of the explicit arithmetic hypotheses in their types.
Development errors were repaired before retaining a result as proved.
No verification submission timed out. These durations are server job
durations, not isolated kernel timing. Workspace-opening duration was not
separately instrumented; status polls respected the 30-second retry interval.
Publication is through the final checkpoint, whose terminal result records
validation of the exact project source and its publication commit.
