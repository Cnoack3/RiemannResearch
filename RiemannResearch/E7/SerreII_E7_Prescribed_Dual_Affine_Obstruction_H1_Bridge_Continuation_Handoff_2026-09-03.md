# Full Serre II / E7 prescribed-dual affine obstruction and H1 bridge

Date: 2026-09-03

Base published commit before this continuation:
`a9263d8070276dc07b239bfd5fb81812023ec203`.

## Status

Full Serre II for the hard inner-`E7`, index-eight row is **not yet
proved**.  This continuation closes the previously unresolved
prescribed-dual incidence problem, identifies the exact remaining affine
obstruction, proves in Lean that a successful crossed quaternion cannot
have a conjugation-stable splitting layer, and constructs an exact bridge
from packet effectivity to the existing `H¹)-neutrality endpoint.

It also supplies two no-go results against an overstrong completion:

1. a completely verified finite `F₂)-model in Lean;
2. a genuine field-theoretic construction over a 2-special field of
   `cd₂ = 2).

Both show that a *fixed* synchronized common-kernel witness need not have a
quaternion crossed class.  Neither is a counterexample to Serre II:
another point of the affine fibre or another LLT layer may still work.

## 1. Prescribed dual incidence is available

Write the hard Brauer packet as quaternion classes `q₁,q₂,q₃), with

    ind(q₁ + q₂ + q₃) = 8.

Choose a quadratic field `M/F` splitting `q₁`.  The
Lam--Leep--Tignol norm-form argument can be oriented so that it constructs
a nonnormal quartic field `L/F` splitting **both** prescribed labels
`q₂` and `q₃`.  Let `U/M` be the quadratic member dual to `L` in
the associated `D₈)-hull.  Tignol's relative Brauer-kernel theorem then
gives

    q₂ ∈ cor(ker(Br₂(M) -> Br₂(U))),
    q₃ ∈ cor(ker(Br₂(M) -> Br₂(U))).

Equivalently, there are `s,t ∈ Br₂(M)`, both split by `U), with

    cor(s) = q₂,    cor(t) = q₃.

References:

- Lam--Leep--Tignol, Theorem 4.2, Proposition 3.3, and the equivalent
  constructions in Theorems 5.10/5.12:
  <https://www.numdam.org/item/PMIHES_1993__77__63_0.pdf>
- Tignol, Corollary 3.5 and Example 5.3:
  <https://arxiv.org/html/1704.04072v1#S5.SS3>

## 2. Exact Lean reduction

The new module
`RiemannResearch/E7/E7IndexEightPrescribedDualCommonSplitter.lean`
introduces

- `HasPrescribedDualCommonSplitter`;
- `CanonicalCrossedFibre`;
- `exists_kernelPreimages_of_prescribedDualCommonSplitter`;
- `canonicalCrossedFibre_nonempty_of_prescribedDualCommonSplitter`;
- `hasCrossedQuaternionKernelRectangle_iff_exists_quaternionPoint`;
- `prescribedDualCommonSplitter_reduces_crossedRectangle_to_quaternionPoint`;
- `totalIndexEight_crossedQuaternion_has_no_stableSplittingLayer`.

For

    alpha = q₂ + q₃,
    beta  = q₁ + q₂,

the crossed-rectangle problem is now exactly

    ∃ r,
      r|_U = 0
      ∧ cor(r) = alpha
      ∧ IsQuaternionClass (r + res(beta)).

Thus LLT--Tignol makes the affine fibre nonempty; the remaining problem is
whether that fibre contains a quaternion point after the canonical
translation.

Lean also proves that if such a translated class is quaternion, then any
quadratic layer splitting it is not stable under the conjugation of
`M/F`.  In field language, a successful common slot cannot descend from
`F`; it must be genuinely `M`-defined.

The principal declarations were checked with `lean_verify`.  They had
no verification warnings and only standard foundational dependencies
(`propext`, and where applicable `Quot.sound`).

## 3. Lean finite no-go model

The new module
`RiemannResearch/E7/E7IndexEightPrescribedDualFiniteNoGo.lean`
builds an exact finite model using

    A = F₂³,    B = F₂² × F₂²,

with explicit restriction, corestriction, conjugation, upper-layer
restriction, symbolic index, and quaternion predicates.  It satisfies all
of the abstract exponent-two, restriction/corestriction, index,
conjugation, stable-layer, and dual-detection interfaces used by the
reduction.

Lean proves:

- the dual layer splits both prescribed labels;
- the canonical affine fibre is nonempty;
- its prescribed translated point is not quaternion;
- no crossed quaternion rectangle exists.

Principal declarations:

- `dual_detection`;
- `dual_splits_prescribed_labels`;
- `prescribedDualCommonSplitter_but_no_quaternionPoint`;
- `no_crossed_rectangle`.

All principal declarations passed source-scanned verification with no
warnings; the only dependencies reported were standard foundations
(`propext`, `Classical.choice`, `Quot.sound`).

This proves that no theorem from the current abstract incidence axioms
alone can close the affine step.

## 4. Genuine cd₂ = 2 fixed-witness no-go

This construction is mathematical and has **not** been formalized down to
field theory in Lean.

Let `k` be algebraically closed of characteristic zero and set

    F₀ = k(e,f,g,a,b,h),
    M₀ = F₀(w),  w² = g,  sigma(w) = -w.

Put

    delta = e - f,
    x = a + bw,
    z = sigma(x) = a - bw,
    y = x + delta,

and

    q₁ = (g,h),
    q₂ = (e,xz),
    q₃ = (f,y(z+delta)),
    s  = (e,x),
    t  = (f,y).

Projection formula gives

    cor(s) = q₂,    cor(t) = q₃.

The symbol identity `(u,v) = (u+v,-uv)` gives

    s = (e+x,-ex),    t = (f+y,-fy).

Since `e+x = f+y =: A), the quadratic extension

    U₀ = M₀(sqrt(A))

splits both `s` and `t).  Nevertheless

    c = t + sigma(s) = (f,y) + (e,z)

is a division biquaternion.  An Albert form is

    <f,y,-fy,-e,-z,ez>.

At the `z`-adic valuation its Springer residues are

    <f,y,-fy,-e>    and    <-1,e>.

The second is anisotropic.  At the `y`-adic valuation the first form has
residues

    <f,-e>    and    <1,-f>,

both anisotropic.  Hence the Albert form is anisotropic and
`ind(c)=4`.

Similarly, an Albert form for `(q₂+q₃)_{M₀}` is

    <e,xz,-exz,-f,-y(z+delta),fy(z+delta)>.

Its `z`-residues are

    <e,-f,-y delta,fy delta>    and    x<1,-e>.

The first form then has `y`-residues

    <e,-f>    and    delta<-1,f>.

The same twice-Springer argument proves
`ind((q₂+q₃)_{M₀})=4`.

For the total hard class, pass to
`K=k(e,f,g,a,b)((h))`.  The first summand is unramified and `(g,h)`
is the ramified Witt character.  Nakayama--Witt gives

    ind(q₁+q₂+q₃)
      = 2 * ind((q₂+q₃)_{K(sqrt(g))}
      = 8.

An exact accessible statement of the index formula is given by
Hanke--Neftin--Sonn, citing Jacob--Wadsworth:
<https://msp.org/ant/2014/8-4/ant-v8-n4-p.pdf>.

Apply Elman--Karpenko--Merkurjev, Theorem 38.4, with `n=4`, preserving
the degree-eight division algebra through the tower of 9-dimensional
quadric function fields, 3-fold Pfister function fields, and 2-special
closures:
<https://www.math.ucla.edu/~rse/book/Kniga.pdf>.

The crossed degree-four division algebra over `M` also survives:
EKM Corollary 30.9 handles the 9-dimensional steps, Corollary 30.11 the
nonzero `I³)-form steps, isotropic quadric steps are rational, and odd
algebraic steps preserve the 2-primary index after the quadratic base
change.

At the limit, `F` is 2-special, `I³(F)=0`, and a nonzero
2-primary Brauer class survives, hence `cd₂(F)=2`.  The same inference
is recorded in Becher--Hoffmann, Remark 5.11:
<https://www.math.uni-bielefeld.de/lag/man/227.pdf>.

With `r=s+t`,

    r|_U = 0,
    cor(r) = q₂+q₃,
    r + res(q₁+q₂) = t + sigma(s) = c,

and `ind(c)=4`, so this point is not quaternion.

Moreover `U/F` is nonnormal.  If it were conjugation-stable, it would
split `s,t,sigma(s),sigma(t)`, hence `c`, impossible for a quadratic
extension of `M`.  Also neither `q₂` nor `q₃` splits over `U`;
either splitting would force `c` (or its conjugate) to split.  The dual
quartic does split both labels because both lie in
`cor(ker(res_U))`.

Exact scope:

- this refutes the universal claim that synchronized representatives in a
  fixed prescribed layer automatically have quaternion crossed class;
- it refutes both direct-label alternatives for this fixed upper layer;
- it does **not** rule out another `r` in the same affine fibre;
- it does **not** rule out another LLT layer;
- it is therefore not a counterexample to Serre II.

## 5. Packet effectivity to H1 neutrality

The new module
`RiemannResearch/AlgebraicGeometry/SerreIIE7PacketEffectivityBridge.lean`
defines `E7D6A1PacketNeutralityBridges`.  It packages the two Brauer
packets attached to the two split-index branches and states exactly that
their effectivity implies neutrality.

Lean proves:

- `E7D6A1PacketNeutralityBridges.toNeutralityBridges`;
- `e7D6A1ReductionProvider_of_packetReductions`;
- `exactFamilyE7_of_quasiSplit_and_packetReductions`.

Consequently the existing exact-family `E7` theorem reduces the full
`H¹) problem to:

1. the already-separated quasi-split provider;
2. effectivity of the two actual attached packets in the index-four
   branches.

The intended final sharpening replaces a universal packet-realization
hypothesis by effectivity hypotheses for only those two attached packets.

## 6. What remains

The hard Brauer-theoretic obligation is now irreducibly existential:

    choose an LLT nonnormal layer U/M and
    choose r in {r | r|_U=0, cor(r)=q₂+q₃}
    such that ind(r+res(q₁+q₂)) <= 2.

The finite Lean model and the genuine `cd₂=2` construction rule out
closing this with a universal fixed-witness argument.  A completion must
use an additional `E7)-specific relation or vary the LLT layer/fibre
point.

As of September 2026, current published work still leaves the general
`E7` case outside its unconditional Serre-II conclusions:

- Izquierdo--Lucchini Arteche:
  <https://arxiv.org/html/2308.00903v3>
- Gille--Izquierdo--Lucchini Arteche proves the complete-DVR
  dimension-two case, where period equals index and the index-eight row
  does not occur:
  <https://arxiv.org/html/2501.01403v2>
- Benoist proves the Stein-surface meromorphic case, again with
  period equals index:
  <https://arxiv.org/html/2410.16809v2>

## 7. Verification / recovery note

Before the verifier transport session terminated, all three new Lean
modules had clean full-file diagnostics, all listed principal
declarations passed source-scanned `lean_verify`, and the umbrella
imports and theorem catalog had been updated.  Two full-project build
attempts reached approximately 98.6% before the remote verifier service
restarted.  The edits still require a successful final
affected-module checkpoint/push once the Lean workspace connection is
restored.

