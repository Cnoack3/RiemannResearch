# Squarefree cumulants and legal lattice packets

Date: October 16, 2026. Source: the user's infinite CRT continuation and
convolution logarithm and exponential proposal.

## Established finite statements

`NumberTheory/SquarefreeCumulantPair.lean` treats the exact two-prime
nilpotent algebra. A triple `(a,b,c)` represents
`1+a*X+b*Y+c*X*Y`, with `X^2=Y^2=0`. Its normalized convolution is

    (a,b,c) * (u,v,w) = (a+u,b+v,c+w+a*v+b*u).

The module proves inverse logarithm and exponential coordinate maps,
logarithmic additivity, exponential multiplicativity, associativity and
commutativity of the normalized product. The mixed exponential coefficient
is `a*b+k`. Reciprocal slope is exactly

    1+a/p+b/q+(a*b+k)/(p*q)
      = (1+a/p)*(1+b/q)+k/(p*q).

It vanishes iff `k=-(p+a)*(q+b)`. The explicit singleton slope defect
shows why reciprocal slope cannot be treated as a character on the entire
nilpotent algebra.

Source for standard squarefree cumulant terminology and the coefficient
formula: T. Sinclair, *Finite free convolution via reproducing kernels and
squarefree algebras*, arXiv:2606.10870v2, Section 4. No RH estimate is imported
from that paper.

`RH/QSquarefreeLatticePackets.lean` uses actual `QHilbert` vectors. It proves:

- finite divisor-stage monotonicity and inclusion in the squarefree span;
- floor-dilation transport from period L to m*L, with explicit squarefree
  and coprimality hypotheses when squarefree legality is asserted;
- legal compensated directions `g_d-(p/d)*g_p`, their exact physical
  values, and their vanishing before both conductors wrap;
- synthesis of every finite reciprocal-zero coefficient combination by
  those compensated directions;
- the literal two-prime packet

      F+a*D_p(F)+b*D_q(F)+(a*b+k)*D_(p*q)(F),

  its exact factorization, finite divisor-stage membership, squarefree
  legality, and preservation of every physical site below p and q;
- its complete signed Q error, including all six diagonal and mixed
  quadratic contributions and every source correlation;
- exact completion of the square in the composite cumulant k.

The last identity, writing `w=D_(p*q)(F)` and
`r=t-twoPrimePacket(F,p,q,a,b,0)`, is

    error(k) = ||r||^2 - <r,w>^2/||w||^2
                 + ||w||^2*(k-<r,w>/||w||^2)^2,

under the explicit condition `w != 0`. It quantifies exactly the extra
full-Q fitting freedom supplied by the composite cumulant.

## Relation to the full exact-head lattice

On paper, the following exhaustive affine description connects these
packets with the existing complete constrained minimum. Fix H>=1, a
squarefree period L containing every prime <=H, and an anchor divisor
r|L with r>H. Let

    S_H=sum_(d<=H) mu(d)/d,
    B=-sum_(2<=d<=H) mu(d)*g_d + r*S_H*g_r.

Every legal function with period L and value one through H is exactly

    B + span{g_d-(r/d)*g_r : H<d|L, d != r}.

The proof uses the physical difference and divisor Mobius inversion to
fix the low coefficients, followed by the reciprocal-zero synthesis
identity formalized in the new module. Full necessity and the entire
affine characterization are not newly formalized here.

At a finite stage, the full exact-head error is the Gram quadratic

    ||1-B||^2 - 2*z^T*h + z^T*K*z,

and its minimum is `||1-B||^2-h^T*K^(-1)*h`. Existing
`QSquarefreeConstrainedMinimum.lean` supplies the equivalent complete-Q
scalar-constrained formulation and its full nonnegative remainder.

## Open arithmetic provider

Open: a cofinal uniformly bounded complete minimum, or the weaker
subpolynomial complete exact-head error estimate in the user's supplied
continuation. A finite strict packet improvement need not accumulate to
the required bound. The new declarations do not assume or prove either
provider, and do not assert RH.

The all-order finite nilpotent algebra, its infinite coefficient
completion, and the sharper direct floor-norm constant remain paper
arguments in the accompanying research theory. The Lean modules verify
the two-prime algebra and the concrete physical packet calculus.

Infinite CRT uses the atomic Q pushforward, not Haar measure. Formal
coefficient convergence does not imply bounded physical syntheses.
Unrestricted substitution X_p -> D_p is not an algebra homomorphism:
X_p^2=0 while D_p^2=D_(p^2) is nonzero. The valid physical convolution
rule requires disjoint prime supports between the multiplied blocks.
