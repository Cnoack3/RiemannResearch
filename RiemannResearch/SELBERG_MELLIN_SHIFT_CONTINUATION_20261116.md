# Estermann Mellin shifts — finite rectangles, collision, and exact finite assembly

Updated 16 November 2026, America/New_York.

## Latest strengthening

The collision coefficient is now explicitly evaluated as
(gamma-log(lam)-2*log(K))/(K*lam). The damped Gamma factor has proved
arbitrary-order decay on closed strips. The remaining global analytic
provider can be reduced to polynomial growth of the continued Estermann
function. An exact zeta-product separation has an entire finite remainder.

See [the new results and concrete research agenda](SELBERG_MELLIN_GROWTH_COLLISION_20261116.md).
The finite-rectangle results below remain established; the global shift
still depends on an actual growth provider.

## Earlier checkpoint status

The rational-character, gcd, coefficient, Gaussian-ray and actual-moment assembly
at b3a5e9295578c55995db65b197080a70e75d70bd remains established and is reused.
This continuation adds unconditional finite-rectangle results and a checked
**conditional research reduction** for the global shift. It does not claim
that the global analytic growth estimate has been proved.

The old checkpoint job job_D06mfZx0DXMzRNjGG2Kw7qisCONvHs6a was inspected:
succeeded, Bazel/BuildBuddy, full //:RiemannResearch, committed and pushed.
The retained workspace was synchronized before editing and main was still
b3a5e9295578c55995db65b197080a70e75d70bd.

## Exact kernel and normalization

Let
```text
F(s) = Gamma(s) * lam^(-s) * estermann h (s+alpha) (s+beta),
lam = -2*pi*i*w, Im(w) > 0.
```

For a real vertical parameter, the normalized Mellin integral is
(1/(2*pi)) times the integral of F(c+i*t) dt. The factor i in ds=i*dt
has already canceled the i in the contour normalization. All powers
remain principal complex powers.

## Unconditional finite rectangle theorem

For a positive modulus K, a unit h in ZMod K, complex alpha,beta,lam with
Re(alpha)<1, Re(beta)<1, alpha != beta, and lam != 0, choose real a,b,T with

- -1 < a < 0;
- b > 1-Re(alpha) and b > 1-Re(beta);
- T > 0, T > |Im(alpha)|, and T > |Im(beta)|.

Then the positively oriented rectangle with corners a-i*T and b+i*T has
normalized integral exactly
```text
R0 + Ralpha + Rbeta,
R0     = estermann h alpha beta,
Ralpha = Gamma(1-alpha) * lam^(alpha-1)
         * K^(-(1-alpha+beta)) * zeta(1-alpha+beta),
Rbeta  = Gamma(1-beta) * lam^(beta-1)
         * K^(-(1-beta+alpha)) * zeta(1-beta+alpha).
```

The theorem proves meromorphy on the complete rectangle, holomorphy away
from 0, 1-alpha, 1-beta, and at most simple poles at those points. Candidate
poles may be removable; their zero residues are handled by the finite
residue sum. No assumption supplies the rectangle identity or any
convergence or growth estimate.

Declarations in Analysis/ConreyBaluyotEstermannMellinShift.lean:

- analyticAt_estermannMellinKernel_off_poles;
- meromorphicAt_estermannMellinKernel;
- hasSimplePolesOn_estermannMellinKernel;
- estermannMellinResidueSum;
- rectangleIntegral_estermannMellinKernel.

## Global identity: exact remaining hypothesis

The global theorem
estermannDampedSeries_eq_residues_add_mellinIntegral_of_tail_bound
has the same distinct shifts, Im(w)>0, -1<a<0, and
1<b+Re(alpha), 1<b+Re(beta). Its remaining analytic hypothesis is:

```lean
∀ r ∈ Icc a b, ∀ t : ℝ, T₀ ≤ |t| →
  ‖estermannMellinKernel (h : ZMod K) α β
      (-2 * (Real.pi : ℂ) * I * w) ((r : ℂ) + t * I)‖
    ≤ B * (1 + t ^ 2)⁻¹
```

Here B and T₀ may depend on the fixed parameters. The initial task is to
prove that such constants exist, not a stronger uniform statement over
the later mollifier/density parameters.

From this single bound the formal proof derives:

1. Absolute integrability on the new negative vertical line. Holomorphy
   handles its compact middle; the estimate controls both tails.
2. Decay of both remote horizontal integrals.
3. Passage from the finite rectangles to improper integrals.
4. The exact identity
   S(w,alpha,beta,h/K) = R0+Ralpha+Rbeta
   + (1/(2*pi))*integral F(a+i*t) dt.

The initial right-line convergence is discharged by the existing
integrable_estermannMellinKernel_vertical theorem. It is not an assumed
provider in the new theorem.

Generic tools in Analysis/VerticalResidueShift.lean:

- MeasureTheory.integrable_of_continuous_of_cauchy_tail;
- Complex.tendsto_horizontal_integrals_zero_of_cauchy_tail;
- Complex.mellin_vertical_eq_of_rectangle_of_cauchy_tail.

The new-line specialization is
integrable_estermannMellinKernel_negative_of_tail_bound.

**Open:** prove the actual uniform closed-strip tail estimate. The known
initial-line norm bound applies only in the joint absolute-convergence
half-plane and does not discharge this obligation. Bounds for the finite
Hurwitz continuation, combined with the Gamma/damping factor, are the
next concrete analytic target.

## Exact gcd and finite-coefficient bridge

Analysis/ConreyBaluyotRationalTwist.lean now also proves
reducedRationalTwist_isUnit. For positive natural h,k, the reduced
numerator H=h/gcd(h,k) defines a unit modulo K=k/gcd(h,k), and so does -H.
This supplies the unit-class hypothesis for both signed rays.

Analysis/ConreyBaluyotEstermannMellinFinite.lean proves
finite_estermannDampedSeries_eq_residues_add_mellinIntegral_of_tail_bound.
It permits:

- an arbitrary finite index set;
- a different positive modulus and unit residue at each index;
- different upper-half-plane damping parameters;
- arbitrary complex coefficients, without a factorization assumption;
- separate constants B_i,T_i for each summand.

It retains each coefficient in the residue sum and moves the exact finite
weighted sum inside the remaining negative-line integral. Integrability
is proved before that exchange.

This is a **conditional finite assembly**, with the actual strip-bound
hypothesis visible for every supported summand. It is not an unconditional
provider of the global shift.

For the Gaussian application one may index by the positive (h,k) pairs
and both signs. The prior actual-moment theorem and its
-(2*sqrt(pi)/Delta)*mollifiedGaussianPoleCoeff correction are unchanged.
No cancellation or estimate of that correction is claimed.

## Collision at l=1/2

Here alpha=beta=0 and the two shifted poles meet at s=1.
Analysis/ConreyBaluyotEstermannMellinCollision.lean proves

```text
lim_{s -> 1, s != 1} (s-1)^2 F(s) = lam^(-1) * K^(-1),
meromorphicOrderAt F 1 = -2.
```

The coefficient is nonzero because K is positive and lam is nonzero.
This is an actual double pole, not merely an upper bound on its order.

The local Laurent theorem further constructs a function g analytic at one
with g(1)=lam^(-1)*K^(-1), and F(s)=g(s)/(s-1)^2 on a punctured neighborhood.
It proves the exact limit

```text
lim_{s -> 1, s != 1}
  (s-1) * (F(s) - (lam^(-1)*K^(-1))/(s-1)^2) = g'(1).
```

Thus the simple Laurent coefficient is characterized after subtracting
the double term. The current rectangle API is for at most simple poles;
its residue of the original double-pole function must not be treated as
the general Laurent residue.

Declarations:

- estermannMellinKernel_diagonal_doublePole_limit;
- meromorphicOrderAt_estermannMellinKernel_diagonal;
- exists_estermannMellinKernel_diagonal_laurent.

**Now closed:** the explicit value is
g'(1)=(gamma-log(lam)-2*log(K))/(K*lam), by
estermannMellinKernel_diagonal_residue_explicit and uniqueness of limits.
The explicit numerator's derivative is proved in
hasDerivAt_estermannDiagonalNumerator_one.

**Open:** prove the double-pole rectangle identity (for example by
subtracting the double term and showing its boundary integral is zero),
and supply the actual tail bound for the collision's global shift.

## Verification evidence and next actions

The coherent rectangle/global-reduction snippet passed Bazel/BuildBuddy
as job_-dAcFPolsTf5POG4JWB7XEVJEvBwYBqO.
The extended finite assembly and Laurent-numerator snippet passed as
job_bDgsREptIJJMk3utiTGh_SVDMhOggwbu.
The persisted modules and their transitive imports passed the focused check
job_h9mUOPIFrFlo4u71VKaCu1CSxa6wfmax. Eight guarded axiom checks then passed
as job_XxGPcBtiyKRpSuFNCaMy4prFggGVdyZ9; each has exactly propext,
Classical.choice and Quot.sound. The guard compares the compiler's actual
axiom output, rather than relying on a prose assertion.

Axiom audit log:
https://app.buildbuddy.io/invocation/f980d509-9c36-4c66-8162-994d5860af7c

Those are focused checks, not a substitute for the final full-project
checkpoint. The final checkpoint record is the publication authority.

No placeholders, project-local axioms, or unsafe declarations are used.

Next work, in order:

1. Establish existence of B,T₀ for the actual closed-strip kernel bound
   above, first for fixed parameters alpha=2*l-1, beta=0, 0<l<1,
   l != 1/2. The new Gamma strip bounds reduce this to polynomial Estermann
   growth; the new agenda gives the a=-l Euler–Maclaurin route.
   This turns the global reduction into an unconditional theorem.
2. Complete the collision rectangle accounting; the residue is now evaluated.
3. Apply the resulting identities under the actual outward Gaussian ray
   integrals, proving every needed splitting/Fubini step.
4. Identify the full signed M1+M2+D1+D2+E decomposition.
5. Continue the Kloosterman estimates and cofinal uniform moment provider.
   Independent Ingham density formalization remains separate; I2 is closed.

No new uniform density estimate or RH conclusion follows from this work.

## Source and persistent workspace

S. A. C. Baluyot, *On the Zeros of Riemann's Zeta-function* (2017),
Lemma 3.1.3, pp. 96–97, and Section 3.3, pp. 116–117:
https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320

Retained token: ws_O5g_HcTqMq11Vgoxn1u4_9Rz7BHKrorF.

Project root:
/home/cri_2025/lean-agent-workspaces/ws_O5g_HcTqMq11Vgoxn1u4_9Rz7BHKrorF/RiemannResearch
