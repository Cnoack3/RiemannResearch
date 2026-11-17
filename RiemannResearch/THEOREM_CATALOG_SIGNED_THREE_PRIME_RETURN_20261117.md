# Signed three-prime moments and complete returns, 2026-11-17

## Provenance and scope

Continuation of commit b2302a1e6df771fec20869491ef5bf1e88a51847 and the
[Ramanujan–Plancherel A1–A2 audit](RAMANUJAN_PLANCHEREL_A1_A2_AUDIT_20261117.md).
The motivating signed numerator is from sections 22–23 of the
[audited A1–A2 manuscript](https://drive.google.com/file/d/1DHIp4gGwApIL1V6nHwV4HDxuOAFdijwG/view).
The finite quantitative consequences below are derived from existing verified
identities. They are not an assertion of mathematical novelty or of A1/A2.

## Baseline supported by the existing declarations

Write w = progressionWeight(P), R = atomResidual(P,x), Q = atomEnergy(P,x),
L = [1,Y], and T = [Y+1,P-1]. Assume Y<P. Let

- a = p(r-q), b = q(r-p), c = r(q-p);
- F = a U_p - b U_q + c U_r, with the complete upper-atom signals U;
- N = a S_Y(p) - b S_Y(q) + c S_Y(r).

Existing atom normality and activated-moment identities imply
N = <R,F>_L = -<R,F>_T. Existing gram_identity and pairing_sq_le give
N² <= E_L(R) E_L(F) and N² <= E_T(R) E_T(F).
Both estimates apply to the combined signed F. Taking absolute values of the
three separate moments first loses information.

No unconditional boundedness of Q, inverse-Gram norm, or target-specific
curvature decay was found in these providers. In particular, the audit's
RH-sufficient bounded-energy premise is not a normalization.

## Arithmetic cancellation and explicit physical-window bound

[ExactHeadSignedMomentBounds.lean](RH/ExactHeadSignedMomentBounds.lean) defines
tripleProfile, tripleMoment and floorTriple and proves:

| Declaration | Checked content and assumptions |
| --- | --- |
| tripleMoment_eq_prefix | N=<h,F>_[1,Y], arbitrary real w,h and integer labels |
| tripleMoment_eq_physical_pairing | The same N=<h,F>_[x+1,Y]; upper atoms vanish on the head |
| floorTriple_eq_residues | The linear position and constant parts cancel exactly |
| abs_floorTriple_le | For 0<p<=q<=r, absolute floorTriple <= (q-1)(r-p) |
| tripleProfile_eq_floorTriple | Identifies the signed atom profile with the floor profile in the safe physical window |
| physical_triple_eq_moment | (r-q)z_Y(p)-(r-p)z_Y(q)+(q-p)z_Y(r)=N in that window |
| tripleMoment_sq_le_prefix | N²<=E_window(h) E_window(F) for nonnegative weights |
| tripleMoment_sq_le_window_mass | N²<=E_window(h) M_window [(q-1)(r-p)]² |
| atomResidual_tripleMoment_sq_le_window_mass | N²<=Q M_window [(q-1)(r-p)]² for the actual optimizer and Y<P |
| atomResidual_tripleMoment_eq_tail | N=-<R,F>_T for the actual optimizer, with only Y<P |

The exact arithmetic identity is

    floorTriple(n) = -(r-q)(n mod p) + (r-p)(n mod q) - (q-p)(n mod r).

The physical-window theorems require P nonzero, prime p,q,r with
p<=q<=r<=x<2p, coverage in P of every prime at most r, and Y<p².
They keep these assumptions in their Lean types. Primorial(x) supplies
the coverage. The norm bound for floorTriple itself needs only positive,
ordered natural labels.

M_window is the sum of the exact periodized Pareto weights on [x+1,Y].
It includes all infinite progression returns in those weights.
This estimate does not extend the bounded floor profile to the full tail:
the lower-class reentry terms there are retained by the original atom profile.

## Exact complete return and strengthened energy budget

[ExactHeadTailReturnEnergy.lean](RH/ExactHeadTailReturnEnergy.lean) constructs
d=returnProfile by projecting -R onto the complete upper-atom span on T.
This finite normal solution exists for nonnegative weights even with dependent
or zero columns. Define K=returnCost=E_T(d). The core identities are

    <d,F>_T = N,
    Q = E_L(R) + E_T(R+d) + K.

R+d is the residual of the tail-optimal fit to the original target, since
R differs from that target by an upper-span vector. This interpretation does
not require a coefficient inverse. The formal providers are return_normal,
returnProfile_mem, return_pairing, and returnCost_budget.

| Declaration | Checked content |
| --- | --- |
| returnCost_eq_signed_score | K = sum_g c_g m_Y(g), including every upper divisor |
| returnGram_equation | G_T c = m_Y on the full upper-atom family |
| returnCost_eq_full_gram | K = sum_(g,k) c_g G_T(g,k) c_k, retaining every cross term |
| returnCost_le_remaining_energy | K <= Q - E_L(R) |
| tripleMoment_eq_return | N=<d,F>_T |
| tripleMoment_sq_le_returnCost | N²<=K E_T(F) |
| tripleMoment_return_budget_identity | Exact two-region remainder after subtracting E_T(R+d) |
| tripleMoment_sq_le_return_budget | (e_L+e_T)N² <= [Q-E_T(R+d)] e_L e_T |
| tripleMoment_sq_le_harmonic | N²<=Q e_L e_T/(e_L+e_T), including zero-energy degeneracy |
| tailGram_period_column_zero | G_T(g,P)=0 on the nonterminal tail |

Here e_L=E_L(F) and e_T=E_T(F). The strengthened exact remainder is

    [Q-E_T(R+d)] e_L e_T - (e_L+e_T)N²
      = e_T [E_L(R)e_L-N²] + e_L [K e_T-N²].

Each bracket is a Cauchy–Schwarz Gram remainder, equal to the complete
nonnegative minor sum given by FiniteProfileEnergy.gram_identity. Thus no
signed cross term was discarded in the identity. For e_L+e_T>0 one can divide
to obtain the stronger harmonic bound with Q-E_T(R+d); the displayed product
inequality needs no division or rank hypothesis.

The period column is zero, so whenever P>x it belongs to the upper family
and the unreduced full tail Gram is singular. An inverse-Gram formulation
must specify a reduced independent basis or an inverse on the feasible range.
The construction above avoids assuming such an inverse. It still charges
the complete cost K; it does not furnish a uniform bound for that cost.

The reusable scalar identities live in
[FiniteWeightedReturnBounds.lean](Analysis/FiniteWeightedReturnBounds.lean):
two_region_gram_identity, two_region_pairing_sq_le, and
two_region_pairing_sq_le_harmonic.

## Corrected Ramanujan–Plancherel applied to the signed prefix

[ExactHeadSignedMomentPlancherel.lean](RH/ExactHeadSignedMomentPlancherel.lean)
uses W(g)=1_(x<g) m_Y(g). Automatically W(g)=0 for g>Y. The signed coefficient
k(g) is a*1_(p|g)-b*1_(q|g)+c*1_(r|g), restricted to x<g<=Y.
This restriction avoids charging inactive dual coordinates.

For squarefree P, tripleMoment_eq_conductor_pairing proves

    N = phi(P)/P * sum_(a|P) Transform(W)(a) Transform(k/phi)(a)/phi(a).

Conductor one is included. These are prefix scores, not the full-period
optimizer scores: upper normality for the latter does not make the former
vanish. No nontrivial-conductor-only identity is substituted.

Without squarefreeness, tripleMoment_sq_le_score_energy proves

    N² <= [sum_(g|P) phi(g) W(g)²] [sum_(g|P) k(g)²/phi(g)].

The theorem tripleMoment_score_gram_identity retains the exact nonnegative
minor remainder behind this bound. The signs within k(g) are combined before
squaring. These are coordinate identities and estimates, not an asymptotic
upper bound for the actual prefix-score energy.

## Verification

- Component acceptance: job_nAwnxGGUGBaHmK1XTopTMKIOmAoAp0l9.
- Backend: Bazel --config=buildbuddy; verified=true, exit_code=0.
- Scope: a snippet importing ExactHeadTailReturnEnergy and
  ExactHeadSignedMomentPlancherel, covering all four new modules and their
  transitive imports.
- [BuildBuddy invocation](https://app.buildbuddy.io/invocation/3d0922fe-9eaf-40a0-9463-6cbeaf8c0a9a).
- Server-reported verification elapsed: 156.684 seconds; this excludes
  workspace setup and conversation/polling delays.

Guarded axiom acceptance also passed:
job_ZZZ7lHMFZlXn9alDWm7yHaTrxuZut3ue,
[BuildBuddy invocation](https://app.buildbuddy.io/invocation/2a0787b9-666b-41d9-af39-8d4c4c0b4c2d),
Bazel verified=true, exit_code=0, 49.303 server seconds. The four guarded
declarations are atomResidual_tripleMoment_sq_le_window_mass,
tripleMoment_sq_le_return_budget, returnCost_eq_full_gram, and
tripleMoment_eq_conductor_pairing. Their dependencies are exactly
[propext, Classical.choice, Quot.sound]. This checks project-axiom absence,
not the discharge of hypotheses explicitly listed in the theorem types.

The final publication checkpoint must additionally validate the complete
//:RiemannResearch target through Bazel --config=buildbuddy, including any
integration with newer main. Component acceptance alone does not certify
that complete target; the checkpoint receipt records the publication result.

## Remaining analytic obligations

| Obligation | Status |
| --- | --- |
| Growth control for Q=atomEnergy(P,x) at the selected cofinal cutoffs | Open; never replaced by 1 |
| Quantitative actual prefix-score cancellation or small Gram remainders | Open |
| Uniform control of K, or of the equivalent inverse/reduced-Gram return cost | Open |
| Control of the complete tail profile energies across the required prime family | Open |
| Passage from these finite numerator bounds to the manuscript's normalized Hessian/curvature rate | Open |
| Any large-sieve input needed for low/high conductor splitting | External/conditional until supplied by a checked provider |
| A1, A2, Q tending to zero, RH | Not established by this continuation |

The next concrete task is to bound the actual score vector in the full
tail Gram geometry, or prove smallness of the displayed signed Gram remainders,
with an explicit cofinal cutoff and the actual factor Q. A bound that uses
only normal equations cannot supply target-specific decay by itself.
