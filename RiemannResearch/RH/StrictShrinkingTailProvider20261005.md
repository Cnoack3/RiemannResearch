# Strict shrinking-cutoff transfer from a retained finite-height density window

Research date: 2026-10-05. Requested audit base:
81ecb78f890611273f961c6ca1d056c448587eb4.
Development continues on its immediate descendant
1b871a2d134ab1f107293d1d2dbb41ab81b77266, preserving that commit's
Hilbert--Schmidt strengthening and inverse-rate density consumers.

## Audit conclusion

The principal harmonic and growing-support declarations at the requested base
are unchanged in the descendant. The cap retains every analytic zero copy,
both exponential channels and their real cross mass d/N(T). Its signed rank-two
calculation keeps the negative sinh square. The strict bad mask is the
complement of |beta-1/2|<=delta, with the original full Ncount(0,T).
All coordinates 1,...,d, including composites, are retained.

The exact nonnegative Landau majorant convergence criterion concerns that
majorant, not necessity for the actual signed residual. The original 2/7
logarithmic extension remains valid. The descendant separately improves the
available Hilbert--Schmidt residual endpoint to 1/3; this audit does not
rewrite the older theorem as a stronger statement.

The fresh GitHub collection query now reports a failed push workflow for 81ecb
(run 37325896890), while its commit-status collection remains empty.
The downloaded log terminates during build output and does not identify a
decisive fatal compiler error. Local compilation and kernel checks are separate
verification evidence.

## Exact counting and boundary correction

Use the source's closed half-plane count
D(T,sigma)=sum multiplicity * 1_{beta>=sigma}.
Let J(T,sigma) count copies with beta=sigma, and let
D(H,T;sigma) count copies with H<gamma<=T and beta>=sigma.
For H<=T, exactly

    D(T,sigma)=D(H,sigma)+D(H,T;sigma).

For delta>=0, reflection preserves both positive heights and analytic
multiplicity, and gives exactly

    strictTail(T,delta)
      =2 rightStrictTail(T,delta)
      =2[D(T,1/2+delta)-J(T,1/2+delta)].

Thus a density-window estimate D(T,sigma)-D(H,sigma)<=F gives

    (strictTail/N(T))*W_d
      <= 2[F+D(H,sigma)-J(T,sigma)]*W_d/N(T).

The current boundary count is subtracted; the initial count is retained.
No finite RH certificate, simplicity premise, or normalized good-count
substitution is used.

## Source and exact rate

Chourasiya--Simonic, An explicit form of Ingham's zero density estimate,
arXiv:2507.15184v2 (2025), Theorem 1, Corollary 1 and their proof:
https://arxiv.org/html/2507.15184v2 .

Theorem 1 estimates the difference N(sigma,T)-N(sigma,H).
Corollary 1 uses a finite-height RH verification to remove N(sigma,H);
that removal is not used here. Table 1 and its first interval give the
near-line shape, with finite/logarithmic terms retained. Importing the
quoted numerical constants also requires verifying the paper's parameter
bounds; this work does not assert those decimals as a Lean theorem.

Put L=log T, I(delta)=4delta/(3-2delta), and M=L+log L. Exactly,

    3(1-(1/2+delta))/(2-(1/2+delta))=1-I(delta),
    (7-5(1/2+delta))/(2-(1/2+delta))=3-I(delta),
    T^(1-I(delta))*L^(3-I(delta))
      =T*L^3*exp[-M I(delta)].

The existing inghamPower_eq_expDecay verifies the last identity.
The extra log-log term in M is retained.

## Optimized one-point cutoff and proved transfer

Set K(T)=C*T*(log T)^3 for a source constant C>0, and more generally
allow any positive K(T) and M(T). Define

    A(T)=2*K(T)*W_{d(T)}/N(T),
    S(T)=max(0,log A(T)+omega(T)),
    delta(T)=3*S(T)/(4*M(T)+2*S(T)).

The positive part removes the extraneous premise log A+omega>=0.
The scalar cutoff is the least nonnegative cutoff meeting the requested
rate margin, within the physical interval when its range test holds.
Exactly M*I(delta)=S, and

    A exp[-M I(delta)] <= exp[-omega].

Assume only the eventual density estimate at this chosen point:

    D(T,1/2+delta(T))-D(H,1/2+delta(T))
      <=K(T) exp[-M(T) I(delta(T))]+B2*(log T)^2+B3*log T.

Then

    (strictTail(T,delta(T))/N(T))*W_{d(T)}
      <= exp[-omega(T)]
         +2[B2*(log T)^2+B3*log T+N(H)]*W_{d(T)}/N(T).

The finite-height count N(H) has not disappeared. The new unconditional
remainder lemma proves that the second term tends to zero whenever
1<=d(T) and log d(T)<=log T/2 eventually. This includes every
square-root-log support schedule, and uses the existing actual
Riemann--von Mangoldt count lower bound.

If omega(T)->infinity and S(T)/M(T)->0, the chosen delta(T)->0 and the
one-point harmonic budget, actualSignedTailBudget and norm of the full
signed bad hyperbolic operator all tend to zero. The source-scale theorem additionally proves the margin-ratio condition
whenever log d(T)/log T->0 and omega(T)/log T->0, with omega(T)->infinity.
These are conditional consumers: the one-point difference inequality is the
only substantive density premise. All support and margin assumptions are
ordinary prescribed growth conditions, with no extra zero-density premise.

For ell~c sqrt L, the paper estimate W_d~d sqrt(ell/8) gives
log A=ell+(9/4)log L+O(1). Choosing any diverging omega=o(sqrt L)
retains the endpoint centering limit delta*ell/2 ->3c^2/8.
This sharper schedule retains the complete harmonic cap and the nonlinear
rate. At fixed polynomial support d~T^theta, the same count-only inverse
margin tends to 3*theta/(4+2*theta), which is not a shrinking cutoff.
The shrinking conclusion concerns subpower support; it is not inferred from
the older polynomial Landau residual result.
This asymptotic schedule statement is paper analysis unless independently
listed as a checked declaration below.

## Precise remaining analytic provider

Open: prove in Lean the displayed actual one-point difference inequality
with the source's M=log T+log log T and K=C*T*(log T)^3, or equivalently its exact power-shaped bound, with justified fixed constants. The source's near-line interval membership is already proved for the chosen schedule; the analytic estimate and its numerical parameter verification remain Open. A uniform theorem
over the whole zero strip is unnecessary for this consumer.

The published proof's Gabriel convexity, Littlewood zero-detector, and
explicit fourth-moment estimates have not been imported or proved here.
No citation is converted into an axiom. The counting identities, reflection,
boundary conversion, cutoff algebra, retained-remainder decay and operator
transfer are proved independently around this remaining provider.

The negative sinh contribution and composite interactions survive through
the existing signedBadHyperbolic norm and form identities. This work does not
discharge the separate fully screened physical Pareto transfer or prove RH.

## Verification

The full baseline project build at 1b871a2d passed. The coherent new candidate
passed Lean with no warnings after proof repairs. Axiom audits of the principal
base harmonic/growing-support results and the new principal counting,
cutoff, remainder and source consumers report only:

    propext, Classical.choice, Quot.sound

There is no sorryAx or project-specific axiom in these audited dependencies.
The analytic hcount remains an explicit local hypothesis in the consumer's
type; #print axioms does not discharge it.
Publication is gated by checkpoint validation of affected modules and local
reverse dependents; a published checkpoint therefore certifies that validation.

Principal declarations:
- ActualZeroOrdinate.rightInclusiveWindow_eq_sub
- ActualZeroOrdinate.strictTail_eq_inclusive_sub_boundary
- ZeroDensityRate.positiveCountCutoff_le_iff_margin
- ZeroDensityRate.positiveCountCutoff_eventually_nearLine
- ActualZeroOrdinate.finiteHeight_log_remainder_tendsto_zero
- ActualZeroOrdinate.sourceCountCutoff_shrinking
- ActualZeroPhaseMoments.shrinking_harmonic_tail_of_sourceDifference
- ActualZeroPhaseMoments.shrinking_harmonic_tail_of_inghamDifference
- ActualZeroPhaseMoments.eventually_signedBadHyperbolic_upper_of_harmonic
- ActualZeroPhaseMoments.goodHyperbolic_distance_tendsto_zero_of_harmonic

The inghamDifference consumer accepts the exact power-shaped literature
statement at the chosen cutoff and proves its conversion to the exponential
budget. The unconditional sourceCountCutoff_shrinking theorem also proves
eventual membership in 0<=delta<=1/32 before any density premise is supplied.
