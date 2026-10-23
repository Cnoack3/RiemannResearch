# Unit-signal boundedness and the missing RH hypothesis

Research audit for Christian Noack, 22 October 2026.

## Conclusion

The selected boundedness argument does not prove RH. For the normalized
projection family, boundedness is already supplied by any fixed admissible
competitor. The existing RH consumer additionally requires physical coordinate
convergence to the constant target. That hypothesis has not been supplied for
the sampled unit-signal family.

This is a missing hypothesis in the proposed inference, not a disproof of RH.

## The two sequences must be distinguished

Put P(n)=1/(n(n+1)), Q(n)=1/(zeta(2)n^2), and g_d(n)=(n mod d)/d.
For nested legal spaces V_j, write p_j=P_{V_j}1 and kappa_j=||p_j||_P^2.
The exact unit-signal optimizer is U_j=p_j/kappa_j. The sampled F_j is a
perturbation of U_j, normalized by the true signal.

The already established exact identity in
Analysis.FiniteGramSignalStability.normalized_target_error_exact is

    ||1-F_j||_P^2 = 1/kappa_j - 1 + ||F_j-U_j||_P^2.

Increasing sampling heights can make the last term vanish. It does not
establish kappa_j -> 1. If h=P_V1 and kappa_infinity=||h||_P^2>0, the
selected strong limit is h/kappa_infinity, with error 1/kappa_infinity-1.
The comparison Q <= (2/zeta(2))P transfers boundedness and strong convergence;
it preserves the same physical limiting function and does not identify it as 1.

## Why uniform boundedness is automatic here

The elementary identity P(N odd)=log 2 gives the legal competitor

    F_star = 2g_2/log 2 = 1_odd/log 2,
    E_P F_star = 1,     ||F_star||_P^2 = 1/log 2.

Every dictionary containing conductor 2 therefore has
||U_j||_P^2 <= 1/log 2, regardless of whether its eventual closed span contains 1.
In the one-dimensional space span(g_2), the exact projection is 1_odd,
kappa=log 2, and the constant optimizer sequence has positive error
1/log 2-1. This illustrates the failure of the abstract inference from
bounded normalized optimizers to target membership; it is not a
counterexample involving the exhausted full legal span.

The same competitor has ||F_star||_Q^2=3/(4(log 2)^2), since Q(N odd)=3/4.
Wolfram independently checked these series evaluations during this audit.
These particular infinite-series evaluations were not newly formalized here.

## New general Lean statements

The following declarations extend Analysis/UnitSignalProjection.lean,
in namespace
RiemannResearch.Analysis.UnitSignalProjection.ProjectionSignalModel:

- admissible_norm_sq:
  ||f||^2 = mass + ||f-target||^2 for any admissible f.
- optimizer_norm_sq_le_admissible:
  every admissible competitor bounds the optimizer's squared norm.
- optimizer_eq_target_iff_energy_eq_mass:
  optimizer=target iff projection energy=target mass.
- normalized_residual_pairing:
  <target-optimizer,f> =
  (1-mass/energy)<target,f> for every f in the trial space.

These are unconditional consequences of the explicit projection-model
hypotheses. They neither assume nor prove an arithmetic closure statement.
For the constant target, take mass=1 and complement=0.

In particular, with r=1-h and w=1-h/kappa_infinity,

    r is perpendicular to V,
    <w,g_d>_P = (1-1/kappa_infinity)log(d)/d.

The normalized residual w must not be replaced by the orthogonal residual r.

## The actual verified RH criterion

RH.QBoundedCoordinateClosure.riemannHypothesis_of_bounded_legal_coordinate_limits
requires all three assertions for the SAME family:

1. f_N belongs to the actual full legal residue span;
2. f_N(k) -> 1 for every fixed k>=1;
3. sup_N ||f_N||_Q < infinity.

The growing-exact-head version requires f_N(k)=1 for 1<=k<=N.
The current bounded optimizer family supplies item 3, but not item 2.
Conversely, constructing exact heads does not transfer the optimizer's bound:
exact-head constraints form a different affine feasible set.

Existing ExactHeadResidualTail and ExactHeadCofinalBounds show that bounded
exact-head errors suffice, even on cofinally many stages. If RH is false,
every such exact-head error family diverges. QOptimalSamplingMobiusResearch20261022.md
records the corresponding canonical-residual tail lower bound and the
unresolved complete signed head-repair cost.

## Precise remaining research obligations

For the sampled unit-signal route, any one of the following would identify
the required target:

- prove kappa_j -> 1;
- prove F_j(k) -> 1 for every fixed positive integer k;
- identify every fixed residue coefficient limit as -mu(d);
- under exact E_P F_j=1, prove ||F_j||_P^2 -> 1.

All four are Open for the family at issue. A finite upper bound greater than
one, convergence to an unidentified projection, and arbitrarily accurate
sampling do not discharge them.

## Verification record

The coherent development snippet and audits of the existing RH criterion
and exact sampled-error identity succeeded in job
job_284wiNH01BUTyWxSHqD3Ig4S3-BSACJC, exit code 0.
All four new declarations and the two audited existing declarations reported
only propext, Classical.choice, and Quot.sound.
Its server-reported verification time was 6.717 seconds; queue delay was
about 3.616 seconds. These are separate from workspace-opening and polling
latency, which were not independently timed. The first development candidate
had tactic/elaboration errors; they were corrected before persistence.

The final source check and publication are governed by the checkpoint receipt.
No RH proof is claimed.
