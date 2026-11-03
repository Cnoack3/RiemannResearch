# Prime tensor CRT reproduction source — 2026-11-02 project

These are the sources of the companion diagnostic archive. The Python files
use NumPy and SciPy; the recorded environment was Python 3.12.14, NumPy 2.3.5,
SciPy 1.17.0. Save the two Python blocks under their displayed filenames
in the same directory, then run the base program followed by the extended
program. Their JSON output separates floating diagnostics from exact rational
enclosures. No numerical trend proves an asymptotic result or RH.

The Wolfram block reproduces the independent cutoff-product check.
The accompanying mathematical memorandum proves the bounds used by the
rational computations; only the explicitly cataloged theorems are Lean checked.

## prime_tensor_crt_diagnostics.py

```python
"""Complete weighted moments and exact rational benchmark, 2026-11-02.

Floating calculations select candidates only. rational_certificate() uses
fractions and integral-test bounds for every omitted positive-integer term.
Source: the supplied Prime Tensor CRT project, sections 4, 6 and Appendix B.
"""
import json
import math
from fractions import Fraction as Q
from functools import lru_cache
import numpy as np
from scipy.special import polygamma


def factors(n):
    out, p = [], 2
    while p*p <= n:
        if n % p == 0:
            a = 0
            while n % p == 0:
                n //= p
                a += 1
            out.append((p,a))
        p += 1
    if n > 1:
        out.append((n,1))
    return out


def mu(n):
    fs = factors(n)
    return 0 if any(a > 1 for _,a in fs) else (-1)**len(fs)


def divisors(n):
    ds = [1]
    for p,a in factors(n):
        ds = [d*p**k for d in ds for k in range(a+1)]
    return sorted(ds)


@lru_cache(None)
def weights(l):
    w = np.empty(l)
    w[0] = 1/l**2
    w[1:] = polygamma(1,np.arange(1,l)/l)/(l*l*(math.pi**2/6))
    assert abs(sum(w)-1) < 1e-12
    return w


@lru_cache(None)
def gram_entry(d,e):
    l = math.lcm(d,e)
    n = np.arange(l)
    return float(weights(l) @ ((n%d)/d*((n%e)/e)))


@lru_cache(None)
def twisted(d,a):
    n = np.arange(d)
    return float(weights(d) @ ((a*n%d)/d))


def row(r,ds):
    j2 = math.prod(p**(2*a)-p**(2*a-2) for p,a in factors(r))
    return [sum(mu(r//a)*twisted(d,a%d) for a in divisors(r))/math.sqrt(j2) for d in ds]


def fit(ds):
    g = np.array([[gram_entry(d,e) for e in ds] for d in ds])
    b = np.array([twisted(d,1) for d in ds])
    c = np.linalg.solve(g,b)
    err = float(1-2*b@c+c@g@c)
    return dict(dictionary=ds, coefficients=c.tolist(), squared_error=err,
                capacity=(1-err)/err, coefficient_l1=float(np.abs(c).sum()),
                condition=float(np.linalg.cond(g)), normal_residual=float(np.linalg.norm(g@c-b))), g,b,c


def rational_certificate():
    ds = [2,3,6]
    c = [Q(1045918,10**6),Q(1069558,10**6),Q(604750,10**6)]
    kmax=tmax=100
    residues = [1-sum((v*Q(n%d,d) for v,d in zip(c,ds)),Q(0)) for n in range(1,7)]
    lo=hi=Q(0)
    for r,e in enumerate(residues,1):
        s = sum((Q(1,(6*k+r)**2) for k in range(kmax)),Q(0))
        tail = Q(1,6*(6*kmax+r))
        lo += e*e*(s+tail)
        hi += e*e*(s+tail+Q(1,(6*kmax+r)**2))
    z = sum((Q(1,n*n) for n in range(1,tmax+1)),Q(0))
    lower,upper = lo/(z+Q(1,tmax)),hi/(z+Q(1,tmax+1))
    assert Q(5476,100000) < lower < upper < Q(5478,100000)
    return dict(coefficients=[str(x) for x in c], K=kmax,T=tmax,
                rigorous_outer_interval=['0.05476','0.05478'],
                lower=str(lower),upper=str(upper))


def main():
    out={'status':'Floating diagnostics except the explicitly rational benchmark.'}
    out['stages']=[fit([d for d in range(2,b+1) if mu(d)])[0] for b in [2,3,6,10,15,20,30]]
    out['primorial']=[fit(divisors(l)[1:])[0] for l in [6,30,210]]
    all_ds=[d for d in range(2,31) if mu(d)]
    selected=[]
    adaptive=[]
    for _ in range(8):
        best=min((fit(sorted(selected+[d])) for d in all_ds if d not in selected),key=lambda x:x[0]['squared_error'])
        selected=best[0]['dictionary']
        adaptive.append(best[0])
    out['adaptive']=adaptive
    info,g,b,c=fit([2,3,6])
    a=np.array([row(r,[2,3,6]) for r in divisors(12)])
    k=g-a.T@a
    y=np.zeros(len(a));y[0]=1
    info['retained_error']=float(np.linalg.norm(y-a@c)**2)
    info['exact_tail']=float(c@k@c)
    diag=np.diag(k)
    info['raw_tail_diagonal']=diag.tolist()
    assert diag.min()>-1e-12
    # g_2 has exactly zero omitted energy here; roundoff may give -1e-16.
    # Clipping is only a floating diagnostic, never an interval certificate.
    info['column_tail_bound']=float((np.abs(c)@np.sqrt(np.maximum(diag,0)))**2)
    info['tail_eigenvalues']=np.linalg.eigvalsh(k).tolist()
    out['benchmark_float']=info
    out['benchmark_rational']=rational_certificate()
    with open('prime_tensor_crt_diagnostics.json','w') as f:
        json.dump(out,f,indent=2)
    print(json.dumps({'stage_errors':[(x['dictionary'][-1],x['squared_error']) for x in out['stages']],
                      'primorial_errors':[x['squared_error'] for x in out['primorial']],
                      'adaptive_dictionary':selected,'adaptive_error':adaptive[-1]['squared_error'],
                      'rational_outer_interval':out['benchmark_rational']['rigorous_outer_interval']},indent=2))


if __name__=='__main__':
    main()
```

## prime_tensor_crt_extended_diagnostics.py

```python
"""Extended reproducible prime tensor / CRT diagnostics, 2026-11-02.

Optimization, nullspace solves, and adaptive rows below use floating point.
They are diagnostics, NOT interval certificates or proofs of optimality.
The separately labelled finite-prime section uses exact Fraction arithmetic
and rigorous integral-test zeta bounds, with the coupling theorem in the
accompanying research note. This module imports, and never edits, the base.
"""
import json
import math
from fractions import Fraction

import numpy as np
from scipy.linalg import null_space
from scipy.optimize import minimize

import prime_tensor_crt_diagnostics as base


DICTIONARY = [2, 3, 5, 6, 7, 10, 11, 13]
M = 60
ZETA2 = math.pi**2 / 6


def cutoff_data(m, ds, gram):
    rows = base.divisors(m)
    a = np.asarray([base.row(r, ds) for r in rows], dtype=float)
    delta = 1 - sum(1/r**2 for r in rows)/ZETA2
    second = 0.0
    for r in rows:
        cell_factor = math.prod(1 - 1/p**2 for p, _ in base.factors(m//r))
        second += 1/(r*r*cell_factor)
    kappa = sum(1/r**2 for r in rows)/ZETA2 - second/ZETA2**2
    raw_tail = np.diag(gram - a.T @ a)
    assert raw_tail.min() > -1e-12
    return rows, a, delta, kappa, raw_tail


def column_record(c, gram, means, rows, a, tau):
    y = np.asarray([1.0 if r == 1 else 0.0 for r in rows])
    retained = float(np.linalg.norm(y-a@c)**2)
    exact_tail = float(c @ (gram-a.T@a) @ c)
    column_tail = float((np.abs(c) @ np.sqrt(np.maximum(tau, 0)))**2)
    return dict(
        coefficients=c.tolist(),
        actual_complete_squared_error=float(1-2*means@c+c@gram@c),
        complete_energy=float(c@gram@c),
        retained_squared_error=retained,
        actual_omitted_squared_energy=exact_tail,
        column_tail_bound=column_tail,
        column_certificate=retained+column_tail,
        coefficient_l1=float(np.abs(c).sum()),
    )


def split_qp(label, weights, a, rows, gram, means, initial):
    """Minimize ||y-Ac||²+(sum weights*|c|)² by c=u-v, u,v>=0."""
    n = len(initial)
    b = np.column_stack((a, -a))
    w = np.concatenate((weights, weights))
    y = np.asarray([float(r == 1) for r in rows])
    x0 = np.concatenate((np.maximum(initial, 0), np.maximum(-initial, 0)))

    def fun(x):
        return float(np.linalg.norm(y-b@x)**2 + (w@x)**2)

    def jac(x):
        return 2*b.T@(b@x-y) + 2*w*(w@x)

    result = minimize(fun, x0, jac=jac, bounds=[(0, None)]*(2*n),
                      method='SLSQP',
                      options=dict(maxiter=5000, ftol=1e-14, disp=False))
    x = np.maximum(result.x, 0)
    c = x[:n]-x[n:]
    gradient = jac(x)
    projected_gradient = np.where(x > 1e-8, gradient, np.minimum(gradient, 0))
    actual_penalty = float((weights @ np.abs(c))**2)
    retained = float(np.linalg.norm(y-a@c)**2)
    return dict(
        label=label,
        status='floating diagnostic; no interval or exact optimality claim',
        solver='scipy.optimize.minimize/SLSQP; split nonnegative coefficients',
        solver_success=bool(result.success), solver_status=int(result.status),
        solver_message=str(result.message), iterations=int(result.nit),
        projected_gradient_inf=float(np.max(np.abs(projected_gradient))),
        complementarity_inf=float(np.max(np.abs(x*gradient))),
        minimum_split_variable=float(x.min()),
        maximum_split_overlap=float(np.minimum(x[:n], x[n:]).max()),
        split_objective=float(result.fun),
        absolute_coefficient_objective=retained+actual_penalty,
        split_objective_gap=float(result.fun)-(retained+actual_penalty),
        coefficients=c.tolist(),
        coefficient_l1=float(np.abs(c).sum()),
        retained_squared_error=retained, certificate_tail=actual_penalty,
        certificate=retained+actual_penalty,
        actual_complete_squared_error=float(1-2*means@c+c@gram@c),
        complete_energy=float(c@gram@c),
    )


def compare_optimizers(ds, m):
    info, gram, means, c = base.fit(ds)
    rows, a, delta, kappa, raw_tau = cutoff_data(m, ds, gram)
    weights = dict(
        universal_delta_l1=np.full(len(ds), math.sqrt(delta)),
        sharp_kappa_weighted_l1=math.sqrt(kappa)*np.asarray([(d-1)/d for d in ds]),
        column_tail=np.sqrt(np.maximum(raw_tau, 0)),
    )
    complete = column_record(c, gram, means, rows, a, raw_tau)
    complete.update(label='complete Gram error minimizer',
                    normal_equation_residual=float(np.linalg.norm(gram@c-means)),
                    condition=float(np.linalg.cond(gram)))
    complete['certificates_at_same_vector'] = {
        label: complete['retained_squared_error']+float((w@np.abs(c))**2)
        for label, w in weights.items()
    }
    sols = [split_qp(label, w, a, rows, gram, means, c)
            for label, w in weights.items()]
    return dict(dictionary=ds, cutoff=m, retained_rows=rows, delta=delta, kappa=kappa,
                raw_tail_diagonal=raw_tau.tolist(),
                floating_negative_tail_policy='Clip only entries above -1e-12 to zero; never an interval claim.',
                complete_gram_minimizer=complete, certificate_minimizers=sols), gram, means, c


def constrained_heads(ds, gram, means):
    outputs = []
    for head in [3, 6, 10]:
        r = np.asarray([[(n%d)/d for d in ds] for n in range(1, head+1)])
        y = np.ones(head)
        c0, _, rank, singular = np.linalg.lstsq(r, y, rcond=1e-12)
        feasible_residual = float(np.linalg.norm(r@c0-y, ord=np.inf))
        record = dict(head=head, rank=int(rank), singular_values=singular.tolist(),
                      least_squares_feasibility_residual_inf=feasible_residual,
                      floating_feasible=feasible_residual <= 1e-10,
                      status='floating feasibility and energy minimization, not exact certificate')
        if not record['floating_feasible']:
            outputs.append(record)
            continue
        z = null_space(r, rcond=1e-12)
        if z.shape[1]:
            reduced = z.T@gram@z
            c = c0-z@np.linalg.solve(reduced, z.T@gram@c0)
            reduced_condition = float(np.linalg.cond(reduced))
        else:
            c, reduced_condition = c0, None
        record.update(
            nullity=int(z.shape[1]), reduced_condition=reduced_condition,
            coefficients=c.tolist(), complete_energy=float(c@gram@c),
            actual_complete_squared_error=float(1-2*means@c+c@gram@c),
            head_values=(r@c).tolist(),
            head_constraint_residual_inf=float(np.linalg.norm(r@c-y, ord=np.inf)),
            nullspace_stationarity_residual=float(np.linalg.norm(z.T@gram@c)),
            nullspace_constraint_residual=float(np.linalg.norm(r@z)),
            period_mean=float(np.asarray([(d-1)/(2*d) for d in ds])@c),
            coefficient_l1=float(np.abs(c).sum()),
        )
        outputs.append(record)
    return outputs


def adaptive_rows(ds, gram, means, c):
    all_rows = {r: np.asarray(base.row(r, ds)) for r in range(1, 61)}
    selected = [1]
    stage_records = []

    def record(rows):
        a = np.asarray([all_rows[r] for r in rows])
        tau = np.diag(gram-a.T@a)
        assert tau.min() > -1e-11
        item = column_record(c, gram, means, rows, a, tau)
        item.pop('coefficients')
        item.update(selected_rows=rows.copy(), raw_tail_diagonal=tau.tolist())
        return item

    current = record(selected)
    current.update(added_row=1, certificate_reduction=None)
    stage_records.append(current)
    stopping = 'all rows exhausted'
    while len(selected) < 60:
        choices = [(r, record(selected+[r])) for r in range(2, 61) if r not in selected]
        r, best = min(choices, key=lambda pair: (pair[1]['column_certificate'], pair[0]))
        gain = current['column_certificate']-best['column_certificate']
        if gain <= 1e-14:
            stopping = 'best floating certificate reduction <= 1e-14'
            break
        selected.append(r)
        best.update(added_row=r, certificate_reduction=float(gain))
        stage_records.append(best)
        current = best
    return dict(status='floating greedy row selection; complete coefficient vector fixed',
                candidates=list(range(1, 61)), coefficients=c.tolist(),
                stopping_reason=stopping, selected_rows=selected, stages=stage_records,
                unchanged_actual_complete_error=float(1-2*means@c+c@gram@c))


def rational_geometric_transition(p, modulus):
    """Exact Markov matrix from a geometric number of multiplication steps."""
    q = Fraction(1, p*p)
    matrix, orbit_records = [], []
    for start in range(modulus):
        orbit, seen = [], {}
        x = start
        while x not in seen:
            seen[x] = len(orbit)
            orbit.append(x)
            x = p*x % modulus
        a = seen[x]
        period = len(orbit)-a
        row = [Fraction(0) for _ in range(modulus)]
        for k in range(a):
            row[orbit[k]] += (1-q)*q**k
        for j in range(period):
            row[orbit[a+j]] += (1-q)*q**(a+j)/(1-q**period)
        assert sum(row) == 1 and min(row) >= 0
        matrix.append(row)
        orbit_records.append(dict(start=start, preperiod=a, period=period, orbit=orbit))
    return matrix, orbit_records


def rat_interval(finite_value, oscillation, omitted_upper, minimum=Fraction(0), maximum=None):
    lo, hi = finite_value-oscillation*omitted_upper, finite_value+oscillation*omitted_upper
    lo = max(lo, minimum)
    if maximum is not None:
        hi = min(hi, maximum)
    return dict(lower=str(lo), upper=str(hi), lower_decimal=float(lo), upper_decimal=float(hi))


def rational_round_down(value, denominator=10**12):
    return Fraction(value.numerator*denominator // value.denominator, denominator)


def rational_round_up(value, denominator=10**12):
    numerator = -((-value.numerator*denominator) // value.denominator)
    return Fraction(numerator, denominator)


def finite_prime_product():
    ps = [2, 3, 5, 7, 11, 13, 17, 19]
    modulus = 6
    dist = [Fraction(int(r == 1)) for r in range(modulus)]
    orbits = {}
    for p in ps:
        trans, orbit = rational_geometric_transition(p, modulus)
        dist = [sum((dist[x]*trans[x][y] for x in range(modulus)), Fraction(0))
                for y in range(modulus)]
        orbits[str(p)] = orbit
    assert sum(dist) == 1 and min(dist) >= 0

    zeta_t = 1000
    zeta_prefix = sum((Fraction(1, n*n) for n in range(1, zeta_t+1)), Fraction(0))
    zeta_lo = zeta_prefix+Fraction(1, zeta_t+1)
    zeta_hi = zeta_prefix+Fraction(1, zeta_t)
    finite_euler = math.prod(Fraction(p*p-1, p*p) for p in ps)
    exact_omitted_lo = 1-Fraction(1)/(zeta_lo*finite_euler)
    exact_omitted_hi = 1-Fraction(1)/(zeta_hi*finite_euler)
    omitted_lo = rational_round_down(exact_omitted_lo)
    omitted_hi = rational_round_up(exact_omitted_hi)
    assert omitted_lo <= exact_omitted_lo <= exact_omitted_hi <= omitted_hi
    display_zeta_lo = rational_round_down(zeta_lo)
    display_zeta_hi = rational_round_up(zeta_hi)
    assert display_zeta_lo <= zeta_lo <= zeta_hi <= display_zeta_hi
    assert 0 <= omitted_lo <= omitted_hi < 1
    assert Fraction(1026686, 10**8) < omitted_lo
    assert omitted_hi < Fraction(1026747, 10**8)

    ds = [2, 3, 6]
    values = {d: [Fraction(r%d, d) for r in range(modulus)] for d in ds}
    moments = []
    for i, d in enumerate(ds):
        observables = [('mean', d, None, values[d], base.twisted(d, 1))]
        observables += [('gram', d, e, [values[d][r]*values[e][r] for r in range(modulus)],
                         base.gram_entry(d, e)) for e in ds[i:]]
        for kind, d, e, f, complete_float in observables:
            value = sum((dist[r]*f[r] for r in range(modulus)), Fraction(0))
            oscillation = max(f)-min(f)
            interval = rat_interval(value, oscillation, omitted_hi, min(f), max(f))
            moments.append(dict(kind=kind, d=d, e=e, finite_prime_exact=str(value),
                                finite_prime_decimal=float(value),
                                observable_oscillation_exact=str(oscillation),
                                coupling_error_upper_exact=str(oscillation*omitted_hi),
                                rigorous_complete_moment_interval=interval,
                                complete_polygamma_float=complete_float,
                                floating_absolute_difference=abs(complete_float-float(value)),
                                floating_inclusion_check=interval['lower_decimal']-1e-14 <= complete_float <= interval['upper_decimal']+1e-14))
    return dict(
        status='Exact rational finite-prime product and coupling enclosures; polygamma comparisons floating only.',
        modulus=modulus, primes=ps, normalization_exactly_one=sum(dist)==1,
        residue_probabilities_exact=[str(x) for x in dist],
        residue_probabilities_decimal=[float(x) for x in dist],
        geometric_orbits=orbits,
        zeta_enclosure=dict(T=zeta_t, lower=str(display_zeta_lo), upper=str(display_zeta_hi),
                            method='Exact Z_T+1/(T+1) < zeta(2) < Z_T+1/T, rounded outward for JSON display only.',
                            display_rounding_denominator=10**12,
                            outward_rounding_verified_by_exact_fraction_assertions=True),
        finite_euler_product_exact=str(finite_euler),
        omitted_prime_probability_interval=dict(lower=str(omitted_lo), upper=str(omitted_hi),
                                                lower_decimal=float(omitted_lo), upper_decimal=float(omitted_hi),
                                                outward_rounding_denominator=10**12,
                                                outward_rounding_verified_by_exact_fraction_assertions=True,
                                                rounded_bounds_used_for_all_coupling_intervals=True,
                                                rigorous_decimal_outer_interval=['0.01026686', '0.01026747']),
        moments=moments,
    )


def main():
    comparison, gram, means, c = compare_optimizers(DICTIONARY, M)
    heads = constrained_heads(DICTIONARY, gram, means)
    adaptive = adaptive_rows(DICTIONARY, gram, means, c)
    prime_product = finite_prime_product()
    out = dict(
        status='Research diagnostics. Floating optimizations are not interval proofs. Exact rational pieces are explicitly marked.',
        certificate_comparison=comparison, exact_head_energy_minimizers=heads,
        adaptive_retained_rows=adaptive, exact_finite_prime_product=prime_product,
    )
    with open('prime_tensor_crt_extended_diagnostics.json', 'w') as stream:
        json.dump(out, stream, indent=2)
    summary = dict(
        complete_error=comparison['complete_gram_minimizer']['actual_complete_squared_error'],
        optimizers=[{k: x[k] for k in ['label', 'solver_success', 'projected_gradient_inf',
                                       'certificate', 'actual_complete_squared_error']}
                    for x in comparison['certificate_minimizers']],
        exact_heads=[{k: x[k] for k in ['head', 'floating_feasible', 'complete_energy',
                                       'head_constraint_residual_inf', 'nullspace_stationarity_residual']}
                     for x in heads],
        adaptive_first_rows=adaptive['selected_rows'][:12],
        adaptive_row_count=len(adaptive['selected_rows']),
        adaptive_initial_certificate=adaptive['stages'][0]['column_certificate'],
        adaptive_final_certificate=adaptive['stages'][-1]['column_certificate'],
        omitted_prime_probability=[prime_product['omitted_prime_probability_interval'][k]
                                   for k in ['lower_decimal', 'upper_decimal']],
        all_polygamma_comparisons_inside_rational_enclosures=all(x['floating_inclusion_check']
                                                               for x in prime_product['moments']),
    )
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
```

## prime_tensor_cutoff_diagnostics.wl

```wolfram
(* Reproduce finite-product cutoff diagnostics. These are numerical checks,
   not interval certificates or a proof of the PNT asymptotic.
   Columns: T, delta_T, kappa_T, omitted-prime r_T,
   kappa_T/delta_T, T Log[T] kappa_T. *)
ClearAll[cutoff]; cutoff[t_Integer?Positive] := Module[{ps=Prime[Range[PrimePi[t]]], a, b, c, r, de, ka, m, q, power},
a=1; b=1; c=1;
Do[m=0; power=p; While[power<=t,m++;power*=p]; q=N[1/p^2,60];
a*= (1-q^(m+1))/(1-q);
b*= (1-q^m)/(1-q)^2+q^m;
c*=1-q,{p,ps}];
r=1-1/(N[Zeta[2],60]*c);
de=1-a/N[Zeta[2],60];
ka=a/N[Zeta[2],60]-b/N[Zeta[2]^2,60];
N[{t,de,ka,r,ka/de,t Log[t] ka},14]];
cutoff /@ {10,30,100,300,1000,10000}
```
