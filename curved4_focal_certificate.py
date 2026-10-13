"""Validated CR18 model sign, NOT a physical complete-action coefficient.

Proof and explicit error bounds: notes/curved4-focal-certificate.md.
`--generate FILE` regenerates every nodal enclosure. `--replay FILE` only
replays arithmetic on recorded nodal evidence; it does NOT validate that
external evidence. Floating-point numbers select work, never prove bounds.
"""
from __future__ import annotations

import argparse
from concurrent.futures import ProcessPoolExecutor
from fractions import Fraction as F
from functools import lru_cache, wraps
import heapq
import json
import math
from pathlib import Path

import flint
from flint import acb, acb_poly, arb, ctx
from scipy.special import roots_jacobi

PRECISION = 192
FIXED_BITS = 40
SCHEMA = "curved4-matched-quartic-model-v1"
SCOPE = "normalized model only; no physical-action coefficient established"
EPSILON = F(1, 100)
TOP = F(256)


class CertificateFailure(RuntimeError):
    """An enclosure or required strict inequality was not established."""


def require(condition, message):
    if not condition:
        raise CertificateFailure(message)


def precise(function):
    @wraps(function)
    def run(*args, **kwargs):
        with ctx.workprec(PRECISION):
            return function(*args, **kwargs)
    return run


def ball(value):
    if isinstance(value, F):
        return arb(value.numerator) / value.denominator
    return arb(value)


def binomial(a, n):
    answer = F(1)
    for j in range(n):
        answer *= (a-j)/(j+1)
    return answer


def multiply(a, b):
    out = [F(0)]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i+j] += x*y
    return out


def integrate_polynomial(coefficients):
    return sum((x/F((j+1)*2**j) for j, x in enumerate(coefficients)
                if j % 2 == 0), F(0))


def primary_coefficient(j):
    moment = math.prod(F(2*k+1, 2*(k+3)) for k in range(j))
    coefficients = [F(0)]*(2*j+1)
    for k in range(j+1):
        coefficients[2*k] = (moment*binomial(-F(2*j+1, 2), j+k)
                             * math.comb(j+k, 2*k)*4**(2*k))
    return coefficients


def primary_majorant(j):
    return (F(math.comb(4*j, 2*j))
            * math.prod(F(2*k+1, 2*(k+3)) for k in range(j)))


def arctan_bounds(x, terms=12):
    partial = sum(((-1)**j*x**(2*j+1)/(2*j+1)
                   for j in range(terms)), F(0))
    next_term = x**(2*terms+1)/(2*terms+1)
    return ((partial, partial+next_term) if terms % 2 == 0
            else (partial-next_term, partial))


def head_bound_checks():
    """Exact rational checks for CC3--CC8; not a numerical fit."""
    p, e = F(9, 7), EPSILON
    coefficients = [[F(1)]]+[primary_coefficient(j) for j in range(1, 5)]
    inverse = [[F(1)]]
    for n in range(1, 4):
        result = [F(0)]*(2*n+1)
        for k in range(1, n+1):
            product = multiply(coefficients[k], inverse[n-k])
            for j, value in enumerate(product):
                result[j] += ((1-p)*k-n)*value/n
        inverse.append(result)
    means = [integrate_polynomial(x) for x in inverse[1:]]
    checks = {
        "primary inverse means": means == [-p/6, -F(249, 784), -F(64983, 38416)],
        "coefficient norms": all(
            integrate_polynomial(multiply(coefficients[j], coefficients[j])) < bound**2
            for j, bound in enumerate((F(41, 100), F(6, 5), F(31, 5), F(43)), 1)),
        "primary fourth remainder norm": 43+primary_majorant(5)*e/(1-16*e) < 69,
        "primary pointwise norm": 1+primary_majorant(2)*e+primary_majorant(3)*e**2/(1-16*e) < F(21, 20),
        "primary L2 norm": F(41, 100)+F(6, 5)*e+F(31, 5)*e**2+69*e**3 < F(423, 1000),
        "quadratic Taylor error": 2*F(41, 100)*(F(31, 5)+69*e)+(F(6, 5)+F(31, 5)*e+69*e**2)**2 < F(73, 10),
        "cubic Taylor error": (F(6, 5)+F(31, 5)*e+69*e**2)*(F(21, 20)**2+F(21, 20)+1) < F(401, 100),
        "fourth Taylor coefficient": p*(p+1)*(p+2)*(p+3)/24/(1-F(21, 20)*e)**6 < 2,
        "averaged fourth remainder": 69*p+F(73, 10)*p*(p+1)/2+F(401, 100)*p*(p+1)*(p+2)/6+2*F(21, 20)**2*F(423, 1000)**2 < 110,
        "primary averaged head": F(249, 784)+F(17, 10)*e+110*e**2 < F(7, 20),
        "primary lower bound": F(1, 4)+primary_majorant(2)*e+primary_majorant(3)*e**2/(1-16*e) < F(3, 10),
    }
    s, k, root = F(969, 1000), F(469, 500), F(857, 1000)
    checks.update({
        "secondary source range": k**2 < 1-12*e and (1+k)/2 == s,
        "secondary root bound": F(305, 1000)**2 > 3*(1-s) and (4*s-1-F(305, 1000))/3 >= root,
        "secondary Morse radius": k*root**2 > F(2, 3),
        "secondary first correction": F(31, 36)/k**2+F(5, 18)/(k**3*(k+1)) < F(6, 5),
        "secondary series": F(6, 5)+F(315, 32)*e/(1-24*e) < F(4, 3),
        "secondary density chord": (1-12*e)*(1+F(33, 10)*e)**4 > 1,
        "opening Jacobian chord": s**3*(1+5*e)**2 > 1,
        "secondary total": F(33, 10)+F(11, 10)*e < F(17, 5),
        "negative power bound": (1-F(3, 10)*e)**-4 < F(51, 50),
        "a0 upper bound": F(41, 50)**7*F(471, 400)**9 > 1,
        "quartic upper tail": F(16, 7)**27 < 6**14,
    })
    lo1, hi1 = arctan_bounds(F(1, 5))
    lo2, hi2 = arctan_bounds(F(1, 239))
    checks["Machin pi bounds"] = F(157, 50) < 16*lo1-4*hi2 and 16*hi1-4*lo2 < F(22, 7)
    dminus = F(51, 50)*(p*(p+1)/10+17*p/35)
    dplus = F(51, 50)*(7*p*(p+1)/20+17*p/35)
    checks["lower head constant"] = F(41, 50)*(F(7, 20)+(F(21, 20)*dminus+5*p/12)/2) < 1
    checks["upper head constant"] = F(41, 50)*(F(7, 20)+(F(21, 20)*dplus+5*p/12)/2) < 2
    require(all(checks.values()), "failed rational checks: "+", ".join(k for k, v in checks.items() if not v))
    return checks


def gegenbauer(n, x):
    if n == 0:
        return arb(1)
    theta, sine = x.acos(), (1-x*x).sqrt()
    return (((n+2)*theta).sin()*x-(n+2)*((n+2)*theta).cos()*sine)/(2*sine**3)


@lru_cache(None)
@precise
def gaussian_rule(n):
    require(n >= 4 and n % 2 == 0, "Gaussian order must be even and at least four")
    seeds, _ = roots_jacobi(n, 1.5, 1.5)
    nodes, brackets = [], []
    for seed in seeds:
        lo, hi = arb(float(seed))-arb(2)**-40, arb(float(seed))+arb(2)**-40
        flo, fhi = gegenbauer(n, lo), gegenbauer(n, hi)
        require(-1 < lo < hi < 1 and flo*fhi < 0, "unvalidated Gaussian root seed")
        for _ in range(70):
            mid = (lo+hi)/2
            fm = gegenbauer(n, mid)
            require(fm > 0 or fm < 0, "indeterminate root bisection sign")
            if fm*flo > 0:
                lo, flo = mid, fm
            else:
                hi = mid
        x = lo.union(hi)
        brackets.append(x)
        # Avoid interval-recurrence blowup. This derivative bound follows
        # from |(C_(n-1)^2)'| <= 4*C_(n-2)^3(1).
        prev = gegenbauer(n-1, x.mid())+arb(0, 4*math.comb(n+3, 5)*x.rad())
        weight = arb.pi()*(n+1)*(n+2)*(1-x*x)/(64*(n+3)*prev*prev)
        require(weight > 0, "Gaussian weight not proven positive")
        nodes.append(((x+1)/2, weight))
    require(all(a.upper() < b.lower() for a, b in zip(brackets, brackets[1:])), "overlapping Gaussian roots")
    require(sum(w for _, w in nodes).contains(3*arb.pi()/128), "Gaussian mass check failed")
    return tuple(nodes)


@lru_cache(None)
def binomial_tail(n):
    return abs(binomial(F(1, 2), n))


def real_roots(e, r):
    roots = acb_poly([-e, 0, 1, 4*r, 1]).roots(tol=1e-24, maxprec=512)
    real = sorted((z.real for z in roots if z.imag.contains(0)), key=lambda x: float(x.mid()))
    require(len(real) in (2, 4), "real quartic root count not certified")
    require(all(a.upper() < b.lower() for a, b in zip(real, real[1:])), "quartic roots not separated")
    return real


def profile_from_roots(e, r, roots):
    total = arb(0)
    for lo, hi in zip(roots[::2], roots[1::2]):
        length = hi-lo
        cc = 4*r+lo+hi
        dd = 1+cc*(lo+hi)-lo*hi
        qlo, qhi = lo*lo+cc*lo+dd, hi*hi+cc*hi+dd
        maximum = max(qlo.upper(), qhi.upper())
        vertex = -cc/2
        if vertex.upper() < lo.lower() or vertex.lower() > hi.upper():
            minimum = max(arb(0), min(qlo.lower(), qhi.lower()))
        else:
            minimum = max(arb(0), (dd-cc*cc/4).lower())
        require(maximum > 0, "nonpositive quadratic range")
        center = (maximum+minimum)/2
        # If the lower bound is zero, the range argument proves eta=1
        # exactly; do not accept an indeterminate floating comparison.
        eta = arb(1) if minimum == 0 else (maximum-minimum)/(maximum+minimum)
        require(eta.is_finite() and eta.upper() <= 1, "unproved binomial domain")
        n = 32
        while True:
            value, moment = arb(0), arb(0)
            for t, weight in gaussian_rule(n):
                x = lo+length*t
                q = x*x+cc*x+dd
                require(q > 0, "Gaussian quadratic value not positive")
                value += weight*q.sqrt()**3
                moment += weight*abs(q/center-1)**(n-2)
            error = 2*center**(arb(3)/2)*ball(binomial_tail(n-2))*moment
            if n >= 512 or error < arb("1e-8")*value.abs_lower():
                break
            n *= 2
        total += length**4*(value+arb(0, error.upper()))
    require(total.is_finite() and total > 0, "nonpositive or nonfinite profile enclosure")
    return total


@precise
def profile_and_derivative(e, r):
    """Enclose f(E,r) and its r derivative; roots, wells and errors retained."""
    e, r = ball(e), ball(r)
    require(e > 0 and r.lower() >= 0 and r.upper() <= arb(1)/2, "require E>0 and 0<=r<=1/2")
    if e == arb(1)/16 and r == arb(1)/2:
        return 1/(70*arb(2).sqrt()), 17/(20*arb(2).sqrt())
    roots = real_roots(e, r)
    value = profile_from_roots(e, r, roots)
    if r == 0:
        return value, arb(0)
    derivative = acb(0)
    for lo, hi in zip(roots[::2], roots[1::2]):
        length = hi-lo
        cc = 4*r+lo+hi
        dd = 1+cc*(lo+hi)-lo*hi
        def integrand(t, analytic):
            x = lo+length*t
            q = x*x+cc*x+dd
            return (x**3*t.sqrt(analytic=analytic)*(1-t).sqrt(analytic=analytic)
                    * q.sqrt(analytic=analytic))
        derivative += -6*length**2*acb.integral(
            integrand, 0, 1, abs_tol=1e-16, rel_tol=1e-12,
            eval_limit=10000, depth_limit=35)
    require(derivative.is_finite(), "nonfinite derivative enclosure")
    return value, derivative.real


@precise
def certify_phi(e, relative_goal=1e-5, max_nodes=20000):
    """Real-variable r quadrature using CC9, including all transitions."""
    e, p = ball(e), arb(9)/7
    require(e > 0 and relative_goal > 0 and max_nodes >= 2, "invalid Phi request")
    count = 0
    def data(r):
        nonlocal count
        count += 1
        return profile_and_derivative(e, r)
    def cell(lo, hi, left, right):
        fa, da = left
        fb, db = right
        lower = fa.lower()
        dbu, dal = max(arb(0), db.upper()), max(arb(0), da.lower())
        df = max(arb(0), fb.upper()-fa.lower())
        dd = max(arb(0), dbu-dal)
        variation = p*(p+1)*lower**(-p-2)*dbu*df+p*lower**(-p-1)*dd
        error = ((hi-lo)**2*variation/8).upper()
        value = (hi-lo)*(fa**(-p)+fb**(-p))/2
        return value, error, lo, hi, left, right
    lo, hi = arb(0), arb(1)/2
    initial = cell(lo, hi, data(lo), data(hi))
    heap = [(-float(initial[1]), 0, initial)]
    error, value, sequence = float(initial[1]), float(initial[0].mid()), 0
    # Floating decisions only choose a partition. The returned enclosure is
    # recomputed from ALL final cells with ball arithmetic, irrespective of
    # whether this work goal or the node cap stopped refinement.
    while error > relative_goal*abs(value) and count < max_nodes:
        _, _, old = heapq.heappop(heap)
        old_value, old_error, lo, hi, left, right = old
        mid = (lo+hi)/2
        middle = data(mid)
        a, b = cell(lo, mid, left, middle), cell(mid, hi, middle, right)
        error += float(a[1])+float(b[1])-float(old_error)
        value += float(a[0].mid())+float(b[0].mid())-float(old_value.mid())
        for sub in (a, b):
            sequence += 1
            heapq.heappush(heap, (-float(sub[1]), sequence, sub))
    total = 2*sum((c[0]+arb(0, c[1]) for _, _, c in heap), arb(0))
    require(total.is_finite() and total > 0, "Phi enclosure failed")
    return total, count


@precise
def energy_error(lo, hi):
    """CC10 and the E-trapezoid Peano bound; rational endpoints."""
    require(F(0) < lo < hi, "energy interval must be positive and ordered")
    a, b, h = ball(lo).lower(), ball(hi).upper(), ball(hi-lo).upper()
    p, c = arb(9)/7, 3*arb.pi()/8
    minimum = c*a*a/(1+4*a.sqrt()).sqrt()
    radius = (1+(1+4*b.sqrt()).sqrt())/2
    maximum = 3*radius*b.sqrt()
    if b < arb(1)/16:
        maximum = min(maximum, (c*b*(2+4/(1-4*b.sqrt()).sqrt())).upper())
    averaged_second = arb(2)/5+6*max(arb(1), a**(-arb(1)/4))
    bound = (p*(p+1)*minimum**(-p-2)*maximum**2
             + p*minimum**(-p-1)*averaged_second)
    return (h**3*bound/12).upper()


def energy_partition(work_goal=.08):
    require(work_goal > 0 and math.isfinite(work_goal), "invalid work goal")
    edges = [EPSILON]
    while edges[-1] < TOP:
        edges.append(min(2*edges[-1], TOP))
    heap, sequence = [], 0
    for lo, hi in zip(edges, edges[1:]):
        error = energy_error(lo, hi)
        heapq.heappush(heap, (-float(error), sequence, (lo, hi)))
        sequence += 1
    total = sum(-item[0] for item in heap)
    while total > work_goal:
        old, _, (lo, hi) = heapq.heappop(heap)
        mid = (lo+hi)/2
        errors = [energy_error(lo, mid), energy_error(mid, hi)]
        total += old+sum(float(x) for x in errors)
        for bounds, error in zip(((lo, mid), (mid, hi)), errors):
            heapq.heappush(heap, (-float(error), sequence, bounds))
            sequence += 1
    return sorted((item[2] for item in heap), key=lambda x: x[0])


@precise
def fixed_enclosure(value):
    """Outward dyadic endpoints. JSON integers must not be read as binary64."""
    scale = arb(2)**FIXED_BITS
    lower = int((value.lower()*scale).floor().unique_fmpz())
    upper = int((value.upper()*scale).ceil().unique_fmpz())
    return lower, upper


def generate_node(pair):
    numerator, denominator = pair
    value, count = certify_phi(F(numerator, denominator))
    lower, upper = fixed_enclosure(value)
    return [numerator, denominator, lower, upper, count]


@precise
def replay(receipt):
    """Arithmetic replay only. External nodal evidence is NOT authenticated."""
    head_bound_checks()
    require(receipt.get("schema") == SCHEMA and receipt.get("scope") == SCOPE, "wrong certificate scope")
    require(receipt.get("fixed_bits") == FIXED_BITS, "wrong fixed-point format")
    rows = receipt.get("nodes", [])
    require(len(rows) >= 2, "missing nodal evidence")
    points, values = [], []
    for row in rows:
        require(isinstance(row, list) and len(row) == 5 and all(type(x) is int for x in row), "malformed nodal evidence")
        numerator, denominator, lower, upper, count = row
        require(denominator > 0 and 0 < lower <= upper and count >= 2, "invalid nodal bounds")
        point = F(numerator, denominator)
        require(not points or point > points[-1], "unordered or duplicate nodes")
        points.append(point)
        scale = arb(2)**-FIXED_BITS
        values.append((arb(lower)*scale).union(arb(upper)*scale))
    require(points[0] == EPSILON and points[-1] == TOP, "incomplete energy interval")
    integral, error = arb(0), arb(0)
    for i, (lo, hi) in enumerate(zip(points, points[1:])):
        integral += ball(hi-lo)*(values[i]+values[i+1])/2
        error += energy_error(lo, hi)
    integral += arb(0, error.upper())
    p, c = arb(9)/7, 3*arb.pi()/8
    a0 = c**(-p)
    opening = acb.integral(
        lambda t, analytic: (-p*(1+t*t).log(analytic=analytic)).exp(),
        0, 1, abs_tol=1e-35, rel_tol=1e-35).real
    require(opening.is_finite(), "opening subtraction enclosure failed")
    a1 = a0*(-p/6+(opening-1)/2)
    epsilon = ball(EPSILON)
    middle = integral-arb(7)/11*a0*epsilon**(-arb(11)/7)-arb(7)/4*a1*epsilon**(-arb(4)/7)
    head = (-arb(7)/3*epsilon**(arb(3)/7)).union(arb(14)/3*epsilon**(arb(3)/7))
    tail = arb(0).union(arb(3)/640)
    answer = middle+head+tail
    return {"finite_integral": integral, "energy_quadrature_error": error,
            "subtracted_middle": middle, "head": head, "tail": tail,
            "matched_model_I": answer}


def generate(path, workers=1):
    require(type(workers) is int and workers >= 1, "worker count must be positive")
    partition = energy_partition()
    points = sorted({x for interval in partition for x in interval})
    pairs = [(x.numerator, x.denominator) for x in points]
    print(f"Regenerating {len(points)} nodal enclosures with {workers} worker(s).", flush=True)
    receipt = {"schema": SCHEMA, "scope": SCOPE, "fixed_bits": FIXED_BITS,
               "precision_bits": PRECISION, "python_flint": flint.__version__, "nodes": []}
    with ProcessPoolExecutor(max_workers=workers) as pool:
        for i, row in enumerate(pool.map(generate_node, pairs)):
            receipt["nodes"].append(row)
            if i % 100 == 0:
                print(f"Enclosed {i+1}/{len(points)} nodes", flush=True)
    result = replay(receipt)
    require(result["matched_model_I"] > arb(1)/4 and result["matched_model_I"] < arb(3)/2,
            "requested model sign enclosure not established")
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(receipt, separators=(",", ":"))+"\n")
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--generate", type=Path, help="regenerate every enclosure and save its receipt")
    mode.add_argument("--replay", type=Path, help="arithmetic replay only; trusts recorded nodal evidence")
    mode.add_argument("--head-checks", action="store_true", help="exact rational CC3--CC8 checks")
    parser.add_argument("--workers", type=int, default=1)
    args = parser.parse_args()
    if args.head_checks:
        print(f"Passed {len(head_bound_checks())} exact rational checks (not the finite integration).")
        return
    if args.generate:
        result = generate(args.generate, args.workers)
        print("Every nodal enclosure regenerated; scope:", SCOPE)
    else:
        result = replay(json.loads(args.replay.read_text()))
        print("Arithmetic replay ONLY; nodal evidence was not regenerated.")
    with ctx.workprec(PRECISION):
        for name, value in result.items():
            print(name, value.str(18, more=True))


if __name__ == "__main__":
    main()
