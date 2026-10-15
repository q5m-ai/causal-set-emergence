"""Finite diagnostics for CT1--CT12; not asymptotic or quadrature certificates.

The written class is arbitrary regular H and positive Omega. This evaluator is
explicitly narrower: a non-axial sine floor and a positive quadratic density.
Sobol cubatures retain masks and physical partner unions; two different pair
parameterizations are provided. No function substitutes a target for an action.
"""

from dataclasses import dataclass
from functools import lru_cache
import math

import numpy as np
from scipy.stats import qmc

from mixed_poisson import _unit_rule
from null_mixed import ACTION_CONSTANT, INTERVAL_CONSTANT


@dataclass(frozen=True)
class TwoTipConformal:
    a: float = 0.4
    T: float = 1.0
    axial: float = 0.12
    transverse: float = 0.08
    bt: float = 0.7
    bx: float = 0.2

    def __post_init__(self):
        values = (self.a, self.T, self.axial, self.transverse, self.bt, self.bx)
        e = abs(self.axial) + abs(self.transverse)
        # Stronger numerical root margins only, not the written theorem class.
        if (not all(math.isfinite(x) for x in values) or self.a <= 0
                or self.T <= 2*self.a or e >= min(0.3, (self.T-self.a)/2)
                or self.bt < 0 or self.bx < 0):
            raise ValueError("require a>0, T>2a, small finite sine floor and bt,bx>=0")

    def floor(self, x):
        return self.T + self.axial*np.sin(x[..., 0]) + self.transverse*np.sin(x[..., 1])

    def gradient(self, x):
        return np.stack((self.axial*np.cos(x[..., 0]),
                         self.transverse*np.cos(x[..., 1]), np.zeros(x.shape[:-1])), axis=-1)

    def density(self, p):
        return 1 + self.bt*p[..., 0]**2 + self.bx*np.sum(p[..., 1:]**2, axis=-1)

    def interval_factor(self, p, q):
        """Actual interior mean A, from full rest-diamond covariance."""
        p, q = np.broadcast_arrays(np.asarray(p, float), np.asarray(q, float))
        if p.shape[-1:] != (4,) or not np.all(np.isfinite(p)) or not np.all(np.isfinite(q)):
            raise ValueError("finite four-dimensional endpoints required")
        d, m = q-p, (p+q)/2
        r2 = np.sum(d[..., 1:]**2, axis=-1)
        sigma = d[..., 0]**2-r2
        if np.any(d[..., 0] < 0) or np.any(sigma < -1e-12*np.maximum(1, d[..., 0]**2)):
            raise ValueError("future causal endpoints required")
        return (self.density(m) + self.bt*(d[..., 0]**2/20-sigma/30)
                + self.bx*(r2/20+sigma/10))

    def bulk_density(self, p):
        """Independent 3 Omega Box Omega in the repository curvature sign."""
        aa = self.density(p)
        return (1.5*(self.bt-3*self.bx)/np.sqrt(aa)
                - 2.25*(self.bt**2*p[..., 0]**2
                        - self.bx**2*np.sum(p[..., 1:]**2, axis=-1))/aa**1.5)

    def radii(self, x):
        plus, minus = x.copy(), x.copy()
        plus[..., 0] -= self.a
        minus[..., 0] += self.a
        return np.linalg.norm(plus, axis=-1), np.linalg.norm(minus, axis=-1)


@lru_cache(maxsize=8)
def _sobol(power, dimensions):
    if not isinstance(power, int) or not 4 <= power <= 21:
        raise ValueError("Sobol power must be an integer from 4 to 21")
    result = qmc.Sobol(dimensions, scramble=True, seed=178).random_base2(power)
    result.flags.writeable = False
    return result


def _sphere(u, v):
    z, phi = 2*u-1, 2*np.pi*v
    return np.stack((z, np.sqrt(1-z*z)*np.cos(phi), np.sqrt(1-z*z)*np.sin(phi)), axis=-1)


def _kernel(z):
    return (1-9*z+8*z*z-4*z**3/3)*np.exp(-z)


def field(p):
    return .5 + .2*np.tanh(p[..., 0]+p[..., 1]+.7*p[..., 2])


def _matrix(weights, p, q):
    cp, cq = field(p), field(q)
    return np.array([[np.mean(weights*x*y) for y in (cq, 1-cq)] for x in (cp, 1-cp)])


def _validate(rho, region):
    if not math.isfinite(rho) or rho <= 0:
        raise ValueError("density must be finite and positive")
    if region not in ('lens', 'union', 'plus', 'minus'):
        raise ValueError("region must be lens, union, plus or minus")


def _points(model, samples, region):
    """Ordinary spatial-box/time parametrization; empty columns have zero mass."""
    B = model.T+abs(model.axial)+abs(model.transverse)+model.a
    x = (2*samples[:, :3]-1)*B
    rp, rm = model.radii(x)
    roof = {'lens': np.maximum(rp, rm), 'union': np.minimum(rp, rm),
            'plus': rp, 'minus': rm}[region]
    height = np.maximum(model.floor(x)-roof, 0)
    p = np.column_stack((-roof-height*samples[:, 3], x))
    return p, (2*B)**3*height


def future_pairs(model, rho, region='lens', power=17, cutoff=None):
    """CT3: q in the actual past set, then every causal predecessor above H.

    Returns point matrix and short/long pair matrices. Both masks are retained.
    Cutoff, if supplied, is one fixed sharp temporal gap (not a limit).
    """
    _validate(rho, region)
    if cutoff is not None and (not math.isfinite(cutoff) or cutoff <= 0):
        raise ValueError("cutoff must be finite and positive")
    s = _sobol(power, 8)
    q, dq = _points(model, s, region)
    n, b = _sphere(s[:, 4], s[:, 5]), np.cbrt(s[:, 6])
    direction = b[:, None]*n
    L = np.maximum(q[:, 0]+model.floor(q[:, 1:]), 0)
    for _ in range(40):
        L = np.maximum(q[:, 0]+model.floor(q[:, 1:]-L[:, None]*direction), 0)
    ell = L*s[:, 7]
    p = q - np.column_stack((ell, ell[:, None]*direction))
    sigma = ell*ell*(1-b*b)
    h = model.interval_factor(p, q)
    measure = dq*(4*np.pi/3)*L**4*s[:, 7]**3
    weights = measure*model.density(p)*model.density(q)*_kernel(INTERVAL_CONSTANT*rho*sigma*sigma*h)
    short = np.ones(len(s), bool) if cutoff is None else ell < cutoff
    return (_matrix(dq*model.density(q), q, q),
            _matrix(weights*short, p, q), _matrix(weights*~short, p, q))


def _diamond(p, tip, s):
    """Entire boosted rest diamond p->tip, sampled in clock-ball coordinates."""
    d = tip-p
    D2 = np.maximum(d[:, 0]**2-np.sum(d[:, 1:]**2, axis=-1), 0)
    D = np.sqrt(D2)
    length = np.linalg.norm(d[:, 1:], axis=-1)
    n = np.divide(d[:, 1:], length[:, None], out=np.zeros_like(d[:, 1:]), where=length[:, None] > 0)
    clock = s[:, 4]
    bound = np.minimum(clock, 1-clock)
    vec = (bound*np.cbrt(s[:, 5]))[:, None]*_sphere(s[:, 6], s[:, 7])
    longitudinal = np.sum(vec*n, axis=-1)
    q = np.empty_like(p)
    q[:, 0] = p[:, 0]+d[:, 0]*clock+length*longitudinal
    q[:, 1:] = (p[:, 1:]+clock[:, None]*d[:, 1:]+D[:, None]*vec
                 + ((d[:, 0]-D)*longitudinal)[:, None]*n)
    # d clock * volume of its radius-bound rest ball, and boost determinant D^4.
    measure = D2*D2*(4*np.pi/3)*bound**3
    return q, measure, D2 > 0


def source_pairs(model, rho, region='lens', power=17):
    """Independent source-first physical union/intersection; no future-gap map.

    Union samples the plus diamond and only the minus diamond's complement.
    It never sums overlapping partner volumes inside the nonlinear phase.
    """
    _validate(rho, region)
    s = _sobol(power, 8)
    p, dp = _points(model, s, region)
    pairs = np.zeros((2, 2))
    tips = [1] if region in ('lens', 'plus') else [-1] if region == 'minus' else [1, -1]
    for sign in tips:
        tip = np.array([0., sign*model.a, 0., 0.])
        q, dy, causal = _diamond(p, tip, s)
        active = (dp > 0) & causal
        rp, rm = model.radii(q[:, 1:])
        if region == 'lens':
            active &= -q[:, 0] >= rm
        if region == 'union' and sign == -1:
            active &= -q[:, 0] < rp
        # Invalid empty columns have zero mass and are never sent to the phase API.
        h = np.ones(len(s))
        h[active] = model.interval_factor(p[active], q[active])
        d = q-p
        sigma = np.maximum(d[:, 0]**2-np.sum(d[:, 1:]**2, axis=-1), 0)
        weights = dp*dy*active*model.density(p)*model.density(q)*_kernel(INTERVAL_CONSTANT*rho*sigma*sigma*h)
        pairs += _matrix(weights, p, q)
    return _matrix(dp*model.density(p), p, p), pairs


def complete_action(model, rho, region='lens', power=17, method='future'):
    if method == 'future':
        point, short, long = future_pairs(model, rho, region, power)
        pairs = short+long
    elif method == 'source':
        point, pairs = source_pairs(model, rho, region, power)
    else:
        raise ValueError("method must be future or source")
    return ACTION_CONSTANT*np.sqrt(rho)*(point-rho*pairs)


def _lens_coordinates(model, samples, ell=0., direction=None):
    """Resolve actual lens clock slices for the *small-gap diagnostic* only.

    z=s*zeta, R^2=s*(1-|zeta|)*(2a+s*(1+|zeta|)), depth=a+s.
    Upper S is solved against the actual translated non-axial floor. Numerical
    parameter margins guarantee a unique closing root in this small-gap use.
    """
    if not math.isfinite(ell) or abs(ell) >= (model.T-model.a)/8:
        raise ValueError("lens root diagnostic requires a small signed gap")
    zeta = 2*samples[:, 0]-1
    k, phi = np.sqrt(samples[:, 1]), 2*np.pi*samples[:, 2]
    direction = np.zeros((len(samples), 3)) if direction is None else direction

    def spatial(t):
        R = np.sqrt(t*(1-np.abs(zeta))*(2*model.a+t*(1+np.abs(zeta))))*k
        return np.column_stack((t*zeta, R*np.cos(phi), R*np.sin(phi)))

    S = np.full(len(samples), model.T-model.a-ell)
    for _ in range(40):
        S = model.floor(spatial(S)-ell*direction)-model.a-ell
    depth = S*samples[:, 3]
    x = spatial(depth)
    q = np.column_stack((-model.a-depth, x))
    jac = (2*np.pi*S*depth**2*(1-np.abs(zeta))
           * (2*model.a+depth*(1+np.abs(zeta))))
    return q, jac


def short_amplitude(model, ell, xi, power=16, source_field=None):
    """F_(3/2)/(4pi sqrt(1-xi)), retaining the moved floor and crease.

    Negative ell is only the Taylor extension, not physical reverse order.
    """
    if not math.isfinite(xi) or not 0 <= xi <= 1:
        raise ValueError("xi must lie in [0,1]")
    s = _sobol(power, 6)
    direction = np.sqrt(1-xi)*_sphere(s[:, 4], s[:, 5])
    q, jac = _lens_coordinates(model, s, ell, direction)
    p = q-np.column_stack((np.full(len(s), ell), ell*direction))
    # Polynomial whole-interval extension to signed ell, not a causal API call.
    h = (model.density((p+q)/2) + model.bt*ell*ell*(1/20-xi/30)
         + model.bx*ell*ell*((1-xi)/20+xi/10))
    chi = 1 if source_field is None else source_field(p)
    return float(np.mean(jac*model.density(p)*model.density(q)*h**(-1.5)*chi))


def residue_diagnostic(model, step=.005, power=16, source_field=None):
    if not math.isfinite(step) or not 0 < step < (model.T-model.a)/8:
        raise ValueError("step must be finite, positive and small")
    def second(xi, h):
        return (short_amplitude(model, h, xi, power, source_field)
                + short_amplitude(model, -h, xi, power, source_field)
                - 2*short_amplitude(model, 0, xi, power, source_field))/(2*h*h)
    def refined(xi):
        return (4*second(xi, step/2)-second(xi, step))/3
    return 8*refined(1)-6*refined(0)


def lens_target(model, power=18):
    """Independent curvature-volume and induced screen-area cubatures."""
    s = _sobol(power, 4)
    q, jac = _lens_coordinates(model, s)
    bulk = float(np.mean(jac*model.bulk_density(q)))
    # Integrate whole cap joint directions, retaining the actual far-sheet mask.
    n = _sphere(s[:, 0], s[:, 1])
    joint = 0.
    for sign in (1, -1):
        center = np.array([sign*model.a, 0., 0.])
        R = np.full(len(s), model.T)
        for _ in range(40):
            R = model.floor(center+R[:, None]*n)
        x = center+R[:, None]*n
        endpoint = np.column_stack((-R, x))
        joint += 4*np.pi*np.mean((sign*x[:, 0] < 0)*R*R*np.sqrt(model.density(endpoint)))
    return bulk, float(joint)


def axial_generator_terms(model, order=30):
    """Independent weighted CT10 test when transverse=0, chi=t.

    Axial symmetry is only this diagnostic's simplification, never the theorem.
    Returns bulk, joint, generator integral, and the nonzero crease endpoints.
    """
    if model.transverse != 0:
        raise ValueError("this separate generator quadrature requires transverse=0")
    nodes, weights = _unit_rule(order)
    bulk = 0.
    # Ordinary z, radius and time integral, split at the actual crease z=0.
    for sign in (-1, 1):
        Z = model.T-model.a
        for _ in range(40):
            Z = model.T+model.axial*np.sin(sign*Z)-model.a
        z = sign*Z*nodes[:, None, None]
        H = model.T+model.axial*np.sin(z)
        d = model.a+np.abs(z)
        R2 = (H*H-d*d)*nodes[None, :, None]
        roof = np.sqrt(d*d+R2)
        t = -roof-(H-roof)*nodes[None, None, :]
        aa = 1+model.bt*t*t+model.bx*(z*z+R2)
        bd = (1.5*(model.bt-3*model.bx)/np.sqrt(aa)
              -2.25*(model.bt**2*t*t-model.bx**2*(z*z+R2))/aa**1.5)
        measure = (np.pi*Z*(H*H-d*d)*(H-roof)*weights[:, None, None]
                   *weights[None, :, None]*weights[None, None, :])
        bulk += np.sum(measure*t*bd)
    joint, generator, crease = 0., 0., 0.
    for sign in (1, -1):
        mu = -sign*(model.a/model.T+(1-model.a/model.T)*nodes)
        wm = (1-model.a/model.T)*weights
        R = np.full(order, model.T)
        for _ in range(40):
            R = model.T+model.axial*np.sin(sign*model.a+R*mu)
        rc = model.a/np.abs(mu)
        rad = rc[:, None]+(R-rc)[:, None]*nodes[None, :]
        x2 = model.a**2+rad**2+2*sign*model.a*rad*mu[:, None]
        W = rad*rad*np.sqrt(1+model.bt*rad*rad+model.bx*x2)
        generator += 2*np.pi*np.sum(wm[:, None]*(R-rc)[:, None]*weights[None, :]*W)  # chi'=-1
        endx2 = model.a**2+R*R+2*sign*model.a*R*mu
        joint -= 2*np.pi*np.sum(wm*R**3*np.sqrt(1+model.bt*R*R+model.bx*endx2))
        cx2 = rc*rc-model.a**2
        crease -= 2*np.pi*np.sum(wm*rc**3*np.sqrt(1+model.bt*rc*rc+model.bx*cx2))
    return tuple(float(x) for x in (bulk, joint, generator, crease))
