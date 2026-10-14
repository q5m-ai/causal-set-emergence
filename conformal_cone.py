"""Finite diagnostics for the whole-class written proof in conformal-cone-limit.md.

The evaluator deliberately specializes to a sine floor and the physical density
 a=Omega**4=1+bt*t**2+bx*|x|**2, not to the full smooth theorem class.
Two different complete pair domains are integrated. Neither evaluates a target
in place of an action, uses a weighted Gaussian shortcut, or certifies errors.
"""

from dataclasses import dataclass
from functools import lru_cache
import math

import numpy as np
from scipy.special import roots_jacobi

from mixed_poisson import _unit_rule
from null_mixed import ACTION_CONSTANT, INTERVAL_CONSTANT


@dataclass(frozen=True)
class QuadraticCone:
    """Nonplanar diagnostic member; bt,bx are density, not Omega coefficients."""

    T: float = 1.0
    epsilon: float = 0.18
    bt: float = 0.7
    bx: float = 0.2

    def __post_init__(self):
        if (not all(math.isfinite(x) for x in (self.T, self.epsilon, self.bt, self.bx))
                or self.T <= abs(self.epsilon) or abs(self.epsilon) >= 0.5
                or self.bt < 0 or self.bx < 0):
            raise ValueError("require T>|epsilon|, |epsilon|<1/2 and bt,bx>=0, finite")

    def floor(self, x1):
        return self.T + self.epsilon*np.sin(x1)

    def density(self, t, r2):
        return 1 + self.bt*t*t + self.bx*r2

    def root(self, slope, shift=0.0, gap=0.0):
        """Solve v+gap=H(v*slope-shift), including the smooth closing extension.

        All call sites have |slope|<=1. This diagnostic's contraction constant
        is <1/2, so 64 iterations leave only floating-point error, not a proof
        certificate. The written theorem instead uses the implicit theorem.
        """
        slope, shift, gap = np.broadcast_arrays(slope, shift, gap)
        if (np.any(~np.isfinite(slope)) or np.any(np.abs(slope) > 1)
                or np.any(~np.isfinite(shift)) or np.any(~np.isfinite(gap))):
            raise ValueError("require finite parameters and |slope|<=1")
        v = np.broadcast_to(self.T-gap, slope.shape)
        for _ in range(64):
            v = self.T-gap + self.epsilon*np.sin(slope*v-shift)
        return v

    def interval_factor(self, p, q):
        """Exact V/(c*sigma**2) for this quadratic a, including null endpoints.

        Midpoint covariance is derived from the full rest diamond, with both
        longitudinal tips. The formula also has the smooth diagonal extension.
        """
        p, q = np.broadcast_arrays(np.asarray(p, float), np.asarray(q, float))
        if p.shape[-1:] != (4,) or np.any(~np.isfinite(p)) or np.any(~np.isfinite(q)):
            raise ValueError("require finite four-dimensional endpoints")
        d, m = q-p, (p+q)/2
        ell2 = d[..., 0]**2
        r2 = np.sum(d[..., 1:]**2, axis=-1)
        sigma = ell2-r2
        if np.any(d[..., 0] < 0) or np.any(sigma < -1e-12*np.maximum(1, ell2)):
            raise ValueError("require future causal endpoints")
        return (self.density(m[..., 0], np.sum(m[..., 1:]**2, axis=-1))
                + self.bt*(ell2/20-sigma/30)
                + self.bx*(r2/20+sigma/10))

    def bulk_density(self, t, r2):
        """Independently 3*Omega*Box(Omega) in #90's curvature convention."""
        a = self.density(t, r2)
        return (1.5*(self.bt-3*self.bx)/np.sqrt(a)
                - 2.25*(self.bt**2*t*t-self.bx**2*r2)/a**1.5)


def _rho(rho):
    if not math.isfinite(rho) or rho <= 0:
        raise ValueError("density must be finite and positive")


def partition(t, x1):
    """A smooth two-cell partition, with nonzero cross-cell causal pairs."""
    return 0.5 + 0.2*np.tanh(t+x1)


def _accumulate(total, weighted_kernel, p, q):
    """All four ordered chart pairs; diagnostic fields depend on t,x1 only."""
    cp, cq = partition(*p), partition(*q)
    for i, source in enumerate((cp, 1-cp)):
        for j, target in enumerate((cq, 1-cq)):
            total[i, j] += np.sum(weighted_kernel*source*target)


def point_and_target(model, order=24):
    """Independent ordinary polar source integral and induced screen integral."""
    nodes, weights = _unit_rule(order)
    point = np.zeros((2, 2))
    bulk, joint = 0.0, 0.0
    for mu, wm in zip(2*nodes-1, 2*weights):
        R = float(model.root(mu))
        r = R*nodes[:, None]
        height = model.floor(r*mu)
        depth = r+(height-r)*nodes[None, :]
        measure = (2*np.pi*wm*R*r*r*(height-r)
                   *weights[:, None]*weights[None, :])
        a = model.density(-depth, r*r)
        cp = partition(-depth, r*mu)
        for i, source in enumerate((cp, 1-cp)):
            for j, target in enumerate((cp, 1-cp)):
                point[i, j] += np.sum(measure*a*source*target)
        bulk += np.sum(measure*model.bulk_density(-depth, r*r))
        joint += 2*np.pi*wm*R*R*np.sqrt(model.density(-R, R*R))
    return point, float(bulk), float(joint)


def _kernel(z):
    return (1-9*z+8*z*z-4*z**3/3)*np.exp(-z)


def cone_ball_pairs(model, rho, order=8, min_gap=0.0, max_gap=None):
    """CC3--CC4 full physical pairs, in a retained fixed temporal band.

    Returns a 2x2 ordered endpoint-partition matrix, not subregion actions.
    The angular symmetry used here is specific to the diagnostic model/fields.
    sqrt(1-xi) is integrated by a Jacobi rule. No high-density accuracy promise.
    """
    _rho(rho)
    if (not math.isfinite(min_gap) or min_gap < 0
            or (max_gap is not None and (not math.isfinite(max_gap) or max_gap <= min_gap))):
        raise ValueError("require a finite nonnegative lower gap and larger upper gap")
    nodes, weights = _unit_rule(order)
    xis, wx = roots_jacobi(order, 0.5, 0)
    xis, wx = (xis+1)/2, wx/2**1.5
    # Remaining axes: ell, ball radius k, ball polar mu, v fraction y, n azimuth.
    k = nodes[None, :, None, None, None]
    mu = (2*nodes-1)[None, None, :, None, None]
    y = nodes[None, None, None, :, None]
    psi = np.arange(2*order)*np.pi/order
    cp = np.cos(psi)[None, None, None, None, :]
    base = (weights[:, None, None, None, None]
            * weights[None, :, None, None, None]*k*k
            * (2*weights)[None, None, :, None, None]
            * weights[None, None, None, :, None] * (2*np.pi)*(np.pi/order))
    total = np.zeros((2, 2))
    for xi, w_xi in zip(xis, wx):
        b = np.sqrt(1-xi)
        for nu, wn in zip(2*nodes-1, 2*weights):
            L = float(model.root(-b*nu))
            hi = min(L, max_gap) if max_gap is not None else L
            if hi <= min_gap:
                continue
            ell = (min_gap+(hi-min_gap)*nodes)[:, None, None, None, None]
            U = model.root(k*mu, ell*b*nu, ell)
            v = U*y
            r2q = (v*k)**2
            dot = v*k*(mu*nu+np.sqrt(1-mu*mu)*np.sqrt(1-nu*nu)*cp)
            r2p = r2q+(ell*b)**2-2*ell*b*dot
            t_q, t_p = -v, -v-ell
            # The actual averaged interior density, not an endpoint substitute.
            h = (1 + model.bt*(v*v+v*ell+ell*ell*(0.3-xi/30))
                 + model.bx*(r2q-ell*b*dot+ell*ell*(0.3-xi/5)))
            phase = INTERVAL_CONSTANT*rho*ell**4*xi*xi*h
            measure = (0.5*ell**3 * U**4*y**3 * (hi-min_gap)
                       * base * wn*w_xi)
            integrand = measure*model.density(t_p, r2p)*model.density(t_q, r2q)*_kernel(phase)
            _accumulate(total, integrand, (t_p, v*k*mu-ell*b*nu), (t_q, v*k*mu))
    return total


@lru_cache(maxsize=6)
def _polar_diamond(order):
    """Independent spherical clock sections of the unit-duration rest diamond."""
    nodes, weights = _unit_rule(order)
    t = np.r_[nodes/2, (1+nodes)/2][:, None, None, None]
    wt = np.tile(weights/2, 2)[:, None, None, None]
    bound = np.minimum(t, 1-t)
    r = bound*nodes[None, :, None, None]
    mu = (2*nodes-1)[None, None, :, None]
    psi = (np.arange(2*order)*np.pi/order)[None, None, None, :]
    measure = (wt*bound*r*r*weights[None, :, None, None]
               * (2*weights)[None, None, :, None] * np.ones_like(psi)*np.pi/order)
    values = np.broadcast_arrays(t, r*mu, r*np.sqrt(1-mu*mu)*np.cos(psi), r*r, measure)
    result = tuple(x.ravel() for x in values)
    for x in result:
        x.flags.writeable = False
    return result


def source_tip_pairs(model, rho, order=8):
    """Independent full source-to-tip pair integration; no cone-ball domain.

    Ordinary source (r,mu,t), then each ENTIRE boosted rest diamond p->0.
    Computes the same signed matrix with a different pair-domain quadrature.
    The shared polynomial interval formula is separately tested against direct
    interior-point cubature; neither pair rule uses the limit or a Gaussian.
    """
    _rho(rho)
    nodes, weights = _unit_rule(order)
    t, bpar, bperp, rest_r2, dw = _polar_diamond(order)
    total = np.zeros((2, 2))
    for mu, wm in zip(2*nodes-1, 2*weights):
        R = float(model.root(mu))
        for r, wr in zip(R*nodes, R*weights):
            H = model.floor(r*mu)
            depth = (r+(H-r)*nodes)[:, None]
            sigma = depth*depth-r*r
            t_q = -depth+depth*t+r*bpar
            longitudinal = r*(1-t)-depth*bpar
            r2q = longitudinal**2+sigma*(rest_r2-bpar*bpar)
            x1q = longitudinal*mu+np.sqrt(sigma)*bperp*np.sqrt(1-mu*mu)
            ell = depth+t_q
            s_pq = sigma*(t*t-rest_r2)
            mid_r2 = (r+longitudinal)**2/4+sigma*(rest_r2-bpar*bpar)/4
            h = (model.density((-depth+t_q)/2, mid_r2)
                 + model.bt*(ell*ell/20-s_pq/30)
                 + model.bx*((ell*ell-s_pq)/20+s_pq/10))
            phase = INTERVAL_CONSTANT*rho*s_pq*s_pq*h
            measure = (2*np.pi*wm*wr*r*r*(H-r)*weights[:, None]
                       * sigma*sigma*dw)
            integrand = (measure*model.density(-depth, r*r)
                         *model.density(t_q, r2q)*_kernel(phase))
            _accumulate(total, integrand, (-depth, r*mu), (t_q, x1q))
    return total


def complete_action(model, rho, order=8, method="cone"):
    """Unchanged point-minus-pair observable, never a target-valued function."""
    _rho(rho)
    if method not in ("cone", "source"):
        raise ValueError("method must be cone or source")
    point, _, _ = point_and_target(model, max(16, order))
    pairs = (cone_ball_pairs if method == "cone" else source_tip_pairs)(model, rho, order)
    return ACTION_CONSTANT*np.sqrt(rho)*(point-rho*pairs)


def short_amplitude(model, ell, xi, mellin=1.5, order=12,
                    source_field=None, target_field=None):
    """F_s/(4*pi*sqrt(1-xi)) from the smooth actual moving-floor formula.

    xi=0 and xi=1 use the divided expression, not 0/0. Small negative ell
    is the analytic Taylor extension only, not a second physical-order claim.
    Its finite differences test CC8--CC9 independently of the target evaluator.
    """
    if (not all(math.isfinite(x) for x in (ell, xi, mellin)) or not 0 <= xi <= 1
            or abs(ell) >= model.T/(4*(1+abs(model.epsilon)))):
        raise ValueError("require a small signed gap and 0<=xi<=1")
    nodes, weights = _unit_rule(order)
    k = nodes[:, None, None, None]
    mu = (2*nodes-1)[None, :, None, None]
    y = nodes[None, None, :, None]
    cp = np.cos(np.arange(2*order)*np.pi/order)[None, None, None, :]
    base = (k*k*weights[:, None, None, None]*(2*weights)[None, :, None, None]
            *weights[None, None, :, None] * (2*np.pi)/(2*order))
    b, total = np.sqrt(1-xi), 0.0
    for nu, wn in zip(2*nodes-1, weights):  # n sphere average: dnu/2 and dpsi/(2pi)
        U = model.root(k*mu, ell*b*nu, ell)
        v = U*y
        r2q = (v*k)**2
        dot = v*k*(mu*nu+np.sqrt(1-mu*mu)*np.sqrt(1-nu*nu)*cp)
        r2p = r2q+(ell*b)**2-2*ell*b*dot
        h = (1+model.bt*(v*v+v*ell+ell*ell*(0.3-xi/30))
             + model.bx*(r2q-ell*b*dot+ell*ell*(0.3-xi/5)))
        source = 1 if source_field is None else source_field(-v-ell, v*k*mu-ell*b*nu)
        target = 1 if target_field is None else target_field(-v, v*k*mu)
        total += wn*np.sum(base*U**4*y**3 * model.density(-v-ell, r2p)
                           *model.density(-v, r2q)*source*target*h**(-mellin))
    return float(total)


def residue_target_diagnostic(model, step=0.004, order=12,
                              source_field=None, target_field=None):
    """Finite-difference diagnostic of -16 Q2 = 8 G2(1)-6 G2(0), not proof."""
    if not math.isfinite(step) or not 0 < step < model.T/(4*(1+abs(model.epsilon))):
        raise ValueError("require a strictly positive small finite difference step")
    def amplitude(ell, xi):
        return short_amplitude(model, ell, xi, order=order,
                               source_field=source_field, target_field=target_field)

    def second(xi, h):
        return (amplitude(h, xi)+amplitude(-h, xi)-2*amplitude(0, xi))/(2*h*h)

    def extrapolated(xi):
        return (4*second(xi, step/2)-second(xi, step))/3

    return 8*extrapolated(1)-6*extrapolated(0)
