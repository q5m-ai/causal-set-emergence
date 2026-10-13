"""Physical pendulum/source-family diagnostics for the written CG1--CG10.

Minimizers are selected using the classification proved in the note, not an
assumed finite branch list. These floating-point routines are diagnostics,
not certified interval-volume integration or a complete-action solver.
The principal source factor is used in the separate written complete-action
proof. Its floating evaluation is not a substitute for that proof or for the
separately regenerated model certificate.
"""
from dataclasses import dataclass
import math

from scipy.integrate import quad
from scipy.optimize import brentq
from scipy.special import ellipe, ellipeinc, ellipj, ellipk, ellipkinc

from curved4_focal_geometry import DURATION, SOURCE_RZ_VOLUME, physical_time_weight


@dataclass(frozen=True)
class CuspData:
    source: float
    parameter: float
    length: float
    action: float
    null_time: float
    quartic: float
    longitudinal: float
    volume_factor: float
    endpoint_jacobian: float


def _elliptic_derivative(m):
    # Positive integral avoids cancellation at m=0.
    return quad(lambda x: .5*math.sin(x)**2/(1-m*math.sin(x)**2)**1.5,
                0, math.pi/2, epsabs=1e-12, epsrel=1e-12)[0]


def cusp_time(m):
    if not math.isfinite(m) or not 0 <= m < 1:
        raise ValueError("requires finite 0 <= elliptic parameter < 1")
    return ((m+2)*ellipk(m)+2*ellipe(m))/4


def cusp_source_data(source):
    """CG4--CG6, source measured from either potential-cell center."""
    if not math.isfinite(source) or not abs(source) < math.pi/4:
        raise ValueError("source displacement must lie strictly inside a cell")
    m = math.sin(2*source)**2
    if m >= 1:
        raise ValueError("source too close to cell wall for floating-point resolution")
    k, second = ellipk(m), ellipe(m)
    length = 2*k
    action = ((m-2)*k+2*second)/4
    quartic = 2*_elliptic_derivative(m)
    def integrand(s):
        sn, _, dn, _ = ellipj(s, m)
        return math.sqrt(2*s*(length-s)/length)*sn/dn
    longitudinal = quad(integrand, 0, length, epsabs=2e-12, epsrel=2e-12)[0]
    volume_factor = 4/3*longitudinal*quartic**(-.25)
    return CuspData(source, m, length, action, length/2+action, quartic,
                    longitudinal, volume_factor, 2*quartic**.75)


def cusp_source_window():
    """Actual closing source p_T; CG4 proves its unique root lies below m=1/2."""
    m = brentq(lambda x: cusp_time(x)-DURATION, 0, .5, xtol=5e-15, rtol=1e-14)
    return math.asin(math.sqrt(m))/2


def internal_cut_data(length):
    """Reflection seam: source aperture, action and null time, including its edge."""
    if not math.isfinite(length) or not math.pi <= length <= 8*DURATION/3:
        raise ValueError("requires pi <= length <= the CR8 causal upper bound")
    m = (0. if length == math.pi else
         brentq(lambda x: 2*ellipk(x)-length, 0, 1-1e-14, xtol=5e-15, rtol=1e-14))
    action = ((m-2)*ellipk(m)+2*ellipe(m))/4
    return {"parameter": m, "source_radius": math.asin(math.sqrt(m))/2,
            "energy": m/8, "action": action, "null_time": length/2+action}


def rotating_cut_data(length):
    """Antipodal rotation seam; both orientations have this same actual action."""
    if not math.isfinite(length) or not 0 < length <= 8*DURATION/3:
        raise ValueError("requires positive length within the CR8 causal range")
    root = brentq(lambda x: 2*x*ellipk(x*x)-length, 0, math.sqrt(1-1e-14),
                  xtol=1e-300, rtol=1e-14)
    m = root*root
    if m == 0:
        raise ValueError("rotation energy exceeds floating-point resolution")
    action = (2*ellipe(m)-ellipk(m))/(4*root)
    return {"parameter": m, "energy": 1/(8*m), "action": action,
            "null_time": length/2+action}


def principal_cusp_density(source):
    """Geometric D0*kappa^(-9/7); the matching proof is separate from this code."""
    data = cusp_source_data(source)
    return (SOURCE_RZ_VOLUME*physical_time_weight(data.length, data.action)
            * data.endpoint_jacobian*data.volume_factor**(-9/7))


def principal_cusp_prefactor():
    """Source coefficient multiplying model I in CG7/CO1 (float diagnostic).

    Four = two cells times source reflection symmetry. Both time endpoints
    and all z partners are in physical_time_weight; no fitted action enters.
    """
    window = cusp_source_window()
    return 16/9*quad(principal_cusp_density, 0, window,
                    epsabs=1e-8, epsrel=2e-10)[0]


def _partial_time(energy, x):
    if energy == 1/8:
        return math.atanh(math.sin(2*x))
    if energy < 1/8:
        m = 8*energy
        angle = math.asin(max(-1., min(1., math.sin(2*x)/math.sqrt(m))))
        return ellipkinc(angle, m)
    m = 1/(8*energy)
    return math.sqrt(m)*ellipkinc(2*x, m)


def _partial_momentum(energy, x):
    if energy == 1/8:
        return math.sin(2*x)/4
    if energy < 1/8:
        m = 8*energy
        angle = math.asin(max(-1., min(1., math.sin(2*x)/math.sqrt(m))))
        return (ellipeinc(angle, m)+(m-1)*ellipkinc(angle, m))/4
    m = 1/(8*energy)
    return ellipeinc(2*x, m)/(4*math.sqrt(m))


def _rotating_arc_action(length, source, target):
    left, right = sorted((source, target))
    def flight(root):
        m = root*root
        return root*(ellipkinc(2*right, m)-ellipkinc(2*left, m))
    root = brentq(lambda x: flight(x)-length, 0, math.sqrt(1-1e-14),
                  xtol=1e-300, rtol=1e-14)
    m = root*root
    if m == 0:
        raise ValueError("rotation energy exceeds floating-point resolution")
    return ((ellipeinc(2*right, m)-ellipeinc(2*left, m))/(4*root)
            - length/(8*m))


def physical_circle_action(length, source, target):
    """Diagnostic of the GLOBAL CR6 minimum for every circle endpoint pair.

    Same-cell folding and the signed time-map comparison select the favored
    branch. Different-cell minima use the shorter rotating arc; at antipodes
    the two orientations tie. Not a sum over geodesic actions.
    """
    if not (math.isfinite(length) and 0 < length <= 8*DURATION/3
            and math.isfinite(source) and math.isfinite(target)):
        raise ValueError("finite endpoints and a positive CR8 length required")
    source, target = math.remainder(source, math.pi), math.remainder(target, math.pi)
    period = math.pi/2
    ip = math.floor((source+math.pi/4)/period)
    iq = math.floor((target+math.pi/4)/period)
    p, q = source-ip*period, target-iq*period
    delta = (target-source+math.pi/2) % math.pi-math.pi/2
    at_wall = abs(p) == math.pi/4 or abs(q) == math.pi/4
    if at_wall and delta == 0:
        return -length/8
    if (ip-iq) % 2 or at_wall:
        return _rotating_arc_action(length, source, source+delta)
    if abs(q) > abs(p):
        p, q = q, p
    if p < 0:
        p, q = -p, -q
    if p == 0:
        return 0. if length <= math.pi else internal_cut_data(length)["action"]
    m0 = math.sin(2*p)**2
    if not 0 < m0 < 1:
        raise ValueError("endpoints exceed floating-point cell resolution")
    energy0 = m0/8
    threshold = ellipk(m0)-_partial_time(energy0, q)
    if length <= threshold:
        def flight(velocity):
            energy = energy0+velocity*velocity/2
            return _partial_time(energy, p)-_partial_time(energy, q)
        if length == threshold:
            energy = energy0
        else:
            high = max(1., (p-q)/length)
            while flight(high) > length:
                high *= 2
            velocity = brentq(lambda x: flight(x)-length, 0, high,
                               xtol=2e-14, rtol=1e-14)
            energy = energy0+velocity*velocity/2
        return _partial_momentum(energy, p)-_partial_momentum(energy, q)-energy*length
    def turn_time(m):
        return 2*ellipk(m)-_partial_time(m/8, p)-_partial_time(m/8, q)
    m = brentq(lambda x: turn_time(x)-length, m0, 1-1e-14,
               xtol=5e-15, rtol=1e-14)
    half_momentum = (ellipe(m)+(m-1)*ellipk(m))/4
    return (2*half_momentum-_partial_momentum(m/8, p)
            - _partial_momentum(m/8, q)-m*length/8)
