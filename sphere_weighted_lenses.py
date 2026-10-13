"""Physical sphere-dependent lens diagnostics, not a limit solver/certificate.

Density callbacks take (time, sphere_point[..., 3], circle_position) and return
Omega**4. The sphere frame is retained; neither orientation is averaged away.
See notes/sphere-dependent-conformal-limit.md for the written proof.
"""

import numpy as np

from curved4_corrected_convergence import diamond_rule
from general_metric_gate import gauss_rule
from sphere_circle_focusing import area_ratio


def frame(p, n):
    p, n = np.asarray(p, dtype=float), np.asarray(n, dtype=float)
    if (p.shape != (3,) or n.shape != (3,) or not np.all(np.isfinite([p, n]))
            or not np.allclose([p@p, n@n, p@n], [1, 1, 0], atol=1e-12, rtol=0)):
        raise ValueError("p,n must be an orthonormal sphere point/tangent frame")
    return p, n, np.cross(p, n)


def positive_density(density, t, point, z):
    value = np.asarray(density(t, point, z), dtype=float)
    if np.any(~np.isfinite(value)) or np.any(value <= 0):
        raise ValueError("density must be finite and strictly positive")
    return value


def sphere_point(theta, x, y, p, n):
    """Exact signed two-distance map; theta=0 is its removable extension.

    One signed Euclidean half-plane maps to ONE spherical orientation. This
    does not sum geodesic tubes. The caller must stay before the upper triangle
    transition. The factored k coordinate avoids subtracting unit squares.
    """
    p, n, k = frame(p, n)
    if not np.isfinite(theta) or not 0 <= theta < np.pi:
        raise ValueError("requires 0<=theta<pi")
    x, y = np.broadcast_arrays(np.asarray(x, float), np.asarray(y, float))
    r, s = np.hypot(x, y), np.hypot(x-theta, y)
    if (np.any(~np.isfinite(r+s))
            or np.any(r+s >= 2*np.pi-theta)):
        raise ValueError("outside the regular spherical triangle range")
    sinc = lambda v: np.sinc(v/np.pi)
    args = ((r+s+theta)/2, (r+s-theta)/2,
            (theta+r-s)/2, (theta-r+s)/2)
    determinant = np.prod([sinc(v) for v in args], axis=0)
    # Divided cosine difference; no division by theta at the circle axis.
    along = ((x-theta/2)*sinc((r+s)/2)*sinc((r-s)/2)
             + theta/2*sinc(theta/2)**2*np.cos(r))/sinc(theta)
    across = y*np.sqrt(np.maximum(0, determinant))/sinc(theta)
    return np.cos(r)[..., None]*p + along[..., None]*n + across[..., None]*k


def regular_factor(ts, zs, theta, b, q, p, n, density, order=12):
    """Actual V/q**2, including q=0, using the full spatial boost."""
    if not all(np.isfinite(v) for v in (ts, zs, theta, b, q)):
        raise ValueError("parameters must be finite")
    radius = np.hypot(theta, b)
    if not 0 <= theta < np.pi or q < 0 or radius == 0:
        raise ValueError("requires a regular angle, q>=0 and nonzero radius")
    tau = np.sqrt(radius*radius+q)
    if tau > 4+1e-12 or np.sqrt(theta*theta+q) >= 2*np.pi-theta:
        raise ValueError("outside the regular-side width-four slab")
    a, b1, b2, b3, weights = diamond_rule(order)
    ell, root = 0.5+a, np.sqrt(q)
    x = theta*ell+tau*theta/radius*b1-b/radius*root*b3
    y = root*b2
    z = zs+b*ell+tau*b/radius*b1+theta/radius*root*b3
    t = ts+tau*ell+radius*b1
    point = sphere_point(theta, x, y, p, n)
    ratio = area_ratio(theta, np.hypot(x, y), np.hypot(x-theta, y))
    return float(np.sum(weights*ratio*positive_density(density, t, point, z)))


def _clock_section(ts, zs, tau, b, r, s, point, density, circle_order, time_order):
    """Actual time integral on the ellipse; rationalized near-null clock gap."""
    u2 = tau*tau-b*b
    u = np.sqrt(u2)
    opening = np.maximum(0, (u-r-s)*(u+r+s))
    width2 = tau*tau/(4*u2*u2)*opening*np.maximum(0, (u-r+s)*(u+r-s))
    half = np.sqrt(width2)
    center = b*(u2+r*r-s*s)/(2*u2)
    cn, cw = gauss_rule(circle_order)
    tn, tw = gauss_rule(time_order)
    v = 2*cn-1
    z = center[..., None]+half[..., None]*v
    lower = np.hypot(r[..., None], z)
    back = np.hypot(s[..., None], z-b)
    c = (u2+r[..., None]**2-s[..., None]**2+2*b*z)/(2*tau)
    denominator = (c+lower)*(tau-lower+back)
    # (c**2-lower**2) = (u2/tau**2)*half**2*(1-v**2).
    gap = np.divide((2*u2/tau)*width2[..., None]*(1-v*v), denominator,
                    out=np.zeros_like(z), where=denominator > 0)
    gap = np.maximum(0, gap)
    times = ts+lower[..., None]+gap[..., None]*tn
    pts = point[..., None, None, :]
    values = positive_density(density, times, pts, zs+z[..., None])
    averaged = np.sum(tw*values, axis=-1)
    return 2*half*np.sum(cw*gap*averaged, axis=-1)


def clock_volume(ts, zs, tau, theta, b, p, n, density,
                 order=32, circle_order=16, time_order=10):
    """Independent polar/clock cubature, also across transitions/at antipodes.

    Both signed azimuths are evaluated with their actual sphere points.
    A zero-width ellipse is not interpreted as an oriented time interval.
    """
    p, n, k = frame(p, n)
    if (not all(np.isfinite(v) for v in (ts, zs, tau, theta, b))
            or not abs(b) < tau <= 4 or not 0 <= theta <= np.pi):
        raise ValueError("requires finite parameters, |b|<tau<=4, 0<=theta<=pi")
    u = np.sqrt(tau*tau-b*b)
    if u <= theta:
        return 0.0
    nodes, weights = gauss_rule(order)
    edges = sorted(set((0., np.pi, min(np.pi, (u-theta)/2),
                        min(np.pi, (u+theta)/2))))
    total = 0.
    for lo, hi in zip(edges, edges[1:]):
        r = (lo+(hi-lo)*nodes)[:, None]
        allowed = u-r
        if theta == 0:
            phi_max = np.where(2*r < u, np.pi, 0.)
        elif theta == np.pi:
            phi_max = np.full_like(r, np.pi)
        else:
            threshold = ((np.cos(np.clip(allowed, 0, np.pi))-np.cos(r)*np.cos(theta))
                         / (np.sin(r)*np.sin(theta)))
            phi_max = np.where(allowed >= np.pi, np.pi, np.where(
                allowed <= 0, 0., np.arccos(np.clip(threshold, -1, 1))))
        for sign in (-1, 1):
            phi = sign*phi_max*nodes[None, :]
            point = (np.cos(r)[..., None]*p + np.sin(r)[..., None]
                     * (np.cos(phi)[..., None]*n+np.sin(phi)[..., None]*k))
            if theta == np.pi:
                s = np.broadcast_to(np.pi-r, phi.shape)
            elif theta == 0:
                s = np.broadcast_to(r, phi.shape)
            else:
                s = np.arccos(np.clip(np.cos(r)*np.cos(theta)
                                     + np.sin(r)*np.sin(theta)*np.cos(phi), -1, 1))
            section = _clock_section(ts, zs, tau, b, r, s, point, density,
                                     circle_order, time_order)
            total += (hi-lo)*np.sum(weights[:, None]*weights[None, :]
                                    * np.sin(r)*phi_max*section)
    return float(total)


def closing_data(a, e, v, xi, zs, p, n, density):
    """Actual two-endpoint amplitude; excludes sin(a) and the frame measure."""
    p, n, _ = frame(p, n)
    if (not all(np.isfinite(x) for x in (a, e, v, xi, zs))
            or not 0 <= a < np.pi or e < 0 or not -1 <= v <= 1
            or not 0 <= xi <= 1):
        raise ValueError("invalid closing coordinates")
    theta, u = np.pi-a, np.pi-a+e
    if not 0 < u < 4:
        raise ValueError("requires 0<u<4")
    width = np.sqrt(16-u*u)
    b, tau = width*v, np.sqrt(u*u+width*width*v*v)
    gap = width*width*(1-v*v)/(4+tau)
    ts = -2+xi*gap
    target = np.cos(theta)*p+np.sin(theta)*n
    amplitude = (gap*u*width/tau*positive_density(density, ts, p, zs)
                 * positive_density(density, ts+tau, target, zs+b))
    return {"theta": theta, "b": b, "tau": tau, "ts": ts,
            "target": target, "amplitude": float(amplitude)}


def cut_factor(a, e, v, xi, zs, p, n, density, order=12):
    """Actual V/e**2 in the regular wedge; no extension through e=2*a."""
    if not 0 < a < np.pi or not 0 <= e < 2*a:
        raise ValueError("requires 0<a<pi and 0<=e<2*a")
    pair = closing_data(a, e, v, xi, zs, p, n, density)
    theta = pair['theta']
    return (2*theta+e)**2*regular_factor(pair['ts'], zs, theta, pair['b'],
        e*(2*theta+e), p, n, density, order)


def antipodal_coefficient(ts, zs, b, p, n, density, order=48):
    """Independent coefficient of (u-pi)**(3/2), not a target coefficient."""
    p, n, k = frame(p, n)
    if not np.isfinite(b) or np.hypot(np.pi, b) >= 4:
        raise ValueError("antipodal arrival must fit in the slab")
    nodes, weights = gauss_rule(order)
    r, phi = (np.pi*nodes)[:, None], (2*np.pi*nodes)[None, :]
    point = np.cos(r)[..., None]*p+np.sin(r)[..., None]*(
        np.cos(phi)[..., None]*n+np.sin(phi)[..., None]*k)
    tau = np.hypot(np.pi, b)
    density_value = positive_density(density, ts+tau*r/np.pi, point, zs+b*r/np.pi)
    integrand = np.sin(r)*np.sqrt(2*r*(np.pi-r)/np.pi)*density_value
    return float(4/3*2*np.pi**2*np.sum(weights[:, None]*weights[None, :]*integrand))


def sphere_rule(order=20):
    """Physical unit sphere measure (not a normalized probability)."""
    n, w = gauss_rule(order)
    height, phi = (2*n-1)[:, None], (2*np.pi*n)[None, :]
    radius = np.sqrt(1-height*height)
    x, y, z = np.broadcast_arrays(radius*np.cos(phi), radius*np.sin(phi), height)
    return np.stack((x, y, z), axis=-1), 4*np.pi*w[:, None]*w[None, :]


def independent_target(omega, omega_tt, omega_zz, sphere_laplacian, order=14):
    """Half-curvature integral from the conformal metric; empty joint."""
    nodes, weights = gauss_rule(order)
    points, sw = sphere_rule(order)
    t = (-2+4*nodes)[:, None, None, None]
    z = (20*nodes)[None, :, None, None]
    points = points[None, None, ...]
    om = positive_density(omega, t, points, z)
    box = (omega_tt(t, points, z)-omega_zz(t, points, z)
           - sphere_laplacian(t, points, z))
    measure = 80*weights[:, None, None, None]*weights[None, :, None, None]*sw
    return float(np.sum(measure*(om*om+3*om*box)))
