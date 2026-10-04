"""Independent finite diagnostics for #75, not substitutes for its written proof.

The unequal-axis height has axes (1,2,3), height 1/4, and future
f=1/8+epsilon*sin(z1). All original margins are retained. Only z1 and n1
enter the integrands, allowing exact azimuthal integrations, not a reduction
of spacetime dimension. Actual phases and both endpoint measures remain.
"""

import unittest

import mpmath as mp
import numpy as np
import sympy as s

from curved_joint_corner import (
    check_joint_corner_identities, future_normal,
    induced_gram, minkowski_inner, tangent_corner_response,
)
from test_curved_boundary_collar import phase_nodes, planar_corner
from test_curved_interior_short import C, LD, PI, VOLUME_CONSTANT as c, actual_h, gauss_nodes, kernel
from test_joint_geometry import joint_data, inner, gram_density


UNIT = ((1, 0, 0), (1, 0, 0))


def face(x, epsilon):
    return LD(1)/8+epsilon*np.sin(x), epsilon*np.cos(x)


def field_value(coefficients, t, x):
    constant, dt, dx = (LD(str(a)) for a in coefficients)
    return constant+dt*t+dx*x


def corner_data(u, v, beta, lam, mu, direction, epsilon):
    """Exact implicit height root, source time, and every moving Jacobian."""
    T, r = (u+v)/2, (v-u)/2
    height = beta*(T-epsilon*np.cos(mu)*r*direction)
    for _ in range(4):
        radial = np.sqrt(1-4*height)
        x, xs = mu*radial, -2*mu/radial
        f, fp = face(x, epsilon)
        fy, fpy = face(x+r*direction, epsilon)
        gap, gap_s = T+f-fy, (fp-fpy)*xs
        height -= (height-beta*gap)/(1-beta*gap_s)
    radial = np.sqrt(1-4*height)
    x, xs = mu*radial, -2*mu/radial
    f, fp = face(x, epsilon)
    fy, fpy = face(x+r*direction, epsilon)
    gap, gap_s = T+f-fy, (fp-fpy)*xs
    alpha = beta+(1-beta)*lam
    t = f-alpha*gap
    gap_u = (1+fpy*direction)/(2*(1-beta*gap_s))
    time_u = (beta*fp*xs-alpha)*gap_u
    h = actual_h(t, u, v)
    hu, ht = t/2+3*u/20+7*v/60, 2*t+(u+v)/2
    phase_u = v*(2*h+u*(hu+ht*time_u))/(2*np.sqrt(h))
    jac = (1-beta)*gap*gap/(1-beta*gap_s)
    return T, r, height, x, t, h, phase_u, jac, radial


def corner_original(rho, delta=.1, epsilon=1/16, weights=UNIT, *, order=36,
                    angles=6, depths=6, flatten=True):
    """Actual finite J in u,v coordinates, with two independent time maps.

    flatten=False integrates s in [0,s_*], A in [s,d(s)] directly.
    flatten=True uses the proof's s=beta*d(s), A=alpha*d(s) rectangle.
    Neither uses phase transport or a tangent approximation.
    """
    rho, delta, epsilon = (LD(str(x)) for x in (rho, delta, epsilon))
    ns, ws = gauss_nodes(order)
    ang, aw = gauss_nodes(angles)
    bs, bw = gauss_nodes(depths)
    ls, lw = gauss_nodes(depths)
    v = delta*ns[:, None, None, None]
    u = v*ns[None, :, None, None]
    beta, lam = bs[None, None, :, None], ls[None, None, None, :]
    T, r = (u+v)/2, (v-u)/2
    base = (delta*v*ws[:, None, None, None]*ws[None, :, None, None]
            * bw[None, None, :, None]*lw[None, None, None, :]*(v-u)**2/8)
    total = LD(0)
    for mu, muw in zip(2*ang-1, 2*aw):
        for direction, dw in zip(2*ang-1, 2*aw):
            if flatten:
                _, _, _, x, t, h, _, jac, radial = corner_data(
                    u, v, beta, lam, mu, direction, epsilon)
            else:
                # The outer contact root is solved only once; the interior
                # height coordinate is then independent of d(s).
                root = corner_data(u, v, LD(1), LD(0), mu, direction, epsilon)[2]
                height = beta*root
                radial = np.sqrt(1-4*height)
                x = mu*radial
                f, _ = face(x, epsilon)
                gap = T+f-face(x+r*direction, epsilon)[0]
                t = f-height-lam*(gap-height)
                jac = root*(gap-height)
                h = actual_h(t, u, v)
            value = (radial*jac*(1+t*t)*(1+(t+T)**2)
                     *field_value(weights[0], t, x)
                     *field_value(weights[1], t+T, x+r*direction)
                     *kernel(c*rho*(u*v)**2*h))
            total += muw*dw*np.sum(base*value)
    # dz=(abc/(2H))*sqrt(1-s/H) ds dS(m), abc=6, H=1/4.
    return -C*rho**LD('1.5')*12*(2*PI)**2*total


def corner_phase(rho, delta=.1, epsilon=1/16, weights=UNIT, *, order=20,
                 radial_order=24, angles=4, depths=4, measures="both", omit_mixed=False):
    """Actual phase-pushed J, retaining the moving diagonal and all partners.

    Subtract the null amplitude before radial quadrature using the exact
    zeroth signed moment. z=sqrt(c*rho)*w is integrated to 12; the Gaussian
    tail is negligible in these finite diagnostic fixtures, not a proof.
    """
    rho, delta, epsilon = (LD(str(x)) for x in (rho, delta, epsilon))
    ns, ws = gauss_nodes(radial_order)
    ang, aw = gauss_nodes(angles)
    bs, bw = gauss_nodes(depths)
    ls, lw = gauss_nodes(depths)
    z, zw = phase_nodes(order)
    scale = np.sqrt(c*rho)
    if scale*delta*delta <= 12:
        raise ValueError("cutoff below the diagnostic phase tail")
    w = (z/scale)[:, None, None, None]
    beta, lam = bs[None, None, :, None], ls[None, None, None, :]
    alpha = beta+(1-beta)*lam
    radial_node = ns[None, :, None, None]
    radial_weight = ws[None, :, None, None]
    depth_weight = bw[None, None, :, None]*lw[None, None, None, :]
    total = np.zeros_like(z)
    for mu, muw in zip(2*ang-1, 2*aw):
        f0 = face(mu, epsilon)[0]
        lower = np.broadcast_to(np.sqrt(w)/(1+f0*f0)**LD('.25'),
                                (len(z), 1, depths, depths)).copy()
        for _ in range(5):
            radial = np.sqrt(1-4*beta*lower)
            f, fp = face(mu*radial, epsilon)
            t = f-alpha*lower
            tv = -2*mu*beta*fp/radial-alpha
            hd = actual_h(t, lower, lower)
            derivative = lower*(4*hd+lower*(t+8*lower/15+(2*t+lower)*tv))/(2*np.sqrt(hd))
            lower -= (lower*lower*np.sqrt(hd)-w)/derivative
        log_range = np.log(delta/lower)
        v = lower*np.exp(radial_node*log_range)
        for direction, dw in zip(2*ang-1, 2*aw):
            def amplitude(u, vv):
                T, r, _, x, t, h, phase_u, jac, spatial = corner_data(
                    u, vv, beta, lam, mu, direction, epsilon)
                jacobian_u = phase_u
                if omit_mixed:
                    jacobian_u = vv*(2*h+u*(t/2+3*u/20+7*vv/60))/(2*np.sqrt(h))
                density = (1+t*t)*(1+(t+T)**2)
                if measures == "source":
                    density = 1+t*t
                elif measures != "both":
                    raise ValueError("unknown measure control")
                return (spatial*jac*(vv-u)**2*density
                        *field_value(weights[0], t, x)
                        *field_value(weights[1], t+T, x+r*direction)/(8*jacobian_u)), h, phase_u

            h0 = corner_data(0, v, beta, lam, mu, direction, epsilon)[5]
            u = w/(v*np.sqrt(h0))
            for _ in range(5):
                data = corner_data(u, v, beta, lam, mu, direction, epsilon)
                h, phase_u = data[5:7]
                u -= (u*v*np.sqrt(h)-w)/phase_u
            actual, _, _ = amplitude(u, v)
            null = amplitude(0, v)[0]
            # Retain the lower strip [0,lower] when subtracting B(0).
            null_strip = amplitude(0, lower*radial_node)[0]
            difference = np.sum(radial_weight*((actual-null)*v*log_range
                                                -lower*null_strip), axis=1, keepdims=True)
            total += muw*dw*np.sum(depth_weight*difference, axis=(1, 2, 3))
    return -C*rho**LD('1.5')*12*(2*PI)**2/scale*np.sum(zw*kernel(z*z)*total)


def tangent_model(rho, delta=.1, epsilon=1/16, weights=UNIT):
    """Finite-cutoff J18, evaluated with exact radial primitives C12.

    Only whole-half-line zero-moment polynomials are removed. The remaining
    cutoff powers are retained; the phase tail is negligible in the fixtures.
    """
    rho, delta, epsilon = (LD(str(x)) for x in (rho, delta, epsilon))
    mu, mw = gauss_nodes(32)
    x = 2*mu-1
    f, p = face(x, epsilon)
    q = 1+f*f
    trace = field_value(weights[0], f, x)*field_value(weights[1], f, x)
    z, zw = phase_nodes(32)
    scale = np.sqrt(c*rho*q)
    sigma = z[:, None]/scale[None, :]
    j0 = -sigma*sigma/(8*delta*delta)+sigma*np.log(sigma/delta**2)/4
    j2 = -sigma**4/(64*delta**4)+sigma*sigma*np.log(sigma/delta**2)/16
    response = np.sum(zw[:, None]*kernel(z[:, None]**2)
                      *(j2+p[None, :]**2*(j2-sigma*j0)/3), axis=0)/scale
    return -C*rho**LD('1.5')*12*(2*PI)**2*np.sum(2*mw*q*q*trace*response/2)


def geometric_targets(epsilon=1/16, weights=UNIT, order=48):
    """Spatial pullback of the independently derived geometry and face flux.

    dA/|Dh|=12 dS for the unequal-axis ellipsoid. The azimuthal integral is
    exact since p, fields and f depend only on z1; Dh_1=-z1/2 on the joint.
    """
    nodes, ws = gauss_nodes(order)
    x = 2*nodes-1
    f, p = face(x, LD(str(epsilon)))
    weight = field_value(weights[0], f, x)*field_value(weights[1], f, x)
    factor = 12*4*PI*ws*np.sqrt(1+f*f)*weight
    pa = -p*x/2
    raw = np.sum(factor*(1-p*p))
    flux = np.sum(factor*(-pa))
    return raw, flux, raw-flux


class CornerCertificates(unittest.TestCase):
    def test_exact_certificates(self):
        check_joint_corner_identities()

    def test_independent_curved_normals_gram_and_chart_overlaps(self):
        with mp.workdps(40):
            eps = mp.mpf(1)/16
            for theta, phi in ((mp.mpf('.3'), mp.mpf('.7')),
                               (mp.mpf('1.1'), mp.mpf('2.4'))):
                v, w, past, future, _, _ = joint_data(theta, phi, eps)
                time = mp.mpf(1)/8+eps*mp.sin(mp.sin(theta)*mp.cos(phi))
                q = 1+time*time
                omega = q**mp.mpf('.25')
                past, future = [tuple(a/omega for a in n) for n in (past, future)]
                gamma = omega**2*inner(past, future)
                self.assertLess(abs(omega**2*inner(past, past)-1), mp.mpf('1e-36'))
                self.assertGreater(gamma, 1)
                self.assertGreater(mp.acosh(gamma), 0)
                for n in (past, future):
                    for tangent in (v, w):
                        self.assertLess(abs(inner(n, tangent)), mp.mpf('1e-36'))
                area = omega**2*gram_density(v, w)
                # A nontrivial orientation-reversing chart-frame change.
                v2 = tuple(2*a+b for a, b in zip(v, w))
                w2 = tuple(-a for a in w)
                self.assertLess(abs(omega**2*gram_density(v2, w2)-2*area), mp.mpf('1e-35'))
                self.assertGreater(omega**2*gram_density(v, w, False), area)

    def test_integrated_target_from_normals_and_actual_tangents(self):
        # No angle-density shortcut inside this independent surface integral.
        with mp.workdps(35):
            ns, ws = mp.gauss_quadrature(24, 'legendre')
            eps = mp.mpf(1)/16
            total = mp.mpf(0)
            for a, wa in zip(ns, ws):
                theta = (a+1)*mp.pi/2
                for b, wb in zip(ns, ws):
                    phi = (b+1)*mp.pi
                    v, w, past, future, _, _ = joint_data(theta, phi, eps)
                    x = mp.sin(theta)*mp.cos(phi)
                    time = mp.mpf(1)/8+eps*mp.sin(x)
                    omega = (1+time*time)**mp.mpf('.25')
                    past, future = [tuple(t/omega for t in n) for n in (past, future)]
                    gamma = omega*omega*inner(past, future)
                    total += wa*wb*omega**2*gram_density(v, w)*gamma/mp.sqrt(gamma**2-1)
            total *= mp.pi**2/2
            self.assertLess(abs(total-mp.mpf(str(geometric_targets()[2]))), mp.mpf('1e-10'))

    def test_constant_factor_and_signed_trace_response(self):
        q, k, p2 = s.Rational(81, 16), s.Rational(1, 3), s.Rational(1, 64)
        response = tangent_corner_response(q, k, p2, -2)
        self.assertEqual(response, s.sqrt(q)*tangent_corner_response(1, k, p2, -2))
        self.assertLess(response, 0)
        self.assertNotEqual(response, tangent_corner_response(q, k, p2))
        self.assertEqual(tangent_corner_response(q, k, p2, 0), 0)
        for factor in (s.Rational(3, 2), s.Rational(2, 3)):
            normal = future_normal((s.Rational(1, 8), 0, 0), factor**4)
            self.assertEqual(s.simplify(factor**2*minkowski_inner(normal, normal)), 1)
            self.assertEqual(induced_gram((0, 1, 0), (0, 0, 1), (s.Rational(1, 8), 0, 0),
                                         factor**4).det(), factor**4)

    def test_curved_variable_angle_example_and_nonzero_flux(self):
        raw, flux, target = geometric_targets()
        self.assertGreater(abs(flux), .005)
        self.assertGreater(abs(raw-target), .005)
        self.assertAlmostEqual(float(raw-flux), float(target), places=12)
        _, planar_flux, planar_target = geometric_targets(epsilon=0)
        self.assertEqual(planar_flux, 0)
        self.assertLess(abs(planar_target-48*PI*np.sqrt(LD(65)/64)), 1e-12)
        # The planar-future curved example already has distinct positive angles.
        self.assertNotEqual(mp.acoth(2), mp.acoth(6))
        self.assertGreater(3*(1-(1/8)**2/2)*(1+(1/8)**2)**(-2.5), 0)

    def test_finite_partition_and_cross_chart_terms(self):
        # Both endpoint partitions sum to one, overlap, and one is signed.
        first = ((.4, .7, .1), (.6, -.7, -.1))
        second = ((1.2, -.3, .2), (-.2, .3, -.2))
        total = sum(geometric_targets(weights=(a, b))[2] for a in first for b in second)
        target = geometric_targets()[2]
        diagonal = sum(geometric_targets(weights=(first[i], second[i]))[2] for i in range(2))
        self.assertLess(abs(total-target), 1e-12)
        self.assertGreater(abs(diagonal-target), 50)
        rho = 1e5
        actual = sum(corner_original(rho, weights=(a, b), order=16, angles=4, depths=4)
                     for a in first for b in second)
        unsplit = corner_original(rho, order=16, angles=4, depths=4)
        self.assertLess(abs(actual-unsplit), 1e-11)

    def test_c3_height_chart_jacobian_is_not_assumed_c3(self):
        # Z(s)=(..., s+eps*s^(7/2)) on s>=0 extends C3, not C4;
        # its volume Jacobian has only C2. The proof differentiates it twice.
        v, ratio = s.symbols('v ratio', positive=True)
        height = v*(1+ratio)/2
        jac_error = s.Rational(7, 32)*height**s.Rational(5, 2)
        for j in range(3):
            expression = s.diff(jac_error, ratio, j)/v
            self.assertEqual(s.limit(expression, v, 0, dir='+'), 0)
        x = s.Symbol('x', positive=True)
        self.assertEqual(s.limit(s.diff(x**s.Rational(5, 2), x, 3), x, 0, dir='+'), s.oo)

    def test_actual_implicit_root_and_total_jacobians(self):
        u, v, beta, lam, mu, direction, eps = map(LD, ('.03', '.1', '.4', '.8', '.2', '.7', '.0625'))
        base = corner_data(u, v, beta, lam, mu, direction, eps)
        gap = base[0]+face(base[3], eps)[0]-face(base[3]+base[1]*direction, eps)[0]
        self.assertLess(abs(base[2]-beta*gap), 1e-17)
        step = LD('1e-6')
        def phase(uu):
            return uu*v*np.sqrt(corner_data(uu, v, beta, lam, mu, direction, eps)[5])
        derivative = (phase(u+step)-phase(u-step))/(2*step)
        self.assertLess(abs(derivative-base[6]), 2e-11)
        def coordinates(b, l):
            data = corner_data(u, v, b, l, mu, direction, eps)
            return np.array([data[2], face(data[3], eps)[0]-data[4]])
        db = (coordinates(beta+step, lam)-coordinates(beta-step, lam))/(2*step)
        dl = (coordinates(beta, lam+step)-coordinates(beta, lam-step))/(2*step)
        self.assertLess(abs(db[0]*dl[1]-db[1]*dl[0]-base[7]), 2e-11)

    def test_moving_diagonal_strip_power(self):
        # Exactly integrable model with the physical v^3*(1-U)^2 zero.
        x, v = s.symbols('x v', positive=True)  # w=x^2
        lower, reference = x+x*x/7, x
        ratio = (lower/v)**2
        strip = s.integrate(v**3*(1-ratio)**2, (v, lower, reference))
        self.assertEqual(s.limit(strip/x**7, x, 0, dir='+'), -s.Rational(4, 1029))
        self.assertEqual(s.limit(strip/x**4, x, 0, dir='+'), 0)
        self.assertNotEqual(strip, 0)


class CornerQuadrature(unittest.TestCase):
    def test_actual_height_time_map_agrees_with_rectangle(self):
        weights = ((.4, .7, .2), (1.1, -.3, .1))
        direct = corner_original(1e6, weights=weights, flatten=False)
        rectangle = corner_original(1e6, weights=weights, flatten=True)
        refined = corner_original(1e6, weights=weights, order=44, angles=8, depths=8)
        self.assertLess(abs(direct-rectangle), 2e-10)
        self.assertLess(abs(refined-rectangle), 2e-8)

    def test_planar_actual_phase_and_original_coordinates(self):
        pushed = corner_phase(1e8, epsilon=0)
        original = planar_corner(1e8)
        self.assertLess(abs(pushed-original), 2e-6)

    def test_nonplanar_actual_phase_remainder_fixed_cutoffs(self):
        weights = ((.4, .7, .2), (1.1, -.3, .1))
        raw_target, flux, target = geometric_targets(weights=weights)
        low = corner_phase(1e8, weights=weights)
        high = corner_phase(1e10, weights=weights)
        other_cutoff = corner_phase(1e10, delta=.075, weights=weights)
        self.assertLess(abs(high-raw_target), abs(low-raw_target)/3)
        self.assertLess(abs(high-flux-target), .15)
        low_model = tangent_model(1e8, weights=weights)
        high_model = tangent_model(1e10, weights=weights)
        self.assertLess(abs(high-high_model), abs(low-low_model)/2)
        self.assertLess(abs(high_model-raw_target), .01)
        self.assertLess(abs(high-other_cutoff), .05)
        refined = corner_phase(1e10, weights=weights, order=24, radial_order=32, angles=5, depths=5)
        self.assertLess(abs(high-refined), .002)

    def test_wrong_measure_and_phase_jacobian_are_detected(self):
        rho = 1e8
        correct = corner_phase(rho, angles=3, depths=3)
        source_only = corner_phase(rho, angles=3, depths=3, measures='source')
        wrong_jac = corner_phase(rho, angles=3, depths=3, omit_mixed=True)
        self.assertGreater(abs(source_only-correct), 1)
        self.assertGreater(abs(wrong_jac-correct), .001)


if __name__ == '__main__':
    unittest.main()
