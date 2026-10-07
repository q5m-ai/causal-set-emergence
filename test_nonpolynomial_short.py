"""Finite regressions for #136; the conventional proof is in the written note.

Actual phase/endpoint integrals, never convergence fits as proof premises.
Shared geometric fixtures and zero-moment quadrature nodes are reused, but no
polynomial-density phase, inverse or diagonal is reused for this metric.
"""

import math
import unittest

import mpmath as mp
import numpy as np
import sympy as s
from scipy.integrate import quad

from calculations import ellipsoid_action
from conformal_geometry import conformal_curvature
from general_metric_gate import time_density_phase, null_ray_phase
from nonpolynomial_short import (
    check_nonpolynomial_identities, density, phase_data, total_phase_derivative,
)
from test_curved_interior_short import LD, PI, C, gauss_nodes, kernel, field_value
from test_curved_boundary_collar import phase_nodes
from test_joint_geometry import joint_data, inner, gram_density

c = PI/24
UNIT = ((1, 0, 0), (1, 0, 0))


def field(coeff, t, x):
    a, b, d = map(LD, coeff)
    return a+b*t+d*x


def future(x, epsilon):
    return LD(1)/8+epsilon*np.sin(x), epsilon*np.cos(x)


def full_probe(t, rho, delta=.08, order=40, field_name="one", *, original=False):
    """Actual local cone versus the ENTIRE finite radial second-jet model."""
    t, rho, delta = map(lambda x: LD(str(x)), (t, rho, delta))
    ns, ws = gauss_nodes(order)
    q, q1, q2 = density(t), 4/(1-t)**5, 20/(1-t)**6
    phi, pt, ptt, lap = {"one": (1, 0, 0, 0), "time2": (t*t, 2*t, 2, 0),
                          "space2": (0, 0, 0, 6)}[field_name]
    if original:
        v = delta*ns[:, None]
        u = v*ns[None, :]
        T, r = (u+v)/2, (v-u)/2
        value = ((v-u)**2/8*density(t+T)*field_value(field_name, t+T, r)
                 *kernel(c*rho*(u*v)**2*phase_data(t, u, v)[0]))
        pair = 4*PI*np.sum(ws[:, None]*ws[None, :]*delta*v*value)
        return C*np.sqrt(rho)*(phi-rho*pair)
    z, zw = phase_nodes(order)
    scale = np.sqrt(c*rho)
    if delta**2*np.sqrt(q)*scale <= 12:
        raise ValueError("fixed cutoff must exceed diagnostic Gaussian tail")
    w = z/scale
    nu = np.sqrt(w)/q**LD('.25')
    for _ in range(6):
        hd, _, hu, hv = phase_data(t, nu, nu)
        nu -= (nu*nu*np.sqrt(hd)-w)/(nu*(4*hd+nu*(hu+hv))/(2*np.sqrt(hd)))
    log_range = np.log(delta/nu)[:, None]
    v = nu[:, None]*np.exp(ns[None, :]*log_range)
    u = w[:, None]/(v*np.sqrt(phase_data(t, 0, v)[0]))
    for _ in range(6):
        h, _, hu, _ = phase_data(t, u, v)
        fu = v*(2*h+u*hu)/(2*np.sqrt(h))
        u -= (u*v*np.sqrt(h)-w[:, None])/fu

    def amplitude(uu, vv):
        T, r = (uu+vv)/2, (vv-uu)/2
        return (density(t+T)*field_value(field_name, t+T, r)*(vv-uu)**2
                /(8*total_phase_derivative(t, uu, vv)))

    diff = 4*PI*(np.sum(ws[None, :]*(amplitude(u, v)-amplitude(0, v))*v*log_range, axis=1)
                  -np.sum(ws[None, :]*nu[:, None]*amplitude(0, nu[:, None]*ns), axis=1))
    actual = C*np.sqrt(rho)*(phi-rho*np.sum(zw*kernel(z*z)*diff)/scale)
    # Independent physical jet using exact generic radial primitives (N13).
    a, d = q1/q, q2/q
    flat_scale = np.sqrt(c*rho*q)
    sigma, Z = z/flat_scale, z*z
    j0 = -sigma**2/(8*delta**2)+sigma*np.log(sigma/delta**2)/4
    j1 = ((delta-sigma/delta)**3-delta**3)/24
    j2 = -sigma**4/(64*delta**4)+sigma**2*np.log(sigma/delta**2)/16
    k = kernel(Z)
    kp = (-10+25*Z-12*Z**2+LD(4)/3*Z**3)*np.exp(-Z)
    kpp = (35-49*Z+16*Z**2-LD(4)/3*Z**3)*np.exp(-Z)
    jet = (j1*(pt*k+a*phi*(k+Z*kp/2))
           +(ptt*j2/2+lap*(j2-sigma*j0)/6)*k+a*pt*j2*(k+Z*kp/2)
           +phi*d*(j2*k/2+Z*(3*j2/20-sigma*j0/60)*kp)
           +phi*a*a*j2*(Z*kp/2+Z*Z*kpp/8))
    model = (phi*C*np.sqrt(rho)*np.exp(-c*rho*q*delta**4)
             -C*rho**LD('1.5')*2*PI*q/flat_scale*np.sum(zw*jet))
    target = (1-t)**2*(ptt-lap)+2*(1-t)*pt+6*phi
    return np.array((actual, model, target))


def boundary_data(kind, u, v, beta, lam, mu, direction, epsilon):
    """Actual depth/height maps and total derivatives; face source x=mu."""
    T, r = (u+v)/2, (v-u)/2
    if kind == "corner":
        height = beta*(T-epsilon*np.cos(mu)*r*direction)
        for _ in range(3):
            radial = np.sqrt(1-4*height)
            x, xs = mu*radial, -2*mu/radial
            f, fp = future(x, epsilon)
            fy, fpy = future(x+r*direction, epsilon)
            gap, ds = T+f-fy, (fp-fpy)*xs
            height -= (height-beta*gap)/(1-beta*ds)
        radial = np.sqrt(1-4*height)
        x, xs = mu*radial, -2*mu/radial
        f, fp = future(x, epsilon)
        fy, fpy = future(x+r*direction, epsilon)
        gap, ds = T+f-fy, (fp-fpy)*xs
        alpha = beta+(1-beta)*lam
        t = f-alpha*gap
        gap_u = (1+fpy*direction)/(2*(1-beta*ds))
        tu = (beta*fp*xs-alpha)*gap_u
        measure = radial*(1-beta)*gap*gap/(1-beta*ds)
    elif kind == "face":
        x = mu
        f, _ = future(x, epsilon)
        fy, fpy = future(x+r*direction, epsilon)
        gap = T+f-fy
        t, tu = f-beta*gap, -beta*(1+fpy*direction)/2
        measure = gap
    else:
        raise ValueError("unknown boundary component")
    h, ht, hu, _ = phase_data(t, u, v)
    fu = v*(2*h+u*(hu+ht*tu))/(2*np.sqrt(h))
    return t, x, measure, h, fu


def boundary_integral(kind, rho, delta=.08, epsilon=1/16, weights=UNIT, *,
                      pushed=True, order=20, radial_order=24, angles=4, depths=4,
                      omit_mixed=False, omit_target=False):
    """Actual F or J, original coordinates OR phase transported.

    Signs are +C*rho^(3/2)*F and -C*rho^(3/2)*J. Corner covers the whole
    ellipsoid collar (axes 1,2,3), with azimuths integrated exactly. Face is
    per source spatial volume at x=.3. No endpoint is restricted by a chart.
    """
    rho, delta, epsilon = map(lambda x: LD(str(x)), (rho, delta, epsilon))
    ns, ws = gauss_nodes(radial_order if pushed else order)
    an, aw = gauss_nodes(angles)
    bn, bw = gauss_nodes(depths)
    corner = kind == "corner"
    beta = bn[None, None, :, None]
    lam = bn[None, None, None, :] if corner else LD(0)
    depth_weights = bw[None, None, :, None]*(bw[None, None, None, :] if corner else 1)
    mus = zip(2*an-1, 2*aw) if corner else [(LD('.3'), LD(1))]
    total = LD(0)
    if pushed:
        z, zw = phase_nodes(order)
        scale = np.sqrt(c*rho)
        if delta**2*scale < 15:
            raise ValueError("cutoff below diagnostic Gaussian tail")
        w = (z/scale)[:, None, None, None]
    else:
        v = delta*ns[:, None, None, None]
        u = v*ns[None, :, None, None]
        base = delta*v*ws[:, None, None, None]*ws[None, :, None, None]*depth_weights
    for mu, muw in mus:
        if pushed:
            f0 = future(mu, epsilon)[0]
            shape = (len(z), 1, depths, depths if corner else 1)
            nu = np.broadcast_to(np.sqrt(w)*(1-f0), shape).copy()
            alpha = beta+(1-beta)*lam if corner else beta
            for _ in range(6):
                if corner:
                    radial = np.sqrt(1-4*beta*nu)
                    f, fp = future(mu*radial, epsilon)
                    time = f-alpha*nu
                    tv = -2*mu*beta*fp/radial-alpha
                else:
                    time, tv = f0-beta*nu, -beta
                h, ht, hu, hv = phase_data(time, nu, nu)
                deriv = nu*(4*h+nu*(hu+hv+ht*tv))/(2*np.sqrt(h))
                nu -= (nu*nu*np.sqrt(h)-w)/deriv
            logs = np.log(delta/nu)
            v = nu*np.exp(ns[None, :, None, None]*logs)
        for direction, dw in zip(2*an-1, 2*aw):
            def amplitude(uu, vv, phase=True):
                t, x, measure, h, fu = boundary_data(kind, uu, vv, beta, lam, mu, direction, epsilon)
                if omit_mixed:
                    fu = total_phase_derivative(t, uu, vv)
                T, r = (uu+vv)/2, (vv-uu)/2
                measure = measure*density(t)*(1 if omit_target else density(t+T))
                value = (measure*field(weights[0], t, x)*field(weights[1], t+T, x+r*direction)
                         *(vv-uu)**2/8)
                return value/fu if phase else value*kernel(c*rho*(uu*vv)**2*h)
            if pushed:
                h0 = boundary_data(kind, 0, v, beta, lam, mu, direction, epsilon)[3]
                u = w/(v*np.sqrt(h0))
                for _ in range(6):
                    data = boundary_data(kind, u, v, beta, lam, mu, direction, epsilon)
                    u -= (u*v*np.sqrt(data[3])-w)/data[4]
                value = amplitude(u, v)-amplitude(0, v)
                # Subtract only the exact zero-moment B(0), retaining the
                # entire lost interval [0,nu] and the TRUE moving diagonal.
                diff = np.sum(ws[None, :, None, None]*(value*v*logs
                              -nu*amplitude(0, nu*ns[None, :, None, None])), axis=1, keepdims=True)
                value = np.sum(depth_weights*diff, axis=(1, 2, 3))
                total += muw*dw*np.sum(zw*kernel(z*z)*value)/scale
            else:
                total += muw*dw*np.sum(base*amplitude(u, v, phase=False))
    factor = -12*(2*PI)**2 if corner else 2*PI
    return factor*C*rho**LD('1.5')*total


def boundary_model(kind, rho, delta=.08, epsilon=1/16, weights=UNIT):
    """Full finite tangent/face jet, not just their limiting coefficients."""
    rho, delta, epsilon = map(lambda x: LD(str(x)), (rho, delta, epsilon))
    ns, ws = gauss_nodes(24)
    x, xw = (2*ns-1, 2*ws) if kind == "corner" else (np.array([LD('.3')]), np.array([LD(1)]))
    f, p = future(x, epsilon)
    q, q1 = density(f), 4/(1-f)**5
    chi, phi = field(weights[0], f, x), field(weights[1], f, x)
    ct, pt, px = map(LD, (weights[0][1], weights[1][1], weights[1][2]))
    z, zw = phase_nodes(32)
    scale = np.sqrt(c*rho*q)
    sigma, Z = z[:, None]/scale[None, :], z[:, None]**2
    j0 = -sigma**2/(8*delta**2)+sigma*np.log(sigma/delta**2)/4
    j1 = -sigma**3/(24*delta**3)
    j2 = -sigma**4/(64*delta**4)+sigma**2*np.log(sigma/delta**2)/16
    if kind == "corner":
        value = q*q*chi*phi/2*(j2+p*p*(j2-sigma*j0)/3)*kernel(Z)
        factor = -12*(2*PI)**2
        target = 12*2*PI*np.sum(xw*np.sqrt(q)*chi*phi*(1-p*p))
    else:
        lapf = -epsilon*np.sin(x)
        a1 = q*q*chi*phi
        a2 = q*q*(chi*pt-ct*phi)/2
        a3 = -q*q*(chi*phi*lapf/6+p*p*(ct*phi+chi*pt)/6+chi*p*px/3)-q*q1*chi*phi*p*p/3
        a4 = -q*q1*chi*phi*p*p/6
        kp = (-10+25*Z-12*Z**2+LD(4)/3*Z**3)*np.exp(-Z)
        value = (a1*j1+a2*j2+a3*(j2-sigma*j0))*kernel(Z)+a4*(j2-sigma*j0)*Z*kp
        factor = 2*PI
        target = np.sum(xw*(-2*a2+6*a3-9*a4)/q**LD('1.5'))
    model = factor*C*rho**LD('1.5')*np.sum(xw/scale*np.sum(zw[:, None]*value, axis=0))
    return model, target


def pilot_pairs(rho, *, delta=.08, part="full", order=40, chi=lambda t: 1,
                phi=lambda t: 1, flat=False, omega=1, wrong=None):
    """Whole unequal-axis planar pilot in original source/target/radius coordinates.

    No proposed limiting coefficient or phase inverse is used. Full_cone is
    the actual auxiliary ambient cone of N15, not a restricted interval claim.
    """
    if part not in ("full", "short", "long", "full_cone", "face", "corner"):
        raise ValueError("unknown component")
    ns, ws = gauss_nodes(order)
    rho, delta, omega = map(lambda x: LD(str(x)), (rho, delta, omega))
    volume, future_time, height = 8*PI, LD(1)/8, LD(1)/4
    q = lambda t: omega**4*(np.ones_like(t) if flat else density(t))
    point, pair = LD(0), LD(0)
    layers = np.zeros(4, dtype=LD)
    if part in ("face", "corner"):
        v = delta*ns[:, None]
        u = v*ns[None, :]
        T = (u+v)/2
        jac = 4*PI*delta*v*ws[:, None]*ws[None, :]*(v-u)**2/8
        for b, bw in zip(ns, ws):
            depth = b*T
            t = future_time-depth
            spatial = volume if part == "face" else -volume*np.expm1(LD('1.5')*np.log1p(-depth/height))
            h = omega**4*(1 if flat else phase_data(t, u, v)[0])
            pair += np.sum(jac*T*bw*spatial*q(t)*q(t+T)*chi(t)*phi(t+T)*kernel(c*rho*(u*v)**2*h))
        return {"pair": pair, "action": (1 if part == "face" else -1)*C*rho**LD('1.5')*pair}
    edges = sorted([LD(0), np.sqrt(1-delta/height), np.sqrt(1-delta/(2*height)), LD(1)])
    for left, right in zip(edges, edges[1:]):
        for a, aw in zip(left+(right-left)*ns, (right-left)*ws):
            t = future_time-height*(1-a*a)
            source = volume*2*height*a**4*aw
            point += source*q(t)*chi(t)*phi(t)
            upper = delta if part == "full_cone" else future_time-t
            cuts = sorted(set([LD(0), upper]+[p for p in (delta/2, delta) if p < upper]))
            for lo, hi in zip(cuts, cuts[1:]):
                T = (lo+(hi-lo)*ns)[:, None]
                rlo, rhi = np.zeros_like(T), T.copy()
                if part in ("short", "full_cone"):
                    rhi = np.minimum(T, np.maximum(0, delta-T))
                elif part == "long":
                    rlo = np.minimum(T, np.maximum(0, delta-T))
                r = rlo+(rhi-rlo)*ns[None, :]
                jac = (hi-lo)*(rhi-rlo)*ws[:, None]*ws[None, :]*4*PI*r*r
                h = omega**4*(1 if flat else phase_data(t, T-r, T+r)[0])
                if wrong == "phase":
                    h = q(t)
                Z = c*rho*(T*T-r*r)**2*h
                measure = (1 if wrong == "source" else q(t))*(1 if wrong == "target" else q(t+T))
                weight = source*jac*measure*chi(t)*phi(t+T)
                pair += np.sum(weight*kernel(Z))
                for k in range(4):
                    layers[k] += np.sum(weight*np.exp(-Z)*Z**k/math.factorial(k))
    if part == "long":
        point = LD(0)
    return {"point": point, "pair": pair, "layers": layers,
            "action": C*np.sqrt(rho)*(point-rho*pair)}


class NonpolynomialCertificates(unittest.TestCase):
    def test_exact_certificates(self):
        check_nonpolynomial_identities()

    def test_actual_phase_independent_rest_diamond_and_null(self):
        for t, u, v in ((-.12, 0, .7), (.1, .02, .3), (.1, .2, .2), (-.4, .8, .8)):
            with self.subTest(t=t, u=u, v=v):
                actual = float(phase_data(t, u, v)[0])
                self.assertAlmostEqual(actual, time_density_phase(density, t, u, v, order=40), places=12)
                if u == 0:
                    self.assertAlmostEqual(actual, null_ray_phase(density, t, v), places=12)
        t, T = -.125, .25
        vertical = 4*np.pi/3*(quad(lambda a: (a-t)**3*float(density(a)), t, t+T/2)[0]
                              +quad(lambda a: (t+T-a)**3*float(density(a)), t+T/2, t+T)[0])
        self.assertAlmostEqual(vertical, float(c*T**4*phase_data(t, T, T)[0]), places=14)
        # The log branch and small-y series agree at the switching boundary.
        for vv in (.7, .8):
            t = 0.
            self.assertAlmostEqual(float(phase_data(t, vv, vv)[0]),
                                   time_density_phase(density, t, vv, vv, order=56), places=10)

    def test_partial_and_moving_time_derivatives(self):
        t, u, v, step = .12, .025, .12, 1e-6
        values = phase_data(t, u, v)
        for j in range(3):
            args1, args2 = [t, u, v], [t, u, v]
            args1[j] += step
            args2[j] -= step
            derivative = (phase_data(*args1)[0]-phase_data(*args2)[0])/(2*step)
            self.assertAlmostEqual(float(derivative), float(values[j+1]), places=8)
        tu = -.7
        F = lambda e: (u+e)*v*np.sqrt(phase_data(t+tu*e, u+e, v)[0])
        numeric = (F(step)-F(-step))/(2*step)
        self.assertAlmostEqual(float(numeric), float(total_phase_derivative(t, u, v, tu)), places=10)
        self.assertGreater(abs(float(numeric-total_phase_derivative(t, u, v))), .002)

    def test_independent_metric_curvature_bulk_and_control(self):
        t, x, y, z = s.symbols("t x y z", real=True)
        metric, _, _, scalar = conformal_curvature(1/(1-t), (t, x, y, z))
        self.assertEqual(s.simplify(metric.det()+(1-t)**-8), 0)
        self.assertEqual(scalar, -12)  # Explicit #90 sign conversion.
        phi = 1+t+t*t+x*x+2*y*y+3*z*z+t*x
        inv, q = metric.inv(), (1-t)**-4
        coords = (t, x, y, z)
        box = sum(s.diff(q*inv[i, j]*s.diff(phi, coords[j]), coords[i])
                  for i in range(4) for j in range(4))/q
        expected = (1-t)**2*(s.diff(phi, t, 2)-sum(s.diff(phi, a, 2) for a in (x, y, z)))+2*(1-t)*s.diff(phi, t)
        self.assertEqual(s.simplify(box-expected), 0)
        bulk_time = 48*np.pi*quad(lambda t: (.5+4*t)**1.5/(1-t)**4, -.125, .125,
                                  epsabs=1e-13, epsrel=1e-12)[0]
        primitive = lambda t: 2/(1-t)**3  # derivative = R*q/2
        bulk_radial = 24*np.pi*quad(lambda r: r*r*(primitive(.125)-primitive(.125-.25*(1-r*r))), 0, 1,
                                    epsabs=1e-13, epsrel=1e-12)[0]
        self.assertAlmostEqual(bulk_time, bulk_radial, places=10)
        self.assertGreater(bulk_time, 15)
        self.assertTrue(2/3 < 1/(1+3/16) < 1/(1-3/16) < 2)
        self.assertLess(.5+1/16, 1)

    def test_induced_variable_angle_and_nonplanar_compensating_flux(self):
        # Direct normal/tangent surface quadrature, independent of N25.
        ns, ws = np.polynomial.legendre.leggauss(24)
        for epsilon in (0., 1/16):
            total = 0.
            for a, wa in zip(ns, ws):
                theta = (a+1)*np.pi/2
                for b, wb in zip(ns, ws):
                    az = (b+1)*np.pi
                    v, w, past, future_normal, _, _ = joint_data(theta, az, epsilon)
                    x = np.sin(theta)*np.cos(az)
                    omega = 1/(1-(.125+epsilon*np.sin(x)))
                    gamma = float(inner(past, future_normal))
                    area = omega**2*float(gram_density(v, w))
                    total += wa*wb*np.pi**2/2*area*gamma/np.sqrt(gamma*gamma-1)
            raw = 24*np.pi*quad(lambda x: (1-(epsilon*np.cos(x))**2)/(1-.125-epsilon*np.sin(x))**2, -1, 1)[0]
            flux = 24*np.pi*quad(lambda x: epsilon*np.cos(x)*x/2/(1-.125-epsilon*np.sin(x))**2, -1, 1)[0]
            self.assertAlmostEqual(total, raw-flux, delta=2e-7)
            if epsilon:
                self.assertGreater(flux, .1)
            else:
                self.assertAlmostEqual(total, 3072*np.pi/49, delta=2e-7)
        self.assertEqual((1/.5, 1/(1/6)), (2, 6))


class NonpolynomialShortDiagnostics(unittest.TestCase):
    def test_full_actual_coordinate_push_and_nonconstant_jets(self):
        phase = full_probe(.05, 1e8, order=40)[0]
        original = full_probe(.05, 1e8, order=80, original=True)
        refined = full_probe(.05, 1e8, order=96, original=True)
        self.assertLess(abs(original-refined), 1e-6)
        self.assertLess(abs(phase-refined), 1e-6)
        for name in ("one", "time2", "space2"):
            low = full_probe(.05, 1e8, field_name=name)
            high = full_probe(.05, 1e12, field_name=name)
            fine = full_probe(.05, 1e12, field_name=name, order=52)
            self.assertLess(np.max(np.abs(high-fine)), 2e-6)
            self.assertLess(abs(high[0]-high[1]), abs(low[0]-low[1]))
            self.assertLess(abs(high[0]-high[1]), .005)
            self.assertLess(abs(high[0]-high[2]), .02)
        # A second fixed cutoff, never a density-dependent cutoff.
        value = full_probe(.05, 1e12, delta=.06)
        self.assertLess(abs(value[0]-value[2]), .02)

    def test_boundary_original_push_and_signed_comparisons(self):
        weights = ((1, 2, -1), (1, -3, 2))
        for kind in ("face", "corner"):
            with self.subTest(kind=kind):
                phase = boundary_integral(kind, 1e8, weights=weights)
                original = boundary_integral(kind, 1e8, weights=weights, pushed=False, order=72)
                fine = boundary_integral(kind, 1e8, weights=weights, pushed=False, order=88)
                self.assertLess(abs(original-fine), 2e-6)
                self.assertLess(abs(phase-fine), 2e-5)
                low_model, _ = boundary_model(kind, 1e8, weights=weights)
                high = boundary_integral(kind, 1e12, weights=weights)
                refined = boundary_integral(kind, 1e12, weights=weights, order=22, radial_order=28,
                                            angles=5, depths=5)
                model, target = boundary_model(kind, 1e12, weights=weights)
                self.assertLess(abs(high-refined), .003)
                self.assertLess(abs(refined-model), abs(phase-low_model))
                self.assertLess(abs(refined-model), .04)
                self.assertLess(abs(refined-target), .08)

    def test_boundary_wrong_jacobian_and_missing_target_measure(self):
        for kind in ("face", "corner"):
            actual = boundary_integral(kind, 1e8)
            wrong = boundary_integral(kind, 1e8, omit_mixed=True)
            missing = boundary_integral(kind, 1e8, omit_target=True)
            self.assertGreater(abs(actual-wrong), .005)
            self.assertGreater(abs(actual-missing), .1)

    def test_nonzero_oriented_diagonal_strips(self):
        from scipy.optimize import brentq

        beta, lam, mu, direction, epsilon = .3, .6, .25, .4, 1/16
        f0 = float(future(mu, epsilon)[0])
        for kind, power in (("face", 3), ("corner", 3.5)):
            ratios = []
            for w in (1e-4, 1e-6):
                nu0 = np.sqrt(w)*(1-f0)
                diagonal = lambda v: v*v*np.sqrt(boundary_data(
                    kind, v, v, beta, lam, mu, direction, epsilon)[3])-w
                nu = brentq(diagonal, .8*nu0, 1.2*nu0, xtol=1e-16)
                self.assertGreater(abs(nu-nu0), .01*w)

                def amplitude(v):
                    F = lambda u: u*v*np.sqrt(boundary_data(
                        kind, u, v, beta, lam, mu, direction, epsilon)[3])-w
                    u = brentq(F, .5*v, 1.5*v, xtol=1e-16)
                    t, _, measure, _, fu = boundary_data(kind, u, v, beta, lam, mu, direction, epsilon)
                    return float(measure*density(t)*density(t+(u+v)/2)*(v-u)**2/(8*fu))

                strip = quad(amplitude, nu, nu0, epsabs=1e-32, epsrel=1e-6)[0]
                self.assertGreater(abs(strip), 1e-30)
                ratios.append(abs(strip)/w**power)
            self.assertTrue(.5 < ratios[1]/ratios[0] < 2)

    def test_both_spacetime_face_fluxes_are_retained(self):
        ns, ws = gauss_nodes(32)
        total, kinetic, upper_flux, lower_flux = (LD(0) for _ in range(4))
        for r, rw in zip(ns, ws):
            for mu, mw in zip(2*ns-1, 2*ws):
                f = future(r*mu, LD(1)/16)[0]
                ell = f-(1-r*r)/4
                t = ell+(f-ell)*ns
                jac = 12*PI*r*r*rw*mw  # abc*r^2 dr dS, abc=6
                chi, pt = 1+2*t, 1+2*t  # chi=1+2t, phi=t+t^2
                box = 2*(1-t)**2+2*(1-t)*pt
                total += jac*(f-ell)*np.sum(ws*chi*box*density(t))
                kinetic -= jac*(f-ell)*np.sum(ws*2*pt/(1-t)**2)
                upper_flux += jac*(1+2*f)**2/(1-f)**2
                lower_flux += jac*(1+2*ell)**2/(1-ell)**2
        self.assertLess(abs(total-kinetic-upper_flux+lower_flux), 1e-10)
        self.assertGreater(abs(upper_flux), 20)
        self.assertGreater(abs(lower_flux), 10)
        self.assertGreater(abs(total-kinetic), 1)

    def test_whole_pair_short_long_and_full_face_corner(self):
        rho = 200000
        full = pilot_pairs(rho)
        fine = pilot_pairs(rho, order=52)
        self.assertLess(abs(full["action"]-fine["action"]), 1e-7)
        for delta in (.07, .12):
            short = pilot_pairs(rho, delta=delta, part="short")
            long = pilot_pairs(rho, delta=delta, part="long")
            cone = pilot_pairs(rho, delta=delta, part="full_cone")
            face = pilot_pairs(rho, delta=delta, part="face")
            corner = pilot_pairs(rho, delta=delta, part="corner")
            self.assertLess(abs(short["action"]+long["action"]-full["action"]), 1e-7)
            self.assertLess(abs(cone["action"]+face["action"]+corner["action"]-short["action"]), 1e-7)
            self.assertGreater(abs(long["action"]), 1)
            self.assertGreater(abs(corner["action"]), .1)
            self.assertEqual(long["point"], 0)

    def test_complete_signed_partitions_and_expectation_coefficients(self):
        rho = 30000
        sources = (lambda t: 1+2*t, lambda t: -2*t)
        targets = (lambda t: .4+3*t, lambda t: .6-3*t)
        pieces = [[pilot_pairs(rho, chi=chi, phi=phi, order=18) for phi in targets] for chi in sources]
        full = pilot_pairs(rho, order=18)
        for key in ("point", "pair", "action"):
            self.assertLess(abs(sum(p[key] for row in pieces for p in row)-full[key]), 1e-9)
        self.assertGreater(abs(pieces[0][1]["pair"]+pieces[1][0]["pair"]), 1e-5)
        self.assertGreater(abs(sum(pieces[i][i]["action"] for i in range(2))-full["action"]), 1)
        pair_mean = rho*rho*np.dot([1, -9, 16, -8], full["layers"])
        mean = C/np.sqrt(rho)*(rho*full["point"]-pair_mean)
        self.assertLess(abs(mean-full["action"]), 1e-9)
        self.assertGreater(abs(C/np.sqrt(rho)*(rho*full["point"]-pair_mean/2)-mean), 1)
        self.assertGreater(abs(C/np.sqrt(rho)*(rho*full["point"]-pair_mean/rho)-mean), 1)
        for wrong in ("source", "target", "phase"):
            self.assertGreater(abs(pilot_pairs(rho, wrong=wrong)["action"]-full["action"]), .1)

    def test_flat_and_constant_factor_calibrations(self):
        rho = 30000
        flat = pilot_pairs(rho, flat=True)["action"]
        with mp.workdps(30):
            reference = ellipsoid_action(rho, .25, (1, 2, 3))
        self.assertAlmostEqual(float(flat), float(reference), delta=1e-8)
        for omega in (.7, 1.4):
            value = pilot_pairs(rho, flat=True, omega=omega)["action"]
            reference = omega**2*pilot_pairs(rho*omega**4, flat=True)["action"]
            self.assertLess(abs(value-reference), 1e-8)


if __name__ == "__main__":
    unittest.main()
