"""Finite evidence for #74's written collar producer, not #75's joint proof.

Quadratures retain the actual interval density, both endpoint measures and the
fixed u,v cutoff. Gauss nodes are generated above float64 precision using the
existing interior diagnostic's quadrature helper. No production API changes.
"""

import unittest

import mpmath as mp
import numpy as np
import sympy as s

from curved_boundary_collar import (
    check_boundary_collar_identities, face_basis_responses, face_jet_coefficients,
    face_response, future_flux_density, moving_lower_second, time_interval_split,
)
from curved_bulk_pilot import scalar_curvature
from test_curved_interior_short import (
    C, LD, PI, VOLUME_CONSTANT as c, actual_h, gauss_nodes, kernel,
)


def profile(x, epsilon, kind="sine"):
    if kind == "sine":
        return LD(1)/8+epsilon*np.sin(x), epsilon*np.cos(x), -epsilon*np.sin(x)
    if kind == "c3":
        a = np.abs(x)
        value = LD(1)/8+epsilon*a**LD("3.5")/(1+x*x)**LD("1.75")
        first = epsilon*LD("3.5")*np.sign(x)*a**LD("2.5")/(1+x*x)**LD("2.75")
        second = epsilon*LD("1.75")*a**LD("1.5")*(5-6*x*x)/(1+x*x)**LD("3.75")
        return value, first, second
    raise ValueError("unknown future profile")


def phase_nodes(order):
    ns, ws = gauss_nodes(order)
    edges = list(map(LD, ("0", ".000001", ".0001", ".01", ".1", ".5", "1", "2", "4", "8", "12")))
    return (np.concatenate([a+(b-a)*ns for a, b in zip(edges, edges[1:])]),
            np.concatenate([(b-a)*ws for a, b in zip(edges, edges[1:])]))


def face_model(z1, rho, delta=.1, epsilon=1/16, weights=(0, 0, 0, 0), kind="sine"):
    """Entire finite face two-jet and its independently derived basis response."""
    z1, rho, delta, epsilon = map(lambda x: LD(str(x)), (z1, rho, delta, epsilon))
    alpha, beta, gamma, kappa = map(lambda x: LD(str(x)), weights)
    f, fp, fpp = profile(z1, epsilon, kind)
    q, q1 = 1+f*f, 2*f
    chi, phi = 1+alpha*f+beta*z1, 1+gamma*f+kappa*z1
    a1 = q*q*chi*phi
    a2 = q*q*(chi*gamma-alpha*phi)/2
    a3 = (-q*q*(chi*phi*fpp/6+fp*fp*(alpha*phi+chi*gamma)/6+chi*fp*kappa/3)
          - q*q1*chi*phi*fp*fp/3)
    a4 = -q*q1*chi*phi*fp*fp/6
    target = (-2*a2+6*a3-9*a4)/q**LD("1.5")
    z, zw = phase_nodes(40)
    scale = np.sqrt(c*rho*q)
    sigma, arg = z/scale, z*z
    # Exact zero signed moments remove only these polynomial pieces. The
    # nonzero finite T*K response and every remaining cutoff term are retained.
    j0 = -sigma*sigma/(8*delta*delta)+sigma*np.log(sigma/delta**2)/4
    j1 = -sigma**3/(24*delta**3)
    j2 = -sigma**4/(64*delta**4)+sigma*sigma*np.log(sigma/delta**2)/16
    kp = (-10+25*arg-12*arg**2+LD(4)/3*arg**3)*np.exp(-arg)
    model = C*rho**LD("1.5")*2*PI/scale*np.sum(zw*(
        (a1*j1+a2*j2+a3*(j2-sigma*j0))*kernel(arg)+a4*(j2-sigma*j0)*arg*kp))
    return model, target


def face_phase(z1, rho, delta=.1, epsilon=1/16, weights=(0, 0, 0, 0), *,
               order=40, angles=6, depths=6, measures="both", omit_mixed=False, kind="sine"):
    """Actual single-face integral after exact depth and phase changes.

    Spatial source is fixed at (z1,0,0); angular symmetry leaves mu=n1.
    Fields are chi=1+alpha*t+beta*z1, phi=1+gamma*t+kappa*z1.
    Integrate z=sqrt(c*rho)*w to 12 with negligible Gaussian tail in the
    high-density fixtures below. The flags are wrong-observable controls.
    """
    z1, rho, delta, epsilon = map(lambda x: LD(str(x)), (z1, rho, delta, epsilon))
    alpha, beta, gamma, kappa = map(lambda x: LD(str(x)), weights)
    ns, ws = gauss_nodes(order)
    ang, aw = gauss_nodes(angles)
    bs, bw = gauss_nodes(depths)
    z, zw = phase_nodes(order)
    scale = np.sqrt(c*rho)
    if scale*delta*delta <= 12:
        raise ValueError("cutoff does not exceed the diagnostic's Gaussian tail")
    w = z/scale
    f, _, _ = profile(z1, epsilon, kind)
    q = 1+f*f
    total = np.zeros_like(w)

    def metric_weights(t, ty):
        if measures == "both":
            return (1+t*t)*(1+ty*ty)
        if measures == "source":
            return 1+t*t
        if measures == "target":
            return 1+ty*ty
        raise ValueError("unknown measure control")

    for mu, muw in zip(2*ang-1, 2*aw):
        for b, wb in zip(bs, bw):
            nu = np.sqrt(w)/q**LD(".25")
            qq = b*b-b+LD(4)/15
            for _ in range(8):
                hd = q+f*(1-2*b)*nu+qq*nu*nu
                hd1 = f*(1-2*b)+2*qq*nu
                nu -= (nu*nu*np.sqrt(hd)-w)/(nu*(4*hd+nu*hd1)/(2*np.sqrt(hd)))
            log_range = np.log(delta/nu)[:, None]
            v = nu[:, None]*np.exp(ns[None, :]*log_range)

            def data(u, v):
                T, r = (u+v)/2, (v-u)/2
                shifted, slope, _ = profile(z1+r*mu, epsilon, kind)
                gap = T+f-shifted
                t = f-b*gap
                h = actual_h(t, u, v)
                ht, hu = 2*t+(u+v)/2, t/2+3*u/20+7*v/60
                gap_u = (1+slope*mu)/2
                fu = v*(2*h+u*(hu-b*gap_u*ht))/(2*np.sqrt(h))
                return T, r, gap, t, h, fu

            _, _, _, _, h0, _ = data(0, v)
            u = w[:, None]/(v*np.sqrt(h0))
            for _ in range(8):
                _, _, _, _, h, fu = data(u, v)
                u -= (u*v*np.sqrt(h)-w[:, None])/fu
            T, r, gap, t, h, fu = data(u, v)
            if omit_mixed:
                fu = v*(2*h+u*(t/2+3*u/20+7*v/60))/(2*np.sqrt(h))
            value = (metric_weights(t, t+T)*(1+alpha*t+beta*z1)
                     *(1+gamma*(t+T)+kappa*(z1+r*mu))*(v-u)**2*gap/(8*fu))

            def null(v0):
                T0, r0, d0, t0, _, fu0 = data(0, v0)
                return (metric_weights(t0, t0+T0)*(1+alpha*t0+beta*z1)
                        *(1+gamma*(t0+T0)+kappa*(z1+r0*mu))*v0*v0*d0/(8*fu0))

            # Subtract B(0) inside the radial integral. Its whole-half-line
            # signed moment is zero; doing this before quadrature is stable.
            difference = (np.sum(ws[None, :]*(value-null(v))*v*log_range, axis=1)
                          - np.sum(ws[None, :]*nu[:, None]*null(nu[:, None]*ns[None, :]), axis=1))
            total += muw*wb*difference
    return C*rho**LD("1.5")*2*PI/scale*np.sum(zw*kernel(z*z)*total)


def face_original(z1, rho, delta=.1, epsilon=1/16, weights=(0, 0, 0, 0), order=96):
    """Independent actual u,v,depth quadrature without a phase Jacobian."""
    z1, rho, delta, epsilon = map(lambda x: LD(str(x)), (z1, rho, delta, epsilon))
    alpha, beta, gamma, kappa = map(lambda x: LD(str(x)), weights)
    ns, ws = gauss_nodes(order)
    ang, aw = gauss_nodes(8)
    bs, bw = gauss_nodes(8)
    v = delta*ns[:, None]
    u = v*ns[None, :]
    T, r = (u+v)/2, (v-u)/2
    f, _, _ = profile(z1, epsilon)
    jac = delta*v*ws[:, None]*ws[None, :]*(v-u)**2/8
    total = LD(0)
    for mu, muw in zip(2*ang-1, 2*aw):
        gap = T+f-profile(z1+r*mu, epsilon)[0]
        for b, wb in zip(bs, bw):
            t = f-b*gap
            values = ((1+t*t)*(1+(t+T)**2)*(1+alpha*t+beta*z1)
                      *(1+gamma*(t+T)+kappa*(z1+r*mu))
                      * kernel(c*rho*(u*v)**2*actual_h(t, u, v)))
            total += muw*wb*np.sum(jac*gap*values)
    return C*rho**LD("1.5")*2*PI*total


def planar_corner(rho, delta=.1, order=128, axes=(1, 2, 3)):
    """Actual J for the unequal-axis height cap, not an assumed hinge jet.

    Interchanging source height and depth gives the exact ellipsoidal collar
    volume. Both time-dependent measures and the curved interval phase remain.
    """
    rho, delta = LD(str(rho)), LD(str(delta))
    ns, ws = gauss_nodes(order)
    bs, bw = gauss_nodes(12)
    v = delta*ns[:, None]
    u = v*ns[None, :]
    T = (u+v)/2
    jac = delta*v*ws[:, None]*ws[None, :]*(v-u)**2/8
    f, height, product = LD(1)/8, LD(1)/4, LD(np.prod(axes))
    total = LD(0)
    for b, wb in zip(bs, bw):
        depth = b*T
        t = f-depth
        collar = -(4*PI*product/3)*np.expm1(LD("1.5")*np.log1p(-depth/height))
        total += wb*np.sum(jac*T*collar*(1+t*t)*(1+(t+T)**2)
                           * kernel(c*rho*(u*v)**2*actual_h(t, u, v)))
    return -C*rho**LD("1.5")*4*PI*total


class CollarCertificates(unittest.TestCase):
    def test_exact_certificates(self):
        check_boundary_collar_identities()

    def test_weighted_time_restoration_including_contacts(self):
        a = s.Symbol("a")
        primitive = a+2*a*a/2+3*a**3/3+5*a**4/4
        for height, gap in ((s.Rational(1, 8), s.Rational(1, 16)),
                            (s.Rational(1, 32), s.Rational(1, 16)),
                            (s.Rational(1, 16), s.Rational(1, 16)),
                            (0, s.Rational(1, 16))):
            actual, full, face, corner = time_interval_split(primitive, a, height, gap)
            self.assertEqual(s.expand(actual-full+face-corner), 0)
            if height <= gap:
                self.assertEqual(actual, 0)
            if height >= gap:
                self.assertEqual(corner, 0)
            else:
                self.assertNotEqual(full-face, actual)

    def test_actual_curved_signed_density_restoration(self):
        # Independent time quadrature, not a polynomial/constant-density hinge.
        with mp.workdps(40):
            f, u, v, mu = map(mp.mpf, (".14", ".03", ".1", ".4"))
            T, r = (u+v)/2, (v-u)/2
            gap = T-mp.mpf(".08")*r*mu-mp.mpf(".03")*(r*mu)**2
            for rho in (mp.mpf(1), mp.mpf("1000000")):
                def density(a):
                    t = f-a
                    phase = 1+t*t+t*(u+v)/2+3*(u+v)**2/40-u*v/30
                    z = mp.pi/24*rho*(u*v)**2*phase
                    k = (1-9*z+8*z*z-mp.mpf(4)/3*z**3)*mp.exp(-z)
                    return (1+t*t)*(1+(t+T)**2)*(1+2*t)*(1-3*(t+T)+r*mu)*k
                for height in (gap/2, gap, gap*2):
                    actual = mp.quad(density, [gap, height]) if height > gap else 0
                    full, face = mp.quad(density, [0, height]), mp.quad(density, [0, gap])
                    corner = mp.quad(density, [height, gap]) if height < gap else 0
                    self.assertLess(abs(actual-full+face-corner), mp.mpf("1e-36"))
                    if height < gap:
                        self.assertGreater(abs(corner), mp.mpf("1e-8"))

    def test_all_moving_reference_boundary_terms(self):
        w, v = s.symbols("w v", real=True)
        lower = 1+w/2+w*w/3
        e = v**4+w*v*v+w*w*(1+v)
        integral = s.integrate(e, (v, lower, 3))
        at = lambda expression: expression.subs(v, lower)
        result = moving_lower_second(s.integrate(s.diff(e, w, 2), (v, lower, 3)),
                                      at(e), at(s.diff(e, w)), at(s.diff(e, v)),
                                      s.diff(lower, w), s.diff(lower, w, 2))
        self.assertEqual(s.expand(result-s.diff(integral, w, 2)), 0)

    def test_oriented_diagonal_strip_is_retained_and_cubic(self):
        with mp.workdps(45):
            z, eps, mu, b = map(mp.mpf, (".2", ".0625", ".4", ".75"))
            f = mp.mpf(1)/8+eps*mp.sin(z)
            q = 1+f*f
            ratios = []
            for w in (mp.mpf("1e-4"), mp.mpf("1e-6"), mp.mpf("1e-8")):
                reference = mp.sqrt(w)/q**mp.mpf(".25")
                diagonal = lambda v: v*v*mp.sqrt(q+f*(1-2*b)*v+(b*b-b+mp.mpf(4)/15)*v*v)
                lower = mp.findroot(lambda v: diagonal(v)-w, reference)

                def amplitude(v):
                    def data(u):
                        T, r = (u+v)/2, (v-u)/2
                        gap = T+f-(mp.mpf(1)/8+eps*mp.sin(z+r*mu))
                        t = f-b*gap
                        h = 1+t*t+t*(u+v)/2+3*(u+v)**2/40-u*v/30
                        hu, ht = t/2+3*u/20+7*v/60, 2*t+(u+v)/2
                        gap_u = (1+eps*mp.cos(z+r*mu)*mu)/2
                        fu = v*(2*h+u*(hu-b*gap_u*ht))/(2*mp.sqrt(h))
                        return T, gap, t, h, fu
                    u = mp.findroot(lambda u: u*v*mp.sqrt(data(u)[3])-w, w/(v*mp.sqrt(q)))
                    T, gap, t, _, fu = data(u)
                    return (1+t*t)*(1+(t+T)**2)*(v-u)**2*gap/(8*fu)

                strip = mp.quad(amplitude, [lower, reference])
                ratios.append(strip/w**3)
                self.assertLess(strip, 0)  # Oriented, not silently clipped away.
                self.assertGreater(abs(strip/w**3), mp.mpf("1e-14"))
                self.assertLess(abs(strip/w**3), 1)
            self.assertLess(abs(ratios[-1]/ratios[-2]-1), mp.mpf(".01"))

    def test_c3_not_c4_future_is_in_the_remainder_class(self):
        # eps*|x|^(7/2)/(1+x^2)^(7/4) is globally C3 and Lipschitz, not C4.
        x, v, ratio = s.symbols("x v ratio", positive=True)
        smooth_side = x**s.Rational(7, 2)/(1+x*x)**s.Rational(7, 4)
        self.assertEqual(s.limit(s.diff(smooth_side, x, 3), x, 0, dir="+"), 0)
        self.assertEqual(s.limit(s.diff(smooth_side, x, 4), x, 0, dir="+"), s.oo)
        # At source zero, D0=(1+ratio)/2 and D1=0.
        remainder = -smooth_side.subs(x, v*(1-ratio)/2)/(16*v)
        for j in range(4):
            evaluator = s.lambdify((v, ratio), s.diff(remainder, ratio, j), "numpy")
            for small in (1/4, 1/8, 1/32, 1/128):
                for r in (0, .3, .9):
                    self.assertLess(abs(evaluator(small, r))/small**2, 1)
        for j in (0, 1):
            evaluator = s.lambdify((v, ratio), s.diff(remainder, v, 1, ratio, j), "numpy")
            for small in (1/4, 1/16, 1/64):
                self.assertLess(abs(evaluator(small, .3))/small, 1)
        # |f'| <= (7/2)*eps; together with the cap's kappa=1/2 this is strict.
        self.assertLess(s.Rational(1, 2)+s.Rational(7, 32), 1)

    def test_partition_and_field_derivatives_are_not_zero_individually(self):
        q = s.Rational(65, 64)
        first = face_response(q, s.Rational(1, 4), s.Rational(1, 16), s.Rational(1, 10),
                              s.Rational(2, 5), 3)
        second = face_response(q, s.Rational(1, 4), s.Rational(1, 16), s.Rational(1, 10),
                               s.Rational(3, 5), -3)
        total = face_response(q, s.Rational(1, 4), s.Rational(1, 16), s.Rational(1, 10))
        self.assertEqual(s.simplify(first+second-total), 0)
        self.assertNotEqual(first, s.Rational(2, 5)*total)
        flux = future_flux_density(q, 1, 2, 3, 4, 5, 6)
        self.assertEqual(flux, 9*s.sqrt(q))
        # Removing the phase derivative changes the actual face coefficient.
        coefficients = face_jet_coefficients(q, s.Rational(1, 4), s.Rational(1, 16), 0)
        self.assertNotEqual(coefficients[3]*face_basis_responses(q)[3], 0)


class CollarQuadrature(unittest.TestCase):
    def test_original_coordinate_and_phase_agree(self):
        weights = (.6, .2, -.4, .3)
        actual = face_original(.2, 1e8, weights=weights)
        pushed = face_phase(.2, 1e8, weights=weights)
        self.assertLess(abs(actual-pushed), 2e-8)

    def test_actual_face_remainder_at_fixed_cutoffs(self):
        for delta, weights in ((.1, (0, 0, 0, 0)), (.1, (.6, .2, -.4, .3)),
                               (1/16, (0, 0, 0, 0))):
            errors = []
            for rho in (1e8, 1e12):
                model, target = face_model(.2, rho, delta, weights=weights)
                actual = face_phase(.2, rho, delta, weights=weights)
                errors.append(abs(actual-model))
                # The finite cutoff's T*K term must not be mistaken for zero.
                self.assertGreater(abs(model-target), .01)
            self.assertLess(errors[1], errors[0]/30)
            self.assertLess(errors[1], .0003)

    def test_phase_refinement_and_c3_example(self):
        ordinary = face_phase(.2, 1e12)
        refined = face_phase(.2, 1e12, order=56, angles=8, depths=8)
        self.assertLess(abs(ordinary-refined), 2e-8)
        actual = face_phase(0, 1e12, kind="c3")
        model, target = face_model(0, 1e12, kind="c3")
        self.assertEqual(target, 0)
        self.assertLess(abs(actual-model), .0003)

    def test_both_measures_and_mixed_phase_jacobian(self):
        # Even a planar future has curved spacetime density. Dropping either
        # endpoint measure manufactures oppositely signed face contributions.
        correct = face_phase(0, 1e12, epsilon=0)
        source_only = face_phase(0, 1e12, epsilon=0, measures="source")
        target_only = face_phase(0, 1e12, epsilon=0, measures="target")
        bad_jacobian = face_phase(0, 1e12, epsilon=0, omit_mixed=True)
        self.assertGreater(source_only-correct, .2)
        self.assertLess(target_only-correct, -.2)
        self.assertGreater(abs(bad_jacobian-correct), .02)

    def test_nonplanar_single_face_joint_flux(self):
        # Compare -div(sqrt(q(f))*Df) in an unequal-axis ball with its boundary
        # flux. This is a single-face divergence check, not a joint action limit.
        ns, ws = gauss_nodes(32)
        mu = 2*ns-1
        axes = (LD(1), LD(2), LD(3))
        product = np.prod(axes)
        eps = LD(1)/16
        r = ns[:, None]
        x = axes[0]*r*mu[None, :]
        f, fp, fpp = profile(x, eps)
        volume = -4*PI*product*np.sum(ws[:, None]*ws[None, :]*r*r
                                     *(np.sqrt(1+f*f)*fpp+f*fp*fp/np.sqrt(1+f*f)))
        fb, fpb, _ = profile(axes[0]*mu, eps)
        boundary = 4*PI*product/axes[0]*np.sum(ws*np.sqrt(1+fb*fb)*fpb*mu)
        self.assertLess(abs(volume+boundary), 1e-12)
        self.assertGreater(abs(boundary), 1e-4)

    def test_both_spacetime_fluxes_in_integration_by_parts(self):
        ns, ws = gauss_nodes(24)
        radius = ns[:, None]
        f = LD(1)/8
        ell = f-(1-radius*radius)/4
        height = f-ell
        t = ell+height*ns[None, :]
        alpha, beta = LD(".6"), LD(".2")
        chi = 1+alpha*t+beta*radius*radius
        box_density = chi*np.sqrt(1+t*t)*(-4+2*t*t/(1+t*t))
        gradient_density = np.sqrt(1+t*t)*(2*alpha*t-4*beta*radius*radius)
        volume = 4*PI*np.sum(ws[:, None]*ws[None, :]*radius*radius*height
                             *(box_density+gradient_density))
        r = ns
        lower = f-(1-r*r)/4
        future = np.sqrt(1+f*f)*(1+alpha*f+beta*r*r)*2*f
        past = np.sqrt(1+lower*lower)*(1+alpha*lower+beta*r*r)*(2*lower+r*r)
        boundary = 4*PI*np.sum(ws*r*r*(future-past))
        self.assertLess(abs(volume-boundary), 1e-12)
        self.assertGreater(abs(4*PI*np.sum(ws*r*r*past)), .01)

    def test_actual_corner_is_not_small_volume_error(self):
        # This original unequal-axis cap has nonzero R and joint angle weights
        # 2 and 6 on different axes. The test is finite evidence only for #75.
        self.assertGreater(scalar_curvature(s.Rational(1, 8)), 0)
        self.assertEqual([s.Rational(b, 1)/(2*s.Rational(1, 4)) for b in (1, 3)], [2, 6])
        independent_target = 48*PI*np.sqrt(1+LD(1)/64)
        low = planar_corner(1e8)
        high = planar_corner(1e9)
        refined = planar_corner(1e9, order=160)
        self.assertGreater(high, 100)
        self.assertLess(abs(high-refined), 2e-7)
        self.assertLess(abs(high-independent_target), abs(low-independent_target))
        self.assertLess(abs(high-independent_target), .5)


if __name__ == "__main__":
    unittest.main()
