"""Independent actual-fibre regressions, not a proof by numerical fitting."""

from functools import lru_cache
import unittest

from mpmath import mp
import sympy as s

import curved_contact_long as cl


def _h(t, u, v):
    # Independent midpoint/boost interval formula, not the symbolic null helper.
    T = (u+v)/2
    return 1+(t+T/2)**2+T*T/20-u*v/30


def _phase(t, u, v):
    return u*v*mp.sqrt(_h(t, u, v))


def _fu(t, u, v):
    H = _h(t, u, v)
    return v*(2*H+u*(t/2+3*u/20+7*v/60))/(2*mp.sqrt(H))


def _inverse(t, v, w):
    if not w:
        return mp.mpf(0)
    return mp.findroot(lambda u: _phase(t, u, v)-w,
                       w/(v*mp.sqrt(_h(t, 0, v))),
                       df=lambda u: _fu(t, u, v), solver="newton")


def _kernel(z):
    return (1-9*z+8*z*z-4*z**3/3)*mp.exp(-z)


@lru_cache(maxsize=12)
def _nodes(order, precision):
    return mp.gauss_quadrature(order, "legendre")


def _quad(function, lower, upper, order=24):
    if lower == upper:
        return mp.mpf(0)
    nodes, weights = _nodes(order, mp.dps)
    middle, half = (upper+lower)/2, (upper-lower)/2
    return half*mp.fsum(weight*function(middle+half*node)
                        for node, weight in zip(nodes, weights))


class _Ray:
    """One actual ellipsoid/sine geometry ray; all future partners retained.

    Only the proved small phase collar w<delta^2/4 is evaluated. No method
    silently substitutes this collar for the full action at finite density.
    """

    def __init__(self, x=("0.2", 0, 0), n=(1, 0, 0), axes=(1, 1, 1),
                 bend=0, delta="0.125", weighted=False):
        self.x, self.n, self.axes = [tuple(map(mp.mpf, a)) for a in (x, n, axes)]
        self.bend, self.delta = mp.mpf(bend), mp.mpf(delta)
        self.weighted = weighted
        self.height = (1-mp.fsum((x/b)**2 for x, b in zip(self.x, self.axes)))/4
        self.lower = self.future(self.x)-max(0, self.height)
        self.root = 0
        if self.height > 0 and self.null_gap(self.delta) > 0:
            self.root = 2*self.height if not self.bend else mp.findroot(
                self.null_gap, (self.delta, 2*self.height/(1-abs(self.bend))))

    def future(self, x):
        return mp.mpf(1)/8+self.bend*mp.sin(x[0])

    def target_space(self, u, v):
        return tuple(x+(v-u)*n/2 for x, n in zip(self.x, self.n))

    def null_gap(self, v):
        return self.future(self.target_space(0, v))-v/2-self.lower

    def upper_time(self, u, v):
        return self.future(self.target_space(u, v))-(u+v)/2

    def tau(self, v, w):
        if not w:
            return self.upper_time(0, v)
        # Solve at the actual future face, not by differentiating a fitted jet.
        u = mp.findroot(lambda u: _phase(self.upper_time(u, v), u, v)-w,
                        w/(v*mp.sqrt(_h(self.upper_time(0, v), 0, v))))
        return self.upper_time(u, v)

    def weight(self, t, u, v):
        if not self.weighted:
            return mp.mpf(1)
        # Signed source with nonzero time derivative; nonconstant target field.
        chi = -1+t+self.x[0]/3
        phi = 1+2*(t+(u+v)/2)+self.target_space(u, v)[0]**2
        return chi*phi

    def amplitude(self, t, v, w):
        u = _inverse(t, v, w)
        return (self.weight(t, u, v)*(1+t*t)*(1+(t+(u+v)/2)**2)
                * (v-u)**2/(8*_fu(t, u, v)))

    def fibre(self, w, order=24):
        w = mp.mpf(w)
        if w < 0 or w >= self.delta**2/4:
            raise ValueError("this diagnostic evaluates only the small phase collar")
        if not self.root:
            return mp.mpf(0)
        def gap(v):
            u = _inverse(self.lower, v, w)
            return self.upper_time(u, v)-self.lower
        if gap(self.delta) <= 0:
            return mp.mpf(0)
        root = self.root if not w else mp.findroot(gap, self.root)
        return _quad(lambda v: _quad(lambda t: self.amplitude(t, v, w),
                                     self.lower, self.tau(v, w), order),
                     self.delta, root, order)


class CurvedContactLongTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        # Symbolically differentiate the FULL density, then evaluate at u=0.
        # d/dw = (1/F_u)*d/du at fixed source time, not just d/du.
        t, u, v, x, n, weighted = s.symbols("t u v x n weighted", real=True)
        chi = -1+t+x/3
        phi = 1+2*(t+(u+v)/2)+(x+(v-u)*n/2)**2
        a = cl.pair_amplitude(t, u, v, 1+weighted*(chi*phi-1))
        aw = s.diff(a, u)/cl.phase_derivative(t, u, v)
        aww = s.diff(aw, u)/cl.phase_derivative(t, u, v)
        cls.derivatives = [s.lambdify((t, v, x, n, weighted), e.subs(u, 0),
                                      "mpmath", cse=True)
                           for e in (a, aw, aww, s.diff(a, t))]

    def setUp(self):
        context = mp.workdps(42)
        context.__enter__()
        self.addCleanup(context.__exit__, None, None, None)

    def assertNear(self, actual, expected, tolerance="1e-24"):
        self.assertLessEqual(abs(actual-expected),
                             mp.mpf(tolerance)*max(1, abs(expected)))

    def _jet(self, ray):
        if not ray.root:
            return (mp.mpf(0),)*4
        funcs = [lambda t, v, fn=fn: fn(t, v, ray.x[0], ray.n[0], int(ray.weighted))
                 for fn in self.derivatives]
        a0, aw, aww, at = funcs

        def time_derivatives(v):
            t = ray.upper_time(0, v)
            target = ray.target_space(0, v)[0]
            slope = ray.bend*mp.cos(target)*ray.n[0]
            hessian = -ray.bend*mp.sin(target)*ray.n[0]**2
            H = _h(t, 0, v)
            b = (1+slope)/2
            return (-b/(v*mp.sqrt(H)), hessian/(4*v*v*H)
                    +(b*(t/2+7*v/60)-b*b*(2*t+v/2))/(v*v*H*H))

        def js(v):
            t = ray.upper_time(0, v)
            t1, t2 = time_derivatives(v)
            integrals = [_quad(lambda time: fn(time, v), ray.lower, t, 24)
                         for fn in (a0, aw, aww)]
            # Spell out (A9) numerically, independently of the symbolic helper.
            return (integrals[0], integrals[1]+a0(t, v)*t1,
                    integrals[2]/2+aw(t, v)*t1+at(t, v)*t1*t1/2+a0(t, v)*t2/2)

        nodes, weights = _nodes(32, mp.dps)
        half, middle = (ray.root-ray.delta)/2, (ray.root+ray.delta)/2
        integrals = [mp.mpf(0)]*3
        for node, weight in zip(nodes, weights):
            values = js(middle+half*node)
            for j in range(3):
                integrals[j] += half*weight*values[j]
        t1, _ = time_derivatives(ray.root)
        slope = ray.bend*mp.cos(ray.target_space(0, ray.root)[0])*ray.n[0]
        contact = a0(ray.lower, ray.root)*t1*t1/(1-slope)
        return (*integrals[:2], integrals[2]+contact, contact)

    def test_exact_phase_leibniz_and_contact_certificates(self):
        cl.check_contact_long_identities()

    def test_phase_and_both_measures_against_midpoint_formula(self):
        for t, u, v in (("-2", ".01", ".2"), (".1", ".003", ".125"),
                        ("3", "1", "2")):
            t, u, v = map(mp.mpf, (t, u, v))
            actual = cl.phase(*map(lambda a: s.Rational(str(a)), (t, u, v)))
            self.assertNear(mp.mpf(str(s.N(actual, 44))), _phase(t, u, v))
            self.assertNear(_inverse(t, v, _phase(t, u, v)), u)
            density = cl.pair_amplitude(*map(lambda a: s.Rational(str(a)), (t, u, v)))
            raw = (1+t*t)*(1+(t+(u+v)/2)**2)*(v-u)**2/8
            self.assertNear(mp.mpf(str(s.N(density, 44)))*_fu(t, u, v), raw)
            self.assertNotEqual(raw/(1+t*t), raw)
            self.assertNotEqual(raw/(1+(t+(u+v)/2)**2), raw)

    def test_actual_time_boundary_derivatives_include_mixed_phase_and_curvature(self):
        for bend in (0, mp.mpf(1)/8):
            ray = _Ray(bend=bend, axes=(1, 2, 3))
            v = mp.mpf(".2")
            t = ray.tau(v, 0)
            slope = bend*mp.cos(ray.target_space(0, v)[0])
            hessian = -bend*mp.sin(ray.target_space(0, v)[0])
            t1, t2 = cl.time_boundary_derivatives(
                *map(lambda a: s.Rational(str(a)), (t, v, slope, hessian)))
            t1, t2 = (mp.mpf(str(s.N(a, 44))) for a in (t1, t2))
            self.assertNear(mp.diff(lambda w: ray.tau(v, w), 0), t1)
            self.assertNear(mp.diff(lambda w: ray.tau(v, w), 0, 2), t2)
            H = _h(t, 0, v)
            omitted = ((1+slope)/2)**2*(2*t+v/2)/(v*v*H*H)
            self.assertGreater(abs(omitted), mp.mpf(".01"))
            if bend:
                self.assertGreater(abs(hessian/(4*v*v*H)), mp.mpf(".01"))

    def test_actual_weighted_jets_and_both_moving_boundaries(self):
        for bend, weighted in ((0, False), (mp.mpf(1)/8, True)):
            ray = _Ray(bend=bend, axes=(1, 2, 3), weighted=weighted)
            b0, b1, b2, contact = self._jet(ray)
            self.assertNear(ray.fibre(0, 32), b0, "1e-22")
            errors = []
            for w in map(mp.mpf, ("1e-6", "1e-7")):
                quotient = (ray.fibre(w, 32)-b0-b1*w)/w**2
                errors.append(abs(quotient-b2))
            self.assertLess(errors[-1], errors[0]/9)
            self.assertNear(quotient, b2, "2e-5")
            self.assertGreater(abs(contact), mp.mpf(".01"))
            self.assertNear(quotient-(b2-contact), contact, "2e-5")
            if weighted:
                self.assertLess(b0, 0)
                self.assertLess(contact, 0)
                # Source derivative really appears in partial_t a0 at the edge.
                t, v = ray.lower, ray.root
                a0 = self.derivatives[0](t, v, ray.x[0], 1, 1)
                chi = -1+t+ray.x[0]/3
                t1 = -((1+bend*mp.cos(ray.target_space(0, v)[0]))/2)
                t1 /= v*mp.sqrt(_h(t, 0, v))
                source_derivative_term = a0/chi*t1*t1/2
                self.assertGreater(abs(source_derivative_term), mp.mpf(".001"))

    def test_exact_cutoff_contacts_empty_sources_and_critical_center(self):
        # Rational contact: H(1/2,0,0)=3/16, delta=3/8.
        contact = _Ray(x=(".5", 0, 0), delta=".375")
        self.assertEqual(contact.null_gap(contact.delta), 0)
        self.assertEqual(self._jet(contact), (0, 0, 0, 0))
        for w in (0, mp.mpf("1e-6")):
            self.assertEqual(contact.fibre(w), 0)
            self.assertEqual(_Ray(x=(2, 0, 0)).fibre(w), 0)
        self.assertGreater(_Ray(x=(0, 0, 0)).fibre(0), 0)
        self.assertEqual(_Ray(delta=1).fibre(0), 0)
        with self.assertRaises(ValueError):
            contact.fibre(contact.delta**2/4)

    def test_approaching_contacts_bounded_but_not_uniform_little_o(self):
        delta, top = mp.mpf(1)/8, mp.mpf(1)/8
        contact_time = top-delta/2
        beta = 1/(2*delta*mp.sqrt(_h(contact_time, 0, delta)))
        a0 = ((1+contact_time**2)*(1+top**2)*delta
              /(8*mp.sqrt(_h(contact_time, 0, delta))))
        target = -a0*beta**2/4  # -a0*beta^2/(8*d), d=1/2
        values = []
        for w in map(mp.mpf, ("1e-5", "1e-6", "1e-8")):
            gap = beta*w/2
            source = mp.sqrt(1-4*(delta/2+gap))
            ray = _Ray(x=(source, 0, 0), delta=delta)
            self.assertGreater(ray.null_gap(delta), 0)
            self.assertEqual(ray.fibre(w), 0)  # already closed on the right
            b0, b1, b2, _ = self._jet(ray)
            values.append(-(b0+b1*w+b2*w*w)/w**2)
            self.assertLess(abs(values[-1]), 1)
        self.assertGreater(abs(values[-1]), mp.mpf(".01"))
        self.assertNear(values[-1], target, "1e-6")
        self.assertLess(abs(values[-1]-target), abs(values[0]-target)/90)

    def test_unequal_axis_geometry_nonzero_curvature_and_variable_angle(self):
        # Independent gradient/normal calculation on the joint, not an action fit.
        for axis, expected in ((0, 2), (2, 6)):
            axes = tuple(map(mp.mpf, (1, 2, 3)))
            x = tuple(axes[i] if i == axis else mp.mpf(0) for i in range(3))
            gradient_norm = mp.sqrt(mp.fsum((x[i]/(2*axes[i]**2))**2 for i in range(3)))
            normal_dot = 1/mp.sqrt(1-gradient_norm**2)
            coth = normal_dot/mp.sqrt(normal_dot**2-1)
            self.assertNear(coth, expected)
        for t in (mp.mpf(-1)/8, 0, mp.mpf(1)/8):
            scalar = 3*(1-t*t/2)/(1+t*t)**mp.mpf("2.5")
            self.assertGreater(scalar, 0)
        # Same height at different axis locations gives the same unweighted
        # planar ray, while endpoint geometry and the joint angles differ.
        first = _Ray(x=(".2", 0, 0), axes=(1, 2, 3))
        third = _Ray(x=(0, 0, ".6"), n=(0, 0, 1), axes=(1, 2, 3))
        for w in (0, mp.mpf("1e-5")):
            self.assertNear(first.fibre(w), third.fibre(w))

    def test_full_signed_pair_disintegration_in_original_coordinates(self):
        # Near-contact planar ray: its ENTIRE long phase support is below e.
        # Independent u,v,t integration includes the actual kernel and weights.
        ray = _Ray(x=(".85", 0, 0), weighted=True)
        delta, length, lower = ray.delta, ray.root, ray.lower
        rho, c = mp.mpf("1e6"), mp.pi/24
        end = _phase(lower, length-delta, delta)
        # u<=length-delta, v<=length, H<=2 throughout this whole ray.
        self.assertLess((length-delta)*length*mp.sqrt(2), delta**2/4)
        self.assertLess(_kernel(c*rho*end**2), 0)

        def raw(v):
            def inner(u):
                return _quad(lambda t: ray.weight(t, u, v)*(1+t*t)
                             *(1+(t+(u+v)/2)**2)*(v-u)**2/8
                             *_kernel(c*rho*_phase(t, u, v)**2),
                             lower, ray.upper_time(u, v), 20)
            return _quad(inner, 0, length-v, 24)
        original = _quad(raw, delta, length, 24)
        pushed = _quad(lambda w: _kernel(c*rho*w*w)*ray.fibre(w, 16), 0, end, 32)
        self.assertNear(pushed/original, 1, "1e-20")
        C = 4/mp.sqrt(6)
        self.assertNear(-C*rho**mp.mpf("1.5")*pushed,
                        -C*rho**mp.mpf("1.5")*original, "1e-20")
        # Signed first-endpoint partitions never impose a partner restriction.
        self.assertNear(mp.fsum(w*pushed for w in (mp.mpf("-.25"),
                                                  mp.mpf(".5"), mp.mpf(".75"))),
                        pushed)

    def test_normalized_signed_time_averaged_ray_not_an_absolute_bound(self):
        ray = _Ray(x=(".85", 0, 0))
        c, C = mp.pi/24, 4/mp.sqrt(6)
        values = []
        for rho in map(mp.mpf, ("1e10", "1e12")):
            scale = mp.sqrt(c*rho)
            # Actual phase amplitude, not its jet. The omitted Gaussian tail
            # has an explicit bound: |F|<1 on this fixture's whole support.
            integrand = lambda z: _kernel(z*z)*ray.fibre(z/scale, 12)
            value = -C*rho/mp.sqrt(c)*mp.fsum(
                _quad(integrand, mp.mpf(a), mp.mpf(b), 32)
                for a, b in ((0, 1), (1, 2), (2, 4), (4, 8), (8, 14)))
            envelope = mp.fsum(abs(coef)*mp.gammainc(mp.mpf(j)+mp.mpf(".5"), 196, mp.inf)/2
                               for j, coef in enumerate((1, -9, 8, -mp.mpf(4)/3)))
            self.assertLess(C*rho/mp.sqrt(c)*envelope, mp.mpf("1e-65"))
            values.append(value)
        self.assertGreater(abs(values[0]), mp.mpf("1e-9"))
        self.assertLess(abs(values[1]), abs(values[0])/8)

    def test_raw_first_endpoint_signed_negative_control_is_still_nonintegrable(self):
        top, delta = mp.mpf(1)/8, mp.mpf(1)/32
        c, C, epsilon = mp.pi/24, 4/mp.sqrt(6), mp.mpf(1)/100
        gamma = C*mp.pi*epsilon**mp.mpf("1.5")/(27*c**mp.mpf("1.5")*2**mp.mpf("1.5")*delta)
        values = []
        for divisor in (8, 32, 128):
            a = delta/divisor
            t = top-(delta+a)/2
            rho = epsilon/(2*c*a*a*(delta+a)**2)
            # The COMPLETE raw-time long triangle, not an absolute-kernel norm.
            integral = mp.pi/2*_quad(lambda v: _quad(
                lambda u: (1+(t+(u+v)/2)**2)*(v-u)**2
                *_kernel(c*rho*_phase(t, u, v)**2), 0, delta+a-v, 16),
                delta, delta+a, 16)
            normalized = C*rho**mp.mpf("1.5")*integral
            self.assertGreater(normalized, gamma/a)
            self.assertGreater(t, (mp.mpf(1)/4)**2/4-top)
            values.append(normalized)
        self.assertGreater(values[-1]/values[-2], mp.mpf("3.9"))
        # dt=-da/2 on a positive spatial ball: an envelope >=gamma/a is not L1.
        self.assertNear(mp.quad(lambda a: 1/a, [mp.mpf(".001"), mp.mpf(".01")]),
                        mp.log(10))


if __name__ == "__main__":
    unittest.main()
