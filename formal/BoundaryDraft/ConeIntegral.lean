import BoundaryDraft.KernelDerivatives

/-!
# Exact radial action-density identity

An integration-by-parts cancellation replaces the exponential-series/beta
argument. All differentiations are dominated on compact rectangles. The
connection of this radial integral with spacetime volume is a separate step.
-/

open MeasureTheory Set
open scoped Interval

noncomputable section
namespace BoundaryDraft

private def thirdPolynomial (z : ℝ) : ℝ := 6 - 204 * z + 288 * z ^ 2 - 64 * z ^ 3
private def thirdPolynomialDiff (z : ℝ) : ℝ := -210 + 780 * z - 480 * z ^ 2 + 64 * z ^ 3
private def coneParameter (ρ H v : ℝ) : ℝ := (Real.pi / 24) * ρ * H ^ 4 * (1 - v ^ 2) ^ 2

/-- Angularly integrated spatial section of the concrete BDG cone integral,
written on a fixed radial interval. -/
def coneRadialSlice (ρ H : ℝ) : ℝ :=
  4 * Real.pi * H ^ 3 * ∫ v in (0 : ℝ)..1,
    v ^ 2 * bdgKernel ((Real.pi / 24) * ρ * H ^ 4 * (1 - v ^ 2) ^ 2)

/-- The fixed radial interval comes from an exact linear substitution. -/
theorem coneRadialSlice_eq_radial (ρ H : ℝ) :
    coneRadialSlice ρ H = 4 * Real.pi * ∫ r in (0 : ℝ)..H,
      r ^ 2 * bdgKernel ((Real.pi / 24) * ρ * (H ^ 2 - r ^ 2) ^ 2) := by
  have hs := intervalIntegral.smul_integral_comp_mul_left
    (a := (0 : ℝ)) (b := 1)
    (fun r => r ^ 2 * bdgKernel ((Real.pi / 24) * ρ * (H ^ 2 - r ^ 2) ^ 2)) H
  simp only [smul_eq_mul, mul_zero, mul_one] at hs
  rw [← hs, coneRadialSlice]
  have he (v : ℝ) : (H * v) ^ 2 * bdgKernel ((Real.pi / 24) * ρ * (H ^ 2 - (H * v) ^ 2) ^ 2) =
      H ^ 2 * (v ^ 2 * bdgKernel ((Real.pi / 24) * ρ * H ^ 4 * (1 - v ^ 2) ^ 2)) := by
    rw [show (Real.pi / 24) * ρ * (H ^ 2 - (H * v) ^ 2) ^ 2 =
      (Real.pi / 24) * ρ * H ^ 4 * (1 - v ^ 2) ^ 2 by ring]
    ring
  simp_rw [he, intervalIntegral.integral_const_mul]
  ring

/-- Radial-time cone integral. Its identification with the original
four-dimensional product-measure integral is not part of this definition. -/
def coneRadialIntegral (ρ H : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..H, coneRadialSlice ρ t

private theorem third_eq (ρ H : ℝ) :
    planeAuxiliaryThird ρ H = 4 * Real.pi * ∫ v in (0 : ℝ)..1,
      v ^ 2 * thirdPolynomial (coneParameter ρ H v) * Real.exp (-coneParameter ρ H v) := by
  unfold planeAuxiliaryThird
  congr 1
  apply intervalIntegral.integral_congr
  intro v _
  change v ^ 2 * (6 + 204 * (-(Real.pi / 24) * ρ * (1 - v ^ 2) ^ 2) * H ^ 4 +
      288 * (-(Real.pi / 24) * ρ * (1 - v ^ 2) ^ 2) ^ 2 * H ^ 8 +
      64 * (-(Real.pi / 24) * ρ * (1 - v ^ 2) ^ 2) ^ 3 * H ^ 12) *
      Real.exp ((-(Real.pi / 24) * ρ * (1 - v ^ 2) ^ 2) * H ^ 4) = _
  congr 1
  · dsimp [thirdPolynomial, coneParameter]
    ring
  · congr 1
    dsimp [coneParameter]
    ring

private theorem hasDerivAt_third_integrand (ρ H v : ℝ) :
    HasDerivAt (fun t => v ^ 2 * thirdPolynomial (coneParameter ρ t v) *
      Real.exp (-coneParameter ρ t v))
      (4 * (Real.pi / 24) * ρ * H ^ 3 * v ^ 2 * (1 - v ^ 2) ^ 2 *
        thirdPolynomialDiff (coneParameter ρ H v) * Real.exp (-coneParameter ρ H v)) H := by
  have hz : HasDerivAt (fun t => coneParameter ρ t v)
      (4 * (Real.pi / 24) * ρ * H ^ 3 * (1 - v ^ 2) ^ 2) H := by
    convert ((((hasDerivAt_id H).pow 4).const_mul ((Real.pi / 24) * ρ)).mul_const
      ((1 - v ^ 2) ^ 2)) using 1
    dsimp [coneParameter]
    ring
  have hp := (((hasDerivAt_const H 6).sub (hz.const_mul 204)).add
    ((hz.pow 2).const_mul 288)).sub ((hz.pow 3).const_mul 64)
  convert (hp.const_mul (v ^ 2)).mul hz.neg.exp using 1
  dsimp [thirdPolynomial, thirdPolynomialDiff]
  ring

/-- A polynomial primitive with zero boundary values effects the exact
radial cancellation. No convergence of a formal power series is presumed. -/
private theorem radial_cancellation (k : ℝ) :
    (∫ v in (0 : ℝ)..1, v ^ 2 * (1 - v ^ 2) ^ 2 *
      thirdPolynomialDiff (k * (1 - v ^ 2) ^ 2) * Real.exp (-(k * (1 - v ^ 2) ^ 2))) =
      -48 * ∫ v in (0 : ℝ)..1, v ^ 2 * bdgKernel (k * (1 - v ^ 2) ^ 2) := by
  let w := fun v : ℝ => 1 - v ^ 2
  let z := fun v : ℝ => k * (w v) ^ 2
  let M := fun v : ℝ => 2 * v ^ 3 * w v *
    (-8 * (z v) ^ 2 * (w v + 1) + 2 * z v * (15 * w v + 14) - 15 * w v - 12) *
      Real.exp (-z v)
  let f := fun v : ℝ => v ^ 2 * (w v) ^ 2 * thirdPolynomialDiff (z v) * Real.exp (-z v)
  let g := fun v : ℝ => v ^ 2 * bdgKernel (z v)
  have hd (v : ℝ) : HasDerivAt M (f v + 48 * g v) v := by
    have hw : HasDerivAt w (-2 * v) v := by
      convert ((hasDerivAt_id v).pow 2).const_sub 1 using 1
      dsimp [w]
      ring
    have hz := (hw.pow 2).const_mul k
    have hp := (((((hz.pow 2).const_mul (-8)).mul (hw.add_const 1)).add
      ((hz.const_mul 2).mul ((hw.const_mul 15).add_const 14))).sub
      (hw.const_mul 15)).sub_const 12
    convert (((((hasDerivAt_id v).pow 3).const_mul 2).mul hw).mul hp).mul
      hz.neg.exp using 1
    dsimp [M, f, g, w, z, thirdPolynomialDiff, bdgKernel, bdgPolynomial]
    ring
  have hf : Continuous f := by dsimp [f, w, z, thirdPolynomialDiff]; fun_prop
  have hg : Continuous g := by dsimp [g, w, z, bdgKernel, bdgPolynomial]; fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hd v)
    ((hf.add (continuous_const.mul hg)).intervalIntegrable 0 1)
  rw [intervalIntegral.integral_add (hf.intervalIntegrable 0 1)
    ((continuous_const.mul hg).intervalIntegrable 0 1), intervalIntegral.integral_const_mul] at h
  have hm0 : M 0 = 0 := by simp [M, w]
  have hm1 : M 1 = 0 := by simp [M, w]
  rw [hm0, hm1] at h
  change (∫ v in (0 : ℝ)..1, f v) = -48 * ∫ v in (0 : ℝ)..1, g v
  linarith

/-- The exact derivative of the third auxiliary derivative is minus the
concrete radial BDG section, including the angular normalization. -/
theorem hasDerivAt_planeAuxiliaryThird (ρ H : ℝ) :
    HasDerivAt (planeAuxiliaryThird ρ) (-8 * Real.pi * ρ * coneRadialSlice ρ H) H := by
  have hd := (hasDerivAt_integral_unitInterval
    (fun t v => v ^ 2 * thirdPolynomial (coneParameter ρ t v) * Real.exp (-coneParameter ρ t v))
    (fun t v => 4 * (Real.pi / 24) * ρ * t ^ 3 * v ^ 2 * (1 - v ^ 2) ^ 2 *
      thirdPolynomialDiff (coneParameter ρ t v) * Real.exp (-coneParameter ρ t v))
    (by dsimp [Function.uncurry, thirdPolynomial, coneParameter]; fun_prop)
    (by dsimp [Function.uncurry, thirdPolynomialDiff, coneParameter]; fun_prop)
    (hasDerivAt_third_integrand ρ) H).const_mul (4 * Real.pi)
  have hi : (∫ v in (0 : ℝ)..1, 4 * (Real.pi / 24) * ρ * H ^ 3 * v ^ 2 * (1 - v ^ 2) ^ 2 *
      thirdPolynomialDiff (coneParameter ρ H v) * Real.exp (-coneParameter ρ H v)) =
      4 * (Real.pi / 24) * ρ * H ^ 3 *
        (-48 * ∫ v in (0 : ℝ)..1, v ^ 2 * bdgKernel (coneParameter ρ H v)) := by
    dsimp only [coneParameter]
    rw [← radial_cancellation ((Real.pi / 24) * ρ * H ^ 4), ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro v _
    dsimp [coneParameter]
    ring
  rw [hi] at hd
  convert hd using 1
  · exact funext fun t => third_eq ρ t
  · dsimp [coneRadialSlice, coneParameter]
    ring

theorem continuous_coneRadialSlice (ρ : ℝ) : Continuous (coneRadialSlice ρ) := by
  unfold coneRadialSlice
  apply Continuous.mul
  · fun_prop
  · exact continuous_iff_continuousAt.mpr fun H =>
      (hasDerivAt_integral_unitInterval
        (fun t v => v ^ 2 * bdgKernel (coneParameter ρ t v))
        (fun t v => v ^ 2 *
          ((-9 + 16 * coneParameter ρ t v - 4 * coneParameter ρ t v ^ 2) -
            bdgPolynomial (coneParameter ρ t v)) *
          Real.exp (-coneParameter ρ t v) *
          (4 * (Real.pi / 24) * ρ * t ^ 3 * (1 - v ^ 2) ^ 2))
        (by dsimp [Function.uncurry, bdgKernel, bdgPolynomial, coneParameter]; fun_prop)
        (by dsimp [Function.uncurry, bdgPolynomial, coneParameter]; fun_prop)
        (by
          intro H v
          have hz : HasDerivAt (fun t => coneParameter ρ t v)
              (4 * (Real.pi / 24) * ρ * H ^ 3 * (1 - v ^ 2) ^ 2) H := by
            convert ((((hasDerivAt_id H).pow 4).const_mul ((Real.pi / 24) * ρ)).mul_const
              ((1 - v ^ 2) ^ 2)) using 1
            dsimp [coneParameter]
            ring
          have hp := (((hasDerivAt_const H 1).sub (hz.const_mul 9)).add
            ((hz.pow 2).const_mul 8)).sub ((hz.pow 3).const_mul (4 / 3))
          convert ((hp.mul hz.neg.exp).const_mul (v ^ 2)) using 1
          dsimp [bdgKernel, bdgPolynomial]
          ring) H).continuousAt

/-- Continuity of the finite-depth cone integral follows from the fundamental
theorem of calculus, including at zero. -/
theorem continuous_coneRadialIntegral (ρ : ℝ) : Continuous (coneRadialIntegral ρ) :=
  continuous_iff_continuousAt.mpr fun H =>
    ((continuous_coneRadialSlice ρ).integral_hasStrictDerivAt 0 H).continuousAt

/-- Exact action-density identity for the radial-time cone integral, at
all real densities and finite heights (oriented when the height is negative). -/
theorem planeAuxiliaryThird_eq_coneRadialIntegral (ρ H : ℝ) :
    planeAuxiliaryThird ρ H / (8 * Real.pi) = 1 - ρ * coneRadialIntegral ρ H := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_planeAuxiliaryThird ρ t)
    ((continuous_const.mul (continuous_coneRadialSlice ρ)).intervalIntegrable 0 H)
  rw [intervalIntegral.integral_const_mul, planeAuxiliaryThird_zero] at h
  unfold coneRadialIntegral
  apply (div_eq_iff (by positivity : 8 * Real.pi ≠ 0)).mpr
  linarith

/-- Integration of the exact radial action density along a finite vertical
fibre gives the existing derivative-defined `planeKernel`. -/
theorem integral_radial_actionDensity (ρ H : ℝ) :
    (∫ t in (0 : ℝ)..H, (4 / Real.sqrt 6) * Real.sqrt ρ *
      (1 - ρ * coneRadialIntegral ρ t)) = planeKernel ρ H := by
  have hc : Continuous (planeAuxiliaryThird ρ) :=
    continuous_iff_continuousAt.mpr fun H => (hasDerivAt_planeAuxiliaryThird ρ H).continuousAt
  simp_rw [← planeAuxiliaryThird_eq_coneRadialIntegral]
  have he (t : ℝ) : (4 / Real.sqrt 6) * Real.sqrt ρ * (planeAuxiliaryThird ρ t / (8 * Real.pi)) =
      Real.sqrt ρ / (2 * Real.pi * Real.sqrt 6) * planeAuxiliaryThird ρ t := by ring
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_planeAuxiliarySecond ρ t) (hc.intervalIntegrable 0 H),
    planeAuxiliarySecond_zero, sub_zero, planeKernel_eq_second]

end BoundaryDraft
