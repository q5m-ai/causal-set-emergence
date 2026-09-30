import BoundaryDraft.DimensionMellin
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# The independent dimension-dependent action constants

These are the published minimal-layer BDG coefficients, not definitions by a
prospective kernel mass. The interval coefficient uses proper time rather than
null-coordinate duration. The compact Gamma expression is equated below with
the sphere-area expression; neither is a limit hypothesis.
-/

open MeasureTheory Set
noncomputable section
namespace BoundaryDraft

/-- Area of the Euclidean unit sphere in spatial dimension `d-1`. -/
def dimensionSphereArea (d : ℕ) : ℝ :=
  2 * Real.pi ^ (((d : ℝ) - 1) / 2) / Real.Gamma (((d : ℝ) - 1) / 2)

/-- Coefficient of proper-time-to-the-`d` in Alexandrov interval volume. -/
def dimensionIntervalCoefficient (d : ℕ) : ℝ :=
  Real.pi ^ (((d : ℝ) - 2) / 2) * Real.Gamma ((d : ℝ) / 2) /
    ((d : ℝ) * Real.Gamma d)

def dimensionActionScale (d : ℕ) : ℝ :=
  dimensionIntervalCoefficient d ^ (2 / (d : ℝ)) / Real.Gamma (1 + 2 / (d : ℝ))

def dimensionPointCoefficient (d : ℕ) : ℝ :=
  (if d % 2 = 0 then 4 else 2) * dimensionActionScale d

def dimensionPairCoefficient (d : ℕ) : ℝ :=
  if d % 2 = 0 then
    (Real.Gamma ((d : ℝ) / 2 + 2) * Real.Gamma ((d : ℝ) / 2) / Real.Gamma d) *
      dimensionPointCoefficient d
  else
    ((d : ℝ) + 1) / (2 : ℝ) ^ (d - 2) * dimensionActionScale d

theorem dimensionSphereArea_pos (d : ℕ) (hd : 2 ≤ d) : 0 < dimensionSphereArea d := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  exact div_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos Real.pi_pos _))
    (Real.Gamma_pos_of_pos (by linarith))

theorem dimensionIntervalCoefficient_pos (d : ℕ) (hd : 2 ≤ d) :
    0 < dimensionIntervalCoefficient d := by
  have hd' : 0 < (d : ℝ) := Nat.cast_pos.mpr (by omega)
  exact div_pos (mul_pos (Real.rpow_pos_of_pos Real.pi_pos _)
    (Real.Gamma_pos_of_pos (div_pos hd' (by norm_num))))
      (mul_pos hd' (Real.Gamma_pos_of_pos hd'))

theorem dimensionActionScale_pos (d : ℕ) (hd : 2 ≤ d) : 0 < dimensionActionScale d := by
  unfold dimensionActionScale
  exact div_pos (Real.rpow_pos_of_pos (dimensionIntervalCoefficient_pos d hd) _)
    (Real.Gamma_pos_of_pos (by positivity))

theorem dimensionPointCoefficient_pos (d : ℕ) (hd : 2 ≤ d) :
    0 < dimensionPointCoefficient d := by
  unfold dimensionPointCoefficient
  split <;> exact mul_pos (by norm_num) (dimensionActionScale_pos d hd)

theorem dimensionPairCoefficient_pos (d : ℕ) (hd : 2 ≤ d) :
    0 < dimensionPairCoefficient d := by
  have hd' : 0 < (d : ℝ) := Nat.cast_pos.mpr (by omega)
  unfold dimensionPairCoefficient
  split
  · exact mul_pos (div_pos (mul_pos (Real.Gamma_pos_of_pos (by positivity))
      (Real.Gamma_pos_of_pos (by positivity))) (Real.Gamma_pos_of_pos hd'))
      (dimensionPointCoefficient_pos d hd)
  · exact mul_pos (div_pos (by positivity) (by positivity)) (dimensionActionScale_pos d hd)

/-- Proper-time and sphere-volume normalizations agree in every supported
integer dimension; the null-coordinate coefficient differs by `2^(d/2)`. -/
theorem dimensionIntervalCoefficient_eq_sphere (d : ℕ) (hd : 2 ≤ d) :
    dimensionIntervalCoefficient d = dimensionSphereArea d /
      ((2 : ℝ) ^ (d - 1) * d * ((d : ℝ) - 1)) := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd₀ : (d : ℝ) ≠ 0 := by linarith
  have hd₁ : (d : ℝ) - 1 ≠ 0 := by linarith
  have hΓd : Real.Gamma (d : ℝ) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hΓs : Real.Gamma (((d : ℝ) - 1) / 2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by linarith)).ne'
  have h₂ : (2 : ℝ) ^ (d - 1) * (2 : ℝ) ^ (1 - (d : ℝ)) = 1 := by
    rw [← Real.rpow_natCast, Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one,
      ← Real.rpow_add (by norm_num)]
    norm_num
  have hπ : Real.pi ^ (((d : ℝ) - 2) / 2) * Real.sqrt Real.pi =
      Real.pi ^ (((d : ℝ) - 1) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add Real.pi_pos]
    congr 1
    ring
  have hdup := Real.Gamma_mul_Gamma_add_half ((d : ℝ) / 2)
  rw [show (d : ℝ) / 2 + 1 / 2 = ((d : ℝ) - 1) / 2 + 1 by ring,
    Real.Gamma_add_one (by linarith : ((d : ℝ) - 1) / 2 ≠ 0),
    show 2 * ((d : ℝ) / 2) = (d : ℝ) by ring] at hdup
  have hmul := congrArg (fun x : ℝ => (2 : ℝ) ^ (d - 1) * x) hdup
  have hr : (2 : ℝ) ^ (d - 1) *
      (Real.Gamma d * (2 : ℝ) ^ (1 - (d : ℝ)) * Real.sqrt Real.pi) =
      Real.Gamma d * Real.sqrt Real.pi := by
    calc
      _ = ((2 : ℝ) ^ (d - 1) * (2 : ℝ) ^ (1 - (d : ℝ))) *
          (Real.Gamma d * Real.sqrt Real.pi) := by ring
      _ = _ := by rw [h₂, one_mul]
  dsimp only at hmul
  rw [hr] at hmul
  unfold dimensionIntervalCoefficient dimensionSphereArea
  rw [← hπ]
  field_simp [hd₀, hd₁, hΓd, hΓs]
  nlinarith [congrArg (fun x : ℝ => 2 * Real.pi ^ (((d : ℝ) - 2) / 2) * x) hmul]

theorem dimensionIntervalCoefficient_two : dimensionIntervalCoefficient 2 = 1 / 2 := by
  norm_num [dimensionIntervalCoefficient]

theorem dimensionIntervalCoefficient_four : dimensionIntervalCoefficient 4 = Real.pi / 24 := by
  norm_num [dimensionIntervalCoefficient, Nat.factorial]

private theorem gamma_three_halves : Real.Gamma (3 / 2) = Real.sqrt Real.pi / 2 := by
  have h := Real.Gamma_add_one (by norm_num : (1 / 2 : ℝ) ≠ 0)
  norm_num [Real.Gamma_one_half_eq] at h
  simpa only [div_eq_mul_inv, one_mul, mul_comm] using h

theorem dimensionIntervalCoefficient_three : dimensionIntervalCoefficient 3 = Real.pi / 12 := by
  norm_num [dimensionIntervalCoefficient, gamma_three_halves, ← Real.sqrt_eq_rpow]
  nlinarith [Real.sq_sqrt Real.pi_pos.le]

theorem dimensionPointCoefficient_two : dimensionPointCoefficient 2 = 2 := by
  norm_num [dimensionPointCoefficient, dimensionActionScale, dimensionIntervalCoefficient_two]

theorem dimensionPairCoefficient_two : dimensionPairCoefficient 2 = 4 := by
  norm_num [dimensionPairCoefficient, dimensionPointCoefficient_two]

theorem dimensionPointCoefficient_four : dimensionPointCoefficient 4 = 4 / Real.sqrt 6 := by
  have hp : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have h₆ : Real.sqrt (6 : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have h₂₄ : Real.sqrt (24 : ℝ) = 2 * Real.sqrt 6 := by
    rw [show (24 : ℝ) = 4 * 6 by norm_num, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num [dimensionPointCoefficient, dimensionActionScale, dimensionIntervalCoefficient_four,
    gamma_three_halves, ← Real.sqrt_eq_rpow]
  rw [h₂₄]
  field_simp
  ring

theorem dimensionPairCoefficient_four : dimensionPairCoefficient 4 = 4 / Real.sqrt 6 := by
  norm_num [dimensionPairCoefficient, dimensionPointCoefficient_four, Nat.factorial]

/-- The action scale cancels its own Gamma/density factor. This algebra is
independent of any asserted slice moment. -/
theorem dimensionPointCoefficient_rescale (d : ℕ) (hd : 2 ≤ d) :
    dimensionPointCoefficient d * dimensionIntervalCoefficient d ^ (-(2 / (d : ℝ))) *
        Real.Gamma (1 + 2 / (d : ℝ)) = if d % 2 = 0 then 4 else 2 := by
  have hc := dimensionIntervalCoefficient_pos d hd
  have hΓ : Real.Gamma (1 + 2 / (d : ℝ)) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hp : dimensionIntervalCoefficient d ^ (2 / (d : ℝ)) *
      dimensionIntervalCoefficient d ^ (-(2 / (d : ℝ))) = 1 := by
    rw [← Real.rpow_add hc, add_neg_cancel, Real.rpow_zero]
  unfold dimensionPointCoefficient dimensionActionScale
  calc
    _ = (if d % 2 = 0 then 4 else 2) *
        (dimensionIntervalCoefficient d ^ (2 / (d : ℝ)) *
          dimensionIntervalCoefficient d ^ (-(2 / (d : ℝ)))) *
        (Real.Gamma (1 + 2 / (d : ℝ)) / Real.Gamma (1 + 2 / (d : ℝ))) := by ring
    _ = _ := by rw [hp, div_self hΓ, mul_one, mul_one]

/-- Independent even-dimensional point/pair normalization in Gamma form. -/
theorem dimensionPairCoefficient_even_normalization (d : ℕ) (hd : 2 ≤ d)
    (heven : d % 2 = 0) :
    dimensionPairCoefficient d *
      (Real.pi ^ (((d : ℝ) - 2) / 2) /
        ((d : ℝ) * Real.Gamma ((d : ℝ) / 2 + 2) * dimensionIntervalCoefficient d)) =
      dimensionPointCoefficient d := by
  have hd' : 0 < (d : ℝ) := Nat.cast_pos.mpr (by omega)
  have hg : Real.Gamma (d : ℝ) ≠ 0 := (Real.Gamma_pos_of_pos hd').ne'
  have hgh : Real.Gamma ((d : ℝ) / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hg₂ : Real.Gamma ((d : ℝ) / 2 + 2) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hp : Real.pi ^ (((d : ℝ) - 2) / 2) ≠ 0 := (Real.rpow_pos_of_pos Real.pi_pos _).ne'
  simp only [dimensionPairCoefficient, heven, if_true, dimensionIntervalCoefficient]
  field_simp
  ring

/-- Independent odd-dimensional point/pair normalization in Gamma form. -/
theorem dimensionPairCoefficient_odd_normalization (d : ℕ) (hd : 2 ≤ d)
    (hodd : d % 2 ≠ 0) :
    dimensionPairCoefficient d *
      (Real.pi ^ (((d : ℝ) - 1) / 2) /
        (2 * (d : ℝ) * Real.Gamma (((d : ℝ) + 3) / 2) * dimensionIntervalCoefficient d)) =
      dimensionPointCoefficient d := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd₀ : (d : ℝ) ≠ 0 := by linarith
  have hd₁ : (d : ℝ) - 1 ≠ 0 := by linarith
  have hdplus : (d : ℝ) + 1 ≠ 0 := by linarith
  have hg : Real.Gamma (((d : ℝ) - 1) / 2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hp : Real.pi ^ (((d : ℝ) - 1) / 2) ≠ 0 := (Real.rpow_pos_of_pos Real.pi_pos _).ne'
  have hshift : Real.Gamma (((d : ℝ) + 3) / 2) =
      (((d : ℝ) + 1) / 2) * (((d : ℝ) - 1) / 2) * Real.Gamma (((d : ℝ) - 1) / 2) := by
    rw [show ((d : ℝ) + 3) / 2 = (((d : ℝ) - 1) / 2 + 1) + 1 by ring,
      Real.Gamma_add_one (by linarith : ((d : ℝ) - 1) / 2 + 1 ≠ 0),
      Real.Gamma_add_one (by linarith : ((d : ℝ) - 1) / 2 ≠ 0)]
    ring
  simp only [dimensionPairCoefficient, dimensionPointCoefficient, hodd, if_false]
  rw [dimensionIntervalCoefficient_eq_sphere d hd, hshift]
  unfold dimensionSphereArea
  rw [show d - 1 = (d - 2) + 1 by omega, pow_succ]
  field_simp
  ring

end BoundaryDraft
