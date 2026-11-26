/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import SpherePacking.MagicFunction.b.Schwartz

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import SpherePacking.ModularForms.ResToImagAxis

/-!
# Double zeroes of `b`

For `s > 2`, `b(s) = -4i sin(π s / 2)² ∫₀^∞ ψ_I(it) e^{-π s t} dt`, where `s` is the squared
radius `‖x‖²`.
-/

@[expose] public section

open Set Filter MeasureTheory Real Complex
open scoped Topology

namespace MagicFunction

private theorem ψI'_imaginaryAxis_continuousOn :
    ContinuousOn (fun t : ℝ ↦ ψI' (I * t)) (Ici 0) := by
have hψ : (fun t : ℝ ↦ ψI' (I * t)) = ψI.resToImagAxis := by
    ext t; by_cases ht : 0 < t <;> simp [ψI', ResToImagAxis, ht]
  have hS := tendsto_resToImagAxis_of_tendsto_atImInfty (F := ψS)
    ((ψS_div_exp_tendsto.mul (UpperHalfPlane.qParam_tendsto_atImInfty two_pos)).congr fun z ↦ by
      rw [Function.Periodic.qParam]; push_cast; field_simp)
  rw [hψ]
  intro t ht
  obtain ht | rfl := (mem_Ici.1 ht).lt_or_eq
  · exact (ResToImagAxis.Differentiable ψI ψI_mdifferentiable t ht).continuousAt.continuousWithinAt
  rw [← continuousWithinAt_Ioi_iff_Ici, ContinuousWithinAt,
    show ψI.resToImagAxis 0 = 0 by simp [ResToImagAxis]]
  refine (((Continuous.tendsto' (f := fun t : ℝ ↦ I ^ 2 * (t : ℂ) ^ 2) (by fun_prop) 0 0 
    (by simp)).mono_left nhdsWithin_le_nhds).zero_mul_isBoundedUnder_le
    (hS.comp tendsto_inv_nhdsGT_zero).norm.isBoundedUnder_le).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  rw [← ψS_slash_S, ResToImagAxis.SlashActionS _ _ ht]
  simp

theorem integrableOn_ψI'_mul_cexp {s : ℝ} (hr : 2 < s) :
    IntegrableOn (fun t : ℝ ↦ ψI' (I * t) * cexp (-π * s * t)) (Ioi 0) := by
 have hO : (fun t : ℝ ↦ ψI' (I * t)) =O[atTop] fun t ↦ rexp (2 * π * t) := by
    refine (((tendsto_resToImagAxis_of_tendsto_atImInfty ψI_mul_exp_tendsto).isBigO_one ℝ).mul
      (Complex.isBigO_ofReal_left.2 (Asymptotics.isBigO_refl (fun t ↦ rexp (2 * π * t)) _))).congr'
      ?_ (.of_forall fun _ ↦ one_mul _)
    filter_upwards [eventually_gt_atTop 0] with t ht
    simp [ResToImagAxis, ht, ψI', mul_assoc, ← Complex.exp_add, ← mul_assoc I I]
  exact ((integrableOn_exp_neg_smul_of_isBigO_exp (b := π * s)
    (ψI'_imaginaryAxis_continuousOn.locallyIntegrableOn measurableSet_Ici) hO
    (by nlinarith [pi_pos])).mono_set Ioi_subset_Ici_self).congr_fun
    (fun t _ ↦ by simp [Complex.real_smul, mul_comm]) measurableSet_Ioi

open b.RealIntegrals in
/-- Combined unbounded contour deformation from Proposition 7.40. The six finite and
infinite pieces defining the contour sum equal the three vertical ray contributions.
The two translated rays contribute phases `exp (π i s)` and `exp (-π i s)`, and the
central ray has coefficient `-2`. -/
theorem b_unbounded_contour_deformation {s : ℝ} (hs : 2 < s) :
    J₁' s + J₂' s + J₃' s + J₄' s + J₅' s + J₆' s =
      I * (∫ t in Ioi (0 : ℝ),
        ψT' (-1 + I * t) * cexp (π * I * s * (-1 + I * t))) -
      2 * I * (∫ t in Ioi (0 : ℝ), ψI' (I * t) * cexp (-π * s * t)) +
      I * (∫ t in Ioi (0 : ℝ),
        ψT' (1 + I * t) * cexp (π * I * s * (1 + I * t))) := by
  sorry

private theorem integral_ψT'_shift {s : ℝ} {a : ℂ} (ha : a = -1 ∨ a = 1) :
    (∫ t in Ioi (0 : ℝ), ψT' (a + I * t) * cexp (π * I * s * (a + I * t))) =
      cexp (π * I * s * a) * ∫ t in Ioi (0 : ℝ), ψI' (I * t) * cexp (-π * s * t) := by
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have ht' : 0 < t := ht
  have hi : (I * (t : ℂ)).im = t := by simp
  have him : 0 < (a + I * (t : ℂ)).im := by
    rcases ha with rfl | rfl <;> simpa [hi] using ht'
  have hψ : ψT' (a + I * t) = ψI' (I * t) := by
    rcases ha with rfl | rfl
    · rw [← ψI'_add_one him]
      congr 1
      ring
    · rw [← ψI'_sub_one him]
      congr 1
      ring
  have he : (π : ℂ) * I * s * (a + I * t) = π * I * s * a + -π * s * t := by
    linear_combination (π : ℂ) * (s : ℂ) * (t : ℂ) * I_sq
  dsimp only
  rw [hψ, he, Complex.exp_add]
  ring

private theorem exp_phase_sum (x : ℂ) :
    cexp (x * I) - 2 + cexp (-(x * I)) = -4 * Complex.sin (x / 2) ^ 2 := by
  have hcos : Complex.cos (2 * (x / 2)) = Complex.cos x := by
    congr 1
    ring
  rw [Complex.cos_two_mul] at hcos
  have he : Complex.cos x = (cexp (x * I) + cexp (-(x * I))) / 2 := by
    rw [Complex.cos, neg_mul]
  rw [he] at hcos
  linear_combination -2 * hcos + 4 * Complex.sin_sq_add_cos_sq (x / 2)

theorem b'_eq_neg_four_mul_I_mul_sin_sq_mul_integral {s : ℝ} (hr : 2 < s) :
    b.RealIntegrals.b' s = -4 * I * (Real.sin (π * s / 2) : ℂ) ^ 2 *
      ∫ t in Ioi (0 : ℝ), ψI' (I * t) * cexp (-π * s * t) := by
  rw [b.RealIntegrals.b', b_unbounded_contour_deformation hr,
    integral_ψT'_shift (Or.inl rfl), integral_ψT'_shift (Or.inr rfl)]
  rw [show (π : ℂ) * I * s * (-1) = -(π * s * I) by ring,
    show (π : ℂ) * I * s * 1 = π * s * I by ring]
  have hphase := exp_phase_sum ((π : ℂ) * s)
  have hsin : Complex.sin ((π : ℂ) * s / 2) = (Real.sin (π * s / 2) : ℂ) := by
    push_cast
    rfl
  rw [hsin] at hphase
  linear_combination
    (I * ∫ t in Ioi (0 : ℝ), ψI' (I * t) * cexp (-π * s * t)) * hphase

theorem b_eq_neg_four_mul_I_mul_sin_sq_mul_integral {x : EuclideanSpace ℝ (Fin 8)} (hx : √2 < ‖x‖) :
    FourierEigenfunctions.b x = -4 * I * (Real.sin (π * ‖x‖ ^ 2 / 2) : ℂ) ^ 2 *
      ∫ t in Ioi (0 : ℝ), ψI' (I * t) * cexp (-π * ‖x‖ ^ 2 * t) := by
  rw [FourierEigenfunctions.b_apply,
    b'_eq_neg_four_mul_I_mul_sin_sq_mul_integral (lt_sq_of_sqrt_lt hx)]
  norm_num

end MagicFunction
