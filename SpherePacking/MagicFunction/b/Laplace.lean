/-
Copyright (c) 2026 mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib contributors:
-/
module

public import SpherePacking.MagicFunction.b.AnalyticContinuation
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Asymptotics

/-!
# Regularized Laplace formula for `b`

Proposition 7.41 subtracts the two leading exponential terms from the Laplace integrand.
The continuation proof clears the denominators before applying the real analytic identity theorem.
-/

@[expose] public section

open Filter MeasureTheory
open scoped Real Topology

noncomputable section

namespace MagicFunction

def bIntegrand (psi : ℂ → ℂ) (r t : ℝ) : ℂ :=
  (psi (Complex.I * (t : ℂ)) - 144 -
    (Real.exp (2 * Real.pi * t) : ℂ)) *
    (Real.exp (-Real.pi * r ^ 2 * t) : ℂ)

/-- Apply the analytic identity theorem on the positive real axis. -/
private theorem eq_on_positive_of_analytic_of_eq_above_two
    {f g : ℝ → ℂ}
    (hf : AnalyticOnNhd ℝ f (Set.Ioi (0 : ℝ)))
    (hg : AnalyticOnNhd ℝ g (Set.Ioi (0 : ℝ)))
    (hlarge : ∀ x : ℝ, 2 < x → f x = g x)
    {x : ℝ} (hx : 0 < x) : f x = g x := by
  exact
    (hf.eqOn_of_preconnected_of_eventuallyEq hg isPreconnected_Ioi
      (show (3 : ℝ) ∈ Set.Ioi (0 : ℝ) by norm_num)
      (by
        filter_upwards
          [Ioi_mem_nhds (show (2 : ℝ) < 3 by norm_num)] with y hy
        exact hlarge y hy)) hx


/-- A real exponential, viewed as a complex-valued integrand. -/
private def expKernel (a t : ℝ) : ℂ := (Real.exp (-a * t) : ℂ)

private theorem integrableOn_expKernel {a : ℝ} (ha : 0 < a) :
    IntegrableOn (expKernel a) (Set.Ioi (0 : ℝ)) := by
  have hneg : (-(a : ℂ)).re < 0 := by
    simp only [Complex.neg_re, Complex.ofReal_re]
    linarith
  change IntegrableOn
    (fun t : ℝ => (Real.exp (-a * t) : ℂ))
    (Set.Ioi (0 : ℝ))
  simp_rw [Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg]
  exact integrableOn_exp_mul_complex_Ioi
    (a := -(a : ℂ)) hneg 0

private theorem integral_expKernel {a : ℝ} (ha : 0 < a) :
    (∫ t in Set.Ioi (0 : ℝ), expKernel a t) = 1 / (a : ℂ) := by
  have hneg : (-(a : ℂ)).re < 0 := by
    simp only [Complex.neg_re, Complex.ofReal_re]
    linarith
  change (∫ t in Set.Ioi (0 : ℝ),
    (Real.exp (-a * t) : ℂ)) = 1 / (a : ℂ)
  simp_rw [Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg]
  simpa using integral_exp_mul_complex_Ioi (a := -(a : ℂ)) hneg 0


/-- The regularized Laplace transform. Its integrability is not automatic. -/
def regularizedIntegral (psi : ℂ → ℂ) (r : ℝ) : ℂ :=
  ∫ t in Set.Ioi (0 : ℝ), bIntegrand psi r t

/-- Pointwise algebra for the two terms being subtracted. -/
private theorem bIntegrand_eq (psi : ℂ → ℂ) (r t : ℝ) :
    bIntegrand psi r t =
      psi (Complex.I * (t : ℂ)) * expKernel (Real.pi * r ^ 2) t -
      144 * expKernel (Real.pi * r ^ 2) t -
      expKernel (Real.pi * (r ^ 2 - 2)) t := by
  have he :
      (Real.exp (2 * Real.pi * t) : ℂ) *
          (Real.exp (-Real.pi * r ^ 2 * t) : ℂ) =
        (Real.exp (-(Real.pi * (r ^ 2 - 2)) * t) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  unfold bIntegrand expKernel
  rw [sub_mul, sub_mul]
  rw [he]
  simp only [neg_mul]
/--
The integral computation when both subtracted exponential terms have convergent integrals.
-/
private theorem laplace_regularization (psi : ℂ → ℂ) {r : ℝ} (hsq : 2 < r ^ 2)
    (hreg : IntegrableOn (bIntegrand psi r) (Set.Ioi (0 : ℝ))) :
    (∫ t in Set.Ioi (0 : ℝ),
        psi (Complex.I * (t : ℂ)) * expKernel (Real.pi * r ^ 2) t) =
      144 / ((Real.pi * r ^ 2 : ℝ) : ℂ) +
      1 / ((Real.pi * (r ^ 2 - 2) : ℝ) : ℂ) +
      regularizedIntegral psi r := by
  have ha : 0 < Real.pi * r ^ 2 :=
    mul_pos Real.pi_pos (by linarith)
  have hd : 0 < Real.pi * (r ^ 2 - 2) :=
    mul_pos Real.pi_pos (by linarith)
  have h0 := integrableOn_expKernel ha
  have h2 := integrableOn_expKernel hd
  have h144 := h0.const_mul (144 : ℂ)
  have hsplit :
      (fun t : ℝ =>
        psi (Complex.I * (t : ℂ)) * expKernel (Real.pi * r ^ 2) t) =
      (fun t : ℝ => bIntegrand psi r t +
        144 * expKernel (Real.pi * r ^ 2) t +
        expKernel (Real.pi * (r ^ 2 - 2)) t) := by
    funext t
    rw [bIntegrand_eq]
    ring
  rw [hsplit]
  rw [integral_add
    (f := fun t : ℝ =>
      bIntegrand psi r t +
        144 * expKernel (Real.pi * r ^ 2) t)
    (g := fun t : ℝ =>
      expKernel (Real.pi * (r ^ 2 - 2)) t)
    (hreg.add h144) h2]
  rw [integral_add
    (f := bIntegrand psi r)
    (g := fun t : ℝ =>
      144 * expKernel (Real.pi * r ^ 2) t)
    hreg h144]
  rw [integral_const_mul,
    integral_expKernel ha,
    integral_expKernel hd]
  unfold regularizedIntegral
  ring

private def denominator (r : ℝ) : ℂ :=
  (Real.pi : ℂ) * (r : ℂ) ^ 2 * ((r : ℂ) ^ 2 - 2)

private def numerator (psi : ℂ → ℂ) (r : ℝ) : ℂ :=
  144 * ((r : ℂ) ^ 2 - 2) + (r : ℂ) ^ 2 +
    denominator r * regularizedIntegral psi r

/-- The coefficient is a parameter so that the sign convention is explicit. -/
def regularizedRhs (c : ℂ) (psi : ℂ → ℂ) (r : ℝ) : ℂ :=
  c * (Real.sin (Real.pi * r ^ 2 / 2) ^ 2 : ℂ) *
    (144 / ((Real.pi * r ^ 2 : ℝ) : ℂ) +
      1 / ((Real.pi * (r ^ 2 - 2) : ℝ) : ℂ) +
      regularizedIntegral psi r)

private theorem denominator_ne_zero {r : ℝ} (hr0 : r ≠ 0) (hr2 : r ^ 2 ≠ 2) :
    denominator r ≠ 0 := by
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr0
  have hs : (r : ℂ) ^ 2 - 2 ≠ 0 := by
    exact_mod_cast (sub_ne_zero.mpr hr2)
  exact mul_ne_zero (mul_ne_zero hp (pow_ne_zero 2 hrc)) hs

/-- Clearing the two explicit denominators creates an analytic expression. -/
private theorem denominator_mul_rhs (c : ℂ) (psi : ℂ → ℂ) {r : ℝ}
    (hr0 : r ≠ 0) (hr2 : r ^ 2 ≠ 2) :
    denominator r * regularizedRhs c psi r =
      c * (Real.sin (Real.pi * r ^ 2 / 2) ^ 2 : ℂ) * numerator psi r := by
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr0
  have hs : (r : ℂ) ^ 2 - 2 ≠ 0 := by
    exact_mod_cast (sub_ne_zero.mpr hr2)
  simp only [regularizedRhs, numerator, denominator]
  push_cast
  field_simp [hp, hrc, hs]
/-- Continue the regularized formula from the initial Laplace range. -/
private theorem b_formula_of_laplace_and_analytic
    (c : ℂ) (b : ℝ → ℂ) (psi : ℂ → ℂ)
    (hb : AnalyticOnNhd ℝ b (Set.Ioi (0 : ℝ)))
    (hL : AnalyticOnNhd ℝ (regularizedIntegral psi) (Set.Ioi (0 : ℝ)))
    (hseed : ∀ x : ℝ, 2 < x → b x = regularizedRhs c psi x)
    (r : ℝ) (hr : 0 < r) (hr2 : r ^ 2 ≠ 2) :
    b r = regularizedRhs c psi r := by
  let D : ℝ → ℝ :=
    fun y => Real.pi * y ^ 2 * (y ^ 2 - 2)
  let A : ℝ → ℝ :=
    fun y => 144 * (y ^ 2 - 2) + y ^ 2
  have hC (x z : ℝ) :
      AnalyticAt ℝ (fun _ : ℝ => z) x :=
    analyticAt_const
  have hDreal (x : ℝ) : AnalyticAt ℝ D x := by
    have hs : AnalyticAt ℝ (fun y : ℝ => y ^ 2) x :=
      (analyticAt_id :
        AnalyticAt ℝ (fun y : ℝ => y) x).fun_pow 2
    simpa only [D] using
      (((hC x Real.pi).fun_mul hs).fun_mul
        (hs.fun_sub (hC x 2)))
  have hAreal (x : ℝ) : AnalyticAt ℝ A x := by
    have hs : AnalyticAt ℝ (fun y : ℝ => y ^ 2) x :=
      (analyticAt_id :
        AnalyticAt ℝ (fun y : ℝ => y) x).fun_pow 2
    simpa only [A] using
      (((hC x 144).fun_mul
        (hs.fun_sub (hC x 2))).fun_add hs)
  have hcast (f : ℝ → ℝ) (x : ℝ)
      (hf : AnalyticAt ℝ f x) :
      AnalyticAt ℝ (fun y : ℝ => (f y : ℂ)) x := by
    have hm : (Complex.ofRealCLM : ℝ → ℂ) =
        (fun y : ℝ => (y : ℂ)) := by
      funext y
      exact Complex.ofRealCLM_apply y
    have hc :
        AnalyticAt ℝ (Complex.ofRealCLM : ℝ → ℂ) (f x) :=
      Complex.ofRealCLM.analyticAt (f x)
    rw [hm] at hc
    exact AnalyticAt.fun_comp (f := f) (x := x) hc hf
  have hDeq (y : ℝ) :
      (D y : ℂ) = denominator y := by
    simp only [D, denominator, Complex.ofReal_mul,
      Complex.ofReal_pow, Complex.ofReal_sub,
      Complex.ofReal_ofNat]
  have hNeq :
      (fun y : ℝ =>
        (A y : ℂ) + D y • regularizedIntegral psi y) =
        numerator psi := by
    funext y
    simp only [A, D, numerator, denominator,
      Complex.real_smul, Complex.ofReal_add,
      Complex.ofReal_mul, Complex.ofReal_pow,
      Complex.ofReal_sub, Complex.ofReal_ofNat]
  have hF : AnalyticOnNhd ℝ
      (fun y => denominator y * b y)
      (Set.Ioi (0 : ℝ)) := by
    intro x hx
    simpa only [Complex.real_smul, hDeq] using
      (hDreal x).fun_smul (hb x hx)
  have hG : AnalyticOnNhd ℝ
      (fun y =>
        c * (Real.sin (Real.pi * y ^ 2 / 2) ^ 2 : ℂ) *
          numerator psi y)
      (Set.Ioi (0 : ℝ)) := by
    intro x hx
    have hN' : AnalyticAt ℝ
        (fun y : ℝ =>
          (A y : ℂ) + D y • regularizedIntegral psi y) x :=
      (hcast A x (hAreal x)).fun_add
        ((hDreal x).fun_smul
          (hL x hx))
    have hN : AnalyticAt ℝ (numerator psi) x := by
      rw [hNeq] at hN'
      exact hN'
    have hid : AnalyticAt ℝ (fun y : ℝ => y) x :=
      analyticAt_id
    have harg : AnalyticAt ℝ
        (fun y : ℝ => Real.pi * y ^ 2 / 2) x :=
      ((hC x Real.pi).fun_mul (hid.fun_pow 2)).div_const
    have hsine : AnalyticAt ℝ
        (fun y : ℝ =>
          Real.sin (Real.pi * y ^ 2 / 2)) x :=
      AnalyticAt.fun_comp
        (f := fun y : ℝ => Real.pi * y ^ 2 / 2)
        (x := x) Real.analyticAt_sin harg
    have hsquare : AnalyticAt ℝ
        (fun y : ℝ =>
          Real.sin (Real.pi * y ^ 2 / 2) ^ 2) x :=
      hsine.fun_pow 2
    have hprod : AnalyticAt ℝ
        (fun y : ℝ =>
          (Real.sin (Real.pi * y ^ 2 / 2) ^ 2 : ℝ) •
            numerator psi y) x :=
      hsquare.fun_smul hN
    simpa only [Complex.real_smul, smul_eq_mul,
      Complex.ofReal_pow, mul_assoc] using
      hprod.fun_const_smul (c := c)
  have hlarge : ∀ x : ℝ, 2 < x →
      denominator x * b x =
        c * (Real.sin (Real.pi * x ^ 2 / 2) ^ 2 : ℂ) *
          numerator psi x := by
    intro x hx
    rw [hseed x hx]
    exact denominator_mul_rhs c psi (r := x)
      (by linarith)
      (by nlinarith [sq_nonneg (x - 2)])
  have hcleared :=
    eq_on_positive_of_analytic_of_eq_above_two
      hF hG hlarge hr
  apply mul_left_cancel₀ (denominator_ne_zero hr.ne' hr2)
  exact hcleared.trans
    (denominator_mul_rhs c psi hr.ne' hr2).symm

private theorem expKernel_b_eq (r t : ℝ) :
    expKernel (Real.pi * r ^ 2) t =
      Complex.exp (-(Real.pi : ℂ) * ((r ^ 2 : ℝ) : ℂ) * (t : ℂ)) := by
  simp [expKernel, Complex.ofReal_exp, neg_mul]

/-- Absolute convergence of the regularized integral in the initial Laplace range. -/
theorem integrableOn_regularized_b_above_two {r : ℝ} (hr : 2 < r ^ 2) :
    IntegrableOn (bIntegrand ψI' r) (Set.Ioi (0 : ℝ)) := by
  have hmain := integrableOn_ψI'_mul_cexp hr
  have h0 := integrableOn_expKernel
    (mul_pos Real.pi_pos (show 0 < r ^ 2 by linarith))
  have h2 := integrableOn_expKernel
    (mul_pos Real.pi_pos (sub_pos.mpr hr))
  have hmain' : IntegrableOn
      (fun t : ℝ => ψI' (Complex.I * (t : ℂ)) * expKernel (Real.pi * r ^ 2) t)
      (Set.Ioi (0 : ℝ)) := by
    simpa only [expKernel_b_eq] using hmain
  convert (hmain'.sub (h0.const_mul (144 : ℂ))).sub h2 using 1
  exact funext (bIntegrand_eq ψI' r)

/-- The regularized formula for the predefined radial function in the initial Laplace range. -/
theorem b_regularized_eq_above_two {r : ℝ} (hs : 2 < r ^ 2) :
    b.RealIntegrals.b' (r ^ 2) = regularizedRhs (-4 * Complex.I) ψI' r := by
  rw [b'_eq_neg_four_mul_I_mul_sin_sq_mul_integral hs]
  simp only [← expKernel_b_eq, ← Complex.ofReal_pow]
  rw [laplace_regularization ψI' hs (integrableOn_regularized_b_above_two hs)]
  simp only [regularizedRhs, Complex.ofReal_pow]

/-- Absolute convergence at zero implies absolute convergence at every real radius. -/
theorem integrableOn_regularized_b_of_zero
    (hzero : IntegrableOn (bIntegrand ψI' 0) (Set.Ioi (0 : ℝ))) (r : ℝ) :
    IntegrableOn (bIntegrand ψI' r) (Set.Ioi (0 : ℝ)) := by
  have hkernel : Continuous (expKernel (Real.pi * r ^ 2)) := by
    unfold expKernel
    fun_prop
  have heq (t : ℝ) : bIntegrand ψI' r t =
      bIntegrand ψI' 0 t * expKernel (Real.pi * r ^ 2) t := by
    simp [bIntegrand, expKernel, neg_mul]
  let μ := volume.restrict (Set.Ioi (0 : ℝ))
  have hbase : Integrable (bIntegrand ψI' 0) μ := hzero
  change Integrable (bIntegrand ψI' r) μ
  refine hbase.mono ?_ ?_
  · rw [show bIntegrand ψI' r = _ from funext heq]
    exact hbase.aestronglyMeasurable.mul hkernel.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with t ht
    rw [heq, norm_mul]
    have hle : ‖expKernel (Real.pi * r ^ 2) t‖ ≤ 1 := by
      have ht' : 0 ≤ t := (Set.mem_Ioi.mp ht).le
      rw [expKernel, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
      exact mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (mul_nonneg Real.pi_pos.le (sq_nonneg r))) ht'
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hle (norm_nonneg _)

/-- The regularized integrand is absolutely integrable even at radius zero. -/
theorem integrableOn_regularized_b_zero :
    IntegrableOn (bIntegrand ψI' 0) (Set.Ioi (0 : ℝ)) := by
  have hcont : ContinuousOn (bIntegrand ψI' 0) (Set.Ici 0) := by
    have he (t : ℝ) : bIntegrand ψI' 0 t =
        ψI' (Complex.I * t) - 144 - (Real.exp (2 * Real.pi * t) : ℂ) := by
      simp [bIntegrand]
    rw [funext he]
    exact (ψI'_imaginaryAxis_continuousOn.sub continuousOn_const).sub (by fun_prop)
  have hO : bIntegrand ψI' 0 =O[atTop] fun t : ℝ ↦ Real.exp (-Real.pi * t) := by
    apply ψI'_I_mul_sub_isBigO_atTop.congr_left
    intro t
    simp only [bIntegrand, zero_pow two_ne_zero, mul_zero, zero_mul, Real.exp_zero,
      Complex.ofReal_one, mul_one, Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_ofNat]
    ring
  have hExp := integrableOn_exp_mul_Ioi (neg_lt_zero.mpr Real.pi_pos) 0
  exact ((hcont.locallyIntegrableOn measurableSet_Ici).integrableOn_of_isBigO_atTop hO
    ⟨Set.Ioi 0, Ioi_mem_atTop 0, hExp⟩).mono_set Set.Ioi_subset_Ici_self

/-- The regularized integral in Proposition 7.41 converges absolutely at every radius. -/
theorem integrableOn_regularized_b (r : ℝ) :
    IntegrableOn (bIntegrand ψI' r) (Set.Ioi (0 : ℝ)) :=
  integrableOn_regularized_b_of_zero integrableOn_regularized_b_zero r

/-- Proposition 7.41, equation (69), away from the removable singularities
at `r = 0` and `r ^ 2 = 2`, given analyticity. -/
theorem b_radial_eq_regularized_laplace_of_analytic
    (hb : AnalyticOnNhd ℝ (fun r : ℝ => b.RealIntegrals.b' (r ^ 2))
      (Set.Ioi (0 : ℝ)))
    (hL : AnalyticOnNhd ℝ (regularizedIntegral ψI') (Set.Ioi (0 : ℝ)))
    {r : ℝ} (hr : 0 < r) (hr2 : r ^ 2 ≠ 2) :
    b.RealIntegrals.b' (r ^ 2) = regularizedRhs (-4 * Complex.I) ψI' r := by
  refine b_formula_of_laplace_and_analytic _ _ _ hb hL ?_ r hr hr2
  intro x hx
  exact b_regularized_eq_above_two (by nlinarith [sq_nonneg (x - 2)])

end MagicFunction

end
