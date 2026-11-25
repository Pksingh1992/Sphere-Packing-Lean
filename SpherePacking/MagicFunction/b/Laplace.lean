
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic
open MeasureTheory
open scoped Real Topology
noncomputable section

def bIntegrand (psi : ℂ → ℂ) (r t : ℝ) : ℂ :=
  (psi (Complex.I * (t : ℂ)) - 144 -
    (Real.exp (2 * Real.pi * t) : ℂ)) *
    (Real.exp (-Real.pi * r ^ 2 * t) : ℂ)

/-- The right side of the submitted theorem, with corrected parentheses. -/

def proposedRhs (psi : ℂ → ℂ) (r : ℝ) : ℂ :=
  4 * Complex.I * (Real.sin (Real.pi * r ^ 2 / 2) ^ 2 : ℂ) *
    (((144 / (Real.pi * r ^ 2) +
      1 / (Real.pi * (r ^ 2 - 2)) : ℝ) : ℂ) +
      ∫ t in Set.Ioi (0 : ℝ), bIntegrand psi r t)

/-- At r = 2 the sine factor forces the proposed right side to vanish. -/

theorem proposedRhs_two (psi : ℂ → ℂ) : proposedRhs psi 2 = 0 := by
  have hangle : Real.pi * (2 : ℝ) ^ 2 / 2 = 2 * Real.pi := by ring
  simp [proposedRhs, hangle, Real.sin_two_pi]

/-- The assumptions on r alone cannot imply the proposed formula. -/

theorem no_unrestricted_formula (psi : ℂ → ℂ) :
    ¬ (∀ (b : ℝ → ℂ) (r : ℝ),
      0 ≤ r → r ≠ 0 → r ^ 2 ≠ 2 →
      b r = proposedRhs psi r) := by
  intro h
  have hbad := h (fun _ => 1) 2
    (by norm_num) (by norm_num) (by norm_num)
  rw [proposedRhs_two] at hbad
  exact one_ne_zero hbad
/--
The real analytic continuation step used after clearing denominators.
This is a general helper, not a proof that the contour integrals or the
regularized integral have the required analyticity.
-/

theorem eq_on_positive_of_analytic_of_eq_above_two
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

def expKernel (a t : ℝ) : ℂ := (Real.exp (-a * t) : ℂ)

theorem integrableOn_expKernel {a : ℝ} (ha : 0 < a) :
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

theorem integral_expKernel {a : ℝ} (ha : 0 < a) :
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

theorem bIntegrand_eq (psi : ℂ → ℂ) (r t : ℝ) :
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
The integral computation in the range needed to seed continuation.
The weaker bound r > 2 is sufficient for that purpose.
-/

theorem laplace_regularization (psi : ℂ → ℂ) {r : ℝ} (hr : 2 < r)
    (hreg : IntegrableOn (bIntegrand psi r) (Set.Ioi (0 : ℝ))) :
    (∫ t in Set.Ioi (0 : ℝ),
        psi (Complex.I * (t : ℂ)) * expKernel (Real.pi * r ^ 2) t) =
      144 / ((Real.pi * r ^ 2 : ℝ) : ℂ) +
      1 / ((Real.pi * (r ^ 2 - 2) : ℝ) : ℂ) +
      regularizedIntegral psi r := by
  have hsq : 2 < r ^ 2 := by nlinarith [sq_nonneg (r - 2)]
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

def denominator (r : ℝ) : ℂ :=
  (Real.pi : ℂ) * (r : ℂ) ^ 2 * ((r : ℂ) ^ 2 - 2)

def numerator (psi : ℂ → ℂ) (r : ℝ) : ℂ :=
  144 * ((r : ℂ) ^ 2 - 2) + (r : ℂ) ^ 2 +
    denominator r * regularizedIntegral psi r

/-- The coefficient is a parameter so that the sign convention is explicit. -/

def regularizedRhs (c : ℂ) (psi : ℂ → ℂ) (r : ℝ) : ℂ :=
  c * (Real.sin (Real.pi * r ^ 2 / 2) ^ 2 : ℂ) *
    (144 / ((Real.pi * r ^ 2 : ℝ) : ℂ) +
      1 / ((Real.pi * (r ^ 2 - 2) : ℝ) : ℂ) +
      regularizedIntegral psi r)

theorem denominator_ne_zero {r : ℝ} (hr0 : r ≠ 0) (hr2 : r ^ 2 ≠ 2) :
    denominator r ≠ 0 := by
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr0
  have hs : (r : ℂ) ^ 2 - 2 ≠ 0 := by
    exact_mod_cast (sub_ne_zero.mpr hr2)
  exact mul_ne_zero (mul_ne_zero hp (pow_ne_zero 2 hrc)) hs

/-- Clearing the two explicit denominators creates an analytic expression. -/

theorem denominator_mul_rhs (c : ℂ) (psi : ℂ → ℂ) {r : ℝ}
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
/--
A sufficient collection of prerequisites, rather than an assertion about
arbitrary functions. These fields must ultimately be proved from the contour
definition and modular-form estimates. These prerequisites are not proved in this file.
-/

structure RegularizationHypotheses (c : ℂ) (b : ℝ → ℂ) (psi : ℂ → ℂ) : Prop where
  regularized_integrable : ∀ r : ℝ, 0 ≤ r →
    IntegrableOn (bIntegrand psi r) (Set.Ioi (0 : ℝ))
  analytic_b : AnalyticOnNhd ℝ b (Set.Ioi (0 : ℝ))
  analytic_regularized :
    AnalyticOnNhd ℝ (regularizedIntegral psi) (Set.Ioi (0 : ℝ))
  laplace_above_two : ∀ r : ℝ, 2 < r →
    b r = c * (Real.sin (Real.pi * r ^ 2 / 2) ^ 2 : ℂ) *
      ∫ t in Set.Ioi (0 : ℝ),
        psi (Complex.I * (t : ℂ)) * expKernel (Real.pi * r ^ 2) t
/--
Conditional regularization theorem. This is a repaired, stronger-hypothesis
version of the submitted declaration. All four fields of h are substantive
prerequisites; in particular convergence and analyticity are not proved here.
-/

theorem b_formula_of_laplace_and_analytic
    (c : ℂ) (b : ℝ → ℂ) (psi : ℂ → ℂ)
    (h : RegularizationHypotheses c b psi)
    (r : ℝ) (hr : 0 ≤ r) (hr0 : r ≠ 0) (hr2 : r ^ 2 ≠ 2) :
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
      (hDreal x).fun_smul (h.analytic_b x hx)

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
          (h.analytic_regularized x hx))
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
    have hb := h.laplace_above_two x hx
    rw [laplace_regularization psi hx
      (h.regularized_integrable x (by linarith))] at hb
    change b x = regularizedRhs c psi x at hb
    rw [hb]
    exact denominator_mul_rhs c psi (r := x)
      (by linarith)
      (by nlinarith [sq_nonneg (x - 2)])

  have hcleared :=
    eq_on_positive_of_analytic_of_eq_above_two
      hF hG hlarge (lt_of_le_of_ne hr (Ne.symm hr0))
  apply mul_left_cancel₀ (denominator_ne_zero hr0 hr2)
  exact hcleared.trans
    (denominator_mul_rhs c psi hr0 hr2).symm

/-- The submitted positive sign, now with its required prerequisites. -/

theorem b_formula_with_hypotheses
    (b : ℝ → ℂ) (psi : ℂ → ℂ)
    (h : RegularizationHypotheses (4 * Complex.I) b psi)
    (r : ℝ) (hr : 0 ≤ r) (hr0 : r ≠ 0) (hr2 : r ^ 2 ≠ 2) :
    b r = proposedRhs psi r := by
  simpa [regularizedRhs, proposedRhs, regularizedIntegral, Complex.ofReal_add,
    Complex.ofReal_div] using
    b_formula_of_laplace_and_analytic (4 * Complex.I) b psi h r hr hr0 hr2

end
