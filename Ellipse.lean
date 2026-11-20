import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Algebraic and quantitative circumellipse lemmas for the counterexample. -/
namespace CrescentEllipse

open Complex

/-- The monic quartic obtained from the intersection of the unit circle with the
ellipse `4(x-u)² + 6(y-v)² = 5R²`. -/
def quartic (B C D z : ℂ) : ℂ := z^4 + B*z^3 + C*z^2 + D*z + 1

def cubicCoeff (u v : ℝ) : ℂ := 8*(u : ℂ) - 12*(v : ℂ)*I

def quadCoeff (u v R : ℝ) : ℂ := -10 - 8*(u : ℂ)^2 - 12*(v : ℂ)^2 + 10*(R : ℂ)^2

def linearCoeff (u v : ℝ) : ℂ := 8*(u : ℂ) + 12*(v : ℂ)*I

/-- Direct conversion, without division by the complex parameter. -/
theorem incidence_quartic (x y u v R : ℝ) (hc : x^2+y^2=1)
    (he : 4*(x-u)^2 + 6*(y-v)^2 = 5*R^2) :
    quartic (cubicCoeff u v) (quadCoeff u v R) (linearCoeff u v) ⟨x,y⟩ = 0 := by
  apply Complex.ext <;>
    simp [quartic, cubicCoeff, quadCoeff, linearCoeff, pow_succ, Complex.mul_re,
      Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im] <;>
    first
      | linear_combination (-8*u*x+12*v*y+9*x^2-11*y^2-1)*hc - 2*(x^2-y^2)*he
      | linear_combination (4*(-2*u*y-3*v*x+5*x*y))*hc - (4*x*y)*he

/-- A monic quartic with constant coefficient one and three distinct roots.
The fourth root is given explicitly by the sum-of-roots identity. -/
theorem factor_three (B C D r s t : ℂ) (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
    (hr : quartic B C D r = 0) (hs : quartic B C D s = 0) (ht : quartic B C D t = 0) :
    let w := -(B+r+s+t)
    (∀ z, quartic B C D z = (z-r)*(z-s)*(z-t)*(z-w)) ∧ r*s*t*w=1 := by
  dsimp only
  let f (z : ℂ) := z^3 + (B+r)*z^2 + (C+B*r+r^2)*z + D+C*r+B*r^2+r^3
  let g (z : ℂ) := z^2 + (B+r+s)*z + C+B*r+r^2+(B+r)*s+s^2
  have hf (z : ℂ) : quartic B C D z = (z-r)*f z := by
    calc
      _ = (z-r)*f z + quartic B C D r := by unfold f quartic; ring
      _ = _ := by rw [hr, add_zero]
  have fs : f s = 0 := (mul_eq_zero.mp ((hf s).symm.trans hs)).resolve_left (sub_ne_zero.mpr hrs.symm)
  have ft : f t = 0 := (mul_eq_zero.mp ((hf t).symm.trans ht)).resolve_left (sub_ne_zero.mpr hrt.symm)
  have hg (z : ℂ) : f z = (z-s)*g z := by
    calc
      _ = (z-s)*g z + f s := by unfold f g; ring
      _ = _ := by rw [fs, add_zero]
  have gt : g t = 0 := (mul_eq_zero.mp ((hg t).symm.trans ft)).resolve_left (sub_ne_zero.mpr hst.symm)
  have fac (z : ℂ) : quartic B C D z = (z-r)*(z-s)*(z-t)*(z- -(B+r+s+t)) := by
    rw [hf, hg]
    calc
      _ = (z-r)*(z-s)*((z-t)*(z- -(B+r+s+t))+g t) := by unfold g; ring
      _ = _ := by rw [gt, add_zero]; ring
  refine ⟨fac, ?_⟩
  have h0 := (fac 0).symm
  simp only [quartic, zero_pow (by decide : 4 ≠ 0), zero_pow (by decide : 3 ≠ 0),
    zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero, zero_add, zero_sub] at h0
  linear_combination h0

/-- The sum identity determines both coordinates of the center. -/
theorem center_coords (u v : ℝ) (S : ℂ) (h : S = -cubicCoeff u v) :
    S.re = -8*u ∧ S.im = 12*v := by
  subst S
  simp [cubicCoeff, Complex.mul_re, Complex.mul_im]

/-- Quantitative center estimates used in the vertical cone argument. -/
theorem center_bounds (u v : ℝ) (S : ℂ) (h : S = -cubicCoeff u v)
    (hclose : ‖S - 4*I‖ < 6/100) : |u| < 3/400 ∧ |v-1/3| < 1/200 := by
  obtain ⟨hr, hi⟩ := center_coords u v S h
  have cr := (Complex.abs_re_le_norm (S-4*I)).trans_lt hclose
  have ci := (Complex.abs_im_le_norm (S-4*I)).trans_lt hclose
  simp [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, hr, hi] at cr ci
  rw [abs_lt] at ci
  constructor
  · linarith
  · rw [abs_lt]; constructor <;> linarith

/-- Complex point at angle π/2 plus x. -/
noncomputable def point (x : ℝ) : ℂ := I * exp ((x : ℂ)*I)

def InArc (x : ℝ) : Prop := 0 < x ∧ x < 1/100

theorem point_re (x : ℝ) : (point x).re = -Real.sin x := by
  simp [point, Complex.mul_re]

theorem point_im (x : ℝ) : (point x).im = Real.cos x := by
  simp [point, Complex.mul_im]

theorem point_cis (x : ℝ) : point x = ⟨Real.cos (Real.pi/2+x), Real.sin (Real.pi/2+x)⟩ := by
  apply Complex.ext <;> simp [point_re, point_im, Real.cos_add, Real.sin_add]

theorem point_ne {x y : ℝ} (hx : InArc x) (hy : InArc y) (hxy : x ≠ y) : point x ≠ point y := by
  intro h
  have eqsin : Real.sin x = Real.sin y := by simpa [point_re] using congrArg Complex.re h
  apply hxy
  apply Real.strictMonoOn_sin.injOn _ _ eqsin <;> constructor <;>
    linarith [Real.two_le_pi, hx.1, hx.2, hy.1, hy.2]

/-- The three northern roots and the reflected fourth point have product one. -/
theorem reflected_product (x y t : ℝ) :
    point x * point y * point t * point (-(x+y+t)) = 1 := by
  unfold point
  push_cast
  calc
    _ = I^4 * (exp ((x:ℂ)*I) * exp ((y:ℂ)*I) * exp ((t:ℂ)*I) *
      exp (-((x:ℂ)+(y:ℂ)+(t:ℂ))*I)) := by ring
    _ = _ := by
      rw [← exp_add, ← exp_add, ← exp_add]
      ring_nf
      simp

/-- The reflected point is strictly to the right of the vertical axis. -/
theorem reflected_ne {x y t q : ℝ} (hx : InArc x) (hy : InArc y) (ht : InArc t)
    (hq : InArc q) : point q ≠ point (-(x+y+t)) := by
  have hsum := Real.sin_pos_of_pos_of_lt_pi (x := x+y+t)
    (by linarith [hx.1,hy.1,ht.1]) (by linarith [hx.2,hy.2,ht.2,Real.two_le_pi])
  have hsin := Real.sin_pos_of_pos_of_lt_pi hq.1 (by linarith [hq.2,Real.two_le_pi])
  intro e
  have := congrArg Complex.re e
  simp only [point_re, Real.sin_neg, neg_neg] at this
  linarith

theorem point_close (x : ℝ) : ‖point x - I‖ ≤ |x| := by
  have hh := Real.norm_exp_I_mul_ofReal_sub_one_le (x := x)
  rw [mul_comm I (x : ℂ), Real.norm_eq_abs] at hh
  simpa [point, ← mul_sub_one, norm_mul] using hh

/-- Sum of the four roots stays near 4i, uniformly for every choice of triple. -/
theorem sum_close {x y t : ℝ} (hx : InArc x) (hy : InArc y) (ht : InArc t) :
    ‖point x+point y+point t+point (-(x+y+t))-4*I‖ < 6/100 := by
  have hsum : 0 ≤ x+y+t := by linarith [hx.1, hy.1, ht.1]
  have h4 := point_close (-(x+y+t))
  rw [abs_neg, abs_of_nonneg hsum] at h4
  calc
    _ = ‖((point x-I)+(point y-I)+(point t-I))+(point (-(x+y+t))-I)‖ := by congr 1; ring
    _ ≤ ‖(point x-I)+(point y-I)+(point t-I)‖+‖point (-(x+y+t))-I‖ := norm_add_le _ _
    _ ≤ (‖point x-I‖+‖point y-I‖+‖point t-I‖)+‖point (-(x+y+t))-I‖ := by
      linarith [norm_add_le (point x-I) (point y-I), norm_add_le ((point x-I)+(point y-I)) (point t-I)]
    _ < _ := by
      have h1 := point_close x
      have h2 := point_close y
      have h3 := point_close t
      rw [abs_of_pos hx.1] at h1
      rw [abs_of_pos hy.1] at h2
      rw [abs_of_pos ht.1] at h3
      linarith [hx.2, hy.2, ht.2]

/-- Equality for the true ellipse metric, squared and scaled by five. -/
def OnEllipse (u v R x : ℝ) : Prop :=
  4*((point x).re-u)^2 + 6*((point x).im-v)^2 = 5*R^2

theorem point_quartic {u v R x : ℝ} (h : OnEllipse u v R x) :
    quartic (cubicCoeff u v) (quadCoeff u v R) (linearCoeff u v) (point x) = 0 := by
  apply incidence_quartic (point x).re (point x).im u v R _ h
  rw [point_re, point_im, neg_sq, Real.sin_sq_add_cos_sq]

/-- Three distinct points of the short arc on one translated ellipse force the
center into the claimed box. Every other arc point misses this same ellipse. -/
theorem triple_controls {u v R x y t : ℝ} (hx : InArc x) (hy : InArc y) (ht : InArc t)
    (hxy : x ≠ y) (hxt : x ≠ t) (hyt : y ≠ t)
    (ex : OnEllipse u v R x) (ey : OnEllipse u v R y) (et : OnEllipse u v R t) :
    (|u| < 3/400 ∧ |v-1/3| < 1/200) ∧
    ∀ q, InArc q → q ≠ x → q ≠ y → q ≠ t → ¬OnEllipse u v R q := by
  obtain ⟨fac, prod⟩ := factor_three _ _ _ _ _ _ (point_ne hx hy hxy)
    (point_ne hx ht hxt) (point_ne hy ht hyt) (point_quartic ex) (point_quartic ey) (point_quartic et)
  have nz (a : ℝ) : point a ≠ 0 := by simp [point, Complex.I_ne_zero, Complex.exp_ne_zero]
  have fourth : -(cubicCoeff u v + point x + point y + point t) = point (-(x+y+t)) := by
    exact mul_left_cancel₀ (mul_ne_zero (mul_ne_zero (nz x) (nz y)) (nz t))
      (prod.trans (reflected_product x y t).symm)
  constructor
  · apply center_bounds u v _ _ (sum_close hx hy ht)
    linear_combination -fourth
  · intro q hq hqx hqy hqt eqe
    have hp := (fac (point q)).symm.trans (point_quartic eqe)
    rw [fourth] at hp
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr (point_ne hq hx hqx))
      (sub_ne_zero.mpr (point_ne hq hy hqy))) (sub_ne_zero.mpr (point_ne hq ht hqt)))
      (sub_ne_zero.mpr (reflected_ne hx hy ht hq))) hp

/-- Every point relative to such a center lies in the vertical cone. In that
cone the elliptic quadratic form strictly dominates both competing squares. -/
theorem ellipse_dominates {u v q : ℝ} (hu : |u| < 3/400) (hv : |v-1/3| < 1/200)
    (hq : InArc q) :
    let X := (point q).re-u
    let Y := (point q).im-v
    0 < Y ∧ |X| < (3/100)*Y ∧
    X^2+Y^2 < (4*X^2+6*Y^2)/5 ∧ ((4/5)*(X+Y))^2 < (4*X^2+6*Y^2)/5 := by
  dsimp only
  have ca := Real.abs_cos_sub_cos_le q 0
  have sa := Real.abs_sin_le_abs (x := q)
  simp [abs_of_pos hq.1] at ca sa
  rw [abs_le] at ca sa
  rw [abs_lt] at hu hv
  rw [point_re, point_im]
  have hx : |(-Real.sin q)-u| < 7/400 := by rw [abs_lt]; constructor <;> linarith [hq.2]
  -- cos q ≥ 1-q from the chord bound. The sharper quadratic estimate with
  -- sin²+cos²=1 recovers the stated 0.66 lower bound on the vertical gap.
  have cospos : 0 < Real.cos q := by linarith [hq.2]
  have sin2 : (Real.sin q)^2 < (1/100:ℝ)^2 := by
    nlinarith [mul_pos (show 0 < 1/100-Real.sin q by linarith [hq.2])
      (show 0 < 1/100+Real.sin q by linarith [hq.2])]
  have clow : (999/1000:ℝ) < Real.cos q := by
    by_contra! bad
    nlinarith [Real.sin_sq_add_cos_sq q,
      mul_nonneg (show 0 ≤ (999/1000)-Real.cos q by linarith) (show 0 ≤ (999/1000)+Real.cos q by linarith)]
  have hy : 66/100 < Real.cos q-v := by linarith
  have hc : |(-Real.sin q)-u| < (3/100)*(Real.cos q-v) := by linarith
  refine ⟨by linarith, hc, ?_, ?_⟩
  all_goals
    rw [abs_lt] at hc
    let X := -Real.sin q-u
    let Y := Real.cos q-v
    change -(3/100*Y) < X ∧ X < 3/100*Y at hc
    have y0 : 0 < Y := by dsimp [Y]; linarith
    have h1 : 0 < (Y-X)*(Y+X) := mul_pos (by linarith) (by linarith)
  · change X^2+Y^2 < _; nlinarith
  · change ((4/5)*(X+Y))^2 < (4*X^2+6*Y^2)/5
    nlinarith [mul_pos (show 0 < (3/100)*Y-X by linarith) y0, sq_nonneg X, sq_pos_of_pos y0]

end CrescentEllipse
