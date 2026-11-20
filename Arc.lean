import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-! The explicit norm, its flat segment, and chord distances on the arc. -/
noncomputable section
namespace CrescentArc

def euclid (x y : ℝ) := Real.sqrt (x^2 + y^2)
def ellipse (x y : ℝ) := Real.sqrt (4/5*x^2 + 6/5*y^2)
def strip (x y : ℝ) := 4/5*|x+y|
def gauge (x y : ℝ) := max (max (euclid x y) (ellipse x y)) (strip x y)

private theorem euclid_complex (x y : ℝ) : euclid x y = ‖(⟨x,y⟩ : ℂ)‖ := by
  simp [euclid, Complex.norm_def, Complex.normSq_apply, pow_two]

private theorem ellipse_scaled (x y : ℝ) :
    ellipse x y = euclid (Real.sqrt (4/5) * x) (Real.sqrt (6/5) * y) := by
  unfold ellipse euclid
  congr 1
  rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : 0 ≤ (4/5:ℝ)),
    Real.sq_sqrt (by norm_num : 0 ≤ (6/5:ℝ))]

theorem euclid_add (x y u v : ℝ) : euclid (x+u) (y+v) ≤ euclid x y + euclid u v := by
  simp only [euclid_complex]
  exact norm_add_le (⟨x,y⟩ : ℂ) ⟨u,v⟩

theorem gauge_add (x y u v : ℝ) : gauge (x+u) (y+v) ≤ gauge x y + gauge u v := by
  have e := euclid_add x y u v
  have f : ellipse (x+u) (y+v) ≤ ellipse x y + ellipse u v := by
    simp only [ellipse_scaled, mul_add]
    exact euclid_add _ _ _ _
  have g : strip (x+u) (y+v) ≤ strip x y + strip u v := by
    unfold strip
    rw [show x+u+(y+v)=x+y+(u+v) by ring]
    linarith [abs_add_le (x+y) (u+v)]
  unfold gauge
  exact max_le (max_le
    (e.trans (add_le_add ((le_max_left ..).trans (le_max_left ..)) ((le_max_left ..).trans (le_max_left ..))))
    (f.trans (add_le_add ((le_max_right ..).trans (le_max_left ..)) ((le_max_right ..).trans (le_max_left ..)))))
    (g.trans (add_le_add (le_max_right ..) (le_max_right ..)))

theorem euclid_scale (t x y : ℝ) : euclid (t*x) (t*y) = |t| * euclid x y := by
  unfold euclid
  rw [show (t*x)^2+(t*y)^2=t^2*(x^2+y^2) by ring,
    Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq_eq_abs]

theorem gauge_scale (t x y : ℝ) : gauge (t*x) (t*y) = |t| * gauge x y := by
  have e : ellipse (t*x) (t*y) = |t| * ellipse x y := by
    simp only [ellipse_scaled]
    rw [mul_left_comm _ t x, mul_left_comm _ t y, euclid_scale]
  have s : strip (t*x) (t*y) = |t| * strip x y := by
    unfold strip
    rw [← mul_add, abs_mul]; ring
  unfold gauge
  rw [euclid_scale,e,s, mul_max_of_nonneg _ _ (abs_nonneg t),
    mul_max_of_nonneg _ _ (abs_nonneg t)]

theorem gauge_nonneg (x y : ℝ) : 0 ≤ gauge x y :=
  (Real.sqrt_nonneg _).trans ((le_max_left (euclid x y) _).trans (le_max_left ..))

theorem gauge_zero_iff (x y : ℝ) : gauge x y = 0 ↔ x=0 ∧ y=0 := by
  constructor
  · intro h
    have he : euclid x y ≤ 0 := h ▸ ((le_max_left ..).trans (le_max_left ..) : euclid x y ≤ gauge x y)
    have hs := Real.sq_sqrt (show 0 ≤ x^2+y^2 by positivity)
    have hz : Real.sqrt (x^2+y^2)=0 := le_antisymm he (Real.sqrt_nonneg _)
    rw [hz] at hs
    constructor <;> nlinarith [sq_nonneg x,sq_nonneg y]
  · rintro ⟨rfl,rfl⟩; norm_num [gauge, euclid, ellipse, strip]

/-- A whole nontrivial segment on the supporting line x+y=5/4. -/
theorem unit_segment (x : ℝ) (hx : 3/5 ≤ x) (hy : x ≤ 13/20) :
    gauge x (5/4-x)=1 := by
  have h1 : x^2+(5/4-x)^2 ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)]
  have h2 : 4/5*x^2+6/5*(5/4-x)^2 ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)]
  have hs : strip x (5/4-x)=1 := by unfold strip; rw [show x+(5/4-x)=(5/4:ℝ) by ring]; norm_num
  have h3 : euclid x (5/4-x) ≤ 1 := by simpa [euclid] using Real.sqrt_le_sqrt h1
  have h4 : ellipse x (5/4-x) ≤ 1 := by simpa [ellipse] using Real.sqrt_le_sqrt h2
  exact (show max (max _ _) _ = _ by rw [hs]; exact max_eq_right (max_le h3 h4))


theorem chord_direction (t : ℝ) (h : |t| ≤ 1/100) :
    gauge (-Real.cos t) (-Real.sin t) = 1 := by
  have ht := Real.abs_sin_le_abs (x:=t) |>.trans h
  have hc : |Real.cos t| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_cos t, Real.cos_le_one t⟩
  have ht2 : (Real.sin t)^2 ≤ (1/100:ℝ)^2 := by
    simpa only [sq_abs] using (pow_le_pow_left₀ (abs_nonneg _) ht 2)
  have hid := Real.sin_sq_add_cos_sq t
  have he : euclid (-Real.cos t) (-Real.sin t) = 1 := by
    unfold euclid
    rw [show (-Real.cos t)^2+(-Real.sin t)^2=1 by nlinarith, Real.sqrt_one]
  have hf : ellipse (-Real.cos t) (-Real.sin t) ≤ 1 := by
    unfold ellipse
    calc
      _ ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by nlinarith)
      _ = _ := Real.sqrt_one
  have hs : strip (-Real.cos t) (-Real.sin t) ≤ 1 := by
    unfold strip
    have H := abs_add_le (-Real.cos t) (-Real.sin t)
    rw [abs_neg, abs_neg] at H
    linarith
  simp only [gauge, he, max_eq_left hf, max_eq_left hs]

def px (t : ℝ) := -Real.sin t
def py (t : ℝ) := Real.cos t

theorem chord_length (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1/100) :
    gauge (px t - px s) (py t - py s) = 2*Real.sin ((t-s)/2) := by
  have hmean : |(t+s)/2| ≤ 1/100 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hsin : 0 ≤ Real.sin ((t-s)/2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_gt_three])
  rw [show px t-px s=(2*Real.sin ((t-s)/2))*(-Real.cos ((t+s)/2)) by
    unfold px; rw [show -Real.sin t - -Real.sin s = -(Real.sin t-Real.sin s) by ring,
      Real.sin_sub_sin]; ring,
    show py t-py s=(2*Real.sin ((t-s)/2))*(-Real.sin ((t+s)/2)) by
      unfold py; rw [Real.cos_sub_cos]; ring,
    gauge_scale, chord_direction _ hmean, mul_one, abs_of_nonneg (by positivity)]

def step (n : ℕ) : ℝ := Real.pi / (1000 * n)
def offset (n j : ℕ) : ℝ := j * step n

theorem step_pos (n : ℕ) (hn : 0<n) : 0 < step n := by unfold step; positivity

theorem offset_bounds {n j : ℕ} (hj : j ≤ n) (hn : 0<n) :
    0 ≤ offset n j ∧ offset n j ≤ 1/100 := by
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  have hj' : (j:ℝ) ≤ n := by exact_mod_cast hj
  unfold offset step
  constructor
  · positivity
  · rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hj' Real.pi_pos.le,
      mul_lt_mul_of_pos_right Real.pi_lt_four hn']

/-- Distance equality for any two increasing pairs of indices, in either direction. -/
theorem gap_iff {n i j k l : ℕ} (hn : 0<n) (hij : i≤j) (hjn : j≤n)
    (hkl : k≤l) (hln : l≤n) :
    gauge (px (offset n j) - px (offset n i)) (py (offset n j) - py (offset n i)) =
      gauge (px (offset n l) - px (offset n k)) (py (offset n l) - py (offset n k)) ↔
      j-i=l-k := by
  have H := step_pos n hn
  have mono : Monotone (offset n) := fun a b hab =>
    mul_le_mul_of_nonneg_right (by exact_mod_cast hab) H.le
  have hi := offset_bounds (hij.trans hjn) hn
  have hj := offset_bounds hjn hn
  have hk := offset_bounds (hkl.trans hln) hn
  have hl := offset_bounds hln hn
  have A := mono hij
  have B := mono hkl
  rw [chord_length _ _ hi.1 A hj.2, chord_length _ _ hk.1 B hl.2]
  have mem (a b : ℝ) (ha : 0 ≤ a) (hab : a≤b) (hb : b≤1/100) :
      (b-a)/2 ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_gt_three]⟩
  have E (a b : ℕ) (hab : a ≤ b) :
      offset n b - offset n a = ((b-a:ℕ):ℝ)*step n := by
    rw [Nat.cast_sub hab]; unfold offset; ring
  constructor
  · intro eq
    have h := Real.strictMonoOn_sin.injOn (mem _ _ hi.1 A hj.2) (mem _ _ hk.1 B hl.2)
      (show Real.sin _ = Real.sin _ by linarith only [eq])
    have h' : offset n j - offset n i = offset n l - offset n k := by linarith
    rw [E _ _ hij, E _ _ hkl] at h'
    have hh := mul_right_cancel₀ H.ne' h'
    exact_mod_cast hh
  · intro h
    rw [E _ _ hij,E _ _ hkl,h]


theorem xdiff (a b : ℝ) :
    px a-px b=2*Real.sin ((b-a)/2)*Real.cos ((b+a)/2) := by
  unfold px
  rw [show -Real.sin a - -Real.sin b = Real.sin b - Real.sin a by ring, Real.sin_sub_sin]

theorem ydiff (a b : ℝ) :
    py a-py b=2*Real.sin ((b-a)/2)*Real.sin ((b+a)/2) := by
  unfold py
  rw [show Real.cos a-Real.cos b = -(Real.cos b-Real.cos a) by ring, Real.cos_sub_cos]
  ring

theorem cross_pos {a b c : ℝ} (ha : 0 ≤ a) (hab : a < b) (hbc : b < c) (hc : c ≤ 1/100) :
    0 < (px a-px b)*(py b-py c) - (py a-py b)*(px b-px c) := by
  rw [xdiff,ydiff,ydiff,xdiff]
  have sinpos (x : ℝ) (hx : 0 < x) (hx' : x ≤ 1/100) : 0 < Real.sin x :=
    Real.sin_pos_of_pos_of_lt_pi hx (by linarith [Real.pi_gt_three])
  have h : Real.sin ((c-a)/2) =
      Real.sin ((c+b)/2)*Real.cos ((b+a)/2)-Real.cos ((c+b)/2)*Real.sin ((b+a)/2) := by
    rw [← Real.sin_sub]; congr 1; ring
  have e : 0 < 4 * Real.sin ((b-a)/2) * Real.sin ((c-b)/2) * Real.sin ((c-a)/2) :=
    mul_pos (mul_pos (mul_pos (by norm_num) (sinpos _ (by linarith) (by linarith)))
      (sinpos _ (by linarith) (by linarith))) (sinpos _ (by linarith) (by linarith))
  rw [h] at e
  linarith only [e]

/-- The chords have strictly positive horizontal and vertical increments, and
the vertical increment is less than one thirtieth of the horizontal one. -/
theorem shallow_chord {a b : ℝ} (ha : 0<a) (hab : a<b) (hb : b≤1/100) :
    0 < px a-px b ∧ 0 < py a-py b ∧ 30*(py a-py b) < px a-px b := by
  have A : 0 < (b-a)/2 := by linarith
  have B : 0 < (b+a)/2 := by linarith
  have B' : (b+a)/2 ≤ 1/100 := by linarith
  have s := Real.sin_pos_of_pos_of_lt_pi A (by linarith [Real.pi_gt_three])
  have t := Real.sin_pos_of_pos_of_lt_pi B (by linarith [Real.pi_gt_three])
  have ht := Real.abs_sin_le_abs (x:=(b+a)/2)
  rw [abs_of_pos B,abs_of_pos t] at ht
  have hc := Real.one_sub_sq_div_two_le_cos (x:=(b+a)/2)
  have hv := mul_nonneg (sub_nonneg.mpr B') B.le
  have cmp : 30*Real.sin ((b+a)/2) < Real.cos ((b+a)/2) := by nlinarith
  have positive : 0 < Real.cos ((b+a)/2) := by linarith
  rw [xdiff,ydiff]
  exact ⟨by positivity, by positivity, by nlinarith [mul_lt_mul_of_pos_left cmp s]⟩

end CrescentArc
