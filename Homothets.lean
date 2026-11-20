import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! An elementary replacement for boundary-intersection theory in the circumcircle proof.
All three squared gauges are multiplied by 25, eliminating square roots and fractions. -/
namespace CrescentCircles

def disk (x y : ℝ) := 25*(x^2+y^2)
def ellipse (x y : ℝ) := 20*x^2+30*y^2
def slab (x y : ℝ) := 16*(x+y)^2
def gauge (x y : ℝ) := max (disk x y) (max (ellipse x y) (slab x y))
theorem disk_le (x y : ℝ) : disk x y ≤ gauge x y := le_max_left _ _
theorem ellipse_le (x y : ℝ) : ellipse x y ≤ gauge x y :=
  (le_max_left _ _).trans (le_max_right _ _)
theorem slab_le (x y : ℝ) : slab x y ≤ gauge x y :=
  (le_max_right _ _).trans (le_max_right _ _)

/-- Vertical cone in which the elliptical branch gives the full gauge. -/
theorem cone_active {x y : ℝ} (hl : -y ≤ 4*x) (hr : 4*x ≤ y) : gauge x y = ellipse x y := by
  have h : 0 ≤ y := by linarith
  have hprod := mul_nonneg (show 0 ≤ y-x by linarith) (show 0 ≤ y+x by linarith)
  have hs := mul_nonneg (show 0 ≤ 5*y-4*(x+y) by linarith)
    (show 0 ≤ 5*y+4*(x+y) by linarith)
  unfold gauge disk ellipse slab
  apply le_antisymm (max_le (by nlinarith) (max_le (le_refl _) (by nlinarith [sq_nonneg x, sq_nonneg y])))
  exact ellipse_le x y

/-- At an intermediate point on the upper arc a candidate circumcircle must be
on its elliptical branch. The left/right neighbors are at horizontal offsets
`-l` and `r`, with secant slopes `t` and `s`. -/
theorem middle_active {x y l r t s : ℝ} (hl : 0 < l) (hr : 0 < r)
    (ht : 0 ≤ t) (ht' : t ≤ 1) (hs : 0 ≤ s) (hs' : s ≤ 1)
    (hleft : gauge (x-l) (y-l*t) ≤ gauge x y)
    (hright : gauge (x+r) (y+r*s) ≤ gauge x y) : gauge x y = ellipse x y := by
  have excludeSlab : gauge x y ≠ slab x y := by
    intro he
    have al := (slab_le (x-l) (y-l*t)).trans (hleft.trans_eq he)
    have ar := (slab_le (x+r) (y+r*s)).trans (hright.trans_eq he)
    unfold slab at al ar
    have dl : 0 < l + l*t := by linarith [mul_nonneg hl.le ht]
    have dr : 0 < r + r*s := by linarith [mul_nonneg hr.le hs]
    by_cases hxy : 0 ≤ x+y
    · nlinarith [mul_nonneg hxy dr.le, sq_pos_of_pos dr]
    · nlinarith [mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hxy) dl.le, sq_pos_of_pos dl]
  by_cases hd : gauge x y = disk x y
  · have al := (disk_le (x-l) (y-l*t)).trans (hleft.trans_eq hd)
    have ar := (disk_le (x+r) (y+r*s)).trans (hright.trans_eq hd)
    unfold disk at al ar
    have dl : 0 ≤ x+t*y := by
      by_contra! h
      nlinarith [mul_neg_of_pos_of_neg hl h, sq_nonneg l, sq_nonneg (l*t)]
    have dr : x+s*y ≤ 0 := by
      by_contra! h
      nlinarith [mul_pos hr h, sq_nonneg r, sq_nonneg (r*s)]
    have bound : x^2 ≤ y^2 := by
      by_cases hy : 0 ≤ y
      · have lo : -y ≤ x := by nlinarith [mul_nonneg (sub_nonneg.mpr ht') hy]
        have hi : x ≤ y := by nlinarith [mul_nonneg hs hy]
        nlinarith [mul_nonneg (sub_nonneg.mpr hi) (show 0 ≤ y+x by linarith)]
      · have hn := le_of_not_ge hy
        have lo : y ≤ x := by nlinarith [mul_nonpos_of_nonneg_of_nonpos ht hn]
        have hi : x ≤ -y := by nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hs') hn]
        nlinarith [mul_nonneg (show 0 ≤ -y-x by linarith) (show 0 ≤ x-y by linarith)]
    apply le_antisymm _ (ellipse_le x y)
    rw [hd]; unfold disk ellipse; nlinarith
  · unfold gauge at hd excludeSlab ⊢
    rcases max_cases (disk x y) (max (ellipse x y) (slab x y)) with h | h
    · exact (hd h.1).elim
    · rcases max_cases (ellipse x y) (slab x y) with h' | h'
      · exact h.1.trans h'.1
      · exact (excludeSlab (h.1.trans h'.1)).elim

/-- If the candidate ellipse agrees at the middle pair and contains the left
point, its center is below the three-point circumcenter, within a vertical cone.
`u,v` are the old center minus the candidate center. -/
theorem center_ray {x y u v l r t s : ℝ} (hl : 0 < l) (hr : 0 < r)
    (hts : s < t) (hs : 0 ≤ s) (hs' : 6*s ≤ 1)
    (oldL : ellipse (x-l) (y-l*t) = ellipse x y)
    (oldR : ellipse (x+r) (y+r*s) = ellipse x y)
    (newL : ellipse (x+u-l) (y+v-l*t) ≤ ellipse (x+u) (y+v))
    (newR : ellipse (x+u+r) (y+v+r*s) = ellipse (x+u) (y+v)) :
    -v ≤ 4*u ∧ 4*u ≤ v := by
  unfold ellipse at oldL oldR newL newR
  have normal : 40*u+60*s*v=0 := by
    apply (mul_eq_zero.mp (show r*(40*u+60*s*v)=0 by nlinarith [oldR,newR])).resolve_left hr.ne'
  have side : 0 ≤ 40*u+60*t*v := by
    by_contra! h
    nlinarith [mul_neg_of_pos_of_neg hl h, oldL, newL]
  have up : 0 ≤ v := by
    by_contra! h
    nlinarith [mul_neg_of_pos_of_neg (sub_pos.mpr hts) h]
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr hs') up]
  · nlinarith [mul_nonneg hs up]

set_option maxHeartbeats 900000 in
/-- Ordered four-point certificate for exclusion of a common circle of the full
gauge. Coordinates are relative to the ellipse center of the first triple.
The first three points are the left, middle and right coordinates in `oldL`
and `oldR`; the fourth is one more step of length `m` and slope `w`.
Only the two outer points need the vertical-cone bounds. -/
theorem exclude_four {x y l r m t s w : ℝ}
    (hl : 0 < l) (hr : 0 < r) (hm : 0 < m)
    (ht : 0 ≤ t) (ht' : t ≤ 1) (hs : 0 ≤ s) (hs' : 6*s ≤ 1)
    (hw : 0 ≤ w) (hw' : w ≤ 1) (hts : s < t)
    (oldL : ellipse (x-l) (y-l*t) = ellipse x y)
    (oldR : ellipse (x+r) (y+r*s) = ellipse x y)
    (coneL : -(y-l*t) ≤ 4*(x-l) ∧ 4*(x-l) ≤ y-l*t)
    (coneD : -(y+r*s+m*w) ≤ 4*(x+r+m) ∧ 4*(x+r+m) ≤ y+r*s+m*w)
    (outside : ellipse (x+r+m) (y+r*s+m*w) ≠ ellipse x y) :
    ¬ ∃ u v R : ℝ, gauge (x+u-l) (y+v-l*t) = R ∧ gauge (x+u) (y+v) = R ∧
         gauge (x+u+r) (y+v+r*s) = R ∧ gauge (x+u+r+m) (y+v+r*s+m*w) = R := by
  rintro ⟨u,v,R,h₁,h₂,h₃,h₄⟩
  have hs1 : s ≤ 1 := by linarith
  have active₂ := middle_active hl hr ht ht' hs hs1 (h₁.trans h₂.symm).le (h₃.trans h₂.symm).le
  have active₃ := middle_active (x:=x+u+r) (y:=y+v+r*s) hr hm hs hs1 hw hw'
    (by simpa using (h₂.trans h₃.symm).le) (h₄.trans h₃.symm).le
  have newR : ellipse (x+u+r) (y+v+r*s) = ellipse (x+u) (y+v) :=
    active₃.symm.trans (h₃.trans (h₂.symm.trans active₂))
  have newL := (ellipse_le (x+u-l) (y+v-l*t)).trans ((h₁.trans (h₂.symm.trans active₂)).le)
  obtain ⟨ul,ur⟩ := center_ray hl hr hts hs hs' oldL oldR newL newR
  have cl := cone_active (x:=x+u-l) (y:=y+v-l*t) (by linarith [coneL.1]) (by linarith [coneL.2])
  have cd := cone_active (x:=x+u+r+m) (y:=y+v+r*s+m*w) (by linarith [coneD.1]) (by linarith [coneD.2])
  have leftEq := cl.symm.trans (h₁.trans (h₂.symm.trans active₂))
  have rightEq := cd.symm.trans (h₄.trans (h₂.symm.trans active₂))
  unfold ellipse at oldL oldR leftEq newR rightEq outside
  have normal : 40*u+60*s*v=0 := (mul_eq_zero.mp (show r*(40*u+60*s*v)=0 by nlinarith only [oldR,newR])).resolve_left hr.ne'
  have normal' : 40*u+60*t*v=0 := (mul_eq_zero.mp (show l*(40*u+60*t*v)=0 by nlinarith only [oldL,leftEq])).resolve_left hl.ne'
  have v0 : v=0 := (mul_eq_zero.mp (show (t-s)*v=0 by nlinarith only [normal,normal'])).resolve_left (sub_ne_zero.mpr hts.ne')
  subst v
  have u0 : u=0 := by linarith only [normal]
  subst u
  exact outside (by simpa using rightEq)

end CrescentCircles
