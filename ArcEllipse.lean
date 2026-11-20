import Arc
import Circumcenter
import Ellipse
import Homothets

/-! On the short arc a circumellipse exists, meets no fourth point, and lies
in the elliptic region of the actual norm at every chosen point. -/
namespace CrescentArcEllipse

open CrescentArc (px py)
open CrescentCircles (ellipse disk slab gauge)

/-- Circumellipse data in the coordinates and normalization of `exclude_four`. -/
structure TripleData (a b c u v R : ℝ) : Prop where
  positive : 0 < R
  center : |u| < 3/400 ∧ |v-1/3| < 1/200
  first : ellipse (px a-u) (py a-v) = 25*R^2
  second : ellipse (px b-u) (py b-v) = 25*R^2
  third : ellipse (px c-u) (py c-v) = 25*R^2
  outside : ∀ q : ℝ, 0<q → q<1/100 → q≠a → q≠b → q≠c →
    ellipse (px q-u) (py q-v) ≠ 25*R^2
  cone : ∀ q : ℝ, 0<q → q<1/100 →
    -(py q-v) ≤ 4*(px q-u) ∧ 4*(px q-u) ≤ py q-v
  dominates : ∀ q : ℝ, 0<q → q<1/100 →
    disk (px q-u) (py q-v) < ellipse (px q-u) (py q-v) ∧
    slab (px q-u) (py q-v) < ellipse (px q-u) (py q-v)
  actual : ∀ q : ℝ, 0<q → q<1/100 →
    gauge (px q-u) (py q-v) = ellipse (px q-u) (py q-v)

private theorem point_px (q : ℝ) : (CrescentEllipse.point q).re = px q :=
  CrescentEllipse.point_re q

private theorem point_py (q : ℝ) : (CrescentEllipse.point q).im = py q :=
  CrescentEllipse.point_im q

private theorem incident_iff (u v R q : ℝ) : CrescentEllipse.OnEllipse u v R q ↔
    ellipse (px q-u) (py q-v) = 25*R^2 := by
  simp only [CrescentEllipse.OnEllipse, point_px, point_py, CrescentCircles.ellipse]
  constructor <;> intro h <;> linarith

theorem ordered_triple {a b c : ℝ} (ha : 0<a) (hab : a<b) (hbc : b<c) (hc : c<1/100) :
    ∃ u v R : ℝ, TripleData a b c u v R := by
  have hd := CrescentArc.cross_pos ha.le hab hbc hc.le
  have determinant : CrescentCircumcenter.det (px a) (py a) (px b) (py b) (px c) (py c) ≠ 0 := by
    unfold CrescentCircumcenter.det
    intro h
    linarith only [h,hd]
  obtain ⟨u,v,R,hR,ea,eb,ec,_⟩ := CrescentCircumcenter.exists_unique_circumcircle _ _ _ _ _ _ determinant
  have incidence (q : ℝ) (hq : CrescentCircumcenter.squared (px q) (py q) u v = 5*R^2) :
      CrescentEllipse.OnEllipse u v R q := by
    simpa only [CrescentEllipse.OnEllipse, point_px, point_py, CrescentCircumcenter.squared] using hq
  have ia : CrescentEllipse.InArc a := ⟨ha, by linarith⟩
  have ib : CrescentEllipse.InArc b := ⟨by linarith, by linarith⟩
  have ic : CrescentEllipse.InArc c := ⟨by linarith, hc⟩
  obtain ⟨bounds,exclude⟩ := CrescentEllipse.triple_controls ia ib ic hab.ne (hab.trans hbc).ne hbc.ne
    (incidence a ea) (incidence b eb) (incidence c ec)
  have dominate (q : ℝ) (lo : 0<q) (hi : q<1/100) :=
    CrescentEllipse.ellipse_dominates bounds.1 bounds.2 (q := q) ⟨lo,hi⟩
  simp only [point_px, point_py] at dominate
  have cone (q : ℝ) (lo : 0<q) (hi : q<1/100) :
      -(py q-v) ≤ 4*(px q-u) ∧ 4*(px q-u) ≤ py q-v := by
    obtain ⟨ypos,ab,_,_⟩ := dominate q lo hi
    rw [abs_lt] at ab
    constructor <;> linarith
  have Rpos : 0<R := by
    have ypos := (dominate a ia.1 ia.2).1
    unfold CrescentCircumcenter.squared at ea
    by_contra! zero
    have : R=0 := le_antisymm zero hR
    rw [this] at ea
    nlinarith [sq_pos_of_pos ypos, sq_nonneg (px a-u)]
  refine ⟨u,v,R,⟨Rpos,bounds,(incident_iff ..).mp (incidence a ea),
    (incident_iff ..).mp (incidence b eb),(incident_iff ..).mp (incidence c ec),?_,cone,?_,?_⟩⟩
  · intro q lo hi qa qb qc e
    exact exclude q ⟨lo,hi⟩ qa qb qc ((incident_iff ..).mpr e)
  · intro q lo hi
    obtain ⟨_,_,e₁,e₂⟩ := dominate q lo hi
    unfold CrescentCircles.disk CrescentCircles.ellipse CrescentCircles.slab
    constructor <;> linarith
  · intro q lo hi
    exact CrescentCircles.cone_active (cone q lo hi).1 (cone q lo hi).2

end CrescentArcEllipse
