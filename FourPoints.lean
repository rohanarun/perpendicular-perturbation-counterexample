import ArcEllipse

/-! Four arbitrary ordered offsets on the chosen circular arc never lie on a
common circle of the full squared gauge. -/
namespace CrescentFourPoints

open CrescentArc (px py)
open CrescentCircles (ellipse gauge)

private theorem chord_parameters {a b : ℝ} (ha : 0<a) (hab : a<b) (hb : b<1/100) :
    ∃ l t : ℝ, 0<l ∧ 0≤t ∧ 6*t≤1 ∧ px a-px b=l ∧ py a-py b=l*t := by
  obtain ⟨hx,hy,hxy⟩ := CrescentArc.shallow_chord ha hab hb.le
  let l := px a-px b
  let t := (py a-py b)/l
  have lpos : 0<l := hx
  have eq : py a-py b = l*t := by dsimp only [t]; field_simp
  have tpos : 0<t := div_pos hy lpos
  refine ⟨l,t,lpos,tpos.le,?_,rfl,eq⟩
  change 30*(py a-py b)<l at hxy
  rw [eq] at hxy
  by_contra! h
  nlinarith [mul_pos lpos (sub_pos.mpr h)]

theorem no_common_circle_sq {a b c d : ℝ} (ha : 0<a) (hab : a<b)
    (hbc : b<c) (hcd : c<d) (hd : d<1/100) (u v R : ℝ) :
    ¬ (gauge (px a-u) (py a-v) = R ∧ gauge (px b-u) (py b-v) = R ∧
       gauge (px c-u) (py c-v) = R ∧ gauge (px d-u) (py d-v) = R) := by
  have hb := ha.trans hab
  have hc := hb.trans hbc
  have hb' := (hbc.trans hcd).trans hd
  have hc' := hcd.trans hd
  obtain ⟨U,V,S,data⟩ := CrescentArcEllipse.ordered_triple hb hbc hcd hd
  obtain ⟨l,t,hl,ht,ht',hxl,hyl⟩ := chord_parameters hc hcd hd
  obtain ⟨r,s,hr,hs,hs',hxr,hyr⟩ := chord_parameters hb hbc hc'
  obtain ⟨m,w,hm,hw,hw',hxm,hym⟩ := chord_parameters ha hab hb'
  have cross := CrescentArc.cross_pos hb.le hbc hcd hd.le
  rw [hxr,hyl,hyr,hxl] at cross
  have hts : s<t := by
    by_contra! h
    nlinarith only [cross,mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hr.le hl.le) (sub_nonpos.mpr h)]
  let x := px c-U
  let y := py c-V
  have locLx : x-l=px d-U := by dsimp [x]; linarith
  have locLy : y-l*t=py d-V := by dsimp [y]; linarith
  have locRx : x+r=px b-U := by dsimp [x]; linarith
  have locRy : y+r*s=py b-V := by dsimp [y]; linarith
  have locDx : x+r+m=px a-U := by dsimp [x]; linarith
  have locDy : y+r*s+m*w=py a-V := by dsimp [y]; linarith
  have eout := data.outside a ha (hab.trans hb') hab.ne (hab.trans hbc).ne ((hab.trans hbc).trans hcd).ne
  have nofour := CrescentCircles.exclude_four (x:=x) (y:=y) hl hr hm ht
    (by linarith : t≤1) hs hs' hw (by linarith : w≤1) hts
    (by rw [locLx,locLy]; exact data.third.trans data.second.symm)
    (by rw [locRx,locRy]; exact data.first.trans data.second.symm)
    (by rw [locLy,locLx]; exact data.cone d (hc.trans hcd) hd)
    (by rw [locDy,locDx]; exact data.cone a ha (hab.trans hb'))
    (by rw [locDx,locDy]; exact fun e => eout (e.trans data.second))
  rintro ⟨hA,hB,hC,hD⟩
  apply nofour
  refine ⟨U-u,V-v,R,?_,?_,?_,?_⟩
  · convert hD using 2 <;> dsimp [x,y] <;> linarith
  · convert hC using 2 <;> dsimp [x,y] <;> linarith
  · convert hB using 2 <;> dsimp [x,y] <;> linarith
  · convert hA using 2 <;> dsimp [x,y] <;> linarith

end CrescentFourPoints
