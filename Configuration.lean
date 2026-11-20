import Arc
import Projection

/-! Finite configurations and the parallel-displacement obstruction. -/
namespace CrescentConfiguration

open CrescentArc

abbrev Plane := ℝ × ℝ
abbrev Gauge := ℝ → ℝ → ℝ

def distance (N : Gauge) (p q : Plane) := N (q.1-p.1) (q.2-p.2)

def determinant (p q r : Plane) :=
  (p.1-q.1)*(q.2-r.2) - (p.2-q.2)*(q.1-r.1)

/-- Pairs, triples and quadruples use their increasing index order. -/
structure LineLikeCrescent {n : ℕ} (N : Gauge) (P : Fin n → Plane) : Prop where
  distinct : Function.Injective P
  gaps : ∀ (i j k l : Fin n), i≤j → k≤l →
    (distance N (P i) (P j) = distance N (P k) (P l) ↔ j.val-i.val=l.val-k.val)
  noncollinear : ∀ (i j k : Fin n), i<j → j<k → determinant (P i) (P j) (P k) ≠ 0
  noFour : ∀ (i j k l : Fin n), i<j → j<k → k<l → ∀ (q : Plane) (R : ℝ),
    ¬ (distance N q (P i)=R ∧ distance N q (P j)=R ∧
       distance N q (P k)=R ∧ distance N q (P l)=R)

/-- A common direction can move the points to integer positions on one progression.
Injective ranks allow arbitrary relabelling and arbitrary skipped positions. -/
def ParallelDisplacements {n : ℕ} (P : Fin n → Plane) : Prop :=
  ∃ (Q V W : Plane), W ≠ 0 ∧ ∃ r : Fin n → ℤ, Function.Injective r ∧
    ∃ t : Fin n → ℝ, ∀ i, P i =
      (Q.1 + (r i : ℝ)*V.1 + t i*W.1, Q.2 + (r i : ℝ)*V.2 + t i*W.2)

noncomputable def angle (n : ℕ) (i : Fin n) := offset n (i.val+1)
noncomputable def point (n : ℕ) (i : Fin n) : Plane := (px (angle n i), py (angle n i))

theorem angle_pos {n : ℕ} (i : Fin n) : 0 < angle n i := by
  have h := step_pos n (Nat.zero_lt_of_lt i.isLt)
  unfold angle offset
  positivity

theorem angle_small {n : ℕ} (i : Fin n) : angle n i < 1/100 := by
  have hn : 0 < (n:ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt i.isLt)
  have hi : ((i.val+1:ℕ):ℝ) ≤ n := by exact_mod_cast (by omega : i.val+1≤n)
  unfold angle offset step
  rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right hi Real.pi_pos.le,
    mul_lt_mul_of_pos_right Real.pi_lt_four hn]

theorem angle_increases {n : ℕ} {i j : Fin n} (h : i<j) : angle n i<angle n j := by
  apply mul_lt_mul_of_pos_right _ (step_pos n (by omega))
  exact_mod_cast (by omega : i.val+1<j.val+1)

theorem distinct_points {n : ℕ} : Function.Injective (point n) := by
  have neq : ∀ i j : Fin n, i<j → point n i ≠ point n j := by
    intro i j ij eq
    have dx := (shallow_chord (angle_pos i) (angle_increases ij) (angle_small j).le).1
    have hx := congrArg Prod.fst eq
    change px (angle n i) = px (angle n j) at hx
    linarith
  intro i j h
  rcases lt_trichotomy i j with lt|eq|lt
  · exact (neq i j lt h).elim
  · exact eq
  · exact (neq j i lt h.symm).elim

theorem gap_pattern {n : ℕ} (i j k l : Fin n) (hij : i≤j) (hkl : k≤l) :
    distance gauge (point n i) (point n j) = distance gauge (point n k) (point n l) ↔
      j.val-i.val=l.val-k.val := by
  simpa [distance,point,angle] using
    (gap_iff (n:=n) (i:=i.val+1) (j:=j.val+1) (k:=k.val+1) (l:=l.val+1)
      (by omega) (by omega) (by omega) (by omega) (by omega))

theorem noncollinear {n : ℕ} (i j k : Fin n) (hij : i<j) (hjk : j<k) :
    determinant (point n i) (point n j) (point n k) ≠ 0 :=
  (cross_pos (angle_pos i).le (angle_increases hij) (angle_increases hjk) (angle_small k).le).ne'

theorem point_polar {n : ℕ} (i : Fin n) : point n i =
    CrescentProjection.arcPoint (Real.pi/2+step n) (CrescentProjection.spacing n) i := by
  unfold point angle offset CrescentProjection.arcPoint
  change (_,_) = (Real.cos (Real.pi/2 + step n + (i.val:ℝ)*step n),
    Real.sin (Real.pi/2 + step n + (i.val:ℝ)*step n))
  rw [show Real.pi/2 + step n + (i.val:ℝ)*step n = Real.pi/2 + ((i.val+1:ℕ):ℝ)*step n by
    push_cast; ring]
  simp [px,py,Real.cos_add,Real.sin_add]

theorem cannot_displace {n : ℕ} (hn : 4≤n) : ¬ ParallelDisplacements (point n) := by
  rintro ⟨Q,V,W,hW,r,hr,t,h⟩
  apply CrescentProjection.no_parallel_displacements n hn (Real.pi/2+step n) Q V W hW r hr t
  intro i
  exact (point_polar i).symm.trans (h i)

end CrescentConfiguration
