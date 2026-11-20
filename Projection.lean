import Mathlib.NumberTheory.Niven
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Parallel displacements cannot carry the circular arc in the construction to
an arithmetic progression, even after relabelling its points. -/
namespace CrescentProjection

open Real

/-- The angular spacing used in the construction. -/
noncomputable def spacing (n : ℕ) : ℝ := π / (1000 * (n : ℝ))

theorem irrational_twice_cos (n : ℕ) (hn : 4 ≤ n) :
    Irrational (2 * cos (spacing n)) := by
  have hpos : 0 < 1000 * n := by omega
  have hden : 3 < ((1000 * n : ℕ) : ℚ)⁻¹.den := by
    rw [Rat.inv_natCast_den_of_pos hpos]
    omega
  have hir := irrational_cos_rat_mul_pi hden
  have angle : ((((1000 * n : ℕ) : ℚ)⁻¹ : ℚ) : ℝ) * π = spacing n := by
    push_cast
    simp [spacing, div_eq_inv_mul]
  rw [angle] at hir
  simpa using hir.ratCast_mul (q := (2 : ℚ)) (by norm_num)

noncomputable def arcPoint (s h : ℝ) (j : ℕ) : ℝ × ℝ :=
  (cos (s+j*h), sin (s+j*h))

noncomputable def projection (A B s h : ℝ) (j : ℕ) : ℝ :=
  A * (arcPoint s h j).1 + B * (arcPoint s h j).2

/-- The same recurrence holds for every choice of linear functional. -/
theorem recurrence (A B s h : ℝ) (j : ℕ) :
    projection A B s h (j+2) + projection A B s h j =
      2*cos h*projection A B s h (j+1) := by
  let t := s + (j+1 : ℕ)*h
  have hplus : s + ((j+2 : ℕ) : ℝ)*h = t+h := by dsimp [t]; push_cast; ring
  have hminus : s + (j : ℝ)*h = t-h := by dsimp [t]; push_cast; ring
  change A*cos _ + B*sin _ + (A*cos _ + B*sin _) = 2*cos h*(A*cos t+B*sin t)
  rw [hplus,hminus]
  simp only [cos_add t h,cos_sub t h,sin_add t h,sin_sub t h]
  ring

theorem four_term (A B s h : ℝ) :
    projection A B s h 3 - projection A B s h 0 =
    (1+2*cos h)*(projection A B s h 2 - projection A B s h 1) := by
  linear_combination recurrence A B s h 1 - recurrence A B s h 0

/-- No nonzero functional is constant on the first three arc points. -/
theorem constant_projection {A B s h : ℝ} (hs : sin h ≠ 0) (hc : 2*cos h ≠ 2)
    (h1 : projection A B s h 1 = projection A B s h 0)
    (h2 : projection A B s h 2 = projection A B s h 0) : A = 0 ∧ B = 0 := by
  have hr := recurrence A B s h 0
  change projection A B s h 2 + projection A B s h 0 =
    2*cos h*projection A B s h 1 at hr
  rw [h1,h2] at hr
  have prod : (2*cos h-2)*projection A B s h 0 = 0 := by linarith
  have z := (mul_eq_zero.mp prod).resolve_left (sub_ne_zero.mpr hc)
  have z1 := h1.trans z
  simp [projection,arcPoint] at z z1
  rw [cos_add,sin_add] at z1
  have hz : (B*cos s-A*sin s)*sin h = 0 := by linear_combination z1 - cos h*z
  have hz' := (mul_eq_zero.mp hz).resolve_right hs
  constructor
  · linear_combination cos s*z - sin s*hz' - A*(sin_sq_add_cos_sq s)
  · linear_combination sin s*z + cos s*hz' - B*(sin_sq_add_cos_sq s)

/-- Four consecutive projected points cannot be four distinctly indexed members
of a single nonconstant real arithmetic progression. -/
theorem no_progression {A B s h base step : ℝ} (hc : Irrational (2*cos h))
    (he : step ≠ 0) (r : ℕ → ℤ) (hr : r 2 ≠ r 1)
    (hp : ∀ i < 4, projection A B s h i = base + (r i : ℝ)*step) : False := by
  have eqFour := four_term A B s h
  rw [hp 3 (by decide),hp 0 (by decide),hp 2 (by decide),hp 1 (by decide)] at eqFour
  have hcancel : (((r 3 : ℝ) - r 0) - (1+2*cos h)*((r 2 : ℝ) - r 1))*step = 0 := by
    linear_combination eqFour
  have ratio := (mul_eq_zero.mp hcancel).resolve_right he
  have hd : (r 2 : ℝ) - r 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hr)
  apply hc
  refine ⟨((r 3 : ℚ) - r 0)/((r 2 : ℚ)-r 1)-1, ?_⟩
  push_cast
  field_simp [hd]
  linarith

/-- No parallel displacements to equally spaced points, in coordinates.
The integer-valued injection allows arbitrary relabelling; its range need not
even consist of consecutive integers. -/
theorem no_parallel_displacements (n : ℕ) (hn : 4 ≤ n) (s : ℝ)
    (Q V W : ℝ × ℝ) (hW : W ≠ 0)
    (r : Fin n → ℤ) (hr : Function.Injective r) (t : Fin n → ℝ) :
    ¬ ∀ i : Fin n, arcPoint s (spacing n) i =
      (Q.1 + (r i : ℝ)*V.1 + t i*W.1, Q.2 + (r i : ℝ)*V.2 + t i*W.2) := by
  intro hp
  let A := -W.2
  let B := W.1
  let idx (j : ℕ) : Fin n := ⟨j % n, Nat.mod_lt _ (by omega)⟩
  let rank (j : ℕ) := r (idx j)
  let step := A*V.1+B*V.2
  let base := A*Q.1+B*Q.2
  have hproj (j : ℕ) (hj : j < 4) :
      projection A B s (spacing n) j = base + (rank j : ℝ)*step := by
    have eqi : (idx j : ℕ) = j := Nat.mod_eq_of_lt (by omega)
    unfold projection
    rw [← eqi, hp (idx j)]
    simp only [eqi]
    dsimp [base,step,rank,A,B]
    ring
  have hi := irrational_twice_cos n hn
  by_cases he : step = 0
  · have hc : 2*cos (spacing n) ≠ 2 := by
      intro eq
      exact hi ⟨2, by norm_num [eq]⟩
    have hn' : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hsp : 0 < spacing n := by unfold spacing; positivity
    have hsp' : spacing n < π := by
      unfold spacing
      apply (div_lt_iff₀ (by positivity)).mpr
      nlinarith [Real.pi_pos, (show 4 ≤ (n : ℝ) by exact_mod_cast hn), Real.pi_pos.le]
    have zs := constant_projection (s := s) (A := A) (B := B)
      (ne_of_gt (sin_pos_of_pos_of_lt_pi hsp hsp')) hc
      (by rw [hproj 1 (by decide),hproj 0 (by decide),he]; ring)
      (by rw [hproj 2 (by decide),hproj 0 (by decide),he]; ring)
    apply hW
    exact Prod.ext zs.2 (neg_eq_zero.mp zs.1)
  · apply no_progression hi he rank _ hproj
    intro h
    have v := congrArg Fin.val (hr h)
    change 2 % n = 1 % n at v
    rw [Nat.mod_eq_of_lt (by omega : 2 < n),Nat.mod_eq_of_lt (by omega : 1 < n)] at v
    omega

end CrescentProjection
