import Condorcet.Core

/-! Finite grade tables for the hand pair/triple arguments and the transfers to three/four seats.
The finite predicates use only natural numbers.  Each successful witness controls all
parameters `2/3 ≤ a ≤ 1` through the affine form `B - D * (1-a)` of its row score. -/
namespace ElectionLift.SmallTables
open Finset
open scoped BigOperators

/-- A loss contributes neither a unit of credit nor a tie penalty. Otherwise the
credit is one unit minus one penalty of `1-a` per tied rival after the first. -/
def units (g : ℕ) (xs : List ℕ) : ℕ := if xs.any (· < g) then 0 else 1

def penalty (g : ℕ) (xs : List ℕ) : ℕ :=
  if xs.any (· < g) then 0 else (xs.filter (· == g)).length - 1

private theorem affine_credit {a : ℝ} (ha : 2/3 ≤ a) (_hb : a ≤ 1)
    (g : ℕ) (xs : List ℕ) (hl : xs.length ≤ 4) :
    rowCredit a g xs = (units g xs : ℝ) - (penalty g xs : ℝ) * (1-a) := by
  have hn := (List.length_filter_le (· == g) xs).trans hl
  unfold rowCredit units penalty
  split <;> simp only [Nat.cast_zero, Nat.cast_one, zero_mul, sub_zero]
  generalize (xs.filter (· == g)).length = n at *
  have cases : n=0 ∨ n=1 ∨ n=2 ∨ n=3 ∨ n=4 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl <;> norm_num [tiesCredit] <;> grind

def B {R T : Type} [Fintype R] (w : R → ℕ) (grade : R → T → ℕ)
    (r : List T) (h : T) : ℕ := ∑ j, w j * units (grade j h) (r.map (grade j))

def D {R T : Type} [Fintype R] (w : R → ℕ) (grade : R → T → ℕ)
    (r : List T) (h : T) : ℕ := ∑ j, w j * penalty (grade j h) (r.map (grade j))

noncomputable def score {R T : Type} [Fintype R] (w : R → ℕ) (grade : R → T → ℕ)
    (r : List T) (h : T) (a : ℝ) : ℝ :=
  ∑ j, (w j : ℝ) * rowCredit a (grade j h) (r.map (grade j))

theorem score_eq {R T : Type} [Fintype R] (w : R → ℕ) (grade : R → T → ℕ)
    (r : List T) (h : T) {a : ℝ} (ha : 2/3 ≤ a) (hb : a ≤ 1) (hl : r.length ≤ 4) :
    score w grade r h a = (B w grade r h : ℝ) - (D w grade r h : ℝ) * (1-a) := by
  simp only [score, B, D, Nat.cast_sum, Nat.cast_mul, Finset.sum_mul, ←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [affine_credit ha hb _ _ (by simpa using hl)]
  ring

/-- A linear witness for the target `K-3*(1-a)` can be verified at its two endpoints. -/
def affineTest {R T : Type} [Fintype R] (w : R → ℕ) (grade : R → T → ℕ)
    (K : ℕ) (r : List T) (h : T) : Bool :=
  let b := B w grade r h
  let d := D w grade r h
  K ≤ b && 3*K + d ≤ 3*b + 3

private theorem affine_sound {R T : Type} [Fintype R] (w : R → ℕ) (g : R → T → ℕ)
    (K : ℕ) (r : List T) (h : T) {a : ℝ} (ha : 2/3 ≤ a) (hb : a ≤ 1)
    (hl : r.length ≤ 4) (ok : affineTest w g K r h = true) :
    (K:ℝ) - 3*(1-a) ≤ score w g r h a := by
  simp only [affineTest, Bool.and_eq_true, decide_eq_true_eq] at ok
  obtain ⟨h₁,h₂⟩ := ok
  have v₁ : (K:ℝ) ≤ B w g r h := by exact_mod_cast h₁
  have v₂ : 3*(K:ℝ) + D w g r h ≤ 3*(B w g r h : ℝ)+3 := by exact_mod_cast h₂
  rw [score_eq w g r h ha hb hl]
  nlinarith [mul_nonneg (sub_nonneg.mpr v₁) (show 0 ≤ 3*a-2 by linarith),
    mul_nonneg (sub_nonneg.mpr v₂) (sub_nonneg.mpr hb)]

/-- Three cyclic positions for each block; types and positions 0–2 belong to X. -/
def easyGrade (j x : Fin 6) : ℕ :=
  if j.val / 3 = x.val / 3 then (x.val % 3 + 3 - j.val % 3) % 3 else 0

def quartetGrade (j x : Fin 4) : ℕ :=
  if j.val = 0 then (if x.val = 0 then 1 else 0)
  else if x.val = 0 ∨ x = j then 0 else 1

def quartetWeight (j : Fin 4) : ℕ := if j.val = 0 then 2 else 1

/-- The two four-row families are shifts of the respective seed words. -/
def sharpGrade (second : Bool) (j : Fin 4) (x : Fin 8) : ℕ :=
  let seed : Array ℕ := if second then #[3,1,1,1,2,1,1,0] else #[3,0,0,0,1,0,0,2]
  seed[(x.val / 4)*4 + (x.val + j.val)%4]!

def sharpTest (r : List (Fin 8)) (h : Fin 8) : Bool :=
  let b₁ := B (fun _ => 1) (sharpGrade false) r h
  let d₁ := D (fun _ => 1) (sharpGrade false) r h
  let b₂ := B (fun _ => 1) (sharpGrade true) r h
  let d₂ := D (fun _ => 1) (sharpGrade true) r h
  b₁ = 3 && b₂ + 3 = b₁ + d₁ && d₂ ≤ d₁

private theorem sharp_sound (r : List (Fin 8)) (h : Fin 8) {a : ℝ}
    (ha : 2/3 ≤ a) (hb : a ≤ 1) (hl : r.length ≤ 4) (ok : sharpTest r h = true) :
    3*a ≤ a * score (fun _ => 1) (sharpGrade false) r h a +
      (1-a) * score (fun _ => 1) (sharpGrade true) r h a := by
  simp only [sharpTest, Bool.and_eq_true, decide_eq_true_eq] at ok
  obtain ⟨⟨s,t⟩,u⟩ := ok
  rw [score_eq _ _ _ _ ha hb hl, score_eq _ _ _ _ ha hb hl]
  generalize B _ (sharpGrade false) r h = b₁ at *
  generalize B _ (sharpGrade true) r h = b₂ at *
  generalize D _ (sharpGrade false) r h = d₁ at *
  generalize D _ (sharpGrade true) r h = d₂ at *
  have e : (b₂ : ℝ) + 3 = b₁ + d₁ := by exact_mod_cast t
  have f : (d₂ : ℝ) ≤ d₁ := by exact_mod_cast u
  have u' : (b₂:ℝ) = d₁ := by rw [s] at e; push_cast at e; linarith
  rw [s,u']; push_cast
  nlinarith [mul_nonneg (sub_nonneg.mpr f) (sq_nonneg (1-a))]

set_option maxRecDepth 100000 in
private theorem easy_all : ∀ (i j k : Fin 6), ∃ h,
    affineTest (fun _ => 1) easyGrade 4 [i,j,k] h = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem quartet_all : ∀ (i j k l : Fin 4), ∃ h,
    affineTest quartetWeight quartetGrade 3 [i,j,k,l] h = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem sharp_all : ∀ (i j k : Fin 8), ∃ h,
    sharpTest [i,j,k] h = true := by decide +kernel

private theorem listThree {T : Type} {P : List T → Prop}
    (f : ∀ x y z, P [x,y,z]) (r : List T) (hl : r.length = 3) : P r := by
  obtain ⟨x,y,z,rfl⟩ := List.length_eq_three.mp hl
  exact f x y z

private theorem listFour {T : Type} {P : List T → Prop}
    (f : ∀ x y z w, P [x,y,z,w]) (r : List T) (hl : r.length = 4) : P r := by
  obtain ⟨x,y,z,w,rfl⟩ := List.length_eq_four.mp hl
  exact f x y z w

/-- The six-position example earns `(1+3a)/6` after dividing by its six rows. -/
theorem easy_triple_table {a : ℝ} (ha : 2/3 ≤ a) (hb : a ≤ 1)
    (r : List (Fin 6)) (hl : r.length = 3) :
    ∃ h, 1+3*a ≤ score (fun _ => 1) easyGrade r h a := by
  obtain ⟨h,ok⟩ := listThree (P := fun t => ∃ h, affineTest (fun _ => 1) easyGrade 4 t h = true) easy_all r hl
  refine ⟨h, ?_⟩
  convert affine_sound (fun _ => 1) easyGrade 4 r h ha hb (by omega) ok using 1
  norm_num
  ring

/-- With relative weights 2,1,1,1, the four-position example earns `3a/5`. -/
theorem quartet_table {a : ℝ} (ha : 2/3 ≤ a) (hb : a ≤ 1)
    (r : List (Fin 4)) (hl : r.length = 4) :
    ∃ h, 3*a ≤ score quartetWeight quartetGrade r h a := by
  obtain ⟨h,ok⟩ := listFour (P := fun t => ∃ h, affineTest quartetWeight quartetGrade 3 t h = true) quartet_all r hl
  refine ⟨h, ?_⟩
  convert affine_sound quartetWeight quartetGrade 3 r h ha hb (by omega) ok using 1
  norm_num
  ring

/-- With rational relative weights `a` and `1-a`, the eight positions earn `3a/4`. -/
theorem sharp_triple_table {a : ℝ} (ha : 2/3 ≤ a) (hb : a ≤ 1)
    (r : List (Fin 8)) (hl : r.length = 3) : ∃ h,
    3*a ≤ a * score (fun _ => 1) (sharpGrade false) r h a +
      (1-a) * score (fun _ => 1) (sharpGrade true) r h a := by
  obtain ⟨h,ok⟩ := listThree (P := fun t => ∃ h, sharpTest t h = true) sharp_all r hl
  exact ⟨h, sharp_sound r h ha hb (by omega) ok⟩

end ElectionLift.SmallTables
