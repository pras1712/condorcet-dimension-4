import Condorcet.SmallTables

/-! The three cyclic words in the elementary pair proof. There are 36 labelled rows,
with their integer multiplicities kept separate from the row scores. -/
namespace ElectionLift.SmallTables
open Finset
open scoped BigOperators

def pairGrade (v : Fin 36) (c : Fin 12) : ℕ :=
  let word : Array ℕ :=
    if v.val < 12 then #[5,0,1,4,0,1,3,0,1,2,0,1]
    else if v.val < 24 then #[2,0,1,0,0,0,2,0,0,0,0,1]
    else #[5,0,1,2,3,4,5,0,1,2,3,4]
  word[(v.val+c.val)%12]!

def pairWeight (v : Fin 36) : ℕ := if v.val < 12 then 64 else if v.val < 24 then 16 else 1

theorem pairWeight_sum : ∑ j, pairWeight j = 972 := by decide +kernel

/-- Translate a pair to (0,r), 0 ≤ r ≤ 6, and translate its challenger back. -/
def pairHead (x y : Fin 12) : Fin 12 :=
  let forward := (y.val+12-x.val)%12
  let base := if forward ≤ 6 then x.val else y.val
  let offset := (#[3,3,11,3,9,8,5] : Array ℕ)[min forward (12-forward)]!
  ⟨(base + offset)%12, Nat.mod_lt _ (by decide)⟩

/- Here B=W+T and D=T, where T is the count of all-three ties. The first
inequality is precisely the paper's W-2(losses) ≥ 4. -/
set_option maxRecDepth 100000 in
private theorem pair_comparison : ∀ x y : Fin 12,
    let b := B pairWeight pairGrade [x,y] (pairHead x y)
    let d := D pairWeight pairGrade [x,y] (pairHead x y)
    2*972 + 4 + d ≤ 3*b ∧ d ≤ 972 := by decide +kernel

private theorem lower_credit {a : ℝ} (g : ℕ) (xs : List ℕ) :
    (units g xs : ℝ) - (penalty g xs : ℝ) * (1-a) ≤ rowCredit a g xs := by
  unfold rowCredit units penalty
  split <;> simp only [Nat.cast_zero, Nat.cast_one, zero_mul, sub_zero, le_refl]
  unfold tiesCredit
  split
  · rename_i h
    have hz : (List.filter (fun x => x == g) xs).length - 1 = 0 := by omega
    simp [hz]
  · exact le_max_right _ _

private theorem lower_score {R G : Type} [Fintype R] (w : R → ℕ) (g : R → G → ℕ)
    (r : List G) (h : G) (a : ℝ) :
    (B w g r h : ℝ) - (D w g r h : ℝ)*(1-a) ≤ score w g r h a := by
  simp only [score, B, D, Nat.cast_sum, Nat.cast_mul, sum_mul, ←sum_sub_distrib]
  apply sum_le_sum
  intro j _
  simpa only [mul_sub, mul_assoc] using
    mul_le_mul_of_nonneg_left (lower_credit (a:=a) (g j h) (r.map (g j))) (Nat.cast_nonneg (w j))

/-- For a ≤ 2/3, this small table improves the ideal pair score by at least 1/729. -/
theorem pair_gain {a : ℝ} (ha : a ≤ 2/3) (r : List (Fin 12)) (hl : r.length = 2) :
    ∃ h, a+1/729 ≤ score pairWeight pairGrade r h a / (∑ j, pairWeight j : ℕ) := by
  obtain ⟨x,y,rfl⟩ := List.length_eq_two.mp hl
  refine ⟨pairHead x y,?_⟩
  obtain ⟨hh,hd⟩ := pair_comparison x y
  have bound := lower_score pairWeight pairGrade [x,y] (pairHead x y) a
  generalize B pairWeight pairGrade [x,y] (pairHead x y) = b at *
  generalize D pairWeight pairGrade [x,y] (pairHead x y) = d at *
  have v₁ : 2*972+4 + (d:ℝ) ≤ 3*(b:ℝ) := by exact_mod_cast hh
  have v₂ : (d:ℝ) ≤ 972 := by exact_mod_cast hd
  rw [pairWeight_sum]
  apply (le_div_iff₀ (by norm_num)).mpr
  push_cast
  nlinarith [mul_nonneg (sub_nonneg.mpr v₂) (sub_nonneg.mpr ha)]

end ElectionLift.SmallTables
