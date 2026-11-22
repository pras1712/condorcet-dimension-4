import Elections

noncomputable section
open Finset
open scoped BigOperators
namespace ElectionLift

/-- Splitting candidates into a type and one independent choice per row
preserves the sum of the individual rows' best responses. -/
structure Menus (K R : Type) (M : ℕ) where
  Choice : K → R → Type
  [finiteChoice : ∀ k r, Fintype (Choice k r)]
  [nonemptyChoice : ∀ k r, Nonempty (Choice k r)]
  row : Fin M → R
  height : ℕ
  grade : ∀ k r, Choice k r → Fin M → ℕ
  bounded : ∀ k r x j, grade k r x j < height

attribute [instance] Menus.finiteChoice Menus.nonemptyChoice
variable {K R : Type} [Fintype K] [Nonempty K] [Fintype R] [DecidableEq R]
variable {M : ℕ} [NeZero M] (m : Menus K R M)

abbrev Menus.Cand := Σ k, ∀ r, m.Choice k r
def Menus.totalGrades : Grades m.Cand M where
  height := m.height
  grade j a := m.grade a.1 (m.row j) (a.2 (m.row j)) j
  bounded j a := m.bounded a.1 _ _ j

def tagCredit (W T k : ℕ) : ℕ := (if k=1 then W else 0)+(if k=2 then T else 0)

theorem sum_tag_credit {M : ℕ} (s : Fin M → ℕ) (W T : ℕ) :
    (∑ j, tagCredit W T (s j)) = W*countTag s 1 + T*countTag s 2 := by
  classical
  simp [tagCredit,Finset.sum_add_distrib,Finset.sum_ite,countTag,Nat.mul_comm]

def Menus.rowScore (W T : ℕ) (a b : m.Cand) (h : K) (r : R) (x : m.Choice h r) : ℕ :=
  ∑ j ∈ univ.filter (fun j => m.row j = r),
    tagCredit W T (kind (m.grade h r x j) (m.totalGrades.grade j a) (m.totalGrades.grade j b))

def Menus.rowMax (W T : ℕ) (a b : m.Cand) (h : K) (r : R) : ℕ :=
  univ.sup (m.rowScore W T a b h r)

omit [Fintype K] [Nonempty K] [NeZero M] in
theorem Menus.assemble (W T : ℕ) (a b : m.Cand) (h : K) :
    ∃ c : m.Cand,
      let tags j := kind (m.totalGrades.grade j c) (m.totalGrades.grade j a) (m.totalGrades.grade j b)
      W*countTag tags 1+T*countTag tags 2 = ∑ r, m.rowMax W T a b h r := by
  classical
  choose x _ hx using fun r => Finset.exists_mem_eq_sup (univ : Finset (m.Choice h r))
    univ_nonempty (m.rowScore W T a b h r)
  let c : m.Cand := ⟨h,x⟩
  let tags j := kind (m.totalGrades.grade j c) (m.totalGrades.grade j a) (m.totalGrades.grade j b)
  refine ⟨c,?_⟩
  change W*countTag tags 1 + T*countTag tags 2 = _
  rw [←sum_tag_credit,←Finset.sum_fiberwise univ m.row (fun i => tagCredit W T (tags i))]
  apply sum_congr rfl
  intro r _
  change _ = univ.sup (m.rowScore W T a b h r)
  rw [hx r]
  apply sum_congr rfl
  intro j hj
  have eq := (mem_filter.mp hj).2
  change tagCredit W T (kind (m.grade h (m.row j) (x (m.row j)) j) _ _) = _
  subst r
  rfl

theorem from_row_maxima {P Q : ℕ} (hP : 0<P) (hQ : 0<Q)
    (cert : ∀ a b : m.Cand, ∃ h : K, ((M+1)*P-1)*M <
      ∑ r, m.rowMax ((M+1)*Q) ((M+1)*P-1) a b h r) :
      (P:ℝ)/Q ≤ A₂ := by
  classical
  let _ : Nonempty m.Cand := ⟨⟨Classical.choice (inferInstance : Nonempty K),fun _ => Classical.choice inferInstance⟩⟩
  apply finite_election_lower_bound m.totalGrades hP hQ
  intro a b
  obtain ⟨h,hh⟩ := cert a b
  obtain ⟨c,hc⟩ := m.assemble ((M+1)*Q) ((M+1)*P-1) a b h
  exact ⟨c,lt_of_lt_of_eq hh hc.symm⟩

-- Any two configurations with equal cell counts differ by a common
-- relabeling of positions.
theorem perm_of_cell_counts {α β : Type} [Fintype α] [DecidableEq β]
    (f g : α → β) (h : ∀ b, Fintype.card {a // f a=b} = Fintype.card {a // g a=b}) :
    ∃ π : Equiv.Perm α, ∀ a, g (π a) = f a := by
  classical
  let e := fun b => Fintype.equivOfCardEq (h b)
  exact ⟨Equiv.ofFiberEquiv e, Equiv.ofFiberEquiv_map e⟩

-- The four cell sizes for two binary markings are determined by their overlap.
theorem overlap_cells {α : Type} [Fintype α] [DecidableEq α] (a b : Finset α) :
    (univ \ (a∪b)).card = Fintype.card α+(a∩b).card-a.card-b.card ∧
    (b \ a).card = b.card-(a∩b).card ∧
    (a \ b).card = a.card-(a∩b).card ∧
    a.card+b.card-Fintype.card α ≤ (a∩b).card ∧
    (a∩b).card ≤ min a.card b.card := by
  have hu := card_union_add_card_inter a b
  have hb := card_le_univ (a∪b)
  have ha := card_le_card (inter_subset_left (s₁:=a) (s₂:=b))
  have hc := card_le_card (inter_subset_right (s₁:=a) (s₂:=b))
  rw [card_sdiff_of_subset (subset_univ _), card_univ, card_sdiff, card_sdiff, inter_comm b a]
  omega

-- The challenger may mark any prescribed number of elements in each cell.
theorem choose_marks {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (cell : α → β) (number : β → ℕ)
    (feasible : ∀ b, number b ≤ Fintype.card {a // cell a=b}) :
    ∃ mark : α → Bool, ∀ b,
      (univ.filter (fun a => cell a=b ∧ mark a=true)).card = number b := by
  classical
  choose t contained hcard using fun b => Finset.exists_subset_card_eq
    (s:=univ.filter (fun a => cell a=b)) (n:=number b) (by
      rw [← Fintype.card_subtype]; exact feasible b)
  let mark (a : α) : Bool := decide (a∈t (cell a))
  refine ⟨mark, fun b => ?_⟩
  rw [← hcard b]
  congr 1
  ext a
  simp only [mem_filter,mem_univ,true_and,mark,decide_eq_true_eq]
  constructor
  · rintro ⟨hab,ha⟩
    exact hab ▸ ha
  · intro ha
    have hb := (mem_filter.mp (contained b ha)).2
    exact ⟨hb,hb ▸ ha⟩

#print axioms from_row_maxima
end ElectionLift
end
