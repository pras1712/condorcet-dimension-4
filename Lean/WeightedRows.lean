import RowMenus
import Checker

noncomputable section
open Finset
open scoped BigOperators
namespace ElectionLift

/-- A positive integer mass represents that many equally weighted voters.
The sum over all copies of a position equals its mass times the position's value. -/
abbrev WeightedSlot {R S : Type} (w : R → S → ℕ) := Σ r, Σ s, Fin (w r s)

variable {R S : Type} [Fintype R] [DecidableEq R] [Fintype S]
variable (w : R → S → ℕ)

omit [DecidableEq R] in
theorem card_weighted_slots : Fintype.card (WeightedSlot w) = ∑ r, ∑ s, w r s := by
  simp [WeightedSlot,Fintype.card_sigma]

theorem weighted_row_sum (r : R) (f : S → ℕ) :
    (∑ j ∈ univ.filter (fun j : WeightedSlot w => j.1=r), f j.2.1) =
      ∑ s, w r s * f s := by
  simp [Finset.sum_filter,Fintype.sum_sigma,WeightedSlot]

def tabSlot {M : ℕ} (hm : Fintype.card (WeightedSlot w)=M) : Fin M ≃ WeightedSlot w :=
  (Fintype.equivFinOfCardEq hm).symm

theorem weighted_fin_sum {M : ℕ} (hm : Fintype.card (WeightedSlot w)=M) (r : R) (f : S → ℕ) :
    (∑ j ∈ univ.filter (fun j => (tabSlot w hm j).1=r), f (tabSlot w hm j).2.1)
      = ∑ s, w r s * f s := by
  rw [←weighted_row_sum]
  simp only [Finset.sum_filter]
  exact Equiv.sum_comp (tabSlot w hm) (fun j : WeightedSlot w => if j.1=r then f j.2.1 else 0)

structure WeightedMenus (K R S : Type) where
  Choice : K → R → Type
  [finiteChoice : ∀ k r, Fintype (Choice k r)]
  [nonemptyChoice : ∀ k r, Nonempty (Choice k r)]
  height : ℕ
  grade : ∀ k r, Choice k r → S → ℕ
  bounded : ∀ k r x s, grade k r x s < height

attribute [instance] WeightedMenus.finiteChoice WeightedMenus.nonemptyChoice
variable {K : Type} [Fintype K] [Nonempty K]
variable (m : WeightedMenus K R S) {M : ℕ} [NeZero M]
variable (hm : Fintype.card (WeightedSlot w)=M)

abbrev WeightedMenus.Cand := Σ k, ∀ r, m.Choice k r

def WeightedMenus.expand : Menus K R M where
  Choice := m.Choice
  row j := (tabSlot w hm j).1
  height := m.height
  grade k r x j := m.grade k r x (tabSlot w hm j).2.1
  bounded k r x _j := m.bounded k r x _

def WeightedMenus.score (W T : ℕ) (a b : m.Cand) (h : K) (r : R) (x : m.Choice h r) : ℕ :=
  ∑ s, w r s * tagCredit W T
    (kind (m.grade h r x s) (m.grade a.1 r (a.2 r) s) (m.grade b.1 r (b.2 r) s))

omit [Fintype K] [Nonempty K] [NeZero M] in
theorem WeightedMenus.expansion_score (W T : ℕ) (a b : m.Cand) (h : K) (r : R) (x : m.Choice h r) :
    (m.expand w hm).rowScore W T a b h r x = m.score w W T a b h r x := by
  classical
  unfold Menus.rowScore WeightedMenus.score
  rw [←weighted_fin_sum w hm r]
  apply Finset.sum_congr rfl
  intro j hj
  have eq := (Finset.mem_filter.mp hj).2
  change (tabSlot w hm j).1 = r at eq
  subst r
  rfl

include hm in
theorem from_weighted_menus {P Q : ℕ} (hP : 0<P) (hQ : 0<Q)
    (cert : ∀ a b : m.Cand, ∃ h : K, ((M+1)*P-1)*M <
      ∑ r, univ.sup (m.score w ((M+1)*Q) ((M+1)*P-1) a b h r)) :
    (P:ℝ)/Q ≤ A₂ := by
  apply from_row_maxima (m.expand w hm) hP hQ
  intro a b
  obtain ⟨h,hh⟩ := cert a b
  refine ⟨h,?_⟩
  have same (r : R) : (m.expand w hm).rowScore ((M+1)*Q) ((M+1)*P-1) a b h r =
      m.score w ((M+1)*Q) ((M+1)*P-1) a b h r :=
    funext (m.expansion_score w hm _ _ a b h r)
  apply lt_of_lt_of_eq hh
  apply Finset.sum_congr rfl
  intro r _
  unfold Menus.rowMax
  rw [same]
  apply congrArg (fun s : Finset (m.Choice h r) => s.sup (m.score w ((M+1)*Q) ((M+1)*P-1) a b h r))
  ext x
  simp
  exact Finset.mem_univ _

end ElectionLift
end

namespace ElectionLift
open Finset
open scoped BigOperators
noncomputable section

theorem reach_below {R : Type} (f g : R → ℕ) {rs : List R} {ss : List Rectangle.Row}
    (matchRows : List.Forall₂ (fun r s => ∃ p∈s.2, p.1≤f r ∧ p.2≤g r) rs ss) :
    ∃ p, Rectangle.Reach (ss.map Prod.snd) p ∧
      p.1 ≤ (rs.map f).sum ∧ p.2 ≤ (rs.map g).sum := by
  induction matchRows with
  | nil => exact ⟨_,Rectangle.Reach.nil,Nat.le_refl _,Nat.le_refl _⟩
  | @cons r s rs ss hp _ ih =>
    obtain ⟨p,hp,hx,hy⟩ := hp
    obtain ⟨q,hq,qx,qy⟩ := ih
    exact ⟨_,Rectangle.Reach.cons hp hq,Nat.add_le_add hx qx,Nat.add_le_add hy qy⟩

variable {R S : Type} [Fintype R] [DecidableEq R] [Fintype S]
variable (w : R → S → ℕ) (m : WeightedMenus (Fin 21) R S)

def concreteMax (i j h : Fin 21) (r : R) (a : m.Choice i r) (b : m.Choice j r) : ℕ :=
  univ.sup (fun c : m.Choice h r => ∑ s, w r s * tagCredit PairBound.den PairBound.num
    (kind (m.grade h r c s) (m.grade i r a s) (m.grade j r b s)))

omit [Fintype R] [DecidableEq R] in
theorem max_swap (i j h : Fin 21) (r : R) (a : m.Choice i r) (b : m.Choice j r) :
    concreteMax w m i j h r a b = concreteMax w m j i h r b a := by
  simp only [concreteMax,kind,min_comm (m.grade j _ _ _),and_comm]

/-- The bridge needs a local finite assertion, one pair of rival menu
choices within a single row at a time. -/
def Matches (rows : List R) (i j h g : Fin 21) : Prop :=
  List.Forall₂ (fun r s => ∀ (a : m.Choice i r) (b : m.Choice j r), ∃ p∈s.2,
    p.1≤concreteMax w m i j h r a b ∧ p.2≤concreteMax w m i j g r a b)
    rows (PairBound.rawRows PairBound.saved i j)

omit [DecidableEq R] in
theorem maxima_from_local
    (rows : List R) (unique : rows.Perm (univ : Finset R).toList)
    (localOk : ∀ i j : Fin 21, i≤j → ∃ h g, Matches w m rows i j h g)
    (a b : m.Cand) :
    ∃ h, PairBound.width*PairBound.num < ∑ r, concreteMax w m a.1 b.1 h r (a.2 r) (b.2 r) := by
  classical
  have S (f : R → ℕ) : (rows.map f).sum = ∑ r, f r := by
    rw [(unique.map f).sum_eq,Finset.sum_map_toList]
  have sorted (a b : m.Cand) (hab : a.1≤b.1) :
      ∃ h, PairBound.width*PairBound.num < ∑ r, concreteMax w m a.1 b.1 h r (a.2 r) (b.2 r) := by
    obtain ⟨h,g,hrows⟩ := localOk a.1 b.1 hab
    have H := hrows.imp (fun r s hrow => hrow (a.2 r) (b.2 r))
    obtain ⟨p,reach,x,y⟩ := reach_below _ _ H
    rcases PairBound.every_row_selection hab reach with hx|hy
    · exact ⟨h,(hx.trans_le x).trans_eq (S _)⟩
    · exact ⟨g,(hy.trans_le y).trans_eq (S _)⟩
  rcases le_total a.1 b.1 with hab|hba
  · exact sorted a b hab
  · obtain ⟨h,hh⟩ := sorted b a hba
    exact ⟨h,by simpa only [max_swap w m b.1 a.1] using hh⟩


theorem lower_bound_of_local_interpretation
    (hm : Fintype.card (WeightedSlot w)=PairBound.width)
    (rows : List R) (unique : rows.Perm (univ : Finset R).toList)
    (localOk : ∀ i j : Fin 21, i≤j → ∃ h g, Matches w m rows i j h g) :
      (PairBound.numerator:ℝ)/PairBound.denominator ≤ A₂ := by
  classical
  let _ : NeZero PairBound.width := ⟨by decide⟩
  apply from_weighted_menus w m hm (by decide) (by decide)
  intro a b
  change ∃ h, PairBound.num * PairBound.width <
    ∑ r, concreteMax w m a.1 b.1 h r (a.2 r) (b.2 r)
  rw [Nat.mul_comm PairBound.num PairBound.width]
  exact maxima_from_local w m rows unique localOk a b

end
end ElectionLift
