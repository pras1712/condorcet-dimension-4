import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

namespace ElectionLift
noncomputable section
open Finset
open scoped BigOperators

def mean {α : Type} [Fintype α] (f : α → ℝ) : ℝ :=
  (∑ x, f x)/(Fintype.card α : ℝ)

theorem mean_mono {α : Type} [Fintype α] {f g : α → ℝ} (h : ∀ a, f a ≤ g a) :
    mean f ≤ mean g := div_le_div_of_nonneg_right (sum_le_sum (fun a _ => h a)) (by positivity)

@[simp] theorem mean_const {α : Type} [Fintype α] [Nonempty α] (c : ℝ) :
    mean (fun _ : α => c) = c := by simp [mean, Fintype.card_ne_zero, mul_comm]

theorem mean_prod {α β : Type} [Fintype α] [Fintype β] (f : α × β → ℝ) :
    mean f = mean (fun a => mean (fun b => f (a,b))) := by
  simp only [mean,Fintype.sum_prod_type,Fintype.card_prod,Nat.cast_mul,←Finset.sum_div]
  ring

theorem mean_add {α : Type} [Fintype α] (f g : α → ℝ) :
    mean (fun x => f x+g x) = mean f+mean g := by simp [mean, Finset.sum_add_distrib,add_div]

def ind (P : Prop) [Decidable P] : ℝ := if P then 1 else 0

theorem ind_mono {P Q : Prop} [Decidable P] [Decidable Q] (h : P → Q) :
    ind P ≤ ind Q := by by_cases hP:P <;> by_cases hQ:Q <;> simp_all [ind]

structure Election where
  C : Type
  V : Type
  [cf : Fintype C]
  [vf : Fintype V]
  [cn : Nonempty C]
  [vn : Nonempty V]
  height : ℕ
  rank : V → C → ℕ
  bounded : ∀ v c, rank v c < height
attribute [instance] Election.cf Election.vf Election.cn Election.vn

def win (e : Election) (v : e.V) (h a b : e.C) := e.rank v h < e.rank v a ∧ e.rank v h < e.rank v b
instance (e : Election) (v : e.V) (h a b : e.C) : Decidable (win e v h a b) := inferInstanceAs (Decidable (_ ∧ _))
def support (e : Election) (h a b : e.C) := mean fun v => ind (win e v h a b)
def blocks (e : Election) (q : ℝ) := ∀ a b : e.C, ∃ h, q ≤ support e h a b
def one (e : Election) (q : ℝ) := ∀ a : e.C, ∃ h, q ≤ support e h a a

-- A final injective key turns each score ballot into a strict ranking.
abbrev refine (e : Election) : Election where
  C := e.C
  V := e.V
  height := e.height * Fintype.card e.C
  rank := fun v a => e.rank v a * Fintype.card e.C + (Fintype.equivFin e.C a).val
  bounded := by
    intro v a
    have h := Nat.mul_le_mul_right (Fintype.card e.C) (e.bounded v a)
    rw [Nat.succ_mul] at h
    have := (Fintype.equivFin e.C a).isLt
    omega

theorem refine_lt (e : Election) {v a b} (h : e.rank v a < e.rank v b) :
    (refine e).rank v a < (refine e).rank v b := by
  have t := Nat.mul_le_mul_right (Fintype.card e.C) h
  rw [Nat.succ_mul] at t
  have := (Fintype.equivFin e.C a).isLt
  change _ + _ < _ + _
  omega

theorem refine_inj (e : Election) (v : e.V) : Function.Injective ((refine e).rank v) := by
  intro a b eq
  by_cases h : e.rank v a = e.rank v b
  · change e.rank v a * _ + _ = e.rank v b * _ + _ at eq
    rw [h] at eq
    exact (Fintype.equivFin e.C).injective (Fin.ext (Nat.add_left_cancel eq))
  · rcases lt_or_gt_of_ne h with hab | hba
    · exact False.elim ((ne_of_lt (refine_lt e hab)) eq)
    · exact False.elim ((ne_of_gt (refine_lt e hba)) eq)

theorem refine_blocks (e : Election) {q : ℝ} (hq : blocks e q) : blocks (refine e) q := by
  classical
  intro a b
  obtain ⟨h,hh⟩ := hq a b
  refine ⟨h,hh.trans (mean_mono fun v => ind_mono fun ⟨h₁,h₂⟩ => ?_)⟩
  exact ⟨refine_lt e h₁, refine_lt e h₂⟩

-- Rotating the start of a circle puts the predecessor ahead except at one cut.
def cyclic {n : ℕ} (start c : Fin n) : ℕ := if start.val ≤ c.val then c.val else n+c.val
def prev {n : ℕ} (c : Fin n) : Fin n := ⟨if c.val=0 then n-1 else c.val-1, by
  split <;> have := c.isLt <;> omega⟩

theorem cyclic_lt {n : ℕ} {start c : Fin n} (h : start ≠ c) :
    cyclic start (prev c) < cyclic start c := by
  have hx : start.val ≠ c.val := fun z => h (Fin.ext z)
  have hc := c.isLt
  have hs := start.isLt
  simp only [cyclic,prev]
  split_ifs <;> omega

abbrev cloning (e : Election) (n : ℕ) [NeZero n] : Election where
  C := e.C × Fin n
  V := e.V × Fin n
  height := e.height*(2*n)
  rank v c := e.rank v.1 c.1 * (2*n) + cyclic v.2 c.2
  bounded := by
    intro v c
    have ht := Nat.mul_le_mul_right (2*n) (e.bounded v.1 c.1)
    rw [Nat.succ_mul] at ht
    have := c.2.isLt
    simp only [cyclic]
    split <;> omega

theorem clone_lt (e : Election) (n : ℕ) [NeZero n] {v : e.V × Fin n} {c d : e.C × Fin n}
    (h : e.rank v.1 c.1 < e.rank v.1 d.1) :
    (cloning e n).rank v c < (cloning e n).rank v d := by
  have ht := Nat.mul_le_mul_right (2*n) h
  rw [Nat.succ_mul] at ht
  have := c.2.isLt
  change _ + cyclic _ _ < _ + cyclic _ _
  simp only [cyclic]
  split_ifs <;> omega

theorem clone_blocks (e : Election) (n : ℕ) [NeZero n] {q : ℝ} (hq : blocks e q) :
    blocks (cloning e n) q := by
  classical
  intro a b
  obtain ⟨h,hh⟩ := hq a.1 b.1
  refine ⟨(h,0), hh.trans ?_⟩
  unfold support
  rw [mean_prod]
  apply mean_mono
  intro v
  rw [←mean_const (α := Fin n) (ind (win e v h a.1 b.1))]
  exact mean_mono fun i => ind_mono fun ⟨ha,hb⟩ => ⟨clone_lt e n ha, clone_lt e n hb⟩

theorem mean_ne {n : ℕ} [NeZero n] (c : Fin n) :
    mean (fun s : Fin n => ind (s ≠ c)) = 1-1/(n:ℝ) := by
  classical
  have point : ∀ s : Fin n, ind (s ≠ c) = 1 - (if s=c then 1 else 0 : ℝ) := by
    intro s; by_cases h:s=c <;> simp [ind,h]
  simp only [mean,point,Finset.sum_sub_distrib]
  simp [sub_div, Fintype.card_fin,NeZero.ne n]

theorem clone_one (e : Election) (n : ℕ) [NeZero n] :
    one (cloning e n) (1-1/(n:ℝ)) := by
  classical
  intro a
  refine ⟨(a.1,prev a.2), ?_⟩
  unfold support
  rw [mean_prod, ←mean_const (α := e.V) (1-1/(n:ℝ))]
  apply mean_mono
  intro v
  rw [← mean_ne a.2]
  apply mean_mono
  intro i
  apply ind_mono
  intro hi
  have h := Nat.add_lt_add_left (cyclic_lt hi) (e.rank v a.1*(2*n))
  exact ⟨h,h⟩


-- A finite list of grade columns; row multiplicities are modeled by
-- repeated equal columns of values in Fin n.
structure Grades (G : Type) (n : ℕ) where
  height : ℕ
  grade : Fin n → G → ℕ
  bounded : ∀ i g, grade i g < height

abbrev grading (e : Election) {G : Type} [Fintype G] [Nonempty G]
    {n : ℕ} [NeZero n] (tab : Grades G n) : Election where
  C := G × (Fin n → e.C)
  V := Fin n × e.V
  height := tab.height * e.height
  rank v c := tab.grade v.1 c.1 * e.height + e.rank v.2 (c.2 v.1)
  bounded := by
    intro v c
    have ht := Nat.mul_le_mul_right e.height (tab.bounded v.1 c.1)
    rw [Nat.succ_mul] at ht
    have := e.bounded v.2 (c.2 v.1)
    omega

theorem order_grade (e : Election) {a b x y : ℕ} (hb : x < e.height)
    (h : a < b ∨ (a=b ∧ x<y)) : a*e.height+x < b*e.height+y := by
  rcases h with h | ⟨rfl, h⟩
  · have := Nat.mul_le_mul_right e.height h
    rw [Nat.succ_mul] at this
    omega
  · omega

def kind (h a b : ℕ) : ℕ :=
  if h > min a b then 0 else if h=a ∧ h=b then 2 else 1
def ideal (tag : ℕ) (b s : ℝ) : ℝ :=
  (if tag=1 then s else 0) + (if tag=2 then b else 0)

theorem local_grade (e : Election) {b s : ℝ} (hp : blocks e b) (hs : one e s)
    (cap : s ≤ 1) (g x y : ℕ) (a c : e.C) :
    ∃ h : e.C, ideal (kind g x y) b s ≤ mean (fun v =>
      ind (g*e.height + e.rank v h < x*e.height + e.rank v a ∧
           g*e.height + e.rank v h < y*e.height + e.rank v c)) := by
  classical
  by_cases loss : g>min x y
  · refine ⟨a, ?_⟩
    simp only [kind,loss,if_true,ideal]
    simp only [show ¬(0=1:Prop) by decide, show ¬(0=2:Prop) by decide,if_false,zero_add]
    rw [← mean_const (α:=e.V) (0:ℝ)]
    apply mean_mono
    intro v; unfold ind; split <;> norm_num
  have gx : g≤x := by omega
  have gy : g≤y := by omega
  by_cases eqx : g=x <;> by_cases eqy : g=y
  · obtain ⟨h,hh⟩ := hp a c
    refine ⟨h,?_⟩
    have hg : kind g x y = 2 := by unfold kind; rw [if_neg loss, if_pos ⟨eqx,eqy⟩]
    rw [hg]
    simp only [ideal,show ¬(2=1:Prop) by decide,if_false,if_true,zero_add]
    exact hh.trans (mean_mono fun v => ind_mono fun ⟨ha,hc⟩ =>
      ⟨order_grade e (e.bounded v h) (Or.inr ⟨eqx,ha⟩),
       order_grade e (e.bounded v h) (Or.inr ⟨eqy,hc⟩)⟩)
  · obtain ⟨h,hh⟩ := hs a
    refine ⟨h,?_⟩
    have hg : kind g x y = 1 := by simp [kind,loss,eqy]
    simp only [hg,ideal,if_true,OfNat.one_ne_ofNat,if_false,add_zero]
    exact hh.trans (mean_mono fun v => ind_mono fun ⟨ha,_⟩ =>
      ⟨order_grade e (e.bounded v h) (Or.inr ⟨eqx,ha⟩),
       order_grade e (e.bounded v h) (Or.inl (by omega))⟩)
  · obtain ⟨h,hh⟩ := hs c
    refine ⟨h,?_⟩
    have hg : kind g x y = 1 := by simp [kind,loss,eqx]
    simp only [hg,ideal,if_true,OfNat.one_ne_ofNat,if_false,add_zero]
    exact hh.trans (mean_mono fun v => ind_mono fun ⟨hc,_⟩ =>
      ⟨order_grade e (e.bounded v h) (Or.inl (by omega)),
       order_grade e (e.bounded v h) (Or.inr ⟨eqy,hc⟩)⟩)
  · refine ⟨a,?_⟩
    have hg : kind g x y = 1 := by simp [kind,loss,eqx]
    simp only [hg,ideal,if_true,OfNat.one_ne_ofNat,if_false,add_zero]
    apply cap.trans
    rw [←mean_const (α:=e.V) (1:ℝ)]
    apply mean_mono
    intro v
    have h₁ := order_grade (y:=e.rank v a) e (e.bounded v a) (Or.inl (show g<x by omega))
    have h₂ := order_grade (y:=e.rank v c) e (e.bounded v a) (Or.inl (show g<y by omega))
    simp [ind,h₁,h₂]

theorem grade_response (e : Election) {G : Type} [Fintype G] [Nonempty G]
    {n : ℕ} [NeZero n] (tab : Grades G n) {b s : ℝ} (hp : blocks e b)
    (hs : one e s) (cap : s≤1) (h : G) (a c : (grading e tab).C) :
    ∃ k : (grading e tab).C,
      mean (fun i => ideal (kind (tab.grade i h) (tab.grade i a.1)
        (tab.grade i c.1)) b s) ≤ support (grading e tab) k a c := by
  classical
  choose f hf using fun i => local_grade e hp hs cap
    (tab.grade i h) (tab.grade i a.1) (tab.grade i c.1) (a.2 i) (c.2 i)
  refine ⟨(h,f),?_⟩
  unfold support
  rw [mean_prod]
  exact mean_mono hf


def countTag {n : ℕ} (tags : Fin n → ℕ) (k : ℕ) : ℕ :=
  (univ.filter (fun i => tags i = k)).card

theorem mean_ideal {n : ℕ} (f : Fin n → ℕ) (b s : ℝ) :
    mean (fun i => ideal (f i) b s) =
      ((countTag f 1:ℝ)*s + (countTag f 2:ℝ)*b)/n := by
  classical
  have first (i : Fin n) (k : ℕ) (v : ℝ) :
      (if f i=k then v else 0) = (if f i=k then 1 else 0 : ℝ)*v := by
    split_ifs <;> simp
  simp only [mean,ideal,first _ _ s,first _ _ b,Finset.sum_add_distrib,
    ← Finset.sum_mul, Finset.sum_boole, countTag, Fintype.card_fin]

def realizable : Set ℝ := {q | ∃ e : Election, (∀ v, Function.Injective (e.rank v)) ∧ blocks e q}
def A₂ : ℝ := sSup realizable

theorem realizable_nonempty : realizable.Nonempty := by
  let seed : Election := {
    C := Fin 3
    V := Unit
    height := 3
    rank := fun _ c => c.val
    bounded := fun _ c => c.isLt }
  refine ⟨0,seed,fun _ => Fin.val_injective, ?_⟩
  intro a b
  refine ⟨a,?_⟩
  unfold support
  rw [←mean_const (α:=seed.V) (0:ℝ)]
  apply mean_mono
  intro v
  unfold ind
  split <;> norm_num

theorem realizable_bounded : BddAbove realizable := by
  refine ⟨1,?_⟩
  intro q hq
  obtain ⟨e,_,he⟩ := hq
  let a := Classical.choice e.cn
  obtain ⟨h,hh⟩ := he a a
  apply hh.trans
  unfold support
  rw [←mean_const (α:=e.V) (1:ℝ)]
  apply mean_mono
  intro v
  unfold ind
  split <;> norm_num

/-- A weighted pure response is encoded by repeating each row according to
its integer weight. The only remaining certificate hypothesis concerns
grades: for every pair of grade assignments, some assignment has enough
strict credit relative to the weight of its non-three-way ties. -/
theorem from_grade_certificate {G : Type} [Fintype G] [Nonempty G] {n : ℕ} [NeZero n]
    (table : Grades G n) (z : ℝ)
    (cert : ∀ a b : G, ∃ h : G,
      let tags i := kind (table.grade i h) (table.grade i a) (table.grade i b)
      let W := countTag tags 1
      let T := countTag tags 2
      T<n ∧ (W:ℝ) ≥ z*((n:ℝ)-T)) :
    z ≤ A₂ := by
  classical
  by_contra! hf
  let δ := (z-A₂)/n
  have np : (0:ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have pos : 0<δ := div_pos (sub_pos.mpr hf) np
  obtain ⟨q, hreal, hq⟩ := exists_lt_of_lt_csSup realizable_nonempty
    (show A₂-δ/3 < sSup realizable by change A₂-δ/3<A₂; linarith)
  have qle : q ≤ A₂ := le_csSup realizable_bounded hreal
  obtain ⟨e,_,he⟩ := hreal
  obtain ⟨k,hk⟩ := exists_nat_one_div_lt (show 0<δ/3 by linarith)
  let n' := k+1
  let inst : NeZero n' := ⟨by dsimp [n']; omega⟩
  let ζ := 1/(n':ℝ)
  have hz : 0≤ζ := by dsimp [ζ]; positivity
  have hzsmall : ζ<δ/3 := by simpa [ζ,n'] using hk
  let inner := cloning e n'
  let outer := grading inner table
  have impossible : blocks outer (q+δ-ζ) := by
    intro a b
    obtain ⟨g,gt⟩ := cert a.1 b.1
    let tags := fun i => kind (table.grade i g) (table.grade i a.1) (table.grade i b.1)
    let W := countTag tags 1
    let T := countTag tags 2
    change T<n ∧ (W:ℝ) ≥ z*((n:ℝ)-T) at gt
    obtain ⟨head,hh⟩ := grade_response inner table
      (clone_blocks e n' he) (clone_one e n') (show 1-1/(n':ℝ)≤1 by change 1-ζ≤1; linarith) g a b
    refine ⟨head,le_trans ?_ hh⟩
    rw [mean_ideal]
    change q+δ-ζ ≤ ((W:ℝ)*(1-ζ)+(T:ℝ)*q)/n
    apply (le_div_iff₀ np).mpr
    have wt : W≤n := by simpa [W,countTag] using
      (Finset.card_le_univ (univ.filter fun i : Fin n => tags i=1))
    have wle : (W:ℝ) ≤ n := by exact_mod_cast wt
    have tn : (1:ℝ) ≤ (n:ℝ)-T := by
      have hh : (T:ℝ)+1≤(n:ℝ) := by exact_mod_cast (show T+1≤n from gt.1)
      linarith
    have deltaeq : δ*(n:ℝ)=z-A₂ := div_mul_cancel₀ _ np.ne'
    have gain := mul_le_mul_of_nonneg_left tn (show 0≤z-q by linarith)
    have loss := mul_le_mul_of_nonneg_right wle hz
    nlinarith [gt.2]
  have large : q+δ-ζ∈realizable := ⟨refine outer, refine_inj outer, refine_blocks outer impossible⟩
  have := le_csSup realizable_bounded large
  change q+δ-ζ≤A₂ at this
  linarith

/-- Perturbing the tie price by one integer unit tests positivity of the
number of nonties as well as the full-credit ratio. -/
theorem score_test {P Q M W T : ℕ} (hP : 0<P) (hc : W+T≤M) :
    ((M+1)*P-1)*M < ((M+1)*Q)*W + ((M+1)*P-1)*T ↔
      T<M ∧ P*(M-T) ≤ Q*W := by
  have ht : T ≤ M := by omega
  have hd : 1 ≤ (M+1)*P := Nat.mul_pos (by omega) hP
  zify [hd,ht]
  constructor
  · intro h
    constructor
    · by_contra! bad
      have hwt : W=0 := by omega
      have htt : T=M := by omega
      simp [hwt,htt] at h
    · by_contra! bad
      have sep : (Q:ℤ)*W+1 ≤ (P:ℤ)*(M-T) := by omega
      have H := mul_le_mul_of_nonneg_left sep (show (0:ℤ)≤M+1 by positivity)
      nlinarith
  · rintro ⟨strict,weak⟩
    have H := mul_le_mul_of_nonneg_left weak (show (0:ℤ) ≤ M+1 by positivity)
    nlinarith


theorem tag_count_bound {n : ℕ} (tags : Fin n → ℕ) :
    countTag tags 1 + countTag tags 2 ≤ n := by
  classical
  let u := univ.filter fun i => tags i=1
  let v := univ.filter fun i => tags i=2
  have hd : Disjoint u v := by
    rw [Finset.disjoint_left]
    intro i h₁ h₂
    have h1 : tags i=1 := (Finset.mem_filter.mp h₁).2
    have h2 : tags i=2 := (Finset.mem_filter.mp h₂).2
    omega
  have hl := Finset.card_le_univ (u∪v)
  rw [Finset.card_union_of_disjoint hd,Fintype.card_fin] at hl
  exact hl

/-- This theorem reduces a lower bound in actual strict elections directly
to a finite statement about the grades of three outer candidates. -/
theorem finite_election_lower_bound {G : Type} [Fintype G] [Nonempty G]
    {M : ℕ} [NeZero M] (table : Grades G M) {P Q : ℕ}
    (hP : 0<P) (hQ : 0<Q)
    (hcert : ∀ a b : G, ∃ h : G,
      let tags i := kind (table.grade i h) (table.grade i a) (table.grade i b)
      let W := countTag tags 1
      let T := countTag tags 2
      ((M+1)*P-1)*M < ((M+1)*Q)*W + ((M+1)*P-1)*T) :
    (P:ℝ)/Q ≤ A₂ := by
  apply from_grade_certificate table
  intro a b
  obtain ⟨h,hh⟩ := hcert a b
  refine ⟨h,?_⟩
  let tags i := kind (table.grade i h) (table.grade i a) (table.grade i b)
  let W := countTag tags 1
  let T := countTag tags 2
  change ((M+1)*P-1)*M < ((M+1)*Q)*W + ((M+1)*P-1)*T at hh
  obtain ⟨hT,hwt⟩ := (score_test hP (tag_count_bound tags)).mp hh
  change T<M ∧ (P:ℝ)/Q*((M:ℝ)-T) ≤ W
  refine ⟨hT,?_⟩
  have qpos : (0:ℝ)<Q := by exact_mod_cast hQ
  rw [div_mul_eq_mul_div,div_le_iff₀ qpos,←Nat.cast_sub (Nat.le_of_lt hT),mul_comm (W:ℝ)]
  exact_mod_cast hwt

#print axioms finite_election_lower_bound

end
end ElectionLift
