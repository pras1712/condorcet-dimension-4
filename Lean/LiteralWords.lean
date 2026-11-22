import WeightedRows

namespace Physical
abbrev V := Fin 64
abbrev N := Fin 65
def first (p : N) : Finset V := Finset.univ.filter fun v => v.val<p.val
def apart (p q t : N) : Finset V := Finset.univ.filter fun v =>
  v.val<t.val ∨ (p.val≤v.val ∧ v.val<p.val+q.val-t.val)

theorem first_card (p : N) : (first p).card = p.val := by
  let e : {v : V // v.val < p.val} ≃ Fin p.val :=
    { toFun := fun v => ⟨v.1.val, v.2⟩
      invFun := fun x => ⟨⟨x.val, by have := p.isLt; have := x.isLt; omega⟩, x.isLt⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  simpa only [Fintype.card_subtype, Fintype.card_fin, first] using Fintype.card_congr e

theorem apart_card (p q t : N) (hlo : p.val+q.val-64 ≤ t.val)
    (hhi : t.val ≤ min p.val q.val) : (apart p q t).card = q.val := by
  let z : N := ⟨p.val+q.val-t.val, by omega⟩
  have h₁ : first p ⊆ first z := by
    intro v hv
    simp [first,z] at *
    omega
  have h₂ : Disjoint (first t) (first z \ first p) := by
    apply Finset.disjoint_left.mpr
    intro v ht h
    simp [first,z] at *
    omega
  have h₃ : apart p q t = first t ∪ (first z \ first p) := by
    ext v
    simp [apart,first,z]
    omega
  rw [h₃, Finset.card_union_of_disjoint h₂, Finset.card_sdiff_of_subset h₁,
    first_card, first_card, first_card]
  change t.val + (p.val+q.val-t.val-p.val) = q.val
  omega

theorem common_card (p q t : N) (ht : t.val≤ min p.val q.val) :
    (first p ∩ apart p q t).card=t.val := by
  rw [←first_card t]
  congr 1
  ext v
  simp [first,apart]
  omega

def capped (p : ℕ) : N := ⟨min 64 p,by omega⟩
end Physical

namespace ElectionLift
open Finset
def membershipCode {α : Type} [DecidableEq α] (a b : Finset α) (x : α) : Bool × Bool :=
  (decide (x∈a), decide (x∈b))

theorem codeCells {α : Type} [Fintype α] [DecidableEq α] (a b : Finset α) :
    univ.filter (fun x => membershipCode a b x = (false,false)) = univ \ (a∪b) ∧
    univ.filter (fun x => membershipCode a b x = (false,true)) = b \ a ∧
    univ.filter (fun x => membershipCode a b x = (true,false)) = a \ b ∧
    univ.filter (fun x => membershipCode a b x = (true,true)) = a ∩ b := by
  refine ⟨?_,?_,?_,?_⟩ <;> ext i <;> simp [membershipCode,and_comm]

theorem common_permutation_of_overlap {α : Type} [Fintype α] [DecidableEq α]
    (a b c d : Finset α) (hac : a.card=c.card) (hbd : b.card=d.card)
    (hcd : (a∩b).card=(c∩d).card) :
    ∃ π : Equiv.Perm α, ∀ x, (x∈a ↔ π x∈c) ∧ (x∈b ↔ π x∈d) := by
  classical
  have ha := codeCells a b
  have hc := codeCells c d
  have counts : ∀ k,
      Fintype.card {x // membershipCode a b x=k} =
      Fintype.card {x // membershipCode c d x=k} := by
    rintro ⟨i,j⟩
    rw [Fintype.card_subtype,Fintype.card_subtype]
    cases i <;> cases j
    · rw [ha.1,hc.1,card_sdiff_of_subset (subset_univ _),card_sdiff_of_subset (subset_univ _),
        card_union,card_union,hac,hbd,hcd]
    · rw [ha.2.1,hc.2.1,card_sdiff,card_sdiff,hbd,hcd]
    · rw [ha.2.2.1,hc.2.2.1,card_sdiff,card_sdiff,inter_comm b a,inter_comm d c,hac,hcd]
    · rw [ha.2.2.2,hc.2.2.2,hcd]
  let e := fun k => Fintype.equivOfCardEq (counts k)
  refine ⟨Equiv.ofFiberEquiv e,fun x => ?_⟩
  have H := Equiv.ofFiberEquiv_map e x
  have hf := congrArg Prod.fst H.symm
  have hs := congrArg Prod.snd H.symm
  exact ⟨decide_eq_decide.mp hf,decide_eq_decide.mp hs⟩

end ElectionLift

namespace Physical
open Finset
open scoped BigOperators
abbrev K := Fin 21
abbrev S := Bool × V

structure Face where
  g : Nat := 0
  h : Nat := 0
  n : Nat := 0
  left : PairBound.Word := #[]
  right : PairBound.Word := #[]
deriving Inhabited

structure Board where
  free : Bool
  leftWeight : Nat
  rightWeight : Nat
  menus : Array (Array Face)
deriving Inhabited

def solo (r : PairBound.Row) : Board :=
  let free := r.mode=="free"
  let transform (o : PairBound.OptionWord) : Face :=
    match o with
    | .band g h n =>
      if free then { g:=g,h:=h,n:=n } else { left:=PairBound.asWord o }
    | .fixed w => { left:=w }
  ⟨free,80*r.weight,0,r.menus.map (Array.map transform)⟩

def dual (r : PairBound.Joined) : Board :=
  ⟨false,r.u*r.weight,(80-r.u)*r.weight,
    r.menus.map (Array.map fun (a,b) => { left:=a,right:=b } )⟩

def boards : Array Board :=
  ((PairBound.saved.joined.map dual) ++
    ((PairBound.saved.rows.reverse.filter (fun r => r.weight>0)).map solo)).toArray
abbrev R := Fin boards.size
def bd (r : R) : Board := boards[r.val]!
def wt (b : Board) (s : S) := if s.1 then b.rightWeight else b.leftWeight
def menu (b : Board) (t : K) : Array Face := b.menus[t.val]?.getD #[]
abbrev Ix (b : Board) (t : K) := Fin (max 1 (menu b t).size)
instance (b : Board) (t : K) : NeZero (max 1 (menu b t).size) := ⟨by omega⟩
def face (b : Board) (t : K) (i : Ix b t) : Face :=
  let m := menu b t
  m[i.val]?.getD (m[0]?.getD default)

def count (b : Board) (f : Face) : N := capped (if b.free then f.n else 0)
abbrev Mark (p : N) := {s : Finset V // s.card=p.val}
instance (p : N) : Nonempty (Mark p) := ⟨⟨first p,first_card p⟩⟩
abbrev Move (b : Board) (t : K) := Σ i : Ix b t, Mark (count b (face b t i))
instance (b : Board) (t : K) : Nonempty (Move b t) :=
  ⟨⟨0,Classical.choice inferInstance⟩⟩

def grade (b : Board) (f : Face) (m : Finset V) (s : S) : Nat :=
  (if b.free then if s.2∈m then f.h else f.g
   else ((if s.1 then f.right else f.left)[s.2.val]?.getD 0)) % 128

/-- A grade-constant band still permits every mark set named in the PDF.
For enumerating *rival grades*, all these choices have the same empty-mask
representative. This eliminates redundant overlaps without changing `Move`. -/
def activeCount (b : Board) (f : Face) : N :=
  if f.g = f.h then 0 else count b f

def activeMark (b : Board) (f : Face) (w : Mark (count b f)) : Mark (activeCount b f) :=
  if H : f.g = f.h then
    ⟨∅, by simp [activeCount,H]⟩
  else
    ⟨w.val, by simpa [activeCount,H] using w.property⟩

theorem active_grade (b : Board) (f : Face) (w : Mark (count b f)) (s : S) :
    grade b f w.val s = grade b f (activeMark b f w).val s := by
  by_cases he : f.g = f.h
  · simp [grade,he]
  · simp [activeMark,he]

noncomputable def model : ElectionLift.WeightedMenus K R S where
  Choice t r := Move (bd r) t
  height := 128
  grade t r a s := grade (bd r) (face _ t a.1) a.2.val s
  bounded _ _ _ _ := Nat.mod_lt _ (by decide)

def weight (r : R) (s : S) : Nat := wt (bd r) s

theorem total_weight : Fintype.card (ElectionLift.WeightedSlot weight) = PairBound.width := by
  rw [ElectionLift.card_weighted_slots]
  native_decide

-- All quantities below operate on physical position words.
def canonicalA (p : N) : V → Bool := fun x => decide (x.val<p.val)
def canonicalB (p q t : N) : V → Bool :=
  fun x => decide (x.val<t.val ∨ (p.val≤x.val ∧ x.val<p.val+q.val-t.val))
def rawGrade (b : Board) (f : Face) (m : V → Bool) (s : S) : Nat :=
  (if b.free then if m s.2 then f.h else f.g
   else ((if s.1 then f.right else f.left)[s.2.val]?.getD 0)) % 128

theorem grade_raw (b : Board) (f : Face) (m : Finset V) (s : S) :
    grade b f m s = rawGrade b f (fun x => decide (x∈m)) s := by simp [grade,rawGrade]

def vs : List V := List.finRange 64
def witness (b : Board) (h a a' : Face) (left right : V → Bool) : Mark (count b h) :=
  let p := count b h
  let gain (v : V) : Int :=
    let x := rawGrade b a left (false,v)
    let y := rawGrade b a' right (false,v)
    (PairBound.credit (h.h%128) x y : Int) - (PairBound.credit (h.g%128) x y : Int)
  let marked : Finset V := if h.g = h.h then first p else if p.val==0 then ∅ else
    (((vs.mergeSort (fun x y => gain x ≥ gain y)).take p.val).toFinset)
  if hm : marked.card=p.val then ⟨marked,hm⟩ else ⟨first p,first_card p⟩

def boardScore (b : Board) (h a a' : Face) (left right : V → Bool) : Nat :=
  let mk := (witness b h a a' left right).val
  let part (side : Bool) (weight : Nat) := if weight=0 then 0 else weight * ∑ x : V,
    PairBound.credit (grade b h mk (side,x)) (rawGrade b a left (side,x)) (rawGrade b a' right (side,x))
  part false b.leftWeight + part true b.rightWeight

def scoreBest (b : Board) (t : K) (a a' : Face) (left right : V → Bool) : Nat :=
  (univ : Finset (Ix b t)).sup fun j => boardScore b (face b t j) a a' left right

end Physical

namespace Physical

def firstHead (i j : K) : K := ⟨min 20 (if i.val>0 then j.val-1 else if 1≤j.val && j.val≤15 then 0 else 20),by omega⟩
def secondHead (i j : K) : K :=
  if i==j && [5,10,16].contains i.val then i else firstHead i j

def checkOne (b : Board) (a a' : Face) (h g : K) (t : N) (points : List Rectangle.Point) : Bool :=
  let p := activeCount b a
  let q := activeCount b a'
  let l := canonicalA p
  let r := canonicalB p q t
  let sx := scoreBest b h a a' l r
  let sy := if h=g then sx else scoreBest b g a a' l r
  points.any fun v => v.1≤ sx && v.2≤ sy

def admissible (b : Board) (a a' : Face) (t : N) : Bool :=
  let p := (activeCount b a).val
  let q := (activeCount b a').val
  p+q-64≤t.val && t.val≤ min p q

def rowCheck (r : R) (i j : K) (s : Rectangle.Row) : Prop :=
  ∀ (x : Ix (bd r) i) (y : Ix (bd r) j) (t : N),
    admissible (bd r) (face _ i x) (face _ j y) t = true →
    checkOne (bd r) (face _ i x) (face _ j y) (firstHead i j) (secondHead i j) t s.2 = true

instance (r : R) (i j : K) (s : Rectangle.Row) : Decidable (rowCheck r i j s) := by
  unfold rowCheck
  infer_instance

def roworder := List.finRange boards.size
theorem roworder_perm : roworder.Perm (Finset.univ : Finset R).toList := by
  apply (List.perm_ext_iff_of_nodup (List.nodup_finRange _) (Finset.nodup_toList _)).mpr
  simp

def matchCheck (i j : K) := List.Forall₂ (fun r s => rowCheck r i j s)
  roworder (PairBound.rawRows PairBound.saved i j)
instance (i j : K) : Decidable (matchCheck i j) := by unfold matchCheck; infer_instance

theorem every_literal_state : ∀ i j : K, i≤j → matchCheck i j := by native_decide
end Physical

noncomputable section
namespace Physical
open Finset
open scoped BigOperators

theorem credit_kind (h a b : ℕ) :
    ElectionLift.tagCredit PairBound.den PairBound.num (ElectionLift.kind h a b) =
      PairBound.credit h a b := by
  unfold ElectionLift.kind PairBound.credit
  by_cases hl : h>min a b
  · rw [if_pos hl,if_pos hl]
    simp [ElectionLift.tagCredit]
  · rw [if_neg hl,if_neg hl]
    have e : ((h==a && h==b)=true) ↔ (h=a ∧ h=b) := by simp
    by_cases hh : h=a ∧ h=b
    · rw [if_pos hh,if_pos (e.mpr hh)]
      simp [ElectionLift.tagCredit]
    · rw [if_neg hh,if_neg (mt e.mp hh)]
      simp [ElectionLift.tagCredit]

def pull {p : N} (π : Equiv.Perm V) (w : Mark p) : Mark p :=
  ⟨w.val.map π.symm.toEmbedding, by simpa using w.property⟩

theorem pull_grade (b : Board) (f : Face) (π : Equiv.Perm V)
    (ok : b.free=true ∨ π=Equiv.refl V) {p} (w : Mark p) (side : Bool) (v : V) :
    grade b f (pull π w).val (side,v) = grade b f w.val (side,π v) := by
  rcases ok with free|rfl
  · simp [grade,pull,free,Finset.mem_map_equiv]
  · have eq : (pull (Equiv.refl V) w).val = w.val := by
      ext x
      simp [pull]
    rw [eq]
    rfl

theorem board_sum (b : Board) (h a a' : Face) (l r : V → Bool) :
    boardScore b h a a' l r = ∑ s : S, wt b s *
      PairBound.credit (grade b h (witness b h a a' l r).val s) (rawGrade b a l s) (rawGrade b a' r s) := by
  rw [Fintype.sum_prod_type,Fintype.sum_bool]
  by_cases h1 : b.leftWeight=0 <;> by_cases h2 : b.rightWeight=0 <;>
    simp [boardScore,wt,h1,h2,←Finset.mul_sum,add_comm]

def represents (b : Board) (π : Equiv.Perm V) (a : Face) (s : Finset V) (l : V → Bool) : Prop :=
  ∀ side v, grade b a s (side,v) = rawGrade b a l (side,π v)

theorem transport (b : Board) (h a a' : Face) (l r : V → Bool) (ma mb : Finset V)
    (π : Equiv.Perm V) (ok : b.free=true ∨ π=Equiv.refl V)
    (rA : represents b π a ma l) (rB : represents b π a' mb r) :
    ∃ w : Mark (count b h), boardScore b h a a' l r =
      ∑ s : S, wt b s * PairBound.credit (grade b h w.val s) (grade b a ma s) (grade b a' mb s) := by
  let w := witness b h a a' l r
  let e : S ≃ S := Equiv.prodCongr (Equiv.refl Bool) π
  let F (s : S) := wt b s * PairBound.credit (grade b h w.val s) (rawGrade b a l s) (rawGrade b a' r s)
  refine ⟨pull π w,?_⟩
  rw [board_sum]
  change (∑ s : S, F s) = _
  rw [←Equiv.sum_comp e F]
  apply Finset.sum_congr rfl
  rintro ⟨side,x⟩ _
  change _ * PairBound.credit (grade b h w.val (side,π x)) _ _ =
    _ * PairBound.credit _ _ _
  rw [pull_grade b h π ok w side x,rA side x,rB side x]
  rfl

def physicalBest (b : Board) (i j h : K) (a : Move b i) (a' : Move b j) : ℕ :=
  univ.sup fun c : Move b h => ∑ s : S, wt b s *
    PairBound.credit (grade b (face b h c.1) c.2.val s)
      (grade b (face b i a.1) a.2.val s) (grade b (face b j a'.1) a'.2.val s)

theorem comparison {α β : Type} (A : Finset α) (B : Finset β) (f : α → ℕ) (g : β → ℕ)
    (resp : ∀ a ∈ A, ∃ b∈B, f a ≤ g b) : A.sup f ≤ B.sup g := by
  apply Finset.sup_le
  intro a ha
  obtain ⟨b,hb,hle⟩ := resp a ha
  exact hle.trans (Finset.le_sup (f:=g) hb)

set_option maxHeartbeats 1000000 in
theorem dominates (b : Board) (i j h : K) (a : Move b i) (a' : Move b j) (l r : V → Bool)
    (π : Equiv.Perm V) (ok : b.free=true ∨ π=Equiv.refl V)
    (rA : represents b π (face b i a.1) a.2.val l) (rB : represents b π (face b j a'.1) a'.2.val r) :
    scoreBest b h (face b i a.1) (face b j a'.1) l r ≤ physicalBest b i j h a a' := by
  let f := fun ix : Ix b h => boardScore b (face b h ix) (face b i a.1) (face b j a'.1) l r
  let g := fun c : Move b h => ∑ s : S, wt b s *
    PairBound.credit (grade b (face b h c.1) c.2.val s)
      (grade b (face b i a.1) a.2.val s) (grade b (face b j a'.1) a'.2.val s)
  change univ.sup f ≤ univ.sup g
  apply comparison (univ : Finset (Ix b h)) (univ : Finset (Move b h)) f g
  intro ix _
  obtain ⟨w,hw⟩ := transport b (face b h ix) (face b i a.1) (face b j a'.1) l r
    a.2.val a'.2.val π ok rA rB
  exact ⟨⟨ix,w⟩,mem_univ _,hw.le⟩

theorem concrete_eq (r : R) (i j h : K) (a : Move (bd r) i) (a' : Move (bd r) j) :
    ElectionLift.concreteMax weight model i j h r a a' = physicalBest (bd r) i j h a a' := by
  simp only [ElectionLift.concreteMax,physicalBest,model,weight,credit_kind]
  apply congrArg (fun st : Finset (Move (bd r) h) => st.sup (fun c =>
    ∑ s : S, wt (bd r) s * PairBound.credit (grade (bd r) (face _ h c.1) c.2.val s)
      (grade (bd r) (face _ i a.1) a.2.val s) (grade (bd r) (face _ j a'.1) a'.2.val s)))
  ext x
  exact ⟨fun _ => Finset.mem_univ _,fun _ => Finset.mem_univ _⟩

end Physical
end

noncomputable section
namespace Physical
open Finset
open scoped BigOperators

theorem canonical_rivals (b : Board) (i j : K) (a : Move b i) (c : Move b j) :
    let fa := face b i a.1
    let fc := face b j c.1
    let p := activeCount b fa
    let q := activeCount b fc
    ∃ t : N, admissible b fa fc t=true ∧ ∃ π : Equiv.Perm V,
      (b.free=true ∨ π=Equiv.refl V) ∧
      represents b π fa a.2.val (canonicalA p) ∧ represents b π fc c.2.val (canonicalB p q t) := by
  dsimp only
  let p := activeCount b (face b i a.1)
  let q := activeCount b (face b j c.1)
  let ma := activeMark b (face b i a.1) a.2
  let mb := activeMark b (face b j c.1) c.2
  have ca : ma.val.card=p.val := ma.property
  have cb : mb.val.card=q.val := mb.property
  cases hf : b.free with
  | false =>
    refine ⟨0,?_,Equiv.refl _,Or.inr rfl,?_,?_⟩
    · simp [admissible,activeCount,count,capped,hf]
    · simp [represents,grade,rawGrade,hf]
    · simp [represents,grade,rawGrade,hf]
  | true =>
    let t : N := ⟨(ma.val ∩ mb.val).card,by
      have := Finset.card_le_univ (ma.val ∩ mb.val)
      simpa [V,Nat.lt_succ_iff] using this⟩
    have bounds := (ElectionLift.overlap_cells ma.val mb.val).2.2.2
    have lo : p.val+q.val-64 ≤ t.val := by simpa [V,t,ca,cb] using bounds.1
    have hi : t.val ≤ min p.val q.val := by simpa [t,ca,cb] using bounds.2
    obtain ⟨π,eq⟩ := ElectionLift.common_permutation_of_overlap ma.val mb.val
      (first p) (apart p q t) (ca.trans (first_card p).symm) (cb.trans (apart_card p q t lo hi).symm)
      (show _ by exact (common_card p q t hi).symm)
    refine ⟨t,?_,π,Or.inl rfl,?_,?_⟩
    · simpa [admissible,p,q] using And.intro lo hi
    · intro side x
      have H := (eq x).1
      simp only [first,mem_filter,mem_univ,true_and] at H
      rw [active_grade b _ a.2 (side,x)]
      change grade b _ ma.val _ = _
      simp [grade,rawGrade,hf,canonicalA,H,p]
    · intro side x
      have H := (eq x).2
      simp only [apart,mem_filter,mem_univ,true_and] at H
      rw [active_grade b _ c.2 (side,x)]
      change grade b _ mb.val _ = _
      simp [grade,rawGrade,hf,canonicalB,H,p,q]

theorem passes_local (r : R) (i j : K) (s : Rectangle.Row) (passed : rowCheck r i j s) :
    ∀ (a : model.Choice i r) (c : model.Choice j r), ∃ v∈s.2,
      v.1 ≤ ElectionLift.concreteMax weight model i j (firstHead i j) r a c ∧
      v.2 ≤ ElectionLift.concreteMax weight model i j (secondHead i j) r a c := by
  intro a c
  obtain ⟨t,had,π,ok,rA,rB⟩ := canonical_rivals (bd r) i j a c
  let fa := face (bd r) i a.1
  let fc := face (bd r) j c.1
  let l := canonicalA (activeCount (bd r) fa)
  let z := canonicalB (activeCount (bd r) fa) (activeCount (bd r) fc) t
  let f (h : K) := scoreBest (bd r) h fa fc l z
  have check := passed a.1 c.1 t had
  change s.2.any (fun v => v.1 ≤ f (firstHead i j) &&
    v.2 ≤ (if firstHead i j=secondHead i j then f (firstHead i j) else f (secondHead i j))) = true at check
  have same (h g : K) : (if h=g then f h else f g) = f g := by
    split
    · rename_i he
      exact congrArg f he
    · rfl
  rw [same] at check
  obtain ⟨v,hv,hxy⟩ := List.any_eq_true.mp check
  simp only [Bool.and_eq_true,decide_eq_true_eq] at hxy
  obtain ⟨hx,hy⟩ := hxy
  have bound (h : K) : f h ≤ ElectionLift.concreteMax weight model i j h r a c := by
    exact (dominates (bd r) i j h a c l z π ok rA rB).trans_eq (concrete_eq r i j h a c).symm
  exact ⟨v,hv,hx.trans (bound _),hy.trans (bound _)⟩

/-- Closed lower bound for the supremum of pair opposition over finite strict elections. -/
theorem pair_opposition :
    (PairBound.numerator : ℝ) / PairBound.denominator ≤ ElectionLift.A₂ := by
  apply ElectionLift.lower_bound_of_local_interpretation weight model total_weight roworder roworder_perm
  intro i j hij
  refine ⟨firstHead i j,secondHead i j,?_⟩
  exact (every_literal_state i j hij).imp (fun r s h => passes_local r i j s h)

theorem pair_opposition_exact :
    (351449648252133 : ℝ) / 512000000000000 ≤ ElectionLift.A₂ := pair_opposition

/-- Every smaller opposition fraction holds in one actual finite strict election. -/
theorem finite_witness (q : ℝ) (hq : q < (PairBound.numerator:ℝ)/PairBound.denominator) :
    ∃ e : ElectionLift.Election, (∀ v, Function.Injective (e.rank v)) ∧ ElectionLift.blocks e q := by
  obtain ⟨b,hb,hqb⟩ := exists_lt_of_lt_csSup ElectionLift.realizable_nonempty
    (show q < sSup ElectionLift.realizable from hq.trans_le pair_opposition)
  obtain ⟨e,strict,good⟩ := hb
  refine ⟨e,strict,fun a c => ?_⟩
  obtain ⟨h,hh⟩ := good a c
  exact ⟨h,hqb.le.trans hh⟩

#print axioms pair_opposition_exact
end Physical
end

namespace Physical
open Finset
open scoped BigOperators
noncomputable section

theorem perturbed_response (a b : model.Cand) :
    ∃ h : model.Cand, PairBound.width * PairBound.num <
      ∑ r : R, model.score weight PairBound.den PairBound.num a b h.1 r (h.2 r) := by
  classical
  have data : ∀ i j : K, i ≤ j → ∃ h g, ElectionLift.Matches weight model roworder i j h g := by
    intro i j ij
    exact ⟨firstHead i j,secondHead i j,(every_literal_state i j ij).imp (fun r s hr => passes_local r i j s hr)⟩
  obtain ⟨t,ht⟩ := ElectionLift.maxima_from_local weight model roworder roworder_perm data a b
  choose c _ hc using fun r => Finset.exists_mem_eq_sup (univ : Finset (model.Choice t r))
    univ_nonempty (model.score weight PairBound.den PairBound.num a b t r)
  refine ⟨⟨t,c⟩, lt_of_lt_of_eq ht ?_⟩
  apply Finset.sum_congr rfl
  intro r _
  exact hc r

end
end Physical
