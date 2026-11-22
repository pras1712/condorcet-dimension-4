import Std

namespace Rectangle
abbrev Point := Nat × Nat
abbrev Row := Bool × List Point

def add (a b : Point) : Point := (a.1+b.1,a.2+b.2)

inductive Reach : List (List Point) → Point → Prop
  | nil : Reach [] (0,0)
  | cons {s ss p ps} (hp : p∈s) (ht : Reach ss ps) : Reach (s::ss) (add p ps)

/-- Test whether a sum of one point from each row fits the budget. -/
def fits : List (List Point) → Nat → Nat → Bool
  | [], _, _ => true
  | row::rest, x, y => row.any fun p =>
      p.1≤x && p.2≤y && fits rest (x-p.1) (y-p.2)

theorem fits_of_reach {ss p} (h : Reach ss p) {x y} (hx : p.1≤x) (hy : p.2≤y) :
    fits ss x y = true := by
  induction h generalizing x y with
  | nil => rfl
  | @cons s ss p ps hp ht ih =>
      simp only [fits,List.any_eq_true,Bool.and_eq_true,decide_eq_true_eq]
      change p.1+ps.1≤x at hx
      change p.2+ps.2≤y at hy
      exact ⟨p,hp,⟨by omega,by omega⟩,ih (by omega) (by omega)⟩

def minCoord (f : Point → Nat) (top : Nat) : List Point → Nat
  | [] => top
  | h::t => min (f h) (minCoord f top t)

theorem minCoord_le (f : Point → Nat) (top : Nat) {p s} (h : p ∈ s) :
    minCoord f top s ≤ f p := by
  induction s with
  | nil => simp at h
  | cons a s ih =>
    rcases List.mem_cons.mp h with rfl | ht
    · exact Nat.min_le_left _ _
    · exact Nat.le_trans (Nat.min_le_right _ _) (ih ht)

def floor (top : Nat) (r : Row) : Point :=
  (minCoord Prod.fst top r.2, minCoord Prod.snd top r.2)

def residual (top : Nat) (r : Row) : List Point :=
  if r.1 then
    let b := floor top r
    r.2.map fun p => (p.1-b.1,p.2-b.2)
  else [(0,0)]

def totalFloor (top : Nat) : List Row → Point
  | [] => (0,0)
  | r::rs => add (floor top r) (totalFloor top rs)

theorem residual_reach (top : Nat) (rs : List Row) {v}
    (hh : Reach (rs.map Prod.snd) v) :
    ∃ q, Reach (rs.map (residual top)) q ∧
      (totalFloor top rs).1+q.1 ≤ v.1 ∧ (totalFloor top rs).2+q.2 ≤ v.2 := by
  induction rs generalizing v with
  | nil => cases hh; exact ⟨_,Reach.nil,Nat.le_refl _,Nat.le_refl _⟩
  | cons r rs ih =>
    cases hh with
    | @cons _ _ p ps hp ht =>
      obtain ⟨q,hq,hx,hy⟩ := ih ht
      let b := floor top r
      have h1 : b.1 ≤ p.1 := minCoord_le _ _ hp
      have h2 : b.2 ≤ p.2 := minCoord_le _ _ hp
      let t : Point := if r.1 then (p.1-b.1,p.2-b.2) else (0,0)
      have hm : t ∈ residual top r := by
        cases he : r.1 with
        | false => simp [t,residual,he]
        | true =>
          simp only [t,residual,he,if_true]
          exact List.mem_map.mpr ⟨p,hp,rfl⟩
      refine ⟨_, Reach.cons hm hq, ?_, ?_⟩
      · change (b.1+_)+(t.1+q.1) ≤ p.1+ps.1
        cases he : r.1 <;> simp [t,he] <;> omega
      · change (b.2+_)+(t.2+q.2) ≤ p.2+ps.2
        cases he : r.1 <;> simp [t,he] <;> omega

def excludes (top cap : Nat) (rs : List Row) : Bool :=
  let b := totalFloor top rs
  cap<b.1 || cap<b.2 || !(fits (rs.map (residual top)) (cap-b.1) (cap-b.2))

theorem excludes_sound {top cap rs} (h : excludes top cap rs = true)
    {v} (hv : Reach (rs.map Prod.snd) v) : cap < v.1 ∨ cap < v.2 := by
  apply Classical.byContradiction
  intro hh
  have hx : v.1 ≤ cap := by omega
  have hy : v.2 ≤ cap := by omega
  obtain ⟨q,hq,h1,h2⟩ := residual_reach top rs hv
  have bad := fits_of_reach hq (x:=cap-(totalFloor top rs).1) (y:=cap-(totalFloor top rs).2)
    (by omega) (by omega)
  simp [excludes,bad,show ¬cap<(totalFloor top rs).1 by omega,
    show ¬cap<(totalFloor top rs).2 by omega] at h

end Rectangle
