import Rectangle
import Lean.Data.Json.Parser

namespace PairBound

def numerator : Nat := 351449648252133
def denominator : Nat := 512000000000000
def mass : Nat := 1000000000000
def width : Nat := 80 * 64 * mass
def den : Nat := (width+1)*denominator
def num : Nat := (width+1)*numerator - 1
def raw : String := include_str "pair-menus.json"

abbrev Word := Array Nat
inductive OptionWord where
  | fixed (v : Word)
  | band (initial marked count : Nat)
deriving Inhabited, Repr
structure Row where
  id : Nat
  mode : String
  weight : Nat
  menus : Array (Array OptionWord)
deriving Inhabited
structure Joined where
  weight : Nat
  u : Nat
  menus : Array (Array (Word × Word))
deriving Inhabited
structure Data where
  rows : List Row := []
  joined : List Joined := []
deriving Inhabited

/-- The appendix uses ASCII order. Refuse characters outside its stated alphabet. -/
def readGrades (s : String) : Except String Word := do
  let w := s.toList.map Char.toNat
  unless w.all (fun c => (48 ≤ c && c ≤ 57) || (65 ≤ c && c ≤ 74)) do
    throw "expected a grade in 0-9 or A-J"
  return w.toArray

def readWord (j : Lean.Json) : Except String Word := do
  let w ← readGrades (← j.getStr?)
  unless w.size == 64 do throw "a grade word must have 64 positions"
  return w

def readGrade (j : Lean.Json) : Except String Nat := do
  let w ← readGrades (← j.getStr?)
  match w.toList with
  | [g] => return g
  | _ => throw "expected a single grade"

def readOption (mode : String) (j : Lean.Json) : Except String OptionWord := do
  if mode == "fixed" then return .fixed (← readWord j)
  let #[g,h,n] ← j.getArr? | throw "expected a grade band"
  let n ← n.getNat?
  unless n ≤ 64 do throw "too many marked positions"
  return .band (← readGrade g) (← readGrade h) n

def readJoined (j : Lean.Json) : Except String (Word × Word) := do
  let #[l,r] ← j.getArr? | throw "expected both halves of a joined option"
  return (← readWord l, ← readWord r)

def readMenus {α} (parseOption : Lean.Json → Except String α) (j : Lean.Json) :
    Except String (Array (Array α)) := do
  let menus ← j.getArr?
  unless menus.size == 21 do throw "expected 21 candidate types"
  menus.mapM fun m => do
    let opts ← m.getArr?
    unless !opts.isEmpty do throw "empty menu"
    opts.mapM parseOption

/-- Decode exactly the positive-weight rows printed in the current appendix. -/
def decode (s : String) : Except String Data := do
  let rows ← (← Lean.Json.parse s).getArr?
  let mut d : Data := {}
  for (row,id) in rows.zipIdx do
    let #[mode,w,u,m] ← row.getArr? | throw "expected a grade row"
    let mode ← mode.getStr?
    let w ← w.getNat?
    let u ← u.getNat?
    unless w > 0 && u ≤ 80 do throw "invalid row weight or split"
    if mode == "joined" then
      let menus ← readMenus readJoined m
      d := { d with joined := ⟨w,u,menus⟩ :: d.joined }
    else
      unless (["free","prefix","fixed"].contains mode) && u == 80 do
        throw "invalid ordinary row"
      let menus ← readMenus (readOption mode) m
      d := { d with rows := ⟨id,mode,w,menus⟩ :: d.rows }
  return d

def parse (s : String) : Data := (decode s).toOption.getD {}

def asWord : OptionWord → Word
  | .fixed w => w
  | .band g h n => Array.replicate n h ++ Array.replicate (64-n) g

def credit (h a b : Nat) : Nat :=
  if h > min a b then 0 else if h == a && h == b then num else den

def fixedScore (h a b : Word) : Nat := Id.run do
  let mut sum := 0
  for i in [:64] do sum := sum + credit h[i]! a[i]! b[i]!
  return sum

-- Among marked positions it is optimal to take the largest gains first.
def freeScore (g h p a0 a1 b0 b1 : Nat) (sizes : List Nat) : Nat := Id.run do
  let cells := [(a0,b0),(a0,b1),(a1,b0),(a1,b1)]
  let gains := (cells.zip sizes).map fun ((a,b),s) =>
    ((credit h a b : Int) - (credit g a b : Int), s, s*credit g a b)
  let mut value : Int := gains.foldl (fun s e => s + e.2.2) 0
  let mut remaining := p
  for (gain,s,_) in gains.mergeSort (fun e f => e.1 ≥ f.1) do
    let used := min remaining s
    value := value + gain * used
    remaining := remaining - used
  return value.toNat

def bands (o : OptionWord) : Nat × Nat × Nat := match o with
  | .band a b p => (a,b,p)
  | .fixed _ => panic! "free shape expected"

def rowVectors (row : Row) (i j : Nat) (targets : List Nat) : List (List Nat) := Id.run do
  let mut out := []
  for a in row.menus[i]! do
    for b in row.menus[j]! do
      if row.mode == "free" then
        let (a0,a1,p) := bands a
        let (b0,b1,q) := bands b
        for m in [(p+q-64):(min p q+1)] do
          let sizes := [64+m-p-q,q-m,p-m,m]
          let v := targets.map fun t =>
            row.menus[t]!.foldl (fun z ho =>
              let (g,h,r) := bands ho
              max z (freeScore g h r a0 a1 b0 b1 sizes)) 0
          out := v :: out
      else
        let aw := asWord a
        let bw := asWord b
        let v := targets.map fun t =>
          row.menus[t]!.foldl (fun z h => max z (fixedScore (asWord h) aw bw)) 0
        out := v :: out
  return out.eraseDups

def joinedVectors (row : Joined) (i j h g : Nat) : List (Nat × Nat) := Id.run do
  let mut out := []
  for a in row.menus[i]! do
    for b in row.menus[j]! do
      let f := fun t => row.menus[t]!.foldl (fun z p => max z
        (row.u * fixedScore p.1 a.1 b.1 + (80-row.u)*fixedScore p.2 a.2 b.2)) 0
      out := (f h, f g) :: out
  return out.eraseDups

def inspect : Nat → List Nat
  | 5 => [8]
  | 16 => [1,4,5]
  | 10 => [0,2,3,6,1000,1001,1002]
  | _ => []

def dataValid : Bool := Id.run do
  let d := parse raw
  if d.rows.length != 96 || (d.rows.filter (fun r => r.weight>0)).length != 96 ||
      d.joined.length != 17 || (d.joined.filter (fun r => r.weight>0)).length != 17 then return false
  if !d.rows.all (fun r => r.menus.size==21 && r.menus.all (fun v => !v.isEmpty)) then
    return false
  if !d.joined.all (fun r => r.u≤80 && r.menus.size==21 &&
      r.menus.all (fun v => !v.isEmpty)) then return false
  if (d.rows.map (·.weight)).sum + (d.joined.map (·.weight)).sum != mass then
    return false
  return true

def rawRows (d : Data) (i j : Nat) : List Rectangle.Row := Id.run do
  let h := if i>0 then j-1 else if 1≤j && j≤15 then 0 else 20
  let g := if i==j && [5,10,16].contains i then i else h
  let observed := if h==g then [] else inspect i
  let mut rows := []
  for r in d.rows do
    if r.weight>0 then
      let vs := rowVectors r i j (if h==g then [h] else [h,g])
      let w := 80*r.weight
      let ps := vs.map fun v =>
        (w*v[0]!, w*(if h==g then v[0]! else v[1]!))
      rows := (observed.contains r.id,ps)::rows
  for (r,k) in d.joined.reverse.zipIdx do
    let ps := (joinedVectors r i j h g).map fun p => (r.weight*p.1,r.weight*p.2)
    rows := (observed.contains (1000+k), ps)::rows
  return rows

def saved : Data := parse raw

def rowTest (i j : Fin 21) : Bool :=
  Rectangle.excludes (width*den) (width*num) (rawRows saved i j)

theorem all_rows_pass : ∀ i j : Fin 21, i ≤ j → rowTest i j = true := by native_decide

/-- Every actual combination of one of the listed pure response vectors
in every row has at least one coordinate strictly above the cutoff. -/
theorem every_row_selection {i j : Fin 21} (ij : i ≤ j) {v}
    (hv : Rectangle.Reach ((rawRows saved i j).map Prod.snd) v) :
    width*num < v.1 ∨ width*num < v.2 :=
  Rectangle.excludes_sound (all_rows_pass i j ij) hv

theorem data_valid : dataValid = true := by native_decide

#print axioms every_row_selection
end PairBound
