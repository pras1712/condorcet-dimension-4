import Elections

/-! Two earlier explicit pair obstructions, and the variable-length extension of
the three-block example in Section 2. An election's `rank` is smaller for a
more-preferred candidate. -/

namespace ElectionLift.Historical
noncomputable section
open Finset

/-- The three cyclic rotations of the outer blocks. -/
def threeCycle : Election where
  C := Fin 3
  V := Fin 3
  height := 6
  rank := cyclic
  bounded := by
    intro s c
    have := c.isLt
    unfold cyclic
    split <;> omega

/-- Three blocks of `n` candidates. On each ballot the same rotation is used in
all three inner blocks. The final injective key gives a strict ranking. -/
abbrev cycleProduct (n : ℕ) [NeZero n] := refine (cloning threeCycle n)

private theorem outer_cases : ∀ a b : Fin 3, a = b ∨ a = prev b ∨ b = prev a := by
  decide +kernel

private theorem mean_const_mul {X : Type} [Fintype X] (c : ℝ) (f : X → ℝ) :
    mean (fun x => c * f x) = c * mean f := by
  simp only [mean, ← Finset.mul_sum, mul_div_assoc]

private theorem mean_mul_const {X : Type} [Fintype X] (c : ℝ) (f : X → ℝ) :
    mean (fun x => f x * c) = mean f * c := by
  simpa only [mul_comm c] using mean_const_mul c f

private theorem two_cuts {n : ℕ} [NeZero n] (u : Fin 3) (v : Fin n)
    (h a b : (cloning threeCycle n).C)
    (good : ∀ s t, s ≠ u → t ≠ v → win (cloning threeCycle n) (s,t) h a b) :
    (1-1/(3:ℝ))*(1-1/(n:ℝ)) ≤ support (cloning threeCycle n) h a b := by
  classical
  have M : mean (fun st : Fin 3 × Fin n => ind (st.1 ≠ u) * ind (st.2 ≠ v)) ≤
      support (cloning threeCycle n) h a b := by
    apply mean_mono
    rintro ⟨s,t⟩
    change ind (s ≠ u) * ind (t ≠ v) ≤ ind (win (cloning threeCycle n) (s,t) h a b)
    by_cases hs : s ≠ u <;> by_cases ht : t ≠ v
    · have hg := good s t hs ht
      unfold ind
      rw [if_pos hs,if_pos ht,if_pos hg,one_mul]
    all_goals simp [ind,hs,ht,apply_ite]
  rw [mean_prod] at M
  change mean (fun s : Fin 3 => mean (fun t : Fin n => ind (s≠u) * ind (t≠v))) ≤ _ at M
  have H (s : Fin 3) : mean (fun t : Fin n => ind (s≠u) * ind (t≠v)) =
      ind (s≠u) * (1-1/(n:ℝ)) := (mean_const_mul _ _).trans (congrArg _ (mean_ne v))
  simp_rw [H] at M
  rw [mean_mul_const,mean_ne] at M
  exact M

/-- The cyclic predecessor of either rival block is sufficient on two of the
three outer rotations. Only the cut at the inner rival can then be lost. -/
theorem cycleProduct_blocks (n : ℕ) [NeZero n] :
    blocks (cycleProduct n) ((1-1/(3:ℝ))*(1-1/(n:ℝ))) := by
  apply refine_blocks
  rintro ⟨A,i⟩ ⟨B,j⟩
  rcases outer_cases A B with rfl | rfl | rfl
  · refine ⟨(prev A,i), two_cuts A i _ _ _ ?_⟩
    intro s t hs _
    exact ⟨clone_lt threeCycle n (cyclic_lt hs),clone_lt threeCycle n (cyclic_lt hs)⟩
  · refine ⟨(prev B,prev i), two_cuts B i _ _ _ ?_⟩
    intro s t hs ht
    refine ⟨?_,clone_lt threeCycle n (cyclic_lt hs)⟩
    change _ + cyclic t (prev i) < _ + cyclic t i
    exact Nat.add_lt_add_left (cyclic_lt ht) _
  · refine ⟨(prev A,prev j), two_cuts A j _ _ _ ?_⟩
    intro s t hs ht
    refine ⟨clone_lt threeCycle n (cyclic_lt hs),?_⟩
    change _ + cyclic t (prev j) < _ + cyclic t j
    exact Nat.add_lt_add_left (cyclic_lt ht) _

/-- Proposition 6 of Elkind, Lang, and Saffidine: every pair in their 15-by-15
election faces an outsider on at least eight of the fifteen ballots. -/
theorem elkind_lang_saffidine :
    Fintype.card (cycleProduct 5).V = 15 ∧ Fintype.card (cycleProduct 5).C = 15 ∧
    (∀ v, Function.Injective ((cycleProduct 5).rank v)) ∧
    blocks (cycleProduct 5) (8/15) := by
  refine ⟨by decide,by decide,refine_inj (cloning threeCycle 5),?_⟩
  convert cycleProduct_blocks 5 using 1
  norm_num

theorem cycle_limit : (2:ℝ)/3 ≤ A₂ := by
  by_contra! h
  obtain ⟨k,hk⟩ := exists_nat_one_div_lt (sub_pos.mpr h)
  have valid : (1-1/(3:ℝ)) * (1-1/((k+1:ℕ):ℝ)) ∈ realizable :=
    ⟨cycleProduct (k+1),refine_inj (cloning threeCycle (k+1)),cycleProduct_blocks _⟩
  have le := le_csSup realizable_bounded valid
  change _ ≤ A₂ at le
  push_cast at le
  have pos : 0 < 1/((k:ℝ)+1) := by positivity
  linarith

/-- The coordinates in Speyer's orbit are 0,...,6 in increasing utility order. -/
def speyerRank (v : Fin 3 × Fin 7) (x : Fin 7) : ℕ :=
  6 - ((2 ^ v.1.val * x.val + v.2.val) % 7)

def speyer : Election where
  C := Fin 7
  V := Fin 3 × Fin 7
  height := 7
  rank := speyerRank
  bounded _ _ := by unfold speyerRank; omega

private theorem speyer_distinct :
    ∀ (v : Fin 3 × Fin 7) (a b : Fin 7), speyerRank v a = speyerRank v b → a = b := by
  decide +kernel

theorem speyer_strict (v : speyer.V) : Function.Injective (speyer.rank v) :=
  fun _ _ => speyer_distinct v _ _

theorem speyer_counts :
    ∀ a b : Fin 7, a ≠ b → ∃ h, h ≠ a ∧ h ≠ b ∧
      ((univ : Finset (Fin 3 × Fin 7)).filter fun v =>
        speyerRank v h < speyerRank v a ∧ speyerRank v h < speyerRank v b).card = 11 := by
  decide +kernel

theorem speyer_eleven_of_twenty_one (a b : speyer.C) (hne : a ≠ b) :
    ∃ h, h ≠ a ∧ h ≠ b ∧ support speyer h a b = (11:ℝ)/21 := by
  obtain ⟨h,ha,hb,hc⟩ := speyer_counts a b hne
  refine ⟨h,ha,hb,?_⟩
  unfold support mean ind
  rw [Finset.sum_boole]
  change ((univ.filter fun v => speyerRank v h < speyerRank v a ∧
      speyerRank v h < speyerRank v b).card : ℝ) / Fintype.card (Fin 3 × Fin 7) = _
  rw [hc]
  norm_num

end
end ElectionLift.Historical
