import Condorcet.Core

namespace ElectionLift
noncomputable section
open Finset
open scoped BigOperators

private theorem ind_le_of_imp {P Q : Prop} {dp : Decidable P} {dq : Decidable Q}
    (h : P → Q) : @ind P dp ≤ @ind Q dq := @ind_mono P Q dp dq h

theorem jointSupport_nonneg (e : Election) (h : e.C) (r : List e.C) :
    0 ≤ jointSupport e h r := by
  classical
  rw [←mean_const (α:=e.V) (0:ℝ)]
  exact mean_mono fun v => by simp [ind]; split <;> norm_num

@[simp] theorem jointSupport_pair (e : Election) (h x y : e.C) :
    jointSupport e h [x,y] = support e h x y := by
  classical
  unfold jointSupport support
  congr 1
  funext v
  by_cases P : e.rank v h < e.rank v x ∧ e.rank v h < e.rank v y <;> simp [ind,win,P]

@[simp] theorem jointSupport_single (e : Election) (h x : e.C) :
    jointSupport e h [x] = support e h x x := by
  classical
  simp [jointSupport, support, win, ind]

theorem joint_intersection (e : Election) (r : List e.C) (w x h : e.C) :
    jointSupport e w r + support e h w x - 1 ≤ jointSupport e h (x :: r) := by
  classical
  let f := fun v : e.V => ind (∀ t ∈ r, e.rank v w < e.rank v t)
  let g := fun v : e.V => ind (win e v h w x)
  have aux : mean (fun v => f v + g v - 1) =
      jointSupport e w r + support e h w x - 1 := by
    change mean (fun v => f v + g v + (-1)) = mean f + mean g - 1
    rw [mean_add, mean_add, mean_const]
    ring
  rw [←aux]
  apply mean_mono
  intro v
  dsimp [f,g]
  by_cases A : ∀ t ∈ r, e.rank v w < e.rank v t
  · by_cases B : win e v h w x
    · have C : ∀ t ∈ x::r, e.rank v h < e.rank v t := by
        intro t ht
        rcases List.mem_cons.mp ht with eq | ht
        · simpa [eq] using B.2
        · exact B.1.trans (A _ ht)
      simp only [ind,if_pos A,if_pos B,if_pos C]; norm_num
    · simp only [ind, if_pos A, if_neg B]
      split <;> norm_num
  · simp only [ind,if_neg A]
    split <;> split <;> norm_num

/-- The common support of a challenge to a list decreases by at most
`1-a` for each additional rival. Entries of the list may coincide. -/
theorem repeated_challenges (e : Election) {a : ℝ} (hp : blocks e a)
    (n : ℕ) (r : List e.C) (hr : r.length = n+2) :
    ∃ h, max 0 (1-((n:ℝ)+1)*(1-a)) ≤ jointSupport e h r := by
  have raw : ∀ (m : ℕ) (s : List e.C), s.length = m+2 →
      ∃ h, 1-((m:ℝ)+1)*(1-a) ≤ jointSupport e h s := by
    intro m
    induction m with
    | zero =>
      rintro (_ | ⟨x,_ | ⟨y,tail⟩⟩) hl
      · simp at hl
      · simp at hl
      · have ht : tail = [] := List.length_eq_zero_iff.mp (by simpa using hl)
        subst tail
        obtain ⟨h, hh⟩ := hp x y
        exact ⟨h,by simpa using hh⟩
    | succ m ih =>
      rintro (_ | ⟨x,s⟩) hl
      · simp at hl
      · obtain ⟨w,hw⟩ := ih s (by simpa [Nat.add_assoc] using hl)
        obtain ⟨h,hh⟩ := hp w x
        refine ⟨h,?_⟩
        have hj := joint_intersection e s w x h
        push_cast
        linarith
  obtain ⟨h, hh⟩ := raw n r hr
  exact ⟨h,max_le (jointSupport_nonneg ..) hh⟩


@[simp] theorem jointSupport_nil (e : Election) (h : e.C) :
    jointSupport e h [] = 1 := by classical simp [jointSupport,ind]

private theorem support_ties (e : Election) (g : ℕ) (rs : List (ℕ × e.C))
    (better : ∀ t ∈ rs, g ≤ t.1) (h : e.C) :
    jointSupport e h ((rs.filter (fun t => t.1 == g)).map Prod.snd) ≤ mean (fun v =>
      @ind (∀ t ∈ rs, g*e.height+e.rank v h < t.1*e.height+e.rank v t.2)
        (Classical.propDecidable _)) := by
  classical
  apply mean_mono
  intro v
  apply ind_le_of_imp
  intro hw t ht
  apply order_grade e (e.bounded v h)
  rcases (better t ht).lt_or_eq with hlt | heq
  · exact Or.inl hlt
  · exact Or.inr ⟨heq,hw t.2 (List.mem_map.mpr ⟨t, List.mem_filter.mpr
        ⟨ht, by simp [heq]⟩,rfl⟩)⟩

private theorem filter_map_grades {C : Type} (rs : List (ℕ × C)) (g : ℕ) :
    ((rs.map Prod.fst).filter (· == g)).length =
    ((rs.filter (fun t => t.1 == g)).map Prod.snd).length := by
  induction rs with
  | nil => rfl
  | cons h t ih =>
    by_cases he : h.1 = g <;> simp_all

/-- A single position is realized simultaneously against any list of opponents.
An inner clone loses one cyclic cut in the single-tie case. -/
theorem local_list_response (e : Election) {a : ℝ} (hp : blocks e a)
    (L : ℕ) [NeZero L] (g : ℕ) (rs : List (ℕ × (cloning e L).C)) :
    ∃ h : (cloning e L).C, rowCredit a g (rs.map Prod.fst) - 1/(L:ℝ) ≤
      mean (fun v => @ind (∀ t ∈ rs, g*(cloning e L).height+(cloning e L).rank v h <
        t.1*(cloning e L).height+(cloning e L).rank v t.2) (Classical.propDecidable _)) := by
  classical
  let E := cloning e L
  have hL : 0 ≤ 1/(L:ℝ) := by positivity
  by_cases bad : (rs.map Prod.fst).any (· < g) = true
  · refine ⟨Classical.choice E.cn, ?_⟩
    rw [rowCredit, if_pos bad]
    apply le_trans (show (0:ℝ)-1/L ≤ 0 by linarith)
    rw [←mean_const (α:=E.V) (0:ℝ)]
    apply mean_mono
    intro v
    unfold ind
    split <;> norm_num
  · have better : ∀ t ∈ rs, g ≤ t.1 := by
      intro t ht
      by_contra! hn
      exact bad (List.any_eq_true.mpr ⟨t.1, List.mem_map.mpr ⟨t,ht,rfl⟩,by simpa using hn⟩)
    let tied : List E.C := (rs.filter (fun t => t.1 == g)).map Prod.snd
    have hc : ∃ h : E.C, tiesCredit a tied.length - 1/(L:ℝ) ≤ jointSupport E h tied := by
      match tied with
      | [] => exact ⟨Classical.choice E.cn, by simp [tiesCredit]⟩
      | [x] =>
        obtain ⟨h,hh⟩ := clone_one e L x
        refine ⟨h,?_⟩
        rw [show tiesCredit a [x].length = 1 by rfl, jointSupport_single E h x]
        exact hh
      | x::y::rest =>
        obtain ⟨h,hh⟩ := repeated_challenges E (clone_blocks e L hp) rest.length
          (x::y::rest) (by simp [Nat.add_assoc])
        refine ⟨h,?_⟩
        simp only [List.length_cons] at *
        rw [tiesCredit, if_neg (by omega)]
        have eq : rest.length+1+1-1 = rest.length+1 := by omega
        rw [eq, Nat.cast_add, Nat.cast_one]
        linarith
    obtain ⟨h,hh⟩ := hc
    refine ⟨h, ?_⟩
    rw [rowCredit,if_neg bad,filter_map_grades]
    exact hh.trans (support_ties E g rs better h)

/-- Uniform slots may be repeated to give integral row weights. Every challenger
uses one grade assignment globally and a separately chosen inner clone per slot. -/
theorem graded_realization {G : Type} [Fintype G] [Nonempty G]
    {n : ℕ} [NeZero n] (tab : Grades G n) (k L : ℕ) [NeZero L] (hk : k < 3*L)
    (e : Election) (ce : 3 ≤ Fintype.card e.C) {a M : ℝ} (hp : blocks e a)
    (cert : ∀ rs : List G, rs.length = k → ∃ g : G, M ≤
      mean (fun i => rowCredit a (tab.grade i g) (rs.map (tab.grade i)))) :
    ∃ out : Election, (∀ v, Function.Injective (out.rank v)) ∧
      k < Fintype.card out.C ∧ blocksList out k (M-1/(L:ℝ)) := by
  classical
  let inner := cloning e L
  let out := grading inner tab
  refine ⟨refine out,refine_inj out,?_,?_⟩
  · let embed : inner.C → out.C := fun x => (Classical.choice ‹Nonempty G›,fun _ => x)
    have inj : Function.Injective embed := by
      intro x y h
      exact congrArg (fun c : out.C => c.2 (0 : Fin n)) h
    have le := Fintype.card_le_of_injective _ inj
    have size : Fintype.card inner.C = Fintype.card e.C * L := by
      change Fintype.card (e.C × Fin L) = _
      simp
    rw [size] at le
    exact hk.trans_le ((Nat.mul_le_mul_right L ce).trans le)
  · intro rs hlen
    obtain ⟨g,hg⟩ := cert (rs.map Prod.fst) (by simpa using hlen)
    let rivals (i : Fin n) : List (ℕ × inner.C) :=
      rs.map fun x => (tab.grade i x.1,x.2 i)
    choose f hf using fun i => local_list_response e hp L (tab.grade i g) (rivals i)
    let h : out.C := (g,f)
    refine ⟨h,?_⟩
    have lower : M-1/(L:ℝ) ≤ jointSupport out h rs := by
      unfold jointSupport
      change _ ≤ mean (α:=Fin n × inner.V) _
      rw [mean_prod]
      calc
        M - 1/(L:ℝ) ≤ mean (fun i => rowCredit a (tab.grade i g)
            ((rs.map Prod.fst).map (tab.grade i))) - 1/(L:ℝ) := sub_le_sub_right hg _
        _ = mean (fun i => rowCredit a (tab.grade i g) ((rivals i).map Prod.fst) -
              1/(L:ℝ)) := by
            simp only [rivals,List.map_map,Function.comp_def]
            simp only [sub_eq_add_neg,mean_add,mean_const]
            rfl
        _ ≤ _ := by
          apply mean_mono
          intro i
          apply (hf i).trans
          apply mean_mono
          intro v
          apply ind_le_of_imp
          intro H x hx
          exact H (_,_) (List.mem_map.mpr ⟨x,hx,rfl⟩)
    apply lower.trans
    unfold jointSupport
    apply mean_mono
    intro v
    apply ind_le_of_imp
    exact fun H x hx => refine_lt out (H x hx)

/-- Integral weights are encoded by literal copies of a row. Clearing common
denominators therefore gives one finite electorate, including zero-weight rows. -/
theorem weighted_realization {R G : Type} [Fintype R] [Fintype G] [Nonempty G]
    (w : R → ℕ) (wpos : 0 < ∑ i, w i) (grade : R → G → ℕ)
    (k L : ℕ) [NeZero L] (hk : k < 3*L)
    (e : Election) (ce : 3 ≤ Fintype.card e.C) {a M : ℝ} (hp : blocks e a)
    (cert : ∀ rs : List G, rs.length = k → ∃ g : G, M ≤
      (∑ i, (w i:ℝ)*rowCredit a (grade i g) (rs.map (grade i))) / (∑ i, w i : ℕ)) :
    ∃ out : Election, (∀ v, Function.Injective (out.rank v)) ∧
      k < Fintype.card out.C ∧ blocksList out k (M-1/(L:ℝ)) := by
  classical
  let n := ∑ i, w i
  have : NeZero n := ⟨Nat.ne_of_gt wpos⟩
  let slots := (Σ i, Fin (w i))
  have card : Fintype.card slots = n := by simp [slots,n,Fintype.card_sigma]
  let σ : Fin n ≃ slots := (Fintype.equivFinOfCardEq card).symm
  let tab : Grades G n := {
    height := (univ.sup fun i => univ.sup (grade i))+1
    grade := fun j g => grade (σ j).1 g
    bounded := fun j g => Nat.lt_succ_of_le (Finset.le_sup_of_le (mem_univ (σ j).1)
                              (Finset.le_sup (f:=grade (σ j).1) (mem_univ g))) }
  apply graded_realization tab k L hk e ce hp
  intro rs hlen
  obtain ⟨g,hg⟩ := cert rs hlen
  refine ⟨g,?_⟩
  let f := fun i => rowCredit a (grade i g) (rs.map (grade i))
  have hs := Equiv.sum_comp σ (fun j : slots => f j.1)
  have hsum : (∑ j : Fin n, f (σ j).1) = ∑ i, (w i:ℝ)*f i := by
    rw [hs]
    simp [slots,Fintype.sum_sigma,nsmul_eq_mul]
  unfold mean
  change M ≤ (∑ j : Fin n, f (σ j).1)/(Fintype.card (Fin n):ℝ)
  rw [hsum,Fintype.card_fin]
  exact hg

end
end ElectionLift
