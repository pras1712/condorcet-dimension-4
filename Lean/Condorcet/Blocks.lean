import Condorcet.Opposition

namespace ElectionLift
noncomputable section
open Finset
open scoped BigOperators

private theorem indicator_mono {P Q : Prop} {d : Decidable P} {e : Decidable Q}
    (h : P → Q) : @ind P d ≤ @ind Q e := @ind_mono P Q d e h

private def lefts {α β : Type} (xs : List (α ⊕ β)) : List α :=
  xs.filterMap (Sum.elim some fun _ => none)
private def rights {α β : Type} (xs : List (α ⊕ β)) : List β :=
  xs.filterMap (Sum.elim (fun _ => none) some)

private theorem lengths {α β : Type} (xs : List (α ⊕ β)) :
    (lefts xs).length + (rights xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases x <;> simp [lefts,rights,List.filterMap_cons] at * <;> omega

private theorem mem_lefts {α β : Type} {xs : List (α ⊕ β)} {x : α}
    (hx : Sum.inl x ∈ xs) : x ∈ lefts xs :=
  List.mem_filterMap.mpr ⟨_,hx,rfl⟩
private theorem mem_rights {α β : Type} {xs : List (α ⊕ β)} {x : β}
    (hx : Sum.inr x ∈ xs) : x ∈ rights xs :=
  List.mem_filterMap.mpr ⟨_,hx,rfl⟩

theorem blocksList_shorter (e : Election) {k : ℕ} {q : ℝ} (H : blocksList e k q)
    (r : List e.C) (hr : r.length ≤ k) : ∃ h, q ≤ jointSupport e h r := by
  let padded := r ++ List.replicate (k-r.length) (Classical.choice e.cn)
  obtain ⟨c,hc⟩ := H padded (by simp [padded]; omega)
  exact ⟨c,hc.trans (joint_antitone _ _ (fun x hx => List.mem_append_left _ hx))⟩

/-- The left block leads on l/(l+r) of the ballots, the right block on the rest.
Irrelevant candidates in a trailing block are separated by final strict refinement. -/
private abbrev mix (e f : Election) (m n : ℕ) : Election where
  C := e.C ⊕ f.C
  V := (Fin (m+1) ⊕ Fin (n+1)) × (e.V × f.V)
  height := max e.height f.height + 1
  rank := fun v => match v.1 with
    | .inl _ => Sum.elim (e.rank v.2.1) (fun _ => e.height)
    | .inr _ => Sum.elim (fun _ => f.height) (f.rank v.2.2)
  bounded := by
    rintro ⟨i,a,b⟩ c
    cases i <;> cases c <;> simp
    all_goals first | exact Nat.lt_succ_of_le (le_max_left ..)
                    | exact Nat.lt_succ_of_le (le_max_right ..)
                    | exact Nat.lt_succ_of_le ((e.bounded _ _).le.trans (le_max_left ..))
                    | exact Nat.lt_succ_of_le ((f.bounded _ _).le.trans (le_max_right ..))

private theorem mean_branch (m n : ℕ) (x y : ℝ) :
    mean (Sum.elim (fun _ : Fin (m+1) => x) (fun _ : Fin (n+1) => y)) =
    (((m+1:ℕ):ℝ)*x + ((n+1:ℕ):ℝ)*y) / ((m:ℝ)+n+2) := by
  simp only [mean,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Fintype.card_sum,Nat.cast_add,Nat.cast_one]
  ring

private theorem left_support (e f : Election) (m n : ℕ) (h : e.C) (s : List (e.C ⊕ f.C)) :
    ((m+1:ℕ):ℝ) * jointSupport e h (lefts s) / ((m:ℝ)+n+2) ≤
    jointSupport (mix e f m n) (.inl h) s := by
  classical
  unfold jointSupport
  rw [mean_prod]
  have step := mean_branch m n (mean fun v : e.V => ind (∀ x ∈ lefts s, e.rank v h < e.rank v x)) 0
  rw [mul_zero,add_zero] at step
  rw [← step]
  apply mean_mono
  intro pos
  cases pos with
  | inl t =>
    rw [mean_prod]
    apply mean_mono
    intro a
    rw [←mean_const (α:=f.V) (ind (∀ x ∈ lefts s, e.rank a h < e.rank a x))]
    apply mean_mono
    intro b
    apply indicator_mono
    intro good x hx
    cases x with
    | inl c => exact good c (mem_lefts hx)
    | inr c => exact e.bounded a h
  | inr t =>
    change 0 ≤ _
    rw [←mean_const (α:=e.V × f.V) (0:ℝ)]
    apply mean_mono
    intro v
    unfold ind
    split <;> norm_num

private theorem right_support (e f : Election) (m n : ℕ) (h : f.C) (s : List (e.C ⊕ f.C)) :
    ((n+1:ℕ):ℝ) * jointSupport f h (rights s) / ((m:ℝ)+n+2) ≤
    jointSupport (mix e f m n) (.inr h) s := by
  classical
  unfold jointSupport
  rw [mean_prod]
  have step := mean_branch m n 0 (mean fun v : f.V => ind (∀ x ∈ rights s, f.rank v h < f.rank v x))
  rw [mul_zero,zero_add] at step
  rw [← step]
  apply mean_mono
  intro pos
  cases pos with
  | inl t =>
    change 0 ≤ _
    rw [←mean_const (α:=e.V × f.V) (0:ℝ)]
    apply mean_mono
    intro v
    unfold ind
    split <;> norm_num
  | inr t =>
    rw [mean_prod]
    change mean _ ≤ _
    rw [←mean_const (α:=e.V) (mean fun v : f.V => ind (∀ x ∈ rights s, f.rank v h < f.rank v x))]
    apply mean_mono
    intro a
    apply mean_mono
    intro b
    apply indicator_mono
    intro good x hx
    cases x with
    | inl c => exact f.bounded b h
    | inr c => exact good c (mem_rights hx)

theorem mix_blocks {m n : ℕ} {q : ℝ}
    (hm : q/(m+1:ℕ) ∈ realizableK m) (hn : q/(n+1:ℕ) ∈ realizableK n) :
    q/((m:ℝ)+n+2) ∈ realizableK (m+n+1) := by
  classical
  obtain ⟨e,_,ec,he⟩ := hm
  obtain ⟨f,_,fc,hf⟩ := hn
  let E := mix e f m n
  apply mem_realizableK_of_list (refine E) (refine_inj E)
  · change m+n+1 < Fintype.card (e.C ⊕ f.C)
    rw [Fintype.card_sum]
    omega
  · intro s hs
    have tr (h : E.C) : jointSupport E h s ≤ jointSupport (refine E) h s :=
      mean_mono fun v => indicator_mono (fun p x hx => refine_lt E (p x hx))
    have den : 0 ≤ (m:ℝ)+n+2 := by positivity
    by_cases hL : (lefts s).length ≤ m
    · obtain ⟨x,hx⟩ := blocksList_shorter e ((list_iff_committees e m _ ec).mpr he) _ hL
      refine ⟨Sum.inl x, le_trans ?_ ((left_support e f m n x s).trans (tr _))⟩
      apply div_le_div_of_nonneg_right _ den
      exact (div_le_iff₀' (by positivity : (0:ℝ)<(m+1:ℕ))).mp hx
    · have hR : (rights s).length ≤ n := by have := lengths s; omega
      obtain ⟨x,hx⟩ := blocksList_shorter f ((list_iff_committees f n _ fc).mpr hf) _ hR
      refine ⟨Sum.inr x, le_trans ?_ ((right_support e f m n x s).trans (tr _))⟩
      apply div_le_div_of_nonneg_right _ den
      exact (div_le_iff₀' (by positivity : (0:ℝ)<(n+1:ℕ))).mp hx

/-- Strong induction on the number of seats, adding one block of capacity three. -/
theorem transfer_from_bases (h₃ : 3*A₂/4 ≤ A 3) (h₄ : 3*A₂/5 ≤ A 4)
    (k : ℕ) (hk : 2 ≤ k) : 3*A₂/((k:ℝ)+1) ≤ A k := by
  have W (n : ℕ) (hn : 2 ≤ n) (q : ℝ) (hq : q < 3*A₂) :
      q/((n:ℝ)+1) ∈ realizableK n := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      rcases Nat.eq_or_lt_of_le hn with rfl|hn
      · apply finite_witness_below
        rw [A_two_eq]
        norm_num
        linarith
      rcases Nat.eq_or_lt_of_le hn with rfl|hn
      · apply finite_witness_below
        norm_num at *
        linarith
      rcases Nat.eq_or_lt_of_le hn with rfl|hn
      · apply finite_witness_below
        norm_num at *
        linarith
      let m := n-3
      have hm : m < n := by dsimp [m]; omega
      have hmn : 2 ≤ m := by dsimp [m]; omega
      have left := ih m hm hmn
      have right : q/(2+1:ℕ) ∈ realizableK 2 := by
        apply finite_witness_below
        rw [A_two_eq]
        norm_num
        linarith
      have mixed := mix_blocks (m:=m) (n:=2) (q:=q) (by simpa using left) right
      have eq : m+2+1=n := by dsimp [m]; omega
      rw [←eq]
      convert mixed using 1
      push_cast
      ring_nf
  apply le_of_forall_lt_imp_le_of_dense
  intro t ht
  have pos : (0:ℝ) < k+1 := by positivity
  have hq := (lt_div_iff₀ pos).mp ht
  have hh := le_A_of_mem (W k hk (t*(k+1)) hq)
  rwa [mul_div_cancel_right₀ _ pos.ne'] at hh

end
end ElectionLift
