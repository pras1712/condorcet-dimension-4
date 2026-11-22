import Condorcet.Core

namespace ElectionLift
noncomputable section
open Finset

/-- Attainable lower bounds on opposition, using actual sets and outside challengers. -/
def realizableK (k : ℕ) : Set ℝ :=
  {q | ∃ e : Election, (∀ v, Function.Injective (e.rank v)) ∧
    k < Fintype.card e.C ∧ ∀ S : Finset e.C, S.card = k →
    ∃ h ∉ S, q ≤ jointSupport e h S.toList}

def A (k : ℕ) : ℝ := sSup (realizableK k)
def C (k : ℕ) : ℝ := 1 - A k

theorem joint_nonneg (e : Election) (h : e.C) (r : List e.C) : 0 ≤ jointSupport e h r := by
  classical
  rw [← mean_const (α := e.V) (0 : ℝ)]
  exact mean_mono fun v => by unfold ind; split <;> norm_num

theorem joint_le_one (e : Election) (h : e.C) (r : List e.C) : jointSupport e h r ≤ 1 := by
  classical
  rw [← mean_const (α := e.V) (1 : ℝ)]
  exact mean_mono fun v => by unfold ind; split <;> norm_num

theorem joint_antitone (e : Election) (h : e.C) {r s : List e.C}
    (sub : ∀ x ∈ r, x ∈ s) : jointSupport e h s ≤ jointSupport e h r := by
  classical
  exact mean_mono fun _ => ind_mono fun p x hx => p x (sub x hx)

theorem joint_zero_of_mem (e : Election) {h : e.C} {r : List e.C} (hh : h ∈ r) :
    jointSupport e h r = 0 := by
  classical
  unfold jointSupport
  have hf (v : e.V) : ¬ (∀ x ∈ r, e.rank v h < e.rank v x) := fun z => (lt_irrefl _) (z h hh)
  simp only [ind, if_neg (hf _), mean_const]

theorem outside_exists (e : Election) (S : Finset e.C) (h : S.card < Fintype.card e.C) :
    ∃ c, c ∉ S := by
  obtain ⟨c, _, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (t := (Finset.univ : Finset e.C)) (by simpa using h)
  exact ⟨c, hc⟩

theorem list_iff_committees (e : Election) (k : ℕ) (q : ℝ) (size : k < Fintype.card e.C) :
    blocksList e k q ↔ ∀ S : Finset e.C, S.card = k → ∃ h ∉ S, q ≤ jointSupport e h S.toList := by
  classical
  constructor
  · intro h S hS
    obtain ⟨c, hc⟩ := h S.toList (by simpa using hS)
    by_cases hmem : c ∈ S
    · rw [joint_zero_of_mem e (Finset.mem_toList.mpr hmem)] at hc
      obtain ⟨x, hx⟩ := outside_exists e S (hS ▸ size)
      exact ⟨x, hx, hc.trans (joint_nonneg _ _ _)⟩
    · exact ⟨c, hmem, hc⟩
  · intro h r hr
    have hcard : r.toFinset.card ≤ k := hr ▸ List.toFinset_card_le r
    obtain ⟨S, hs, hc⟩ := Finset.exists_superset_card_eq hcard size.le
    obtain ⟨x, _, hx⟩ := h S hc
    exact ⟨x,hx.trans (joint_antitone e x (fun a ha => by simpa using hs (List.mem_toFinset.mpr ha)))⟩

theorem mem_realizableK_of_list {k : ℕ} {q : ℝ} (e : Election)
    (s : ∀ v, Function.Injective (e.rank v)) (hc : k < Fintype.card e.C)
    (h : blocksList e k q) : q ∈ realizableK k :=
  ⟨e,s,hc,(list_iff_committees e k q hc).mp h⟩

theorem zero_mem_realizableK (k : ℕ) : 0 ∈ realizableK k := by
  let e : Election := { C := Fin (k+1), V := Unit, height := k+1,
                        rank := fun _ i => i.val, bounded := fun _ i => i.isLt }
  apply mem_realizableK_of_list e (fun _ => Fin.val_injective)
  · change k < Fintype.card (Fin (k+1))
    simp
  · exact fun r _ => ⟨0, joint_nonneg e 0 r⟩

theorem realizableK_le_one {k : ℕ} {q : ℝ} (hq : q ∈ realizableK k) : q ≤ 1 := by
  obtain ⟨e, _, size, h⟩ := hq
  let x := Classical.choice e.cn
  obtain ⟨c,hc⟩ := (list_iff_committees e k q size).mpr h (List.replicate k x) (by simp)
  exact hc.trans (joint_le_one _ _ _)

theorem realizableK_bdd (k : ℕ) : BddAbove (realizableK k) := ⟨1, fun _ => realizableK_le_one⟩

theorem le_A_of_mem {k : ℕ} {q : ℝ} (h : q ∈ realizableK k) : q ≤ A k :=
  le_csSup (realizableK_bdd _) h

theorem A_nonneg (k : ℕ) : 0 ≤ A k := le_A_of_mem (zero_mem_realizableK k)
theorem A_le_one (k : ℕ) : A k ≤ 1 := csSup_le ⟨0,zero_mem_realizableK k⟩ (fun _ => realizableK_le_one)

theorem finite_witness_below {k : ℕ} {q : ℝ} (h : q < A k) : q ∈ realizableK k := by
  obtain ⟨b, ⟨e,s,size,good⟩, hb⟩ := exists_lt_of_lt_csSup ⟨0,zero_mem_realizableK k⟩ h
  refine ⟨e,s,size,fun S hs => ?_⟩
  obtain ⟨c,hc,hq⟩ := good S hs
  exact ⟨c,hc,hb.le.trans hq⟩

@[simp] theorem joint_pair (e : Election) (h a b : e.C) :
    jointSupport e h [a,b] = support e h a b := by
  classical
  unfold jointSupport support
  congr 1
  funext v
  by_cases ha : e.rank v h < e.rank v a <;> by_cases hb : e.rank v h < e.rank v b <;>
    simp [ind,win,ha,hb]

theorem blocksList_two (e : Election) (q : ℝ) : blocksList e 2 q ↔ blocks e q := by
  constructor
  · intro H a b
    simpa using H [a,b] rfl
  · intro H r hr
    match r with
    | [a,b] => simpa using H a b
    | [] | [_] | _ :: _ :: _ :: _ => simp_all

theorem A_two_eq : A 2 = A₂ := by
  apply le_antisymm
  · apply csSup_le ⟨0, zero_mem_realizableK 2⟩
    rintro q ⟨e,strict,size,h⟩
    apply le_csSup realizable_bounded
    exact ⟨e,strict,(blocksList_two e q).mp ((list_iff_committees e 2 q size).mpr h)⟩
  · apply csSup_le realizable_nonempty
    rintro q ⟨e,_,h⟩
    let e' := cloning e 3
    have size : 2 < Fintype.card (refine e').C := by
      change 2 < Fintype.card (e.C × Fin 3)
      rw [Fintype.card_prod, Fintype.card_fin]
      have := Fintype.card_pos (α := e.C)
      omega
    exact le_A_of_mem (mem_realizableK_of_list _ (refine_inj e') size
      ((blocksList_two _ q).mpr (refine_blocks e' (clone_blocks e 3 h))))

end
end ElectionLift
