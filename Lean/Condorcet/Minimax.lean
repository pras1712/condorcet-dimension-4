import Condorcet.Opposition
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Lattice.Fold

namespace ElectionLift
noncomputable section
open Finset

/-- Maximal opposition to one committee. In an election with no outsider we use zero. -/
def opposition (e : Election) (S : Finset e.C) : ℝ := by
  classical
  let outsiders := univ \ S
  exact if h : outsiders.Nonempty then outsiders.sup' h (fun t => jointSupport e t S.toList) else 0

theorem le_opposition_iff (e : Election) (S : Finset e.C) (size : S.card < Fintype.card e.C) (q : ℝ) :
    q ≤ opposition e S ↔ ∃ h ∉ S, q ≤ jointSupport e h S.toList := by
  classical
  obtain ⟨h,hh⟩ := outside_exists e S size
  have H : (univ \ S).Nonempty := ⟨h,by simpa using hh⟩
  simp [opposition,H,Finset.le_sup'_iff]

/-- The minimum over all committees of their maximal opposition. -/
def electionValue (e : Election) (k : ℕ) (size : k < Fintype.card e.C) : ℝ := by
  classical
  exact ((univ : Finset e.C).powersetCard k).inf'
    (Finset.powersetCard_nonempty.mpr (by simpa using size.le)) (opposition e)

theorem le_electionValue_iff (e : Election) (k : ℕ) (size : k < Fintype.card e.C) (q : ℝ) :
    q ≤ electionValue e k size ↔
    ∀ S : Finset e.C, S.card = k → ∃ h ∉ S, q ≤ jointSupport e h S.toList := by
  classical
  simp only [electionValue, Finset.le_inf'_iff, Finset.mem_powersetCard, Finset.subset_univ,
    true_and]
  exact forall_congr' fun S => forall_congr' fun hs => le_opposition_iff e S (hs ▸ size) q

def electionValues (k : ℕ) : Set ℝ := {x | ∃ (e : Election) (_ : ∀ v, Function.Injective (e.rank v))
  (size : k < Fintype.card e.C), x = electionValue e k size}

theorem value_mem_realizable (e : Election) (strict : ∀ v, Function.Injective (e.rank v))
    {k : ℕ} (size : k < Fintype.card e.C) : electionValue e k size ∈ realizableK k :=
  ⟨e,strict,size,(le_electionValue_iff e k size _).mp le_rfl⟩

theorem values_bdd (k : ℕ) : BddAbove (electionValues k) := by
  refine ⟨1,?_⟩
  rintro x ⟨e,strict,size,rfl⟩
  exact realizableK_le_one (value_mem_realizable _ strict size)

/-- Identifies the attainable-threshold definition with the paper's sup-min-max expression. -/
theorem A_eq_sup_min_max (k : ℕ) : A k = sSup (electionValues k) := by
  refine le_antisymm (csSup_le ⟨0,zero_mem_realizableK k⟩ ?_) ?_
  · rintro q ⟨e,strict,size,H⟩
    exact ((le_electionValue_iff e k size q).mpr H).trans
      (le_csSup (values_bdd k) (show electionValue e k size ∈ electionValues k from ⟨_,strict,size,rfl⟩))
  · obtain ⟨e,strict,size,_⟩ := zero_mem_realizableK k
    apply csSup_le (show (electionValues k).Nonempty from ⟨_,e,strict,size,rfl⟩)
    rintro _ ⟨f,s,c,rfl⟩
    exact le_A_of_mem (value_mem_realizable f s c)

/-- Best coverage across committees is one minus the minimum opposition. -/
def electionCoverages (k : ℕ) : Set ℝ := (fun x : ℝ => 1-x) '' electionValues k

/-- The infimum of the finite-election coverage values is the stated C. -/
theorem C_eq_inf_best_coverage (k : ℕ) : C k = sInf (electionCoverages k) := by
  obtain ⟨e,strict,size,_⟩ := zero_mem_realizableK k
  have nonempty : (electionValues k).Nonempty := ⟨_,e,strict,size,rfl⟩
  have bounded : BddBelow (electionCoverages k) := by
    refine ⟨0,?_⟩
    rintro _ ⟨x,⟨f,s,c,rfl⟩,rfl⟩
    exact sub_nonneg.mpr (realizableK_le_one (value_mem_realizable f s c))
  unfold C
  rw [A_eq_sup_min_max]
  apply le_antisymm
  · apply le_csInf (nonempty.image _)
    rintro _ ⟨x,hx,rfl⟩
    exact sub_le_sub_left (le_csSup (values_bdd k) hx) 1
  · have hsup : sSup (electionValues k) ≤ 1 - sInf (electionCoverages k) := by
      apply csSup_le nonempty
      intro x hx
      have h := csInf_le bounded (show 1-x ∈ electionCoverages k from ⟨x,hx,rfl⟩)
      linarith
    linarith

def CoverageGuarantee (k : ℕ) (b : ℝ) : Prop :=
  ∀ (e : Election), (∀ v, Function.Injective (e.rank v)) → k < Fintype.card e.C →
  ∃ S : Finset e.C, S.card = k ∧ ∀ h ∉ S, b ≤ 1 - jointSupport e h S.toList

/-- The lower coverage guarantee is attained in every election, even at the endpoint. -/
theorem coverage_guarantee_iff (k : ℕ) (b : ℝ) : CoverageGuarantee k b ↔ b ≤ C k := by
  classical
  constructor
  · intro H
    have hA : A k ≤ 1-b := by
      apply csSup_le ⟨0,zero_mem_realizableK k⟩
      rintro q ⟨e,strict,size,bad⟩
      obtain ⟨S,card,good⟩ := H e strict size
      obtain ⟨h,nh,hh⟩ := bad S card
      linarith [good h nh]
    unfold C
    linarith
  · intro hb e strict size
    have N : ((univ : Finset e.C).powersetCard k).Nonempty := Finset.powersetCard_nonempty.mpr (by simpa using size.le)
    obtain ⟨S,hS,eq⟩ := Finset.exists_mem_eq_inf' N (opposition e)
    have card := (Finset.mem_powersetCard.mp hS).2
    refine ⟨S,card,fun h nh => ?_⟩
    have ha := le_A_of_mem (value_mem_realizable e strict size)
    have bound : jointSupport e h S.toList ≤ opposition e S :=
      (le_opposition_iff e S (card ▸ size) _).mpr ⟨h,nh,le_rfl⟩
    change electionValue e k size = opposition e S at eq
    unfold C at hb
    linarith

end
end ElectionLift
