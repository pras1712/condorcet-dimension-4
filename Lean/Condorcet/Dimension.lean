import Condorcet.Minimax
import Mathlib.Data.Finset.Max

namespace ElectionLift
noncomputable section
open Finset

/-- A strict majority must have a committee member above each given outsider. -/
def Winning (e : Election) (S : Finset e.C) : Prop :=
  ∀ h ∉ S, jointSupport e h S.toList < 1/2

theorem winning_mono (e : Election) {S T : Finset e.C} (hST : S ⊆ T)
    (hS : Winning e S) : Winning e T := by
  intro h nh
  exact (joint_antitone e h (fun x hx => by simpa using hST (Finset.mem_toList.mp hx))).trans_lt
    (hS h (fun hh => nh (hST hh)))

def winningSizes (e : Election) : Finset ℕ := by
  classical
  exact ((univ : Finset e.C).powerset.filter (Winning e)).image Finset.card

private theorem winSizes_ne (e : Election) : (winningSizes e).Nonempty := by
  classical
  refine ⟨Fintype.card e.C, Finset.mem_image.mpr ⟨univ,?_,Finset.card_univ⟩⟩
  simp [Winning]

def dimension (e : Election) : ℕ := (winningSizes e).min' (winSizes_ne e)

theorem dimension_le_iff (e : Election) (k : ℕ) :
    dimension e ≤ k ↔ ∃ S : Finset e.C, S.card ≤ k ∧ Winning e S := by
  classical
  constructor
  · intro h
    obtain ⟨S,hS,eq⟩ := Finset.mem_image.mp (show dimension e ∈ winningSizes e from
      Finset.min'_mem _ _)
    exact ⟨S,eq ▸ h,(Finset.mem_filter.mp hS).2⟩
  · rintro ⟨S,hs,hw⟩
    apply le_trans _ hs
    exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨S,Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.subset_univ S),hw⟩,rfl⟩)

theorem dimension_gt_of_blocked {e : Election} {k : ℕ} (size : k < Fintype.card e.C)
    (op : ∀ S : Finset e.C, S.card = k → ∃ h ∉ S, (1:ℝ)/2 ≤ jointSupport e h S.toList) :
    k < dimension e := by
  by_contra! H
  obtain ⟨S,hs,hw⟩ := (dimension_le_iff e k).mp H
  obtain ⟨T,hT,card⟩ := Finset.exists_superset_card_eq hs size.le
  obtain ⟨h,hn,hb⟩ := op T card
  exact (not_lt_of_ge hb) ((winning_mono e hT hw) h hn)

end
end ElectionLift
