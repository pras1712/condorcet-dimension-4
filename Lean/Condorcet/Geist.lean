import Condorcet.Dimension
import Mathlib.Data.Fin.VecNotation

/-! Christian Geist's six-voter election in Figure 2 of
*Finding Preference Profiles of Condorcet Dimension k via SAT* (AAMAS 2014).
Candidates a through f are represented by 0 through 5. -/

namespace ElectionLift.Historical
open Finset

/-- Rank positions (0 = first) in candidate order a,b,c,d,e,f.
The six ballots, in Geist's column order, are abcdef, bcedfa, cdfaeb,
dfbeac, eadbcf, feabcd. -/
private def geistRank : Fin 6 → Fin 6 → Fin 6 :=
  ![![0,1,2,3,4,5], ![5,0,1,3,2,4], ![3,5,0,1,4,2],
    ![4,2,5,0,3,1], ![1,3,4,2,0,5], ![2,3,4,5,1,0]]

abbrev geist : Election where
  C := Fin 6
  V := Fin 6
  height := 6
  rank v c := (geistRank v c).val
  bounded v c := (geistRank v c).isLt

theorem geist_strict (v : geist.V) : Function.Injective (geist.rank v) := by
  exact (by decide +kernel : ∀ v a b : Fin 6,
    (geistRank v a).val = (geistRank v b).val → a = b) v

private def tally (h : Fin 6) (S : Finset (Fin 6)) : ℕ :=
  (univ.filter fun v => ∀ x ∈ S, geistRank v h < geistRank v x).card

private theorem geist_fraction (h : Fin 6) (S : Finset (Fin 6)) :
    jointSupport geist h S.toList = (tally h S : ℝ)/6 := by
  classical
  simp only [jointSupport, mean, ind, Finset.sum_boole, tally, geist,
    Finset.mem_toList, Fintype.card_fin, Nat.cast_ofNat, Fin.val_fin_lt]

private theorem pair_tallies : ∀ S : Finset (Fin 6), S.card = 2 →
    (∀ h, tally h S ≤ 3) ∧ ∃ h ∉ S, tally h S = 3 := by
  decide +kernel

/-- Every pair has maximum opposition exactly three of six voters. -/
theorem geist_pair_opposition (S : Finset geist.C) (hs : S.card = 2) :
    opposition geist S = 1/2 := by
  have size : S.card < Fintype.card geist.C := by rw [hs]; decide
  obtain ⟨upper,h,hn,he⟩ := pair_tallies S hs
  apply le_antisymm
  · obtain ⟨t,_,ht⟩ := (le_opposition_iff geist S size _).mp le_rfl
    rw [geist_fraction] at ht
    have bound : (tally t S : ℝ) ≤ 3 := by exact_mod_cast upper t
    linarith
  · apply (le_opposition_iff geist S size _).mpr
    exact ⟨h,hn,by rw [geist_fraction,he]; norm_num⟩

/-- The triple a,b,c defeats each outsider by a strict majority. -/
theorem geist_winning_triple : Winning geist ({0,1,2} : Finset (Fin 6)) := by
  intro h hn
  rw [geist_fraction]
  have hc : tally h {0,1,2} ≤ 2 :=
    (by decide +kernel : ∀ h : Fin 6, tally h {0,1,2} ≤ 2) h
  have : (tally h {0,1,2} : ℝ) ≤ 2 := by exact_mod_cast hc
  linarith

theorem geist_dimension : dimension geist = 3 := by
  have lo : 2 < dimension geist := by
    apply dimension_gt_of_blocked (by decide : 2 < Fintype.card geist.C)
    intro S hs
    exact (le_opposition_iff geist S (by rw [hs]; decide) _).mp (geist_pair_opposition S hs).ge
  have hi := (dimension_le_iff geist 3).mpr
    ⟨{0,1,2}, by decide, geist_winning_triple⟩
  omega

end ElectionLift.Historical
