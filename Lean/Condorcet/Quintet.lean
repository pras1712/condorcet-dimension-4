import Condorcet.Dimension
import Condorcet.Quantile
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-! The election-theoretic part of Ramakrishnan's five-candidate proof. An iid
committee and its assigned challenger have the same one-candidate marginal at a
fixed point. No independence between the challenger and its committee is used. -/
namespace ElectionLift
noncomputable section
open Finset
open scoped BigOperators

/-- A stationary law for each response map on ordered five-tuples. -/
def HasQuintetStationary (C : Type) [Fintype C] : Prop := by
  classical
  exact ∀ f : (Fin 5 → C) → C, ∃ p : C → ℝ, (∀ c, 0 ≤ p c) ∧ (∑ c, p c) = 1 ∧
    ∀ c, (∑ s : Fin 5 → C, if f s = c then ∏ i, p (s i) else 0) = p c

private theorem iid_mass {C : Type} [Fintype C] (p : C → ℝ) :
    (∑ s : Fin 5 → C, ∏ i, p (s i)) = (∑ c, p c)^5 := by
  simpa using (Fintype.prod_sum (ι:=Fin 5) (κ:=fun _ => C) (fun _ c => p c)).symm

private theorem iid_event {C : Type} [Fintype C] (p : C → ℝ)
    (P : C → Prop) [DecidablePred P] :
    (∑ s : Fin 5 → C, if ∀ i, P (s i) then ∏ i, p (s i) else 0) =
      (∑ c, if P c then p c else 0)^5 := by
  rw [←iid_mass (fun c => if P c then p c else 0)]
  apply sum_congr rfl
  intro s _
  by_cases h : ∀ i, P (s i)
  · simp [h]
  · simp only [if_neg h]
    push Not at h
    obtain ⟨i,hi⟩ := h
    exact (Finset.prod_eq_zero (mem_univ i) (by simp [hi])).symm

private theorem pushforward_sum {S C : Type} [Fintype S] [Fintype C] [DecidableEq C]
    (f : S → C) (w : S → ℝ) (p : C → ℝ)
    (stat : ∀ c, (∑ s, if f s = c then w s else 0) = p c)
    (P : C → Prop) [DecidablePred P] :
    (∑ s, if P (f s) then w s else 0) = ∑ c, if P c then p c else 0 := by
  calc
    _ = ∑ s, ∑ c, if f s = c then (if P c then w s else 0) else 0 := by simp
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro c _
      by_cases hc : P c <;> simp only [hc,if_true,if_false,ite_self,Finset.sum_const_zero,stat]

private theorem quintet_ballot_bound (e : Election)
    (strict : ∀ v, Function.Injective (e.rank v)) (v : e.V) (p : e.C → ℝ)
    (hp : ∀ c, 0 ≤ p c) (hs : ∑ c, p c = 1) (f : (Fin 5 → e.C) → e.C)
    [DecidableEq e.C]
    (stat : ∀ c, (∑ s : Fin 5 → e.C, if f s = c then ∏ i, p (s i) else 0) = p c) :
    (∑ s : Fin 5 → e.C, if ∀ i, e.rank v (f s) < e.rank v (s i)
      then ∏ i, p (s i) else 0) ≤ 1/3+(2/3:ℝ)^5 := by
  obtain ⟨c,above,below⟩ := ballot_quantile e strict v p hp hs
  let w := fun s : Fin 5 → e.C => ∏ i, p (s i)
  have nonneg (s) : 0 ≤ w s := Finset.prod_nonneg (fun i _ => hp (s i))
  have comp (s : Fin 5 → e.C) : (∀ i, e.rank v (f s) < e.rank v (s i)) →
      e.rank v (f s) < e.rank v c ∨ ∀ i, e.rank v c < e.rank v (s i) := by
    intro h
    by_cases h' : e.rank v (f s) < e.rank v c
    · exact Or.inl h'
    · exact Or.inr (fun i => lt_of_le_of_lt (le_of_not_gt h') (h i))
  calc
    _ ≤ ∑ s : Fin 5 → e.C, ((if e.rank v (f s) < e.rank v c then w s else 0) +
        (if ∀ i, e.rank v c < e.rank v (s i) then w s else 0)) := by
      apply sum_le_sum
      intro s _
      change (if _ then w s else 0) ≤ _
      have disj := comp s
      have pos := nonneg s
      split_ifs <;> simp_all
    _ = (∑ x : e.C, if e.rank v x < e.rank v c then p x else 0) +
        (∑ x : e.C, if e.rank v c < e.rank v x then p x else 0)^5 := by
      rw [Finset.sum_add_distrib,pushforward_sum f w p stat (fun x => e.rank v x < e.rank v c),
        iid_event p (fun x => e.rank v c < e.rank v x)]
    _ ≤ _ := add_le_add above (pow_le_pow_left₀ (Finset.sum_nonneg fun x _ => by
      split <;> simp [hp]) below 5)

private theorem support_image (e : Election) (f : (Fin 5 → e.C) → e.C) (s : Fin 5 → e.C)
    [DecidableEq e.C] : jointSupport e (f s) (univ.image s).toList =
    mean (fun v => if ∀ i, e.rank v (f s) < e.rank v (s i) then 1 else 0) := by
  unfold jointSupport
  apply congrArg mean
  funext v
  simp [ind]

private theorem average_swap {S V : Type} [Fintype S] [Fintype V]
    (w : S → ℝ) (P : S → V → Prop) [∀ s, DecidablePred (P s)] :
    (∑ s, w s * mean (fun v => if P s v then 1 else 0)) =
      mean (fun v => ∑ s, if P s v then w s else 0) := by
  simp only [mean,←mul_div_assoc, Finset.mul_sum,←Finset.sum_div]
  rw [Finset.sum_comm]
  apply congrArg (fun x : ℝ => x/(Fintype.card V:ℝ))
  apply sum_congr rfl; intro v _
  apply sum_congr rfl; intro s _
  by_cases h : P s v <;> simp [h]

/-- Every strict election has a majority-winning set of size at most five once
the response map admits a stationary law, as provided by Brouwer's theorem. -/
theorem quintet_of_stationarity (e : Election) (strict : ∀ v, Function.Injective (e.rank v))
    (fixed : HasQuintetStationary e.C) : dimension e ≤ 5 := by
  classical
  by_contra! large
  have bad (s : Fin 5 → e.C) : ∃ h, (1:ℝ)/2 ≤ jointSupport e h (univ.image s).toList := by
    have small : (univ.image s).card ≤ 5 := by simpa using (Finset.card_image_le (f:=s) (s:=univ))
    have lose : ¬ Winning e (univ.image s) := fun H => (not_le.mpr large)
      ((dimension_le_iff e 5).mpr ⟨_,small,H⟩)
    unfold Winning at lose
    push Not at lose
    obtain ⟨h,_,hs⟩ := lose
    exact ⟨h,hs⟩
  choose f hf using bad
  obtain ⟨p,hp,hs,stat⟩ := fixed f
  let w := fun s : Fin 5 → e.C => ∏ i, p (s i)
  have wn : ∀ s, 0 ≤ w s := fun s => Finset.prod_nonneg (fun i _ => hp (s i))
  have wt : ∑ s, w s = 1 := by change (∑ s : Fin 5 → e.C, ∏ i, p (s i)) = 1; rw [iid_mass,hs]; norm_num
  let P := fun (s : Fin 5 → e.C) (v : e.V) => ∀ i, e.rank v (f s) < e.rank v (s i)
  have bound : (1:ℝ)/2 ≤ 1/3+(2/3:ℝ)^5 := calc
    (1:ℝ)/2 = ∑ s, w s * (1/2) := by rw [←Finset.sum_mul,wt]; ring
    _ ≤ ∑ s, w s * mean (fun v => if P s v then 1 else 0) := by
      apply sum_le_sum
      intro s _
      exact mul_le_mul_of_nonneg_left ((hf s).trans_eq (support_image e f s)) (wn s)
    _ = _ := average_swap w P
    _ ≤ mean (fun _ : e.V => 1/3+(2/3:ℝ)^5) :=
      mean_mono (fun v => quintet_ballot_bound e strict v p hp hs f stat)
    _ = _ := mean_const _
  norm_num at bound

end
end ElectionLift
