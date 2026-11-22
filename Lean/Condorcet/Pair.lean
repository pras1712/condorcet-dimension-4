import Elections
import Mathlib.Data.Finset.Lattice.Fold

/-! The self-improvement argument for pairs (Corollary 3).
A table may repeat positions to represent any rational voter weights. -/

noncomputable section
namespace ElectionLift.Grades

open Finset

variable {G : Type} [Fintype G] [Nonempty G] {n : ℕ} [NeZero n]
variable (table : Grades G n)

/-- Number of full-credit positions (tag 1) or three-way ties (tag 2). -/
def tally (a b h : G) (tag : ℕ) : ℕ :=
  countTag (fun i => kind (table.grade i h) (table.grade i a) (table.grade i b)) tag

/-- The normalized score when three-way ties receive credit `x`. -/
def pairScore (x : ℝ) (a b h : G) : ℝ :=
  (table.tally a b h 1 + (table.tally a b h 2 : ℝ) * x) / n

/-- The worst pair's best response, including pairs with repeated assignments. -/
def pairValue (x : ℝ) : ℝ :=
  (univ : Finset (G × G)).inf' univ_nonempty fun p =>
    (univ : Finset G).sup' univ_nonempty (table.pairScore x p.1 p.2)

omit [NeZero n] in
theorem response_at_value (x : ℝ) (a b : G) :
    ∃ h, table.pairValue x ≤ table.pairScore x a b h := by
  classical
  obtain ⟨h, _, hh⟩ := Finset.exists_mem_eq_sup' (s := (univ : Finset G))
    univ_nonempty (table.pairScore x a b)
  refine ⟨h, ?_⟩
  unfold pairValue
  exact (Finset.inf'_le _ (mem_univ (a,b))).trans_eq hh

omit [NeZero n] in
theorem lt_pairValue {x y : ℝ}
    (h : ∀ a b : G, ∃ c, y < table.pairScore x a b c) : y < table.pairValue x := by
  classical
  unfold pairValue
  apply (Finset.lt_inf'_iff _).mpr
  rintro ⟨a,b⟩ _
  obtain ⟨c,hc⟩ := h a b
  exact (Finset.lt_sup'_iff _).mpr ⟨c,mem_univ _,hc⟩

/-- At the supremum over strict finite elections, a grade table cannot improve the value. -/
theorem pairValue_le : table.pairValue A₂ ≤ A₂ := by
  by_contra! hgt
  apply (not_le.mpr hgt)
  apply from_grade_certificate table
  intro a b
  obtain ⟨c,hc⟩ := table.response_at_value A₂ a b
  refine ⟨c,?_⟩
  change table.tally a b c 2 < n ∧
    (table.tally a b c 1 : ℝ) ≥ table.pairValue A₂ * ((n : ℝ) - table.tally a b c 2)
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have bound : table.tally a b c 1 + table.tally a b c 2 ≤ n :=
    tag_count_bound _
  have H := (le_div_iff₀ hn).mp hc
  constructor
  · by_contra! bad
    have e : table.tally a b c 2 = n := by omega
    have z : table.tally a b c 1 = 0 := by omega
    rw [e,z] at H
    push_cast at H
    nlinarith [mul_pos (sub_pos.mpr hgt) hn]
  · have hT : 0 ≤ (table.tally a b c 2 : ℝ) := by positivity
    nlinarith [mul_nonneg hT (sub_nonneg.mpr hgt.le)]

/-- Weak form, with at least one position having a nonzero win or loss count. -/
theorem weak_pair_certificate {θ : ℝ}
    (cert : ∀ a b : G, ∃ h, table.tally a b h 2 < n ∧
      θ * ((n : ℝ) - table.tally a b h 2) ≤ table.tally a b h 1) : θ ≤ A₂ :=
  from_grade_certificate table θ cert

/-- Strict form. Finiteness of both menus makes the finite minimum strictly positive. -/
theorem strict_pair_certificate {θ : ℝ}
    (cert : ∀ a b : G, ∃ h, θ * ((n : ℝ) - table.tally a b h 2) <
      table.tally a b h 1) : θ < A₂ := by
  by_contra! bad
  apply (not_lt.mpr table.pairValue_le)
  apply table.lt_pairValue
  intro a b
  obtain ⟨h,hh⟩ := cert a b
  refine ⟨h,?_⟩
  have hn : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have bnd : table.tally a b h 1 + table.tally a b h 2 ≤ n :=
    tag_count_bound _
  have hT : (table.tally a b h 2 : ℝ) ≤ n :=
    Nat.cast_le.mpr (by omega)
  apply (lt_div_iff₀ hn).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr bad) (sub_nonneg.mpr hT)]

end ElectionLift.Grades
