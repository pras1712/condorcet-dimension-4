import Condorcet.Theorem
import Condorcet.Quintet
import Condorcet.Stationary

namespace ElectionLift

/-- Song, Nguyen and Lin's five-seat upper bound, using Ramakrishnan's proof. -/
theorem five_suffice (e : Election) (s : ∀ v, Function.Injective (e.rank v)) :
    dimension e ≤ 5 := by
  classical
  exact quintet_of_stationarity e s (fun f => stationary_reply f)

/-- The largest Condorcet dimension of a finite strict election is four or five. -/
theorem four_or_five :
    ∃ d ∈ ({4,5} : Finset ℕ),
      (∃ e : Election, (∀ v, Function.Injective (e.rank v)) ∧ dimension e = d) ∧
      ∀ e : Election, (∀ v, Function.Injective (e.rank v)) → dimension e ≤ d :=
  four_or_five_of_five_suffice five_suffice

end ElectionLift
