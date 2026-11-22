import Condorcet.Opposition
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Order.LiminfLimsup

namespace ElectionLift
open Filter Topology

/-- The extended real liminf permits divergence to positive infinity. -/
theorem liminf_of_coverage_bound (t : ℝ) (H : ∀ n : ℕ, 2 ≤ n → C n ≤ 1-t/(n+1)) :
    (t : EReal) ≤ liminf (fun n : ℕ => ((n*(1-C n):ℝ) : EReal)) atTop := by
  let g : ℕ → ℝ := fun n => t * (1-1/((n:ℝ)+1))
  have hg : Tendsto g atTop (𝓝 t) := by
    have H₁ : Tendsto (fun n : ℕ => (1:ℝ)-1/((n:ℝ)+1)) atTop (𝓝 (1-0)) :=
      tendsto_const_nhds.sub tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [g] using (tendsto_const_nhds (x:=t)).mul H₁
  have hg' : Tendsto (fun n => (g n : EReal)) atTop (𝓝 (t : EReal)) :=
    continuous_coe_real_ereal.continuousAt.tendsto.comp hg
  rw [←hg'.liminf_eq]
  refine liminf_le_liminf ?_
  filter_upwards [eventually_ge_atTop (2:ℕ)] with n hn
  apply EReal.coe_le_coe_iff.mpr
  have upper := H n hn
  have low : t/((n:ℝ)+1) ≤ 1-C n := by linarith
  calc
    g n = n*(t/((n:ℝ)+1)) := by dsimp [g]; field_simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left low (by positivity)

end ElectionLift
