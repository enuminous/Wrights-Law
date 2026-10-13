import Mathlib

namespace Wright
open Set

/-- Conditional continuous-time correction law on a specified interval.
Continuity at the endpoints and derivatives on the interior are explicit. -/
theorem exponential_bound (V V' : ℝ → ℝ) (lam t : ℝ) (ht : 0 ≤ t)
    (hcont : ContinuousOn V (Icc 0 t))
    (hd : ∀ x ∈ Ioo 0 t, HasDerivAt V (V' x) x)
    (hbound : ∀ x ∈ Ioo 0 t, V' x ≤ -lam * V x) :
    V t ≤ V 0 * Real.exp (-lam * t) := by
  let W : ℝ → ℝ := fun x => Real.exp (lam*x) * V x
  have hW (x : ℝ) (hx : x ∈ Ioo 0 t) :
      HasDerivAt W (Real.exp (lam*x) * (V' x + lam*V x)) x := by
    convert (((hasDerivAt_id x).const_mul lam).exp.mul (hd x hx)) using 1 <;> dsimp [W] <;> ring
  have hmono : AntitoneOn W (Icc 0 t) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 t)
    · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).mul hcont
    · intro x hx
      rw [interior_Icc] at hx
      exact (hW x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hW x hx).deriv]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (by linarith [hbound x hx])
  have h := hmono ⟨le_rfl,ht⟩ ⟨ht,le_rfl⟩ ht
  have hprod : V t * Real.exp (lam*t) ≤ V 0 := by simpa [W, mul_comm] using h
  have hdiv := (le_div_iff₀ (Real.exp_pos (lam*t))).mpr hprod
  simpa [neg_mul, Real.exp_neg, div_eq_mul_inv] using hdiv

/-- The strictly positive decay rate is needed for asymptotic decay, not for
the integrating-factor inequality itself. -/
theorem exponential_rate_tends_to_zero (lam : ℝ) (hlam : 0 < lam) :
    Filter.Tendsto (fun t : ℝ => Real.exp (-lam*t)) Filter.atTop (nhds 0) := by
  exact Real.tendsto_exp_atBot.comp (Filter.Tendsto.const_mul_atTop_of_neg (neg_neg_of_pos hlam) Filter.tendsto_id)

/-- Exact sufficient decrease implied by the descent lemma's quadratic model.
This theorem explicitly takes that model as a hypothesis. -/
theorem descent_of_quadratic_upper_bound (Jold Jnew L α g2 : ℝ)
    (hL : 0 < L) (hα : 0 < α) (hαL : α < 2/L) (hg : 0 ≤ g2)
    (hmodel : Jnew ≤ Jold - α*g2 + (L/2)*α^2*g2) : Jnew ≤ Jold := by
  have hαL' : α*L < 2 := (lt_div_iff₀ hL).mp hαL
  have hc : 0 ≤ α * (1 - L*α/2) := mul_nonneg hα.le (by nlinarith)
  have hp := mul_nonneg hc hg
  nlinarith

theorem strict_descent_of_quadratic_upper_bound (Jold Jnew L α g2 : ℝ)
    (hL : 0 < L) (hα : 0 < α) (hαL : α < 2/L) (hg : 0 < g2)
    (hmodel : Jnew ≤ Jold - α*g2 + (L/2)*α^2*g2) : Jnew < Jold := by
  have hαL' : α*L < 2 := (lt_div_iff₀ hL).mp hαL
  have hc : 0 < α * (1 - L*α/2) := mul_pos hα (by nlinarith)
  have hp := mul_pos hc hg
  nlinarith

theorem relational_effect_zero_iff {E : Type*} [NormedAddCommGroup E]
    (coupled baseline : E) (ε : ℝ) (hε : 0 < ε) :
    ‖coupled - baseline‖ / (‖baseline‖ + ε) = 0 ↔ coupled = baseline := by
  have hd : ‖baseline‖ + ε ≠ 0 := ne_of_gt (by positivity)
  simp [div_eq_zero_iff, hd, norm_eq_zero, sub_eq_zero]

end Wright
