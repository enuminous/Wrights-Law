import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

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
    exact (((hasDerivAt_id x).const_mul lam).exp.mul (hd x hx)).congr_deriv (by dsimp; ring)
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

/-- The quadratic upper model follows from a genuine Lipschitz gradient.
The proof differentiates along the line segment; it does not assume the model. -/
theorem quadratic_upper_bound_of_lipschitz_gradient
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (g : E → E) (L : ℝ)
    (hg : ∀ z, HasGradientAt f (g z) z)
    (hLip : ∀ u v, ‖g u - g v‖ ≤ L * ‖u - v‖) (x d : E) :
    f (x + d) ≤ f x + inner ℝ (g x) d + (L / 2) * ‖d‖ ^ 2 := by
  let F : ℝ → ℝ := fun t =>
    f (x + t • d) - f x - t * inner ℝ (g x) d - (L / 2) * t ^ 2 * ‖d‖ ^ 2
  have hline (t : ℝ) : HasDerivAt (fun s : ℝ => f (x + s • d))
      (inner ℝ (g (x + t • d)) d) t := by
    have hp : HasDerivAt (fun s : ℝ => x + s • d) d t := by
      simpa using ((hasDerivAt_id t).smul_const d).const_add x
    simpa using (hg (x + t • d)).hasFDerivAt.comp_hasDerivAt t hp
  have hF (t : ℝ) : HasDerivAt F
      (inner ℝ (g (x + t • d) - g x) d - L * t * ‖d‖ ^ 2) t := by
    apply ((((hline t).sub_const (f x)).sub
      ((hasDerivAt_id t).mul_const (inner ℝ (g x) d))).sub
      ((((hasDerivAt_id t).pow 2).const_mul (L / 2)).mul_const (‖d‖ ^ 2))).congr_deriv
    simp only [inner_sub_left, id_eq]
    ring
  have hmono : AntitoneOn F (Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · exact (continuous_iff_continuousAt.mpr fun t => (hF t).continuousAt).continuousOn
    · intro t ht
      exact (hF t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hF t).deriv]
      have hnorm : ‖g (x + t • d) - g x‖ ≤ L * (t * ‖d‖) := by
        simpa [norm_smul, Real.norm_eq_abs, abs_of_pos ht.1] using hLip (x + t • d) x
      have hb := (real_inner_le_norm (g (x + t • d) - g x) d).trans
        (mul_le_mul_of_nonneg_right hnorm (norm_nonneg d))
      nlinarith
  have h := hmono (by simp) (by simp) (by norm_num : (0 : ℝ) ≤ 1)
  simpa [F, add_comm, add_left_comm, add_assoc] using h

/-- A gradient step obeys the exact quadratic decrease estimate. -/
theorem gradient_step_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (g : E → E) (L α : ℝ)
    (hg : ∀ z, HasGradientAt f (g z) z)
    (hLip : ∀ u v, ‖g u - g v‖ ≤ L * ‖u - v‖) (x : E) :
    f (x - α • g x) ≤ f x - α * ‖g x‖ ^ 2 + (L / 2) * α ^ 2 * ‖g x‖ ^ 2 := by
  have h := quadratic_upper_bound_of_lipschitz_gradient f g L hg hLip x (-α • g x)
  simpa [neg_smul, sub_eq_add_neg, inner_smul_right, real_inner_self_eq_norm_sq,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, neg_mul, add_assoc, mul_assoc] using h

/-- The gradient step is nonincreasing, including at a stationary point. -/
theorem gradient_step_descent
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (g : E → E) (L α : ℝ)
    (hg : ∀ z, HasGradientAt f (g z) z)
    (hLip : ∀ u v, ‖g u - g v‖ ≤ L * ‖u - v‖)
    (hL : 0 < L) (hα : 0 < α) (hαL : α < 2 / L) (x : E) :
    f (x - α • g x) ≤ f x := by
  exact descent_of_quadratic_upper_bound _ _ L α _ hL hα hαL
    (sq_nonneg _) (gradient_step_bound f g L α hg hLip x)

/-- Strict decrease additionally requires a nonzero gradient. -/
theorem gradient_step_strict_descent
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (g : E → E) (L α : ℝ)
    (hg : ∀ z, HasGradientAt f (g z) z)
    (hLip : ∀ u v, ‖g u - g v‖ ≤ L * ‖u - v‖)
    (hL : 0 < L) (hα : 0 < α) (hαL : α < 2 / L) (x : E) (hx : g x ≠ 0) :
    f (x - α • g x) < f x := by
  exact strict_descent_of_quadratic_upper_bound _ _ L α _ hL hα hαL
    (sq_pos_of_pos (norm_pos_iff.mpr hx)) (gradient_step_bound f g L α hg hLip x)

/-- The first-order supporting inequality is derived from convexity. -/
theorem convex_gradient_support
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (x y grad : E) (hf : ConvexOn ℝ univ f)
    (hg : HasGradientAt f grad x) : f x + inner ℝ grad (y - x) ≤ f y := by
  have hc : ConvexOn ℝ univ (fun t : ℝ => f (x + t • (y - x))) := by
    simpa [Function.comp_def, AffineMap.lineMap_apply_module', add_comm] using
      hf.comp_affineMap (AffineMap.lineMap x y)
  have hp : HasDerivAt (fun t : ℝ => x + t • (y - x)) (y - x) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (y - x)).const_add x
  have hg0 : HasGradientAt f grad (x + (0 : ℝ) • (y - x)) := by simpa using hg
  have hd : HasDerivAt (fun t : ℝ => f (x + t • (y - x)))
      (inner ℝ grad (y - x)) 0 := by
    simpa using hg0.hasFDerivAt.comp_hasDerivAt 0 hp
  have hs := hc.le_slope_of_hasDerivAt (by simp) (by simp) (by norm_num : (0 : ℝ) < 1) hd
  simp [slope] at hs
  linarith

/-- KKT sufficiency for differentiable convex objectives and finitely many
convex inequality constraints. This does not assert existence of multipliers. -/
theorem kkt_sufficient
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [Fintype ι] (f : E → ℝ) (c : ι → E → ℝ) (x grad : E) (gc : ι → E) (μ : ι → ℝ)
    (hf : ConvexOn ℝ univ f) (hc : ∀ i, ConvexOn ℝ univ (c i))
    (hdf : HasGradientAt f grad x) (hdc : ∀ i, HasGradientAt (c i) (gc i) x)
    (hμ : ∀ i, 0 ≤ μ i) (hfeasible : ∀ i, c i x ≤ 0)
    (hcomp : ∀ i, μ i * c i x = 0) (hstation : grad + ∑ i, μ i • gc i = 0) :
    (∀ i, c i x ≤ 0) ∧ ∀ y, (∀ i, c i y ≤ 0) → f x ≤ f y := by
  refine ⟨hfeasible, ?_⟩
  intro y hy
  have hterm (i : ι) : μ i * inner ℝ (gc i) (y - x) ≤ 0 := by
    have hs := convex_gradient_support (c i) x y (gc i) (hc i) (hdc i)
    have hm := mul_le_mul_of_nonneg_left hs (hμ i)
    have hz := mul_nonpos_of_nonneg_of_nonpos (hμ i) (hy i)
    nlinarith [hcomp i]
  have hsum : (∑ i, μ i * inner ℝ (gc i) (y - x)) ≤ 0 :=
    Finset.sum_nonpos fun i _ => hterm i
  have hs : inner ℝ grad (y - x) + ∑ i, μ i * inner ℝ (gc i) (y - x) = 0 := by
    have h := congrArg (fun v => inner ℝ v (y - x)) hstation
    simpa [inner_add_left, sum_inner, inner_smul_left] using h
  have hf' := convex_gradient_support f x y grad hf hdf
  linarith

end Wright
