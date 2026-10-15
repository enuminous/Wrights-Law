import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Tactic.FunProp
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


/-- A convex program satisfying Slater's condition has Lagrange multipliers.
This separation argument establishes their existence; no multiplier premise
or first-order optimality condition is assumed. -/
theorem convex_slater_multipliers
    {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Fintype ι]
    (f : E → ℝ) (c : ι → E → ℝ) (x : E)
    (hf : ConvexOn ℝ univ f) (hc : ∀ i, ConvexOn ℝ univ (c i))
    (hx : ∀ i, c i x ≤ 0)
    (hmin : ∀ y, (∀ i, c i y ≤ 0) → f x ≤ f y)
    (hslater : ∃ z, ∀ i, c i z < 0) :
    ∃ μ : ι → ℝ, (∀ i, 0 ≤ μ i) ∧ (∀ i, μ i * c i x = 0) ∧
      ∀ y, f x ≤ f y + ∑ i, μ i * c i y := by
  classical
  let V : E → Option ι → ℝ := fun y j => j.elim (f y - f x) (fun i => c i y)
  have hV (j : Option ι) : ConvexOn ℝ univ (fun y => V y j) := by
    cases j with
    | none => exact hf.sub_const _
    | some i => exact hc i
  let U : Set (Option ι → ℝ) := {v | ∃ y, ∀ j, V y j < v j}
  have hopen : IsOpen U := by
    have heq : U = ⋃ y : E, ⋂ j : Option ι, {v | V y j < v j} := by
      ext v
      simp [U]
    rw [heq]
    exact isOpen_iUnion fun y => isOpen_iInter_of_finite fun j =>
      isOpen_lt continuous_const (continuous_apply j)
  have hconv : Convex ℝ U := by
    intro a ha b hb s t hs ht hst
    obtain ⟨y, hy⟩ := ha
    obtain ⟨z, hz⟩ := hb
    refine ⟨s • y + t • z, fun j => ?_⟩
    have hj := (hV j).2 (mem_univ y) (mem_univ z) hs ht hst
    change V (s • y + t • z) j < s * a j + t * b j
    change V (s • y + t • z) j ≤ s * V y j + t * V z j at hj
    rcases lt_or_eq_of_le hs with hs' | hs'
    · exact hj.trans_lt (add_lt_add_of_lt_of_le
        (mul_lt_mul_of_pos_left (hy j) hs') (mul_le_mul_of_nonneg_left (hz j).le ht))
    · have hs0 : s = 0 := hs'.symm
      have ht1 : t = 1 := by linarith
      simpa [hs0, ht1] using hz j
  have hzero : (0 : Option ι → ℝ) ∉ U := by
    rintro ⟨y, hy⟩
    have hfeas : ∀ i, c i y ≤ 0 := fun i => (hy (some i)).le
    have hobj := hy none
    have := hmin y hfeas
    change f y - f x < 0 at hobj
    linarith
  obtain ⟨L, hL⟩ := geometric_hahn_banach_point_open hconv hopen hzero
  have hpos : ∀ v ∈ U, 0 < L v := by simpa using hL
  have hbound (y : E) (v : Option ι → ℝ) (hv : ∀ j, V y j ≤ v j) : 0 ≤ L v := by
    have hcont : Continuous (fun t : ℝ => L (v + t • (fun _ => (1 : ℝ)))) := by
      fun_prop
    have hlim := hcont.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
    have hevent : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 ≤ L (v + t • (fun _ => (1 : ℝ))) :=
      Filter.eventually_of_mem self_mem_nhdsWithin fun t ht =>
        (hpos _ ⟨y, fun j => by
          change V y j < v j + t * 1
          have := hv j
          change 0 < t at ht
          linarith⟩).le
    simpa using le_of_tendsto hlim hevent
  let w : Option ι → ℝ := fun j => L (Pi.single j 1)
  have hw (j : Option ι) : 0 ≤ w j := by
    by_contra h
    have hn : w j < 0 := lt_of_not_ge h
    let b := V x
    have hb : 0 ≤ L b := hbound x b fun _ => le_rfl
    let t := (L b + 1) / (-w j)
    have ht : 0 ≤ t := div_nonneg (by linarith) (by linarith)
    have hb' : 0 ≤ L (b + t • Pi.single j 1) := hbound x _ fun k => by
      change b k ≤ b k + t * (Pi.single j (1 : ℝ) k)
      have hp : 0 ≤ (Pi.single j (1 : ℝ) k) := by
        by_cases hk : j = k <;> simp [Pi.single_apply, hk]
      linarith [mul_nonneg ht hp]
    have htw : t * w j = -(L b + 1) := by
      dsimp [t]
      field_simp
      <;> ring
    rw [map_add, map_smul] at hb'
    change 0 ≤ L b + t * w j at hb'
    linarith
  have hrepr (v : Option ι → ℝ) : L v = ∑ j, w j * v j := by
    have hv : v = ∑ j : Option ι, v j • Pi.single j 1 := by
      ext k
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hv]
    simp [map_sum, map_smul, w, mul_comm]
  have hraw (y : E) : 0 ≤ w none * (f y - f x) + ∑ i, w (some i) * c i y := by
    have h := hbound y (V y) fun _ => le_rfl
    simpa [hrepr, V, Fintype.sum_option, add_comm] using h
  have hsome : w none ≠ 0 ∨ ∃ i, w (some i) ≠ 0 := by
    by_contra h
    push_neg at h
    have htest := hpos (fun j => V x j + 1) ⟨x, fun j => by linarith⟩
    rw [hrepr] at htest
    simp [Fintype.sum_option, h.1, h.2] at htest
  obtain ⟨z, hz⟩ := hslater
  have hα : 0 < w none := by
    rcases (hw none).eq_or_lt with hα | hα
    · have hα0 : w none = 0 := hα.symm
      obtain ⟨i, hi⟩ := hsome.resolve_left hα0
      have hi0 : 0 < w (some i) := lt_of_le_of_ne (hw _) (Ne.symm hi)
      have hsum : (∑ j, w (some j) * c j z) < 0 :=
        Finset.sum_neg' (fun j _ => mul_nonpos_of_nonneg_of_nonpos (hw _) (hz j).le)
          ⟨i, Finset.mem_univ _, mul_neg_of_pos_of_neg hi0 (hz i)⟩
      have := hraw z
      simp only [hα0, zero_mul, zero_add] at this
      linarith
    · exact hα
  have hcomp : ∀ i, w (some i) * c i x = 0 := by
    have hnonpos (i : ι) : w (some i) * c i x ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (hw _) (hx i)
    have hzsum : (∑ i, w (some i) * c i x) = 0 :=
      le_antisymm (Finset.sum_nonpos fun i _ => hnonpos i) (by simpa using hraw x)
    exact fun i => (Finset.sum_eq_zero_iff_of_nonpos (fun j _ => hnonpos j)).mp
      hzsum i (Finset.mem_univ _)
  refine ⟨fun i => w (some i) / w none, fun i => div_nonneg (hw _) hα.le, ?_, ?_⟩
  · intro i
    rw [div_mul_eq_mul_div, hcomp, zero_div]
  · intro y
    have hmul : w none * (f y - f x + ∑ i, (w (some i) / w none) * c i y) =
        w none * (f y - f x) + ∑ i, w (some i) * c i y := by
      rw [mul_add, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      field_simp
    have hnonneg : 0 ≤ f y - f x + ∑ i, (w (some i) / w none) * c i y :=
      (mul_nonneg_iff_of_pos_left hα).mp (hmul ▸ hraw y)
    linarith

/-- KKT necessity for the same convex inequality problem as kkt_sufficient,
with Slater's condition as the explicit constraint qualification. -/
theorem kkt_necessary_slater
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [Fintype ι] (f : E → ℝ) (c : ι → E → ℝ) (x grad : E) (gc : ι → E)
    (hf : ConvexOn ℝ univ f) (hc : ∀ i, ConvexOn ℝ univ (c i))
    (hdf : HasGradientAt f grad x) (hdc : ∀ i, HasGradientAt (c i) (gc i) x)
    (hx : ∀ i, c i x ≤ 0)
    (hmin : ∀ y, (∀ i, c i y ≤ 0) → f x ≤ f y)
    (hslater : ∃ z, ∀ i, c i z < 0) :
    ∃ μ : ι → ℝ, (∀ i, 0 ≤ μ i) ∧ (∀ i, μ i * c i x = 0) ∧
      grad + ∑ i, μ i • gc i = 0 := by
  obtain ⟨μ, hμ, hcomp, hlag⟩ := convex_slater_multipliers f c x hf hc hx hmin hslater
  refine ⟨μ, hμ, hcomp, ?_⟩
  let d := grad + ∑ i, μ i • gc i
  let q : ℝ → ℝ := fun t => f (x + t • d) + ∑ i, μ i * c i (x + t • d)
  have hp : HasDerivAt (fun t : ℝ => x + t • d) d 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add x
  have hdf0 : HasGradientAt f grad (x + (0 : ℝ) • d) := by simpa using hdf
  have hdc0 (i : ι) : HasGradientAt (c i) (gc i) (x + (0 : ℝ) • d) := by
    simpa using hdc i
  have hq : HasDerivAt q (inner ℝ grad d + ∑ i, μ i * inner ℝ (gc i) d) 0 := by
    exact (hdf0.hasFDerivAt.comp_hasDerivAt 0 hp).add
      (HasDerivAt.fun_sum fun i _ => ((hdc0 i).hasFDerivAt.comp_hasDerivAt 0 hp).const_mul (μ i))
  have hminq : IsLocalMin q 0 := by
    apply Filter.Eventually.of_forall
    intro t
    simpa [q, hcomp] using hlag (x + t • d)
  have hz := hminq.hasDerivAt_eq_zero hq
  have hd : inner ℝ d d = 0 := by
    simpa [d, inner_add_left, sum_inner, inner_smul_left] using hz
  exact (inner_self_eq_zero.mp hd)

/-- Necessary and sufficient KKT conditions for a convex differentiable
inequality program with a strictly feasible point. -/
theorem kkt_iff_slater
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [Fintype ι] (f : E → ℝ) (c : ι → E → ℝ) (x grad : E) (gc : ι → E)
    (hf : ConvexOn ℝ univ f) (hc : ∀ i, ConvexOn ℝ univ (c i))
    (hdf : HasGradientAt f grad x) (hdc : ∀ i, HasGradientAt (c i) (gc i) x)
    (hx : ∀ i, c i x ≤ 0) (hslater : ∃ z, ∀ i, c i z < 0) :
    (∀ y, (∀ i, c i y ≤ 0) → f x ≤ f y) ↔
      ∃ μ : ι → ℝ, (∀ i, 0 ≤ μ i) ∧ (∀ i, μ i * c i x = 0) ∧
        grad + ∑ i, μ i • gc i = 0 := by
  constructor
  · intro hmin
    exact kkt_necessary_slater f c x grad gc hf hc hdf hdc hx hmin hslater
  · rintro ⟨μ, hμ, hcomp, hstation⟩
    exact (kkt_sufficient f c x grad gc μ hf hc hdf hdc hμ hx hcomp hstation).2

end Wright
