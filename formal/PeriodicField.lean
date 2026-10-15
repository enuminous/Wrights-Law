import Foundations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! A specified continuum realization of FOUNDATIONS.md. The invariant sector
is the real span of 1, cos(x), ..., cos(N x) on the 2π-periodic line. This is an
exact sector of the stated PDE, not a claim about all initial fields. -/
noncomputable section
open scoped BigOperators Topology
namespace Wright.PeriodicField

def rate (D gamma beta : ℝ) (i : ℕ) : ℝ :=
  if i = 0 then beta-gamma else -D * (i:ℝ)^2-gamma

def flow {N : ℕ} (D gamma beta : ℝ) (initial : Fin (N+1) → ℝ) (t : ℝ)
    (i : Fin (N+1)) : ℝ := initial i * Real.exp (rate D gamma beta i * t)

def field {N : ℕ} (coefficient : Fin (N+1) → ℝ) (x : ℝ) : ℝ :=
  ∑ i, coefficient i * Real.cos ((i:ℝ)*x)

def firstSpatial {N : ℕ} (coefficient : Fin (N+1) → ℝ) (x : ℝ) : ℝ :=
  ∑ i, -coefficient i * (i:ℝ) * Real.sin ((i:ℝ)*x)

def secondSpatial {N : ℕ} (coefficient : Fin (N+1) → ℝ) (x : ℝ) : ℝ :=
  ∑ i : Fin (N+1), -((i:ℝ)^2) * coefficient i * Real.cos ((i:ℝ)*x)

theorem flow_initial {N : ℕ} (D gamma beta : ℝ) (a : Fin (N+1) → ℝ) :
    flow D gamma beta a 0 = a := by
  funext i; simp [flow]

theorem flow_hasDerivAt {N : ℕ} (D gamma beta : ℝ) (a : Fin (N+1) → ℝ)
    (t : ℝ) (i : Fin (N+1)) :
    HasDerivAt (fun s => flow D gamma beta a s i)
      (rate D gamma beta i * flow D gamma beta a t i) t := by
  convert (((hasDerivAt_id t).const_mul (rate D gamma beta i)).exp.const_mul (a i)) using 1 <;>
    simp only [flow, id_eq] <;> ring

/-- Integrating-factor uniqueness, with the ODE as a derivative assertion. -/
theorem scalar_unique (r : ℝ) (y : ℝ → ℝ)
    (hy : ∀ t, HasDerivAt y (r*y t) t) (t : ℝ) :
    y t = y 0 * Real.exp (r*t) := by
  let z := fun s => Real.exp (-r*s) * y s
  have hz (s : ℝ) : HasDerivAt z 0 s := by
    convert ((((hasDerivAt_id s).const_mul (-r)).exp).mul (hy s)) using 1 <;>
      dsimp [z] <;> ring
  have he := is_const_of_deriv_eq_zero (fun s => (hz s).differentiableAt)
    (fun s => (hz s).deriv) t 0
  have he' : Real.exp (-r*t) * y t = y 0 := by simpa [z] using he
  have hc : Real.exp (r*t) * Real.exp (-r*t) = 1 := by
    rw [← Real.exp_add]; convert Real.exp_zero using 1 <;> ring
  have h := congrArg (fun v => Real.exp (r*t) * v) he'
  dsimp at h
  rw [← mul_assoc, hc, one_mul] at h
  simpa [mul_comm] using h

theorem flow_unique {N : ℕ} (D gamma beta : ℝ) (a : Fin (N+1) → ℝ)
    (y : ℝ → Fin (N+1) → ℝ) (hy0 : y 0 = a)
    (hy : ∀ t i, HasDerivAt (fun s => y s i) (rate D gamma beta i * y t i) t) :
    y = flow D gamma beta a := by
  funext t i
  simpa [flow, hy0] using scalar_unique (rate D gamma beta i) (fun s => y s i)
    (fun s => hy s i) t

theorem field_hasDerivAt {N : ℕ} (a : Fin (N+1) → ℝ) (x : ℝ) :
    HasDerivAt (field a) (firstSpatial a x) x := by
  apply HasDerivAt.fun_sum
  intro i _
  convert (((hasDerivAt_id x).const_mul (i:ℝ)).cos.const_mul (a i)) using 1 <;> simp only [id_eq] <;> ring

theorem firstSpatial_hasDerivAt {N : ℕ} (a : Fin (N+1) → ℝ) (x : ℝ) :
    HasDerivAt (firstSpatial a) (secondSpatial a x) x := by
  apply HasDerivAt.fun_sum
  intro i _
  convert (((hasDerivAt_id x).const_mul (i:ℝ)).sin.const_mul (-a i * (i:ℝ))) using 1 <;> simp only [id_eq] <;> ring

theorem spatial_derivatives {N : ℕ} (a : Fin (N+1) → ℝ) :
    deriv (field a) = firstSpatial a ∧ deriv (deriv (field a)) = secondSpatial a := by
  have h : deriv (field a) = firstSpatial a := funext fun x => (field_hasDerivAt a x).deriv
  exact ⟨h, by rw [h]; exact funext fun x => (firstSpatial_hasDerivAt a x).deriv⟩

/-- The real spatial functions obey the periodic boundary condition. -/
theorem field_periodic {N : ℕ} (a : Fin (N+1) → ℝ) :
    Function.Periodic (field a) (2*Real.pi) := by
  intro x
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  have hp := Real.cos_periodic.nsmul (i:ℕ)
  simpa [mul_add, nsmul_eq_mul, mul_assoc] using hp ((i:ℝ)*x)

/-- The normalized integral kernel K(x,y)=1/(2π) selects the constant mode. -/
theorem field_mean {N : ℕ} (a : Fin (N+1) → ℝ) :
    (∫ x in (0:ℝ)..(2*Real.pi), field a x) / (2*Real.pi) = a 0 := by
  have hi (i : Fin (N+1)) : IntervalIntegrable
      (fun x => a i * Real.cos ((i:ℝ)*x)) MeasureTheory.volume 0 (2*Real.pi) := by
    apply Continuous.intervalIntegrable
    fun_prop
  unfold field
  rw [intervalIntegral.integral_finset_sum (fun i _ => hi i)]
  rw [Fin.sum_univ_succ]
  have hz (i : Fin N) :
      (∫ x in (0:ℝ)..(2*Real.pi), a i.succ * Real.cos ((i.succ:ℝ)*x)) = 0 := by
    have hn : (i.succ:ℝ) ≠ 0 := by simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one]; positivity
    rw [intervalIntegral.integral_const_mul]
    have hd (x : ℝ) : HasDerivAt (fun y => Real.sin ((i.succ:ℝ)*y) / (i.succ:ℝ))
        (Real.cos ((i.succ:ℝ)*x)) x := by
      convert (((hasDerivAt_id x).const_mul (i.succ:ℝ)).sin.div_const (i.succ:ℝ)) using 1
      simp only [id_eq]
      field_simp
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 2*Real.pi)
      (fun x _ => hd x) (by apply Continuous.intervalIntegrable; fun_prop)
    rw [h]
    have hs : Real.sin ((i.succ:ℝ)*(2*Real.pi)) = 0 := by
      have hp := Real.sin_periodic.nsmul (i.succ:ℕ)
      simpa [nsmul_eq_mul] using hp 0
    rw [hs]
    simp
  simp only [hz, Finset.sum_const_zero, add_zero]
  simp [ne_of_gt Real.pi_pos]

/-- The actual field solves the diffusion/damping/nonlocal PDE with u=0. -/
theorem field_solves_pde {N : ℕ} (D gamma beta : ℝ) (a : Fin (N+1) → ℝ)
    (t x : ℝ) :
    HasDerivAt (fun s => field (flow D gamma beta a s) x)
      (D * deriv (deriv (field (flow D gamma beta a t))) x -
       gamma * field (flow D gamma beta a t) x +
       beta * ((∫ y in (0:ℝ)..(2*Real.pi), field (flow D gamma beta a t) y) / (2*Real.pi))) t := by
  have hd : HasDerivAt (fun s => field (flow D gamma beta a s) x)
      (∑ i : Fin (N+1), rate D gamma beta i * flow D gamma beta a t i * Real.cos ((i:ℝ)*x)) t := by
    simpa only [field, Finset.sum_apply] using
      HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => (flow_hasDerivAt D gamma beta a t i).mul_const (Real.cos ((i:ℝ)*x)))
  apply hd.congr_deriv
  rw [(spatial_derivatives _).2, field_mean]
  have hr (i : Fin (N+1)) :
      rate D gamma beta i * flow D gamma beta a t i * Real.cos ((i:ℝ)*x) =
      D * (-((i:ℝ)^2) * flow D gamma beta a t i * Real.cos ((i:ℝ)*x)) -
      gamma * (flow D gamma beta a t i * Real.cos ((i:ℝ)*x)) +
      (if i = 0 then beta * flow D gamma beta a t 0 else 0) := by
    by_cases h : i = 0
    · subst i
      simp [rate]
      ring
    · have hn : (i:ℕ) ≠ 0 := fun e => h (Fin.ext e)
      simp [rate, hn, h]
      ring
  simp_rw [hr]
  simp [field, secondSpatial, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.mul_sum]

/-- Squared coefficient norm; proportional to physical L² energy after
weighting the constant mode. It is sufficient for stability in this sector. -/
def energy {N : ℕ} (a : Fin (N+1) → ℝ) : ℝ := ∑ i, (a i)^2

theorem rate_bound (D gamma beta decay : ℝ) (hD : 0 ≤ D)
    (h0 : decay ≤ gamma-beta) (h1 : decay ≤ gamma) (i : ℕ) :
    rate D gamma beta i ≤ -decay := by
  unfold rate
  split
  · linarith
  · have := mul_nonneg hD (sq_nonneg (i:ℝ)); linarith

theorem energy_decay {N : ℕ} (D gamma beta decay : ℝ) (a : Fin (N+1) → ℝ)
    (hD : 0 ≤ D) (h0 : decay ≤ gamma-beta) (h1 : decay ≤ gamma)
    (t : ℝ) (ht : 0 ≤ t) :
    energy (flow D gamma beta a t) ≤ energy a * Real.exp (-(2*decay)*t) := by
  have hterm (i : Fin (N+1)) : (flow D gamma beta a t i)^2 ≤
      (a i)^2 * Real.exp (-(2*decay)*t) := by
    have hr := rate_bound D gamma beta decay hD h0 h1 i
    have he : Real.exp (2*(rate D gamma beta i*t)) ≤ Real.exp (-(2*decay)*t) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right hr ht]
    have hs : (Real.exp (rate D gamma beta i*t))^2 =
        Real.exp (2*(rate D gamma beta i*t)) := by
      rw [pow_two, ← Real.exp_add]; congr 1; ring
    simpa [flow, mul_pow, hs] using mul_le_mul_of_nonneg_left he (sq_nonneg (a i))
  simpa [energy, Finset.sum_mul] using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hterm i)

/-- Constant-mode instability is a counterexample to unconditional damping. -/
theorem constant_mode_grows (D gamma beta a t : ℝ) (ha : 0 < a)
    (hbg : gamma < beta) (ht : 0 < t) :
    a < flow (N := 0) D gamma beta (fun _ => a) t 0 := by
  have he : 1 < Real.exp ((beta-gamma)*t) := Real.one_lt_exp_iff.mpr (mul_pos (sub_pos.mpr hbg) ht)
  simpa [flow, rate] using mul_lt_mul_of_pos_left he ha
end Wright.PeriodicField

namespace Wright.Transport
/-- Constant-velocity, zero-source realization of Lambda_t + (v Lambda)_x=0. -/
def solution (initial : ℝ → ℝ) (v t x : ℝ) : ℝ := initial (x-v*t)

theorem initial_data (initial : ℝ → ℝ) (v x : ℝ) : solution initial v 0 x = initial x := by
  simp [solution]

theorem solves_continuity (initial initial' : ℝ → ℝ) (v t x : ℝ)
    (hi : ∀ y, HasDerivAt initial (initial' y) y) :
    deriv (fun s => solution initial v s x) t +
      deriv (fun y => v * solution initial v t y) x = 0 := by
  have ht : HasDerivAt (fun s => solution initial v s x)
      (initial' (x-v*t) * (-v)) t := by
    simpa using (hi (x-v*t)).comp t (((hasDerivAt_id t).const_mul v).const_sub x)
  have hx : HasDerivAt (fun y => v * solution initial v t y)
      (v * initial' (x-v*t)) x := by
    convert ((hi _).comp x ((hasDerivAt_id x).sub_const (v*t))).const_mul v using 1 <;> simp
  rw [ht.deriv, hx.deriv]
  ring

theorem periodic (initial : ℝ → ℝ) (v t period : ℝ)
    (hp : Function.Periodic initial period) : Function.Periodic (solution initial v t) period := by
  intro x
  simpa [solution, add_sub_right_comm] using hp (x-v*t)

theorem mass_conserved (initial : ℝ → ℝ) (v t period : ℝ)
    (hp : Function.Periodic initial period) :
    (∫ x in (0:ℝ)..period, solution initial v t x) = ∫ x in (0:ℝ)..period, initial x := by
  unfold solution
  rw [intervalIntegral.integral_comp_sub_right]
  convert hp.intervalIntegral_add_eq (-v*t) 0 using 1 <;> congr 1 <;> ring

theorem nonnegative (initial : ℝ → ℝ) (v t x : ℝ) (hi : ∀ y, 0 ≤ initial y) :
    0 ≤ solution initial v t x := hi _

/-- The PDE for a differentiable spacetime density, in actual coordinate
Frechet derivatives. This is the constant-v, zero-source continuity equation. -/
def Solves (v : ℝ) (density : ℝ × ℝ → ℝ) : Prop :=
  Differentiable ℝ density ∧ ∀ p,
    fderiv ℝ density p (1,0) + v * fderiv ℝ density p (0,1) = 0

theorem unique (initial : ℝ → ℝ) (v : ℝ) (density : ℝ × ℝ → ℝ)
    (h : Solves v density) (h0 : ∀ x, density (0,x) = initial x) (t x : ℝ) :
    density (t,x) = solution initial v t x := by
  let b := x-v*t
  let characteristic : ℝ → ℝ × ℝ := fun s => (s,b+v*s)
  have hc (s : ℝ) : HasDerivAt characteristic (1,v) s := by
    simpa [characteristic] using (hasDerivAt_id s).prodMk
      (((hasDerivAt_id s).const_mul v).const_add b)
  have hz (s : ℝ) : HasDerivAt (fun u => density (characteristic u)) 0 s := by
    have hd := (h.1 (characteristic s)).hasFDerivAt.comp_hasDerivAt s (hc s)
    have hp : (1,v) = (1,0) + v • ((0,1) : ℝ × ℝ) := by ext <;> simp
    apply hd.congr_deriv
    rw [hp, map_add, map_smul]
    exact h.2 (characteristic s)
  have he := is_const_of_deriv_eq_zero (fun s => (hz s).differentiableAt)
    (fun s => (hz s).deriv) t 0
  have hb : b+v*t = x := by dsimp [b]; ring
  simpa [characteristic, hb, h0, solution, b] using he
end Wright.Transport
