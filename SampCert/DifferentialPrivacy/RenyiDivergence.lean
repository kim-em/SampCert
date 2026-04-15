/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import SampCert.Util.Log
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Analysis.Convex.Integral

/-! Renyi Divergence

This file defines the Renyi divergence, and equations for evaluating it.
-/


open Real ENNReal PMF MeasureTheory Measure
open Classical


/--
Simplified consequence of absolute continuity between PMF's.
-/
def AbsCts (p q : T -> ENNReal) : Prop := ∀ x : T, q x = 0 -> p x = 0


/--
All PMF's are absolutely continuous with respect to themselves.
-/
lemma AbsCts_refl (q : PMF T) : AbsCts q q  := by
  rw [AbsCts]
  simp

/--
Obtain simplified absolute continuity from the measure-theoretic version of absolute continuity in a discrete space.
-/
lemma PMF_AbsCts [MeasurableSpace T] [MeasurableSingletonClass T] (p q : PMF T)
    (H : AbsolutelyContinuous (PMF.toMeasure p) (PMF.toMeasure q)) : AbsCts p q := by
  intro x Hx
  have Hxm : q.toMeasure {x} = 0 := by
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    exact Hx
  have Hpm : p.toMeasure {x} = 0 := H Hxm
  rwa [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)] at Hpm

lemma PMF_mul_mul_inv_eq_mul_cancel (p q : PMF T) (HA : AbsCts p q) (a : T) :
    (p a / q a) * q a = p a := by
  apply mul_mul_inv_eq_mul_cancel
  · exact fun h => HA a h
  · exact fun ⟨_, h⟩ => apply_ne_top q a h

variable {T : Type}

/--
Definition of the Renyi divergence as an EReal.
-/
noncomputable def RenyiDivergence_def (p q : PMF T) (α : ℝ) : EReal :=
  (α - 1)⁻¹  * (elog (∑' x : T, (p x)^α  * (q x)^(1 - α)))

/--
Rearrange the definition of ``RenyiDivergence_def`` to obtain an equation for the inner series.
-/
lemma RenyiDivergence_def_exp (p q : PMF T) {α : ℝ} (h : 1 < α) :
  eexp (((α - 1)) * RenyiDivergence_def p q α) = (∑' x : T, (p x)^α * (q x)^(1 - α)) := by
  rw [RenyiDivergence_def]
  rw [<- mul_assoc]
  have H1 : (α.toEReal - OfNat.ofNat 1) =  (α - OfNat.ofNat 1).toEReal := by
    rw [EReal.coe_sub]
    congr
  have H2 : ((α.toEReal - OfNat.ofNat 1) * (α - OfNat.ofNat 1)⁻¹.toEReal = 1) := by
    rw [H1]
    rw [← EReal.coe_mul]
    rw [mul_inv_cancel₀ (by linarith : (α - 1 : ℝ) ≠ 0)]
    simp
  simp [H2]

lemma EReal_sub_one_pos_of_one_lt {α : ℝ} (Hα : 1 < α) :
    (0 : EReal) < α.toEReal - OfNat.ofNat 1 := by
  rw [show (OfNat.ofNat 1 : EReal) = (1 : ℝ).toEReal from rfl, ← EReal.coe_sub]
  exact_mod_cast sub_pos.mpr Hα

lemma EReal_sub_one_lt_top (α : ℝ) :
    (α.toEReal - OfNat.ofNat 1) < ⊤ := by
  rw [show (OfNat.ofNat 1 : EReal) = (1 : ℝ).toEReal from rfl, ← EReal.coe_sub]
  exact EReal.coe_lt_top _

lemma RenyiDivergenceExpectation_pointwise (a b : ENNReal) {α : ℝ} (h : 1 < α)
    (Hac : b = 0 → a = 0) : a ^ α * b ^ (1 - α) = (a / b) ^ α * b := by
  rcases eq_or_ne b 0 with hb0 | hb0
  · subst hb0
    rw [Hac rfl]
    rw [ENNReal.zero_rpow_of_pos (by linarith : 0 < α)]
    simp
  rcases eq_or_ne b ⊤ with hbt | hbt
  · subst hbt
    rw [ENNReal.top_rpow_of_neg (by linarith : (1 - α) < 0)]
    rw [ENNReal.div_top, ENNReal.zero_rpow_of_pos (by linarith : 0 < α)]
    simp
  rcases eq_or_ne a 0 with ha0 | ha0
  · subst ha0
    rw [ENNReal.zero_rpow_of_pos (by linarith : 0 < α), ENNReal.zero_div,
        ENNReal.zero_rpow_of_pos (by linarith : 0 < α)]
    simp
  rcases eq_or_ne a ⊤ with hat | hat
  · subst hat
    rw [ENNReal.top_rpow_of_pos (by linarith : 0 < α)]
    rw [ENNReal.top_div_of_ne_top hbt]
    rw [ENNReal.top_rpow_of_pos (by linarith : 0 < α)]
    have hb_pow_ne : b ^ (1 - α) ≠ 0 := by
      intro hc
      rcases ENNReal.rpow_eq_zero_iff.mp hc with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact hb0 h1
      · exact hbt h1
    rw [ENNReal.top_mul hb_pow_ne, ENNReal.top_mul hb0]
  rw [ENNReal.rpow_sub _ _ hb0 hbt, ← ENNReal.mul_comm_div,
      ← ENNReal.div_rpow_of_nonneg _ _ (by linarith : (0 : ℝ) ≤ α), ENNReal.rpow_one]

/--
Renyi Divergence series written as a conditional expectation, conditioned on q.
-/
theorem RenyiDivergenceExpectation (p q : T → ENNReal) {α : ℝ} (h : 1 < α) (H : AbsCts p q) :
    (∑' x : T, (p x)^α * (q x)^(1 - α)) = ∑' x : T, (p x / q x)^α * (q x) := by
  refine tsum_congr (fun x => ?_)
  exact RenyiDivergenceExpectation_pointwise (p x) (q x) h (H x)


lemma RenyiDivergenceExpectation'_pointwise (a b : ENNReal) {α : ℝ} (h : 1 < α)
    (Ha_ne_zero : a ≠ 0) (Ha_ne_top : a ≠ ⊤) :
    a ^ α * b ^ (1 - α) = (a / b) ^ (α - 1) * a := by
  rcases eq_or_ne b 0 with hb0 | hb0
  · subst hb0
    rw [ENNReal.zero_rpow_of_neg (by linarith : (1 - α) < 0)]
    rw [ENNReal.div_zero Ha_ne_zero]
    rw [ENNReal.top_rpow_of_pos (by linarith : 0 < α - 1)]
    rw [ENNReal.top_mul Ha_ne_zero]
    rw [ENNReal.mul_top (by
      intro hc
      exact Ha_ne_zero (ENNReal.rpow_eq_zero_iff_of_pos (by linarith : 0 < α) |>.mp hc))]
  rcases eq_or_ne b ⊤ with hbt | hbt
  · subst hbt
    rw [ENNReal.top_rpow_of_neg (by linarith : (1 - α) < 0)]
    rw [ENNReal.div_top, ENNReal.zero_rpow_of_pos (by linarith : 0 < α - 1)]
    simp
  rw [ENNReal.div_rpow_of_nonneg _ _ (by linarith : (0 : ℝ) ≤ α - 1)]
  rw [ENNReal.div_eq_inv_mul, mul_assoc, mul_comm]
  have Hsplit : a ^ α = a ^ (α - 1) * a := by
    nth_rewrite 3 [← ENNReal.rpow_one a]
    rw [← ENNReal.rpow_add _ _ Ha_ne_zero Ha_ne_top]
    congr 1; ring
  rw [Hsplit]
  congr 1
  rw [← ENNReal.rpow_neg]; congr 1; ring

/--
Renyi Divergence series written as a conditional expectation, conditioned on p.
-/
theorem RenyiDivergenceExpectation' (p q : PMF T) {α : ℝ} (h : 1 < α) :
    (∑' x : T, (p x)^α * (q x)^(1 - α)) = ∑' x : T, (p x / q x)^(α - 1) * (p x) := by
  have K1 : Function.support (fun x : T => (p x / q x)^(α - 1) * p x) ⊆ { t : T | p t ≠ 0 } := by
    intro a Ha hpa
    apply Ha
    show (p a / q a)^(α - 1) * p a = 0
    rw [hpa, mul_zero]
  rw [<- tsum_subtype_eq_of_support_subset K1]
  have K2 : Function.support (fun x : T => (p x)^α * (q x)^(1 - α)) ⊆ { t : T | p t ≠ 0 } := by
    intro a Ha hpa
    apply Ha
    show (p a)^α * (q a)^(1 - α) = 0
    rw [hpa, ENNReal.zero_rpow_of_pos (by linarith : 0 < α)]
    simp
  rw [<- tsum_subtype_eq_of_support_subset K2]
  refine tsum_congr (fun ⟨x', Hx'⟩ => ?_)
  exact RenyiDivergenceExpectation'_pointwise (p x') (q x') h Hx' (PMF.apply_ne_top p x')

/-!
## Jensen's inequality
-/
section Jensen

variable {T : Type}
variable [t1 : MeasurableSpace T]

variable {U V : Type}
variable [m2 : MeasurableSpace U]
variable [count : Countable U]
variable [disc : DiscreteMeasurableSpace U]
variable [Inhabited U]

lemma Integrable_rpow (f : T → ℝ) (nn : ∀ x : T, 0 ≤ f x) (μ : Measure T) (α : ENNReal)
    (mem : MemLp f α μ) (h1 : α ≠ 0) (h2 : α ≠ ⊤) :
    MeasureTheory.Integrable (fun x : T => (f x) ^ α.toReal) μ := by
  have HRP := @MeasureTheory.MemLp.integrable_norm_rpow T ℝ t1 μ _ f α mem h1 h2
  have Hcongr : (fun x : T => ‖f x‖ ^ α.toReal) = (fun x : T => (f x) ^ α.toReal) := by
    funext x; rw [Real.norm_of_nonneg (nn x)]
  rwa [Hcongr] at HRP

lemma continuousOn_rpow_Ici_of_one_lt {α : ℝ} (h : 1 < α) :
    ContinuousOn (fun x : ℝ => x ^ α) (Set.Ici 0) := by
  apply ContinuousOn.rpow continuousOn_id continuousOn_const
  intro x hx
  rcases (Set.mem_Ici.mp hx).lt_or_eq.symm.imp Eq.symm id with rfl | hxpos
  · exact Or.inr (lt_trans zero_lt_one h)
  · exact Or.inl hxpos.ne'

lemma Integrable_rpow_of_one_lt {f : T → ℝ} {α : ℝ} (h : 1 < α)
    (h2 : ∀ x : T, 0 ≤ f x) {μ : Measure T}
    (mem : MemLp f (ENNReal.ofReal α) μ) :
    MeasureTheory.Integrable (fun x : T => f x ^ α) μ := by
  have hα0 : ENNReal.ofReal α ≠ 0 := by simp; linarith
  have hαt : ENNReal.ofReal α ≠ ⊤ := by simp
  have Z := Integrable_rpow f h2 μ (ENNReal.ofReal α) mem hα0 hαt
  rwa [toReal_ofReal (le_of_lt (lt_trans zero_lt_one h))] at Z

lemma Integrable_of_MemLp_one_lt {f : T → ℝ} {α : ℝ} (h : 1 < α)
    {μ : Measure T} [IsFiniteMeasure μ]
    (mem : MemLp f (ENNReal.ofReal α) μ) : MeasureTheory.Integrable f μ := by
  apply MeasureTheory.MemLp.integrable _ mem
  rw [one_le_ofReal]; exact le_of_lt h

/--
Jensen's inequality for the exponential applied to the real-valued function ``(⬝)^α``.
-/
theorem Renyi_Jensen_real [t2 : MeasurableSingletonClass T] (f : T → ℝ) (q : PMF T) (α : ℝ) (h : 1 < α) (h2 : ∀ x : T, 0 ≤ f x) (mem : MemLp f (ENNReal.ofReal α) (PMF.toMeasure q)) :
  ((∑' x : T, (f x) * (q x).toReal)) ^ α ≤ (∑' x : T, (f x) ^ α * (q x).toReal) := by
  simp_rw [show ∀ x : T, f x * (q x).toReal = (q x).toReal • f x from
    fun x => by rw [smul_eq_mul, mul_comm]]
  simp_rw [show ∀ x : T, f x ^ α * (q x).toReal = (q x).toReal • f x ^ α from
    fun x => by rw [smul_eq_mul, mul_comm]]
  rw [← PMF.integral_eq_tsum]
  rw [← PMF.integral_eq_tsum]

  have A := @convexOn_rpow α (le_of_lt h)
  have B := continuousOn_rpow_Ici_of_one_lt h
  have C : IsClosed (Set.Ici (0 : ℝ)) := isClosed_Ici
  have D := @ConvexOn.map_integral_le T ℝ t1 _ _ _ (PMF.toMeasure q) (Set.Ici 0) f
    (fun (x : ℝ) => x ^ α) (PMF.toMeasure.isProbabilityMeasure q) A B C
  simp at D
  apply D
  · exact MeasureTheory.ae_of_all (PMF.toMeasure q) h2
  · exact Integrable_of_MemLp_one_lt h mem
  · rw [Function.comp_def]; exact Integrable_rpow_of_one_lt h h2 mem
  · exact Integrable_rpow_of_one_lt h h2 mem
  · exact Integrable_of_MemLp_one_lt h mem


/--
Strict version of Jensen't inequality applied to the function ``(⬝)^α``.
-/
theorem Renyi_Jensen_strict_real [t2 : MeasurableSingletonClass T] [tcount : Countable T] (f : T → ℝ) (q : PMF T) (α : ℝ) (h : 1 < α) (h2 : ∀ x : T, 0 ≤ f x) (mem : MemLp f (ENNReal.ofReal α) (PMF.toMeasure q)) (HT_nz : ∀ t : T, q t ≠ 0):
  ((∑' x : T, (f x) * (q x).toReal)) ^ α < (∑' x : T, (f x) ^ α * (q x).toReal) ∨ (∀ x : T, f x = ∑' (x : T), (q x).toReal * f x) := by
  simp_rw [show ∀ x : T, f x * (q x).toReal = (q x).toReal • f x from
    fun x => by rw [smul_eq_mul, mul_comm]]
  simp_rw [show ∀ x : T, f x ^ α * (q x).toReal = (q x).toReal • f x ^ α from
    fun x => by rw [smul_eq_mul, mul_comm]]
  rw [← PMF.integral_eq_tsum]
  rw [← PMF.integral_eq_tsum]

  have A := strictConvexOn_rpow h
  have B := continuousOn_rpow_Ici_of_one_lt h
  have C : IsClosed (Set.Ici (0 : ℝ)) := isClosed_Ici
  haveI : IsProbabilityMeasure (PMF.toMeasure q) := PMF.toMeasure.isProbabilityMeasure q
  have D := @StrictConvexOn.ae_eq_const_or_map_average_lt T ℝ t1 _ _ _ (PMF.toMeasure q)
    (Set.Ici 0) f (fun (x : ℝ) => x ^ α) inferInstance A B C
    (MeasureTheory.ae_of_all (PMF.toMeasure q) h2)
    (Integrable_of_MemLp_one_lt h mem)
    (by rw [Function.comp_def]; exact Integrable_rpow_of_one_lt h h2 mem)
  simp at D
  · cases D
    · rename_i HR
      right
      simp at HR
      -- Because T is discrete, almost-everywhere equality should become equality
      have HR' := @Filter.EventuallyEq.eventually _ _ (ae q.toMeasure) f (Function.const T (⨍ (x : T), f x ∂q.toMeasure)) HR
      simp [Filter.Eventually] at HR'
      -- The measure of the compliment of the set in HR' is zero
      simp [ae] at HR'
      rw [PMF.toMeasure_apply _ ?Hmeas] at HR'
      case Hmeas =>
        exact MeasurableSet.of_discrete
      -- Sum is zero iff all elements are zero
      apply ENNReal.tsum_eq_zero.mp at HR'
      -- Indicator is zero when proposition is not true
      intro x
      have HR' := HR' x
      simp at HR'
      by_cases Heqx : f x = ⨍ (x : T), f x ∂q.toMeasure
      ·
        -- Rewrite the average
        rw [MeasureTheory.average] at Heqx
        rw [MeasureTheory.integral_countable] at Heqx
        · simp at Heqx
          conv at Heqx =>
            rhs
            arg 1
            intro x
            rw [MeasureTheory.measureReal_def]
            rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
          simpa using Heqx
        · simp
          apply MeasureTheory.MemLp.integrable _ mem
          have X : (1 : ENNReal) = ENNReal.ofReal (1 : ℝ) := by simp
          rw [X]
          apply ofReal_le_ofReal_iff'.mpr
          left
          linarith
      · -- At type T, q x is never zero
        exact absurd (HR' Heqx) (HT_nz x)
    · rename_i HR
      left
      rw [<- MeasureTheory.integral_average]
      rw [<- MeasureTheory.integral_average]
      simp
      rw [<- MeasureTheory.integral_average]
      rw [<- MeasureTheory.integral_average]
      simp
      apply HR
  · exact Integrable_rpow_of_one_lt h h2 mem
  · exact Integrable_of_MemLp_one_lt h mem

end Jensen


/--
Quotient from the Real-valued Jenen's inequality applied to the series in the Renyi divergence.
-/
noncomputable def Renyi_Jensen_f (p q : PMF T) : T -> ℝ := (fun z => (p z / q z).toReal)

/--
Summand from the Renyi divergence equals a real-valued summand, except in a special case.
-/
lemma Renyi_Jensen_div_ne_top (p q : PMF T) (H : AbsCts p q)
    (Hspecial : ∀ x : T, ¬(p x = ⊤ ∧ q x ≠ 0 ∧ q x ≠ ⊤)) (a : T) : p a / q a ≠ ⊤ := by
  intro HK
  rcases div_eq_top.mp HK with ⟨HK1, HK2⟩ | ⟨HK1, HK2⟩
  · exact HK1 (H a HK2)
  · refine Hspecial a ⟨HK1, ?_, HK2⟩
    intro hz
    have hp0 : p a = 0 := H a hz
    rw [hp0] at HK1
    exact ENNReal.zero_ne_top HK1

lemma PMF_q_ne_top_pq (p q : PMF T) (z : T) : ¬(p z ≠ 0 ∧ q z = ⊤) :=
  fun ⟨_, hqt⟩ => PMF.apply_ne_top q z hqt

lemma PMF_div_mul_eq (p q : PMF T) (H : AbsCts p q) (z : T) : p z / q z * q z = p z := by
  rw [division_def, mul_mul_inv_eq_mul_cancel (H z) (PMF_q_ne_top_pq p q z)]

lemma Renyi_Jensen_rw (p q : PMF T) {α : ℝ} (h : 1 < α) (H : AbsCts p q)
    (Hspecial : ∀ x : T, ¬(p x = ⊤ ∧ q x ≠ 0 ∧ q x ≠ ⊤)) (x : T) :
    (p x / q x)^α * (q x) = ENNReal.ofReal (((Renyi_Jensen_f p q) x)^α * (q x).toReal) := by
  unfold Renyi_Jensen_f
  rw [ENNReal.toReal_rpow, ← ENNReal.toReal_mul, ENNReal.ofReal_toReal]
  refine mul_ne_top (rpow_ne_top_of_nonneg (by linarith) ?_) (apply_ne_top q x)
  exact Renyi_Jensen_div_ne_top p q H Hspecial x

lemma Renyi_Jensen_f_MemLp [MeasurableSpace T] [MeasurableSingletonClass T] [Countable T]
    (p q : PMF T) {α : ℝ} (h : 1 < α) (H : AbsCts p q)
    (Hspecial : ∀ x : T, ¬(p x = ⊤ ∧ q x ≠ 0 ∧ q x ≠ ⊤))
    (Hnts : ∑' (a : T), (p a / q a) ^ α * q a ≠ ⊤) :
    MemLp (Renyi_Jensen_f p q) (ENNReal.ofReal α) (PMF.toMeasure q) := by
  haveI : DiscreteMeasurableSpace T := MeasurableSingletonClass.toDiscreteMeasurableSpace
  have HRJf_nonneg (a : T) : 0 ≤ Renyi_Jensen_f p q a := toReal_nonneg
  have HRJf_nt := Renyi_Jensen_div_ne_top p q H Hspecial
  simp [MemLp]
  refine ⟨?_, ?_⟩
  · apply MeasureTheory.StronglyMeasurable.aestronglyMeasurable
    apply Measurable.stronglyMeasurable
    apply Measurable.ennreal_toReal
    conv => right; intro x; rw [division_def]
    exact (Measurable.of_discrete).mul ((Measurable.of_discrete).inv)
  · simp [eLpNorm]
    split
    · simp
    · rename_i Hα
      simp [eLpNorm']
      rw [MeasureTheory.lintegral_countable']
      rw [toReal_ofReal (le_of_lt (lt_trans zero_lt_one h))]
      apply rpow_lt_top_of_nonneg
      · simp; exact le_of_not_ge Hα
      have Hsummand_eq : ∀ a : T,
          ‖Renyi_Jensen_f p q a‖ₑ ^ α * (PMF.toMeasure q) {a} = (p a / q a) ^ α * q a := by
        intro a
        congr 1
        · rw [enorm_eq_nnnorm, ← Real.toNNReal_eq_nnnorm_of_nonneg (HRJf_nonneg a),
              Renyi_Jensen_f, ← ENNReal.ofReal.eq_1, ENNReal.ofReal_toReal (HRJf_nt a)]
        · exact PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)
      simp_rw [Hsummand_eq]
      exact Hnts

/--
Jensen's inquality applied to ENNReals, in the case that q is nonzero.
-/
lemma Renyi_Jensen_ENNReal_reduct [MeasurableSpace T] [MeasurableSingletonClass T] [Countable T]
  (p q : PMF T) {α : ℝ} (h : 1 < α) (H : AbsCts p q) :
  (∑' x : T, (p x / q x) * q x) ^ α ≤ (∑' x : T, (p x / q x) ^ α * q x) := by
  haveI : DiscreteMeasurableSpace T := MeasurableSingletonClass.toDiscreteMeasurableSpace
  by_cases Hnts : ∑' (a : T), (p a / q a) ^ α * q a = ⊤
  · rw [Hnts]; exact OrderTop.le_top _
  by_cases Hspecial : ∀ x : T, ¬(p x = ⊤ ∧ q x ≠ 0 ∧ q x ≠ ⊤)
  · -- Typical case
    simp_rw [Renyi_Jensen_rw p q h H Hspecial]
    rw [<- ENNReal.ofReal_tsum_of_nonneg ?Hnonneg ?Hsummable]
    case Hnonneg =>
      intro t
      exact mul_nonneg (rpow_nonneg toReal_nonneg α) toReal_nonneg
    case Hsummable =>
      have Hcongr : (fun x => Renyi_Jensen_f p q x ^ α * (q x).toReal)
                  = (fun x => ((p x / q x) ^ α * q x).toReal) := by
        funext x
        rw [Renyi_Jensen_f, ENNReal.toReal_rpow, ← ENNReal.toReal_mul]
      rw [Hcongr]
      exact ENNReal.summable_toReal Hnts
    have HRJf_nonneg (a : T) : 0 <= Renyi_Jensen_f p q a := by apply toReal_nonneg
    apply (le_trans ?G1 ?G2)
    case G2 =>
      apply ofReal_le_ofReal
      exact Renyi_Jensen_real (Renyi_Jensen_f p q) q α h
        (fun _ => toReal_nonneg) (Renyi_Jensen_f_MemLp p q h H Hspecial Hnts)
    case G1 =>
      rw [<- ENNReal.ofReal_rpow_of_nonneg
            (tsum_nonneg (fun _ => mul_nonneg (HRJf_nonneg _) toReal_nonneg))
            (by linarith : (0 : ℝ) ≤ α)]
      apply ENNReal.rpow_le_rpow _ (by linarith : (0 : ℝ) ≤ α)
      have Hcancel : ∀ a, p a / q a * q a = p a :=
        fun a => PMF_mul_mul_inv_eq_mul_cancel p q H a
      have Hsum_pq : ∑' a : T, p a / q a * q a = 1 := by
        simp_rw [Hcancel]; exact tsum_coe p
      rw [show (fun a => Renyi_Jensen_f p q a * (q a).toReal)
            = (fun a => (p a / q a * q a).toReal) from by
            funext a; rw [Renyi_Jensen_f, ← ENNReal.toReal_mul]]
      rw [← ENNReal.tsum_toReal_eq (fun a => by rw [Hcancel]; exact apply_ne_top p a)]
      rw [Hsum_pq]
      simp
  · -- Special case: There exists some element x0 with p x0 = ⊤ but q x0 ∈ ℝ+
    simp only [not_forall, not_not, ne_eq] at Hspecial
    rcases Hspecial with ⟨x0, Hpx0, Hqx0_nz, Hqx0_nt⟩
    have Hdiv : p x0 / q x0 = ⊤ := div_eq_top.mpr (Or.inr ⟨Hpx0, Hqx0_nt⟩)
    have HT1 : (∑' (x : T), p x / q x * q x) ^ α = ⊤ := by
      apply rpow_eq_top_iff.mpr
      refine Or.inr ⟨?_, by linarith⟩
      exact ENNReal.tsum_eq_top_of_eq_top
        ⟨x0, mul_eq_top.mpr (Or.inr ⟨Hdiv, Hqx0_nz⟩)⟩
    have HT2 : ∑' (x : T), (p x / q x) ^ α * q x = ⊤ := by
      apply ENNReal.tsum_eq_top_of_eq_top
      refine ⟨x0, mul_eq_top.mpr (Or.inr ⟨?_, Hqx0_nz⟩)⟩
      exact rpow_eq_top_iff.mpr (Or.inr ⟨Hdiv, by linarith⟩)
    rw [HT1, HT2]


/--
On types where q is nonzero, Jensen's inequality for the Renyi divergence sum is tight only for equal distributions.
-/
lemma Renyi_Jensen_ENNReal_converse_reduct [MeasurableSpace T] [MeasurableSingletonClass T] [Countable T]
  (p q : PMF T) {α : ℝ} (h : 1 < α) (H : AbsCts p q) (Hq : ∀ t, q t ≠ 0)
  (Hsumeq : (∑' x : T, (p x / q x) * q x) ^ α = (∑' x : T, (p x / q x) ^ α * q x)) :
  (p = q) := by
  haveI : DiscreteMeasurableSpace T := MeasurableSingletonClass.toDiscreteMeasurableSpace
  by_cases Hnts : ∑' (a : T), (p a / q a) ^ α * q a = ⊤
  · -- One of the series is Top, so the other series is too
    rw [Hnts] at Hsumeq
    -- This series should actually be 1 by PMF
    simp_rw [PMF_mul_mul_inv_eq_mul_cancel p q H] at Hsumeq
    rw [PMF.tsum_coe, ENNReal.one_rpow] at Hsumeq
    exact (ENNReal.one_ne_top Hsumeq).elim
  by_cases Hspecial : ∀ x : T, ¬(p x = ⊤ ∧ q x ≠ 0 ∧ q x ≠ ⊤)
  · -- Typical case
    simp_rw [Renyi_Jensen_rw p q h H Hspecial] at Hsumeq
    rw [<- ENNReal.ofReal_tsum_of_nonneg ?Hnonneg ?Hsummable] at Hsumeq
    case Hnonneg =>
      intro t
      exact mul_nonneg (rpow_nonneg toReal_nonneg α) toReal_nonneg
    case Hsummable =>
      have Hcongr : (fun x => Renyi_Jensen_f p q x ^ α * (q x).toReal)
                  = (fun x => ((p x / q x) ^ α * q x).toReal) := by
        funext x
        rw [Renyi_Jensen_f, ENNReal.toReal_rpow, ← ENNReal.toReal_mul]
      rw [Hcongr]
      exact ENNReal.summable_toReal Hnts
    have HRJf_nonneg (a : T) : 0 <= Renyi_Jensen_f p q a := by apply toReal_nonneg
    have HRJf_nt := Renyi_Jensen_div_ne_top p q H Hspecial

    -- Apply the converse lemma
    have Hieq := Renyi_Jensen_strict_real (Renyi_Jensen_f p q) q α h HRJf_nonneg
      (Renyi_Jensen_f_MemLp p q h H Hspecial Hnts) Hq
    cases Hieq
    · rename_i Hk
      exfalso
      have HkLHS_eq : (fun z : T => Renyi_Jensen_f p q z * (q z).toReal)
                    = (fun z : T => (p z).toReal) := by
        funext z; rw [Renyi_Jensen_f, ← ENNReal.toReal_mul, PMF_div_mul_eq p q H]
      rw [HkLHS_eq] at Hk
      simp_rw [division_def, mul_assoc, ENNReal.inv_mul_cancel (Hq _) (PMF.apply_ne_top _ _),
        mul_one] at Hsumeq
      rw [<- ENNReal.tsum_toReal_eq fun _ => PMF.apply_ne_top _ _] at Hk
      rw [PMF.tsum_coe] at Hk Hsumeq
      simp only [ENNReal.toReal_one, Real.one_rpow] at Hk
      have Hsumeq' : (1 : ℝ) = ∑' n : T, Renyi_Jensen_f p q n ^ α * (q n).toReal := by
        have h2 := congrArg ENNReal.toReal Hsumeq
        simpa [ENNReal.toReal_ofReal (tsum_nonneg fun _ =>
          mul_nonneg (rpow_nonneg (HRJf_nonneg _) _) toReal_nonneg), Real.one_rpow] using h2
      rw [Hsumeq'] at Hk
      linarith
    · rename_i Hext
      -- RHS of Hext is 1, LHS is p/q
      apply PMF.ext
      intro x
      have Hext' := Hext x
      rw [Renyi_Jensen_f] at Hext'
      have HextRHS_eq : (fun z : T => (q z).toReal * Renyi_Jensen_f p q z)
                      = (fun z : T => (p z).toReal) := by
        funext z; rw [Renyi_Jensen_f, ← ENNReal.toReal_mul, mul_comm, PMF_div_mul_eq p q H]
      rw [HextRHS_eq] at Hext'
      rw [<- ENNReal.tsum_toReal_eq] at Hext'
      · rw [PMF.tsum_coe] at Hext'
        apply (@ENNReal.mul_left_inj _ _ ((q x)⁻¹) ?G1 ?G2).mp
        case G1 =>
          simp
          apply PMF.apply_ne_top
        case G2 =>
          simp
          apply Hq
        rw [ENNReal.mul_inv_cancel ?G1 ?G2]
        case G1 => apply Hq
        case G2 => apply PMF.apply_ne_top
        apply (toReal_eq_toReal_iff' (HRJf_nt x) ?G3).mp
        case G3 => simp
        apply Hext'
      · intro
        apply PMF.apply_ne_top
  · -- Special case: There exists some element x0 with p x0 = ⊤ but q x0 ∈ ℝ+
    -- This means the sum in Hnts will actually be ⊤
    exfalso
    apply Hnts
    apply ENNReal.tsum_eq_top_of_eq_top
    simp only [not_forall, not_not, ne_eq] at Hspecial
    rcases Hspecial with ⟨x, Hx1, Hx2, Hx3⟩
    exact ⟨x, mul_eq_top.mpr (Or.inr ⟨rpow_eq_top_iff.mpr
      (Or.inr ⟨div_eq_top.mpr (Or.inr ⟨Hx1, Hx3⟩), by linarith⟩), Hx2⟩)⟩

/--
Restriction of the PMF f to the support of q.
-/
def reducedPMF_def (f q : PMF T) (x : { t : T // ¬q t = 0 }) : ENNReal := f x.val

/--
Restricted PMF has sum  1
-/
lemma reducedPMF_norm_acts (p q : PMF T) (H : AbsCts p q) : HasSum (reducedPMF_def p q) 1 := by
  have H1 : Summable (reducedPMF_def p q) := by exact ENNReal.summable
  have H2 := Summable.hasSum H1
  have H3 : (∑' (b : { t // q t ≠ 0 }), reducedPMF_def p q b) = 1 := by
    have K1 : Function.support (fun x => p x) ⊆ { t : T | q t ≠ 0 } := by
      rw [Function.support]
      simp
      intro a Hp Hcont
      rw [AbsCts] at H
      apply Hp
      apply H
      apply Hcont
    have S1 : ∑' (x : ↑{t | q t ≠ 0}), p ↑x = ∑' (x : T), p x := by
      apply tsum_subtype_eq_of_support_subset K1
    have T1 : ∑' (x : T), p x = 1 := by exact tsum_coe p
    rw [<- T1]
    rw [<- S1]
    simp
    rfl
  rw [<- H3]
  apply H2

/--
Restriction of the PMF f to the support of q
-/
noncomputable def reducedPMF {p q : PMF T} (H : AbsCts p q): PMF { t : T // ¬q t = 0 } :=
  ⟨ reducedPMF_def p q, reducedPMF_norm_acts p q H ⟩

@[simp]
lemma reducedPMF_apply {p q : PMF T} (H : AbsCts p q) (x : { t : T // ¬q t = 0 }) :
    (reducedPMF H) x = p x.val := rfl

/--
`reducedPMF` is nonzero everywhere
-/
lemma reducedPMF_pos {q : PMF T} (H : AbsCts q q) (a : T) (Ha : ¬q a = 0) :
    (reducedPMF H) ⟨a, Ha⟩ ≠ 0 := by
  rw [reducedPMF_apply]; exact Ha

lemma reducedPMF_tsum_mul_eq (p q : PMF T) (H : AbsCts p q)
    (Hq : AbsCts q q) (f : ENNReal → ENNReal → ENNReal) :
    (∑' x : T, f (p x) (q x) * q x) =
    ∑' x : { t : T // ¬q t = 0 }, f (reducedPMF H x) (reducedPMF Hq x) * reducedPMF Hq x := by
  have Hsupp : Function.support (fun x : T => f (p x) (q x) * q x) ⊆ { t : T | q t ≠ 0 } := by
    intro a Ha hqa; apply Ha
    show f (p a) (q a) * q a = 0
    rw [hqa, mul_zero]
  rw [<- tsum_subtype_eq_of_support_subset Hsupp]
  rfl

/--
Jensen's inquality for the Renyi divergence sum between absolutely continuous PMFs
-/
theorem Renyi_Jensen_ENNReal [MeasurableSpace T] [MeasurableSingletonClass T] [Countable T]
    (p q : PMF T) {α : ℝ} (h : 1 < α) (Hac : AbsCts p q) :
    (∑' x : T, (p x / q x) * q x) ^ α ≤ (∑' x : T, (p x / q x) ^ α * q x) := by
  have Hq : AbsCts q q := AbsCts_refl q
  rw [reducedPMF_tsum_mul_eq p q Hac Hq (fun a b => a / b)]
  rw [reducedPMF_tsum_mul_eq p q Hac Hq (fun a b => (a / b) ^ α)]
  apply Renyi_Jensen_ENNReal_reduct _ _ h
  intro a Ha
  exact absurd Ha (reducedPMF_pos Hq a.val a.property)

/--
Converse of Jensen's inquality for the Renyi divergence sum between absolutely continuous PMFs
-/
lemma Renyi_Jensen_ENNReal_converse [MeasurableSpace T] [MeasurableSingletonClass T] [Countable T]
    (p q : PMF T) {α : ℝ} (h : 1 < α) (H : AbsCts p q)
    (Hsumeq : (∑' x : T, (p x / q x) * q x) ^ α = (∑' x : T, (p x / q x) ^ α * q x)) :
    (p = q) := by
  have Hq : AbsCts q q := AbsCts_refl q
  rw [reducedPMF_tsum_mul_eq p q H Hq (fun a b => a / b)] at Hsumeq
  rw [reducedPMF_tsum_mul_eq p q H Hq (fun a b => (a / b) ^ α)] at Hsumeq
  have Hreduced : reducedPMF H = reducedPMF Hq := by
    apply Renyi_Jensen_ENNReal_converse_reduct (reducedPMF H) (reducedPMF Hq) h
    · intro a Ha
      exact absurd Ha (reducedPMF_pos Hq a.val a.property)
    · intro a
      exact reducedPMF_pos Hq a.val a.property
    · exact Hsumeq
  apply PMF.ext
  intro x
  by_cases Hqz : q x = 0
  · rw [Hqz]; exact H _ Hqz
  · have Hreduced' : reducedPMF H ⟨x, Hqz⟩ = reducedPMF Hq ⟨x, Hqz⟩ :=
      congrFun (congrArg DFunLike.coe Hreduced) ⟨x, Hqz⟩
    rwa [reducedPMF_apply, reducedPMF_apply] at Hreduced'

/--
The ``EReal``-valued Renyi divergence is nonnegative.

Use this lemma to perform rewrites through the ``ENNReal.ofEReal`` in the
``ENNReal``-valued ``RenyiDivergence``
-/
theorem RenyiDivergence_def_nonneg [MeasurableSpace T] [MeasurableSingletonClass T] [Countable T] (p q : PMF T) (Hpq : AbsCts p q) {α : ℝ} (Hα : 1 < α) :
  (0 ≤ RenyiDivergence_def p q α) := by
  have H1 : eexp (((α - 1)) * 0)  ≤ eexp ((α - 1) * RenyiDivergence_def p q α) := by
    rw [RenyiDivergence_def_exp p q Hα]
    rw [RenyiDivergenceExpectation p q Hα Hpq]
    simp
    apply (le_trans ?G1 (Renyi_Jensen_ENNReal p q Hα Hpq))
    have Hone : (∑' (x : T), p x / q x * q x) = 1 := by
      simp_rw [PMF_mul_mul_inv_eq_mul_cancel p q Hpq]
      exact tsum_coe p
    have Hle : (∑' (x : T), p x / q x * q x) ≤ (∑' (x : T), p x / q x * q x) ^ α := by
      apply ENNReal.le_rpow_self_of_one_le
      · rw [Hone]
      · linarith
    apply le_trans ?X Hle
    rw [Hone]
  apply eexp_mono_le.mpr at H1
  apply ereal_smul_le_left (α.toEReal - OfNat.ofNat 1)
    (EReal_sub_one_pos_of_one_lt Hα) (EReal_sub_one_lt_top α) H1

/--
Renyi divergence between identical distributions is zero
-/
lemma RenyiDivergence_refl_zero (p : PMF T) {α : ℝ} (Hα : 1 < α) : (0 = RenyiDivergence_def p p α) := by
  have H1 : 1 = eexp ((α - 1) * RenyiDivergence_def p p α) := by
    rw [RenyiDivergence_def_exp p p Hα]
    rw [RenyiDivergenceExpectation p p Hα (AbsCts_refl p)]
    have HRW (x : T) : (p x / p x) ^ α * p x = p x := by
      by_cases Hz : p x = 0
      · rw [Hz]; simp
      · rw [ENNReal.div_self Hz (PMF.apply_ne_top p x)]; simp
    have Hcongr : (fun x : T => (p x / p x) ^ α * p x) = (fun x : T => p x) := funext HRW
    rw [Hcongr]
    exact (tsum_coe p).symm

  apply ereal_smul_eq_left (α.toEReal - OfNat.ofNat 1)
    (EReal_sub_one_pos_of_one_lt Hα) (EReal_sub_one_lt_top α)
  apply eexp_injective
  rw [<- H1]
  simp

/--
Renyi divergence is zero if and only if the distributions are equal
-/
theorem RenyiDivergence_def_eq_0_iff [MeasurableSpace T] [MeasurableSingletonClass T] [Countable T]
  (p q : PMF T) {α : ℝ} (Hα : 1 < α) (Hcts : AbsCts p q) :
  (RenyiDivergence_def p q α = 0) <-> (p = q) := by
  apply Iff.intro
  · intro Hrdeq
    apply Renyi_Jensen_ENNReal_converse
    · apply Hα
    · apply Hcts
    · have H1 : eexp (((α - 1)) * 0) = eexp ((α - 1) * RenyiDivergence_def p q α) := by rw [Hrdeq]
      simp at H1
      rw [RenyiDivergence_def_exp p q Hα] at H1
      rw [RenyiDivergenceExpectation p q Hα Hcts] at H1
      rw [<- H1]
      clear H1
      simp_rw [PMF_div_mul_eq p q Hcts]
      simp
  · intro Hpq
    rw [Hpq]
    symm
    apply RenyiDivergence_refl_zero
    apply Hα

/--
The logarithm in the definition of the Renyi divergence is nonnegative.
-/
lemma RenyiDivergence_def_log_sum_nonneg [MeasurableSpace T] [MeasurableSingletonClass T] [Countable T]
  (p q : PMF T) (Hac : AbsCts p q) {α : ℝ} (Hα : 1 < α ): (0 ≤ (elog (∑' x : T, (p x)^α  * (q x)^(1 - α)))) := by
  have Hrd := RenyiDivergence_def_nonneg p q Hac Hα
  rw [RenyiDivergence_def] at Hrd
  apply ofEReal_nonneg_scal_l at Hrd
  · assumption
  · apply inv_pos_of_pos
    linarith

/--
The ``ENNReal``-valued Renyi divergence between PMF's.
-/
noncomputable def RenyiDivergence (p q : PMF T) (α : ℝ) : ENNReal :=
  ENNReal.ofEReal (RenyiDivergence_def p q α)


/--
The Renyi divergence between absolutely continuous distributions is zero if and only if the
distributions are equal.
-/
theorem RenyiDivergence_aux_zero [MeasurableSpace T] [MeasurableSingletonClass T] [Countable T]
  (p q : PMF T) {α : ℝ} (Hα : 1 < α) (Hac : AbsCts p q) : p = q <-> RenyiDivergence p q α = 0 := by
  apply Iff.intro
  · intro Heq
    rw [Heq]
    rw [RenyiDivergence]
    rw [<- RenyiDivergence_refl_zero _ Hα]
    simp
  · intro H
    apply (RenyiDivergence_def_eq_0_iff p q Hα Hac).mp
    symm
    rw [RenyiDivergence] at H
    have H' := RenyiDivergence_def_nonneg p q Hac Hα
    refine (ofEReal_nonneg_inj ?mpr.Hw H').mpr ?mpr.a
    · simp
    simp [H]

/--
Renyi divergence is bounded above by the Max Divergence ε

-/
lemma RenyiDivergence_le_MaxDivergence {p q : PMF T} {ε : ENNReal} {α : ℝ} (Hα : 1 < α)
    (Hmax_divergence : ∀ t : T, (p t / q t) ≤ ENNReal.eexp ε) :
    RenyiDivergence p q α ≤ ε := by
  rw [RenyiDivergence]
  conv =>
    rhs
    rw [<- @ofEReal_toENNReal ε]
  apply ofEReal_le_mono

  -- Rewrite to expectation conditioned on q
  apply (ENNReal.ereal_smul_le_left (α - 1) ?G1 ?G2)
  case G1 =>
    rw [← EReal.coe_one]
    rw [<- EReal.coe_sub]
    apply EReal.coe_pos.mpr
    linarith
  case G2 => exact EReal.coe_lt_top _
  apply ENNReal.eexp_mono_le.mpr
  rw [RenyiDivergence_def_exp p q Hα]
  rw [RenyiDivergenceExpectation' p q Hα]

  -- Pointwise bound
  have H : ∑' (x : T), (p x / q x) ^ (α - 1) * p x  ≤ ∑' (x : T), (eexp ε) ^ (α - 1) * p x  := by
    apply ENNReal.tsum_le_tsum
    intro x
    apply mul_le_mul
    · apply ENNReal.rpow_le_rpow (Hmax_divergence x)
      linarith
    · rfl
    · apply _root_.zero_le
    · apply _root_.zero_le
  apply (le_trans H)
  rw [ENNReal.tsum_mul_left]
  rw [tsum_coe]
  simp
  have Hα_sub_pos : (0 : EReal) < α.toEReal - OfNat.ofNat 1 := EReal_sub_one_pos_of_one_lt Hα
  have H : eexp ε.toEReal ^ (α - OfNat.ofNat 1) = eexp (ε * (α - OfNat.ofNat 1)) := by
    rcases ε
    · simp
      rw [EReal.top_mul_of_pos Hα_sub_pos]
      simp
      trivial
    simp
    rw [ENNReal.ofNNReal, ENNReal.toEReal.eq_def]
    simp
    rw [ENNReal.ofReal_rpow_of_pos (exp_pos _), ← Real.exp_mul]
    rfl
  rw [H]
  clear H

  apply eexp_mono_le.mp
  rw [mul_comm]
