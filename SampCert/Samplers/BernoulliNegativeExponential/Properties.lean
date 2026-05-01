/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.Foundations.Basic
import SampCert.Samplers.Uniform.Basic
import SampCert.Samplers.Bernoulli.Basic
import SampCert.Samplers.BernoulliNegativeExponential.Code
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# ``BernoulliNegExpSample`` Properties

This file proves evaluation and normalization for ``BernoulliNegExpSample``.
-/

noncomputable section

open PMF Nat BigOperators Finset

namespace SLang

@[simp]
theorem BernoulliExpNegSampleUnitAux_zero (num : ℕ) (den : ℕ+) (st st' : Bool × ℕ+) (wf : num ≤ den) :
  probWhileCut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) 0 st st' = 0 := by
  simp [probWhileCut]

@[simp]
theorem BernoulliExpNegSampleUnitAux_returns_false (num : ℕ) (den : ℕ+) (fuel : ℕ) (st : Bool × ℕ+) (r : ℕ+) (wf : num ≤ den) :
  probWhileCut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) fuel st (true, r) = 0 := by
  revert st r
  induction fuel
  · simp [probWhileCut]
  · rename_i fuel IH
    intro st r
    simp [probWhileCut, probWhileFunctional]
    unfold probBind
    unfold probPure
    simp [ite_apply]
    split
    · rename_i h
      cases st
      rename_i b n
      simp at h
      subst h
      conv =>
        left
        arg 1
        intro a
        rw [IH a r]
      simp
    · rename_i h
      cases st
      rename_i b n
      simp at h
      subst h
      simp

@[simp]
theorem BernoulliExpNegSampleUnitAux_ite_simpl (x r : ℕ+) (k : ENNReal) :
  @ite ENNReal (x = r + 1) (Classical.propDecidable (x = r + 1)) 0
  (if x = r + 1 then k else 0) = 0 := by
  split_ifs <;> simp

@[simp]
theorem BernoulliExpNegSampleUnitAux_succ_true (num : ℕ) (den : ℕ+) (fuel : ℕ) (st : Bool × ℕ+) (r : ℕ+) (wf : num ≤ den) :
  probWhileCut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) (succ fuel) (true, r) st =
    (num / (r * den)) * probWhileCut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) fuel (true, r + 1) st
    + (1 - (num / (r * den))) * probWhileCut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) fuel (false, r + 1) st := by
  cases st
  rename_i b' r'
  simp only [probWhileCut, probWhileFunctional, ite_apply, BernoulliExpNegSampleUnitLoop,
    Bind.bind, Pure.pure, SLang.bind_apply, SLang.pure_apply, if_true]
  rw [ENNReal.tsum_prod']
  simp only [tsum_bool]
  rw [tsum_eq_single (r + 1) (by intro b hb; simp [hb])]
  rw [tsum_eq_single (r + 1) (by intro b hb; simp [hb])]
  simp
  ring


@[simp]
theorem BernoulliExpNegSampleUnitAux_succ_false (num : ℕ) (den : ℕ+) (fuel : ℕ) (st : Bool × ℕ+) (r : ℕ+) (wf : num ≤ den) :
  probWhileCut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) (succ fuel) (false, r) st =
  if st = (false,r) then 1 else 0 := by
  cases st
  simp [probWhileCut, probWhileFunctional]

@[simp]
theorem BernoulliExpNegSampleUnitAux_monotone_counter (num : ℕ) (den : ℕ+) (fuel : ℕ) (st : Bool × ℕ+) (n : ℕ+) (wf : num ≤ den)  (h1 : st ≠ (false,n)) (h2 : st.2 ≥ n) :
  probWhileCut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) fuel st (false, n) = 0 := by
  revert st
  induction fuel
  · simp
  · rename_i fuel IH
    intro st h1 h2
    cases st
    rename_i stb stn
    simp at h1
    simp at h2
    cases stb
    · simp
      exact Ne.symm (h1 rfl)
    · simp [BernoulliExpNegSampleUnitAux_succ_true]
      have A : (false, stn + 1) ≠ (false, n) := by
        simp
        have OR : n = stn ∨ n < stn := by exact eq_or_lt_of_le h2
        cases OR
        · rename_i h
          subst h
          exact _root_.ne_of_gt le.refl
        · rename_i h
          exact _root_.ne_of_gt (le.step h)
      have B : (true, stn + 1) ≠ (false, n) := by simp
      rw [IH _ A]
      rw [IH _ B]
      simp
      exact le.step h2
      exact le.step h2

-- The following two functions are useful to keep the dependent definition of PNat under control
-- Otherwise, the terms become large and unreadable

def plus_one (k : ℕ) : ℕ+ := ⟨ k + (1 : ℕ+) , Nat.add_pos_right k le.refl ⟩

def plus_two (k fuel : ℕ) : ℕ+ := ⟨ fuel + k + 2 , Nat.add_pos_right (fuel + k) (le.step le.refl) ⟩

theorem plus_one_prop (k : ℕ) :
  plus_one k = k + 1 := by
  simp [plus_one]

-- Warning! BernoulliExpNegSampleUnitAux has a transition phase
-- This min is suspicious: (min (fuel + 2) (fuel + k + 1) - 2)
theorem BernoulliExpNegSampleUnitAux_progress (num : ℕ) (den : ℕ+) (fuel k : ℕ) (wf : num ≤ den) :
  probWhileCut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) (fuel + 2) (true, plus_one k ) (false, plus_two k fuel ) = (∏ i ∈ range fuel, (num : ENNReal) / ((k + 1 + i) * den)) * (1 - ((num : ENNReal) / ((fuel + k + 1) * den))) := by
  revert k
  induction fuel
  · intro k
    simp
    split
    · rename_i h
      rw [plus_one_prop]
      simp
    · rename_i h
      exfalso
      apply h
      apply PNat.coe_injective
      simp [plus_one, plus_two]
  · rename_i fuel IH
    intro k
    rw [BernoulliExpNegSampleUnitAux_succ_true]
    rw [BernoulliExpNegSampleUnitAux_succ_false]
    have IH' := IH (k + 1)
    clear IH
    have A : plus_one (k + 1) = plus_one k + 1 := rfl
    have B : plus_two (k + 1) fuel = plus_two k (succ fuel) := by
      apply PNat.coe_injective
      simp [plus_two]; omega
    rw [← A]
    rw [← B]
    rw [IH']
    have C : ¬ plus_two (k + 1) fuel = plus_one (k + 1) := by
      intro h
      have := congrArg PNat.val h
      simp [plus_one, plus_two] at this
      omega
    simp [C]
    have E : (fuel : ENNReal) + (k + (1 : ENNReal)) + 1 = (fuel : ENNReal) + 1 + k + 1 := by
      ring
    rw [E]
    simp [prod_range_succ']
    rw [plus_one_prop]
    have F : (∀ x ∈ range fuel,
        ((num : ENNReal) / ((k + 1 + (x + 1)) * (den : ENNReal)))
          = (num : ENNReal) / (((k + 1) + 1 + x) * (den : ENNReal))) := by
      intro x _
      congr 2; ring
    rw [Finset.prod_congr rfl F]
    push_cast
    rw [mul_comm, mul_right_comm]

theorem nat_sub_two_add_one (n : ℕ) (h : n > 1) :
  n - 2 + 1 = n - 1 := by
  omega

theorem ennreal_sub_two_add_one (n : ℕ) (h : n > 1) :
  (n : ENNReal) - 2 + 1 = (n : ENNReal) - 1 := by
  have step : ((n - 2 + 1 : ℕ) : ENNReal) = ((n - 1 : ℕ) : ENNReal) :=
    congrArg Nat.cast (nat_sub_two_add_one n h)
  simpa [Nat.cast_sub h.le, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (by omega : n ≠ 0))] using step

theorem BernoulliExpNegSampleUnitAux_progress' (num : ℕ) (den : ℕ+) (n : ℕ) (wf : num ≤ den) (h : n > 1) :
  probWhileCut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) n (true, 1 ) (false, ⟨ n , lt_of_succ_lt h ⟩ ) = (∏ i ∈ range (n - 2), (num : ENNReal) / ((1 + i) * den)) * (1 - ((num : ENNReal) / ((n - 1) * den))) := by
  have prog := BernoulliExpNegSampleUnitAux_progress num den (n - 2) 0 wf
  have A : n - 2 + 2 = n := Nat.sub_add_cancel h
  rw [A] at prog
  have B : plus_two 0 (n - 2) = ⟨ n , lt_of_succ_lt h ⟩ := by
    simp [plus_two]
    conv =>
      left
      left
      rw [A]
  rw [B] at prog
  simp [plus_one] at prog
  have C := ennreal_sub_two_add_one n h
  rw [C] at prog
  trivial

theorem BernoulliExpNegSampleUnitAux_preservation (num : ℕ) (den : ℕ+) (fuel fuel' k : ℕ) (wf : num ≤ den) (h1 : fuel ≥ fuel') :
  probWhileCut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) (1 + fuel + 2) (true, plus_one k ) (false, plus_two k fuel')
    = probWhileCut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) (fuel + 2) (true, plus_one k ) (false, plus_two k fuel') := by
  revert fuel' k
  induction fuel
  · intro fuel' k h1
    have A : fuel' = 0 := by exact le_zero.mp h1
    subst A
    simp [BernoulliExpNegSampleUnitAux_succ_true]
    -- rewrites of plus_* properties do not work because the type is wrong
    have B : ¬ plus_two k 0 = plus_one k + 1 + 1 := by
      intro h
      have := congrArg PNat.val h
      simp [plus_two, plus_one] at this
    simp [B]
  · rename_i fuel IH
    intro fuel' k h1
    conv =>
      congr
      · rw [BernoulliExpNegSampleUnitAux_succ_true]
      · rw [BernoulliExpNegSampleUnitAux_succ_true]
    have A : succ fuel + 1 = fuel + 2 := by exact rfl
    rw [A]
    have B : 1 + succ fuel + 1 = 1 + fuel + 2 := by exact rfl
    rw [B]
    have Pre : fuel ≥ fuel' - 1 := by exact sub_le_of_le_add h1
    have IH' := IH (fuel' - 1) (k + 1) Pre
    clear IH
    cases fuel'
    · rw [BernoulliExpNegSampleUnitAux_succ_false]
      rw [BernoulliExpNegSampleUnitAux_succ_false]
      have C : plus_two k Nat.zero = plus_one k + 1 := by   -- Useful for cleanup
        simp [plus_two, plus_one]
        rfl
      rw [C]
      simp
    · rename_i fuel'
      have C : succ fuel' - 1 = fuel' := rfl
      rw [C] at IH'
      have D : plus_two (k + 1) fuel' = plus_two k (succ fuel') := by
        apply PNat.coe_injective
        simp [plus_two]; omega
      rw [D] at IH'
      have E : plus_one (k + 1) = plus_one k + 1 := rfl
      rw [E] at IH'
      rw [IH']
      rfl

theorem BernoulliExpNegSampleUnitAux_preservation' (num : ℕ) (den : ℕ+) (n m : ℕ) (wf : num ≤ den) (h1 : m > 1) (h2 : n ≥ m) :
  probWhileCut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) (n + 1) (true, 1) (false, ⟨ m, zero_lt_of_lt h1 ⟩ )
    = probWhileCut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) n (true, 1) (false, ⟨ m, zero_lt_of_lt h1 ⟩) := by
  have X : n - 2 ≥ m - 2 := by exact Nat.sub_le_sub_right h2 2
  have prog := BernoulliExpNegSampleUnitAux_preservation num den (n - 2) (m - 2) 0 wf X
  have A : 1 + (n - 2) + 2 = n + 1 := by
    rw [add_assoc]
    rw [add_comm]
    rw [_root_.add_left_inj]
    rw [Nat.sub_add_cancel (Nat.lt_of_lt_of_le h1 h2)]
  have B : n - 2 + 2 = n := Nat.sub_add_cancel (Nat.lt_of_lt_of_le h1 h2)
  have C : plus_one 0 = 1 := by
    simp [plus_one]
  have D : plus_two 0 (m - 2) = ⟨ m, zero_lt_of_lt h1 ⟩ := by
    simp [plus_two]
    conv =>
      left
      left
      rw [Nat.sub_add_cancel h1]
  rw [A, B, C, D] at prog
  trivial

theorem BernoulliExpNegSampleUnitAux_characterization (num : ℕ) (den : ℕ+) (n extra : ℕ) (wf : num ≤ den) (h : n > 1) :
  probWhileCut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) (extra + n) (true, 1) (false, ⟨ n, by exact zero_lt_of_lt h ⟩)
    =  (∏ i ∈ range (n - 2), (num : ENNReal) / ((1 + i) * den)) * (1 - ((num : ENNReal) / ((n - 1) * den))) := by
  revert n
  induction extra
  · simp
    intro n h
    apply BernoulliExpNegSampleUnitAux_progress' num den n wf h
  · rename_i extra IH
    intro n h
    have IH' := IH n h
    clear IH
    rw [← BernoulliExpNegSampleUnitAux_preservation'] at IH'
    · have B : extra + n + 1 = succ extra + n := by omega
      rw [← B]
      trivial
    · trivial
    · exact Nat.le_add_left n extra

theorem BernoulliExpNegSampleUnitAux_sup (num : ℕ) (den : ℕ+) (n : ℕ+) (wf : num ≤ den) :
  ⨆ i, probWhileCut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) i (true, 1) (false, n)
    = if n = 1 then 0 else (∏ i ∈ range (n - 2), (num : ENNReal) / ((1 + i) * den)) * (1 - ((num : ENNReal) / ((n - 1) * den))) := by
  apply iSup_eq_of_tendsto
  · apply probWhileCut_monotonic
  · rw [Iff.symm (Filter.tendsto_add_atTop_iff_nat n)]
    split
    · rename_i h
      subst h
      rw [ENNReal.tendsto_atTop_zero]
      intro ε _
      existsi 0
      intro n _
      simp [BernoulliExpNegSampleUnitAux_monotone_counter]
    · rename_i h
      have h' : n > 1 := by
        by_contra h'
        simp at *
        subst h'
        contradiction
      have FOO (n_1 : ℕ) := @BernoulliExpNegSampleUnitAux_characterization num den n n_1 wf h'
      have BAR : n = (⟨(n : ℕ), Nat.zero_lt_of_lt h'⟩ : ℕ+) := rfl
      conv =>
        congr
        intro n_1
        right
        rw [BAR]
      conv =>
        congr
        intro E
        rw [FOO E]
      rw [tendsto_const_nhds_iff]

@[simp]
theorem BernoulliExpNegSampleUnitAux_at_zero (num : ℕ) (den : ℕ+) (wf : num ≤ den) :
  (BernoulliExpNegSampleUnitAux num den wf) 0 = 0 := by
  simp only [BernoulliExpNegSampleUnitAux, Bind.bind, Pure.pure, SLang.bind_apply, probWhile,
    SLang.pure_apply, ENNReal.tsum_eq_zero, _root_.mul_eq_zero, ENNReal.iSup_eq_zero, Prod.forall,
    Bool.forall_bool,
    BernoulliExpNegSampleUnitAux_returns_false, forall_const, true_or, and_true]
  intro b
  right
  split
  · rename_i h
    cases b
    rename_i b pb
    subst h
    contradiction
  simp only

theorem if_simpl' (num : ℕ) (den : ℕ+) (x n : ℕ+) :
  @ite ENNReal (x = n) (Classical.propDecidable (x = n)) 0
  (if n = x then
    (if x = 1 then 0
    else ((∏ i ∈ range (↑x - 2), ↑num / (((1 : ENNReal) + ↑i) * ↑↑den)) * (1 - ↑num / ((↑↑x - 1) * ↑↑den)))) else 0) = 0 := by
  by_cases hxn : x = n
  · simp [hxn]
  · rw [if_neg hxn, if_neg (fun h => hxn h.symm)]

theorem BernoulliExpNegSampleUnitAux_apply (num : ℕ) (den : ℕ+) (n : ℕ+) (wf : num ≤ den) :
  (BernoulliExpNegSampleUnitAux num den wf) n =
    if n = 1 then 0 else (∏ i ∈ range (n - 2), (num : ENNReal) / ((1 + i) * den)) * (1 - ((num : ENNReal) / ((n - 1) * den))) := by
  simp [BernoulliExpNegSampleUnitAux]
  rw [ENNReal.tsum_prod']
  rw [tsum_bool]
  simp [probWhile]
  simp [BernoulliExpNegSampleUnitAux_sup]
  rw [ENNReal.tsum_eq_add_tsum_ite n]
  simp
  rw [tsum_congr (fun x => if_simpl' num den x n)]
  simp

@[simp]
theorem BernoulliExpNegSampleUnitAux_at_one (num : ℕ) (den : ℕ+) (wf : num ≤ den) :
  (BernoulliExpNegSampleUnitAux num den wf) 1 = 0 := by
  change (BernoulliExpNegSampleUnitAux num den wf) (1 : ℕ+) = 0
  rw [BernoulliExpNegSampleUnitAux_apply]
  simp

theorem gamma_extract' (num : Nat) (den : PNat) (x : ENNReal) (h1 : x ≠ 0) (_h2 : x ≠ ⊤) :
  ((num : ENNReal) / (x * den)) = ((num : ENNReal) / (den : ENNReal)) * x⁻¹ := by
  have hd0 : (den : ENNReal) ≠ 0 := NeZero.natCast_ne (↑den) ENNReal
  have hxd : (x * (den : ENNReal))⁻¹ = x⁻¹ * ((den : ENNReal))⁻¹ :=
    ENNReal.mul_inv (Or.inl h1) (Or.inr hd0)
  rw [div_eq_mul_inv, hxd, div_eq_mul_inv]
  ring

theorem gamma_extract (num : Nat) (den : PNat) (n : ℕ) (_h : n > 1) :
  (∏ i ∈ range (n - 2), (num : ENNReal) / ((1 + i) * den)) =
  (((num : ENNReal) / (den : ENNReal))^(n - 2) * ((factorial (n - 2)) : ENNReal)⁻¹) := by
  have X : ∀ i : ℕ, (1 : ENNReal) + i ≠ 0 := by
    intro i
    simp
  have Y : ∀ i : ℕ, (1 : ENNReal) + i ≠ ⊤ := by
    intro i
    simp
  rw [Finset.prod_congr rfl (fun i _ => gamma_extract' _ _ _ (X i) (Y i))]
  rw [prod_mul_distrib]
  rw [← pow_eq_prod_const]
  congr
  rw [← prod_range_add_one_eq_factorial, Nat.cast_prod]
  rw [ENNReal.prod_inv_distrib (fun _ _ _ _ _ => Or.inl (by push_cast; positivity))]
  apply Finset.prod_congr rfl
  intro i _
  push_cast
  rw [add_comm]

noncomputable def mass (n : ℕ) (γ : ENNReal) := (γ^(n - 2) * (((n - 2)!) : ENNReal)⁻¹) * (1 - (γ * ((n : ENNReal) - 1)⁻¹))

theorem BernoulliExpNegSampleUnitAux_apply' (num : ℕ) (den : ℕ+) (n : ℕ) (wf : num ≤ den) (h : n > 1) (γ : ENNReal) (gam : γ = (num : ENNReal) / (den : ENNReal)) :
  (BernoulliExpNegSampleUnitAux num den wf) n = mass n γ := by
  unfold mass
  cases n
  · contradiction
  · rename_i n
    let m : ℕ+ := ⟨ succ n , by exact Fin.pos { val := n, isLt := le.refl } ⟩
    have A : n + 1 = m := rfl
    rw [A]
    rw [BernoulliExpNegSampleUnitAux_apply num den m wf]
    split
    · rename_i h'
      rw [h'] at A
      rw [A] at h
      contradiction
    · rename_i h'
      cases n
      · contradiction
      · rename_i n
        rw [gamma_extract]
        · rw [← A]
          simp only [succ_sub_succ_eq_sub, add_tsub_cancel_right, cast_succ,
            ne_eq, ENNReal.one_ne_top, not_false_eq_true, ENNReal.add_sub_cancel_right]
          have B : (n : ENNReal) + 1 ≠ 0 := by exact cast_add_one_ne_zero n
          have C : (n : ENNReal) + 1 ≠ ⊤ := by simp
          rw [gamma_extract' num den (↑n + 1) B C]
          simp only [gam]
        · rw [← A]
          simp only [gt_iff_lt, one_lt_succ_succ]

noncomputable def mass' (n : ℕ) (γ : ENNReal) := (γ^n * (((n)!) : ENNReal)⁻¹)

theorem mass'_neq_top (n : ℕ) (γ : ENNReal) (h : γ ≠ ⊤) :
  mass' n γ ≠ ⊤ := by
  unfold mass'
  rw [ne_iff_lt_or_gt]
  left
  rw [ENNReal.mul_lt_top_iff]
  left
  constructor
  · induction n
    · simp
    · rename_i n IH
      rw [_root_.pow_succ]
      rw [ENNReal.mul_lt_top_iff]
      left
      constructor
      · trivial
      · exact Ne.lt_top h
  · have A : n ! > 0 := by exact factorial_pos n
    rw [@ENNReal.inv_lt_iff_inv_lt]
    simp
    exact A

theorem mass'_series_exp (γ : ENNReal) (h : γ ≠ ⊤) :
  (∑' (i : ℕ), mass' i γ).toReal = Real.exp (γ.toReal) := by
  unfold mass'
  rw [ENNReal.tsum_toReal_eq]
  · conv =>
      left
      arg 1
      intro a
      rw [ENNReal.toReal_mul]
      rw [ENNReal.toReal_pow]
      rw [ENNReal.toReal_inv]
      simp
      rw [← division_def]
    show (fun x : ℝ => ∑' a : ℕ, x ^ a / a.factorial) γ.toReal = _
    rw [← @NormedSpace.exp_eq_tsum_div ℝ]
    rw [← Real.exp_eq_exp_ℝ]
  · intro a
    apply mass'_neq_top _ _ h

theorem mass'_series_converges (γ : ENNReal) (h : γ ≠ ⊤) :
  (∑' (i : ℕ), mass' i γ) ≠ ⊤ := by
  by_contra h'
  have A := mass'_series_exp γ h
  rw [h'] at A
  simp at A
  have B := Real.exp_pos (ENNReal.toReal γ)
  rw [← A] at B
  simp at B

theorem ite_zero_inst_propDecidable {α : Type*} {p : α → α → Prop} [∀ x y, Decidable (p x y)]
    (a : α) (f : α → ENNReal) (n : α) :
    (if p n a then (0 : ENNReal) else f n)
      = @ite ENNReal (p n a) (Classical.propDecidable (p n a)) 0 (f n) := by
  by_cases hn : p n a <;> simp [hn]

theorem mass'_series_converges' (γ : ENNReal) (h : γ ≠ ⊤) :
  (∑' (i : ℕ), mass' (i + 1) γ) ≠ ⊤ := by
  have A := mass'_series_converges γ h
  rw [ENNReal.tsum_eq_add_tsum_ite 0] at A
  have B := tsum_shift'_1 (λ x => mass' x γ)
  conv at B =>
    left; arg 1; ext n
    rw [ite_zero_inst_propDecidable 0 (fun n => mass' n γ) n]
  rw [B] at A
  by_contra h
  rw [h] at A
  simp at A

theorem mass'_series_converges'_even (γ : ENNReal) (h : γ ≠ ⊤) :
  (∑' (i : ℕ), mass' (2 * i) γ) ≠ ⊤ := by
  have A := mass'_series_converges γ h
  rw [← tsum_even_add_odd ENNReal.summable ENNReal.summable] at A
  exact fun h' => by rw [h'] at A; simp at A

theorem mass'_series_converges'_odd (γ : ENNReal) (h : γ ≠ ⊤) :
  (∑' (i : ℕ), mass' (2 * i + 1) γ) ≠ ⊤ := by
  have A := mass'_series_converges γ h
  rw [← tsum_even_add_odd ENNReal.summable ENNReal.summable] at A
  exact fun h' => by rw [h'] at A; simp at A

theorem mass_simpl (n : ℕ) (γ : ENNReal) (h : n ≥ 2) :
  mass n γ = mass' (n - 2) γ - mass' (n - 1) γ := by
  unfold mass
  unfold mass'
  rw [ENNReal.mul_sub]
  · simp only [mul_one]
    rw [mul_mul_mul_comm]
    conv =>
      left
      right
      left
      rw [mul_comm]
      rw [← _root_.pow_succ']
    rw [nat_sub_two_add_one n h]
    congr
    rw [← ENNReal.mul_inv]
    · rw [inv_eq_iff_eq_inv]
      rw [inv_inv]
      rw [mul_comm]
      have A := @Nat.mul_factorial_pred (n - 1) (Nat.sub_pos_of_lt h).ne'
      have B : n - 1 - 1 = n - 2 := rfl
      rw [B] at A
      clear B
      rw [← A]
      simp only [cast_mul, ENNReal.natCast_sub, cast_one]
    · simp only [ne_eq, cast_eq_zero, ENNReal.sub_eq_top_iff, ENNReal.natCast_ne_top,
      ENNReal.one_ne_top, not_false_eq_true, and_true, or_true]
    · simp only [ne_eq, ENNReal.natCast_ne_top, not_false_eq_true, true_or]
  · intro _ h2
    have hγ : γ ≠ ⊤ := by
      intro hγ
      subst hγ
      have hinv : ((n : ENNReal) - 1)⁻¹ ≠ 0 := by
        apply ENNReal.inv_ne_zero.mpr
        exact ENNReal.sub_ne_top (ENNReal.natCast_ne_top n)
      rw [ENNReal.top_mul hinv] at h2
      exact absurd h2 (by simp)
    rw [ne_iff_lt_or_gt]
    left
    have neq := mass'_neq_top (n - 2) γ hγ
    unfold mass' at neq
    exact lt_of_le_of_ne le_top neq

theorem if_ge_2 (x : ℕ) (num : ℕ) (den : ℕ+) (wf : num ≤ den) (gam : γ = (num : ENNReal) / (den : ENNReal)) :
  (@ite ENNReal (x = 0) (Classical.propDecidable (x = 0)) 0
  (@ite ENNReal (x = 1) (Classical.propDecidable (x = 1)) 0 (BernoulliExpNegSampleUnitAux num den wf x)))
    = if x = 0 then 0 else if x = 1 then 0 else mass x γ := by
  split_ifs with h₀ h₁
  · rfl
  · rfl
  · exact BernoulliExpNegSampleUnitAux_apply' _ _ _ wf
      (one_lt_iff_ne_zero_and_ne_one.mpr ⟨h₀, h₁⟩) γ gam

theorem mass'_antitone (n : ℕ) (γ : ENNReal) (h : γ ≤ 1) :
  mass' n γ ≥ mass' (n + 1) γ  := by
  unfold mass'
  rw [pow_add]
  simp [factorial]
  rw [ENNReal.mul_inv]
  · have A : γ ^ n * γ * (((n : ENNReal) + 1)⁻¹ * (↑n !)⁻¹)
        = (γ ^ n * (↑n !)⁻¹) * (γ * ((n : ENNReal) + 1)⁻¹) := by ring
    rw [A]
    have C : ((n: ENNReal) + 1)⁻¹ ≤ 1 := by
      simp only [ENNReal.inv_le_one, self_le_add_left]
    calc γ ^ n * (↑n !)⁻¹ * (γ * ((n : ENNReal) + 1)⁻¹)
        ≤ γ ^ n * (↑n !)⁻¹ * 1 := by
          gcongr
          exact mul_le_one' h C
      _ = γ ^ n * (↑n !)⁻¹ := mul_one _
  · simp
  · simp

theorem mass'_series_converges'_sub (γ : ENNReal) (h1 : γ ≠ ⊤) (h2 : γ ≤ 1) :
  ∑' (n : ℕ), (mass' (2 * n) γ - mass' (2 * n + 1) γ) ≠ ⊤ := by
  rw [ENNReal.tsum_sub]
  · have A := mass'_series_converges'_even _ h1
    apply ENNReal.sub_ne_top A
  · apply mass'_series_converges'_odd _ h1
  · rw [Pi.le_def]
    intro i
    rw [← ge_iff_le]
    apply mass'_antitone _ _ h2

theorem γ_ne_top (num : ℕ) (den : ℕ+) (gam : γ = (num : ENNReal) / (den : ENNReal)) :
  γ ≠ ⊤ := by
  subst gam
  rw [ne_iff_lt_or_gt]
  left
  rw [ENNReal.div_eq_inv_mul]
  rw [ENNReal.mul_lt_top_iff]
  left
  constructor
  · rw [ENNReal.inv_lt_top]
    apply NeZero.pos
  · apply (cmp_eq_gt_iff _ _).mp
    rfl

theorem γ_le_1 (num : ℕ) (den : ℕ+) (wf : num ≤ den) (gam : γ = (num : ENNReal) / (den : ENNReal)) :
  γ ≤ 1 := by
  subst gam
  rw [ENNReal.div_le_iff_le_mul (Or.inl (NeZero.natCast_ne (↑den) ENNReal))
    (Or.inl (ENNReal.natCast_ne_top _)), one_mul, Nat.cast_le]
  exact wf

theorem BernoulliExpNegSampleUnitAux_normalizes (num : ℕ) (den : ℕ+) (wf : num ≤ den) (gam : γ = (num : ENNReal) / (den : ENNReal)) :
  ∑' n : ℕ, (BernoulliExpNegSampleUnitAux num den wf) n = 1 := by
  rw [ENNReal.tsum_eq_add_tsum_ite 1]
  rw [ENNReal.tsum_eq_add_tsum_ite 0]
  simp
  rw [tsum_congr (fun x => if_ge_2 x num den wf gam)]
  rw [tsum_shift'_2]
  rw [tsum_congr (fun n => mass_simpl _ _ (by simp))]
  simp
  rw [ENNReal.tsum_sub]
  · rw [ENNReal.tsum_eq_add_tsum_ite 0]
    have X := tsum_shift'_1 (fun n => mass' n γ)
    conv =>
      left; left; right; arg 1; intro n
      rw [← ite_zero_inst_propDecidable 0 (fun n => mass' n γ) n]
    rw [X]
    rw [ENNReal.add_sub_cancel_right]
    · simp [mass']
    · apply mass'_series_converges' _ (γ_ne_top num den gam)
  · apply mass'_series_converges' _ (γ_ne_top num den gam)
  · rw [@Pi.le_def]
    intro i
    rw [← ge_iff_le]
    apply mass'_antitone
    · -- γ ≤ 1
      rw [gam]
      apply γ_le_1 num den wf rfl

theorem series_step_1 (num : Nat) (den : PNat)  (wf : num ≤ den) (γ : ENNReal) (gam : γ = (num : ENNReal) / (den : ENNReal)) :
  (∑' (a : ℕ), if a % 2 = 0 then BernoulliExpNegSampleUnitAux num den wf a else 0)
    = (∑' (n : ℕ), mass (2 * (n + 1)) γ) := by
  rw [← tsum_even_add_odd]
  · rw [tsum_congr (fun k => show (if (2 * k) % 2 = 0 then BernoulliExpNegSampleUnitAux num den wf (2 * k) else 0)
        = BernoulliExpNegSampleUnitAux num den wf (2 * k) from by simp)]
    rw [tsum_congr (fun k => show (if (2 * k + 1) % 2 = 0 then BernoulliExpNegSampleUnitAux num den wf (2 * k + 1) else 0)
        = 0 from by simp)]
    simp
    rw [ENNReal.tsum_eq_add_tsum_ite 0]
    simp only [mul_zero, BernoulliExpNegSampleUnitAux_at_zero, zero_add]
    have X := tsum_shift'_1 (fun n => BernoulliExpNegSampleUnitAux num den wf (2 * n))
    rw [tsum_congr (fun n => (ite_zero_inst_propDecidable 0
      (fun k => BernoulliExpNegSampleUnitAux num den wf (2 * k)) n).symm)]
    rw [X]
    have C : ∀ n, 2 * (n + 1) > 1 := fun n => one_lt_succ_succ (Nat.mul 2 (Nat.add n 0))
    rw [tsum_congr (fun k => BernoulliExpNegSampleUnitAux_apply' _ _ _ wf (C k) γ gam)]
  · exact ENNReal.summable
  · exact ENNReal.summable

noncomputable def mass_real (n : ℕ) (γ : ℝ) : ℝ := γ ^ n * ((n.factorial : ℝ))⁻¹

theorem series_step_4 (γ : ENNReal) (h : γ ≠ ⊤) (h' : γ ≤ 1) :
  (∑' n : ℕ, (mass' (2 * n) γ - mass' (2 * n + 1) γ))
    = ENNReal.ofReal (∑' n : ℕ, mass_real n (- γ.toReal)) := by
  rw [← @ENNReal.ofReal_toReal (∑' (n : ℕ), (mass' (2 * n) γ - mass' (2 * n + 1) γ))]
  · rw [ENNReal.tsum_sub]
    · congr
      rw [ENNReal.toReal_sub_of_le]
      · rw [ENNReal.tsum_toReal_eq (fun a => mass'_neq_top _ _ h)]
        · rw [ENNReal.tsum_toReal_eq (fun a => mass'_neq_top _ _ h)]
          · simp only [mass', ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv]
            simp
            have hinj2 : Function.Injective (fun n : ℕ => 2 * n) := fun _ _ h => by simpa using h
            have hinj2' : Function.Injective (fun n : ℕ => 2 * n + 1) := fun _ _ h => by simpa using h
            have X := NormedSpace.expSeries_div_summable (𝔸 := ℝ) (-ENNReal.toReal γ)
            have summ_mass_real : ∀ (g : ℕ → ℕ), Function.Injective g →
                Summable fun k => mass_real (g k) (-ENNReal.toReal γ) := fun g hg => by
              refine (X.comp_injective hg).congr ?_
              intro k; simp [mass_real, div_eq_mul_inv]
            have A := summ_mass_real _ hinj2
            have B := summ_mass_real _ hinj2'
            rw [← @tsum_even_add_odd ℝ _ _ _ _ (fun k => mass_real k (-ENNReal.toReal γ)) A B]
            simp only [mass_real]
            simp
            have A : ∀ k : ℕ, (-ENNReal.toReal γ) ^ (2 * k + 1) * (↑(2 * k + 1)!)⁻¹
                = - ((ENNReal.toReal γ) ^ (2 * k + 1) * (↑(2 * k + 1)!)⁻¹) := fun k => by
              rw [neg_mul_eq_neg_mul, Odd.neg_pow (Exists.intro k rfl) (ENNReal.toReal γ)]
            simp_rw [A, tsum_neg]
            rfl
      · apply ENNReal.tsum_le_tsum
        intro a
        rw [← ge_iff_le]
        apply mass'_antitone
        exact h'
      · apply mass'_series_converges'_even _ h
    · apply mass'_series_converges'_odd _ h
    · rw [Pi.le_def]
      intro i
      rw [← ge_iff_le]
      apply mass'_antitone
      exact h'
  · apply mass'_series_converges'_sub _ h
    exact h'

@[simp]
theorem BernoulliExpNegSampleUnit_apply_true (num : Nat) (den : PNat)  (wf : num ≤ den) (γ : ENNReal) (gam : γ = (num : ENNReal) / (den : ENNReal)) :
  (BernoulliExpNegSampleUnit num den wf) true = ENNReal.ofReal (Real.exp (- (γ.toReal))) := by
  have h := γ_ne_top num den gam
  have h' := γ_le_1 num den wf gam
  simp [BernoulliExpNegSampleUnit, ite_apply]
  rw [series_step_1 num den wf γ gam]
  rw [show (∑' n : ℕ, mass (2 * (n + 1)) γ) = ∑' n : ℕ, (mass' (2 * n) γ - mass' (2 * n + 1) γ)
        from tsum_congr (fun n => mass_simpl (2 * (n + 1)) γ (by simp))]
  rw [series_step_4 γ h h']
  congr
  unfold mass_real
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  simp
  congr

theorem BernoulliExpNegSampleUnit_normalizes (num : Nat) (den : PNat)  (wf : num ≤ den) (γ : ENNReal) (gam : γ = (num : ENNReal) / (den : ENNReal)) :
  (∑' b : Bool, (BernoulliExpNegSampleUnit num den wf) b) = 1 := by
  rw [tsum_bool, ← BernoulliExpNegSampleUnitAux_normalizes num den wf gam]
  simp [BernoulliExpNegSampleUnit, ite_apply]
  rw [← ENNReal.tsum_add]
  exact tsum_congr (fun b => by split <;> simp)

@[simp]
theorem BernoulliExpNegSampleUnit_apply_false (num : Nat) (den : PNat)  (wf : num ≤ den) (γ : ENNReal) (gam : γ = (num : ENNReal) / (den : ENNReal)) :
  (BernoulliExpNegSampleUnit num den wf) false = 1 - ENNReal.ofReal (Real.exp (- (γ.toReal))) := by
  have A := BernoulliExpNegSampleUnit_normalizes num den wf γ gam
  rw [tsum_bool] at A
  rw [BernoulliExpNegSampleUnit_apply_true num den wf γ gam] at A
  exact ENNReal.eq_sub_of_add_eq ENNReal.ofReal_ne_top A

theorem BernoulliExpNegSampleGenLoop_normalizes (iter : Nat) :
  (∑' b : Bool, (BernoulliExpNegSampleGenLoop iter) b) = 1 := by
  induction iter
  · simp [BernoulliExpNegSampleGenLoop]
  · rename_i iter IH
    rw [BernoulliExpNegSampleGenLoop]
    simp [ite_apply]
    rw [tsum_bool] at IH
    -- Goal: e * true + (e * false + (1 - e)) = 1
    rw [← add_assoc, ← mul_add, add_comm (BernoulliExpNegSampleGenLoop iter true), IH, mul_one,
        add_comm]
    exact tsub_add_cancel_of_le (by simp : ENNReal.ofReal (Real.exp (-1)) ≤ 1)

theorem BernoulliExpNegSampleGenLoop_apply_true (iter : Nat) :
  (BernoulliExpNegSampleGenLoop iter) true = ENNReal.ofReal (Real.exp (- iter)) := by
  induction iter
  · simp [BernoulliExpNegSampleGenLoop]
  · rename_i iter IH
    unfold BernoulliExpNegSampleGenLoop
    split
    · contradiction
    · rename_i h
      simp
      simp [IH]
      clear IH
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]

theorem BernoulliExpNegSampleGenLoop_apply_false (iter : Nat) :
  (BernoulliExpNegSampleGenLoop iter) false = 1 - ENNReal.ofReal (Real.exp (- iter)) := by
  have A := BernoulliExpNegSampleGenLoop_normalizes iter
  simp at A
  rw [BernoulliExpNegSampleGenLoop_apply_true] at A
  rw [← A]
  simp

/--
Bernoulli negative exponential sampler is a proper distribution
-/
@[simp]
theorem BernoulliExpNegSample_normalizes (num : Nat) (den : PNat) :
  (∑' b : Bool, (BernoulliExpNegSample num den) b) = 1 := by
  unfold BernoulliExpNegSample
  split
  · rename_i h
    have A := BernoulliExpNegSampleUnit_normalizes num den h ((num : NNReal) / (den : NNReal)) rfl
    simp at *
    rw [A]
  · rename_i h
    simp
    rw [← add_assoc, ← mul_add]
    have e1 : ENNReal.ofReal (Real.exp (-(((num % (den : ℕ) : ℕ) : ℝ) / ((den : ℕ) : ℝ)))) +
        (1 - ENNReal.ofReal (Real.exp (-(((num % (den : ℕ) : ℕ) : ℝ) / ((den : ℕ) : ℝ))))) = 1 := by
      rw [add_comm]
      exact tsub_add_cancel_of_le
        (ENNReal.ofReal_le_one.mpr (Real.exp_le_one_iff.mpr (by
          rw [neg_nonpos]; positivity)))
    rw [e1, mul_one]
    have B := BernoulliExpNegSampleGenLoop_normalizes (num / den)
    rw [tsum_bool] at B
    rw [add_comm]
    exact B

/--
Evaluation of Bernoulli negative exponential sampler at ``true``
-/
@[simp]
theorem BernoulliExpNegSample_apply_true (num : Nat) (den : PNat):
  (BernoulliExpNegSample num den) true = ENNReal.ofReal (Real.exp (- ((num : NNReal) / (den : NNReal)))) := by
  simp [BernoulliExpNegSample]
  split
  · rename_i h
    rw [BernoulliExpNegSampleUnit_apply_true num den h ((num : NNReal) / (den : NNReal)) rfl]
    congr
    rw [ENNReal.toReal_div]
    simp
  · rename_i h
    simp
    rw [BernoulliExpNegSampleGenLoop_apply_true]
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    congr 1
    rw [← neg_add]
    congr 1
    have hden : (den : ℝ) ≠ 0 := NeZero.natCast_ne (↑den) ℝ
    field_simp
    have h1 : ((num / (den : ℕ) : ℕ) : ℝ) * ((den : ℕ) : ℝ) + ((num % (den : ℕ) : ℕ) : ℝ)
        = (num : ℝ) := by
      have := Nat.div_add_mod num (den : ℕ)
      exact_mod_cast by linarith
    linarith

/--
Evaluation of Bernoulli negative exponential sampler at ``false``
-/
@[simp]
theorem BernoulliExpNegSample_apply_false (num : Nat) (den : PNat) :
  (BernoulliExpNegSample num den) false = 1 - ENNReal.ofReal (Real.exp (- ((num : NNReal) / (den : NNReal)))) := by
  have A := BernoulliExpNegSample_normalizes num den
  simp at A
  rw [← A]
  simp

end SLang
