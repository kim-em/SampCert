/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import SampCert.DifferentialPrivacy.Queries.MWEM.Code

/-!
# Real-valued multiplicative-weights updater

The textbook MWEM update from Hardt 2012, instantiated with
`State = Fin numBins → NNReal` and `Real.exp` for the multiplicative factor.

The synthetic state is a non-negative real-valued histogram over `Fin numBins`.
Records are bin indices directly (no separate binning function — the dataset is
already histogrammed). Queries are integer-valued coefficient vectors
`q : Fin (n+1) → Fin numBins → ℤ` with a uniform per-bin bound `Δ`.

If the renormalization total degenerates to zero, the updater returns the zero
histogram. The privacy proof does not depend on non-degeneracy.
-/

noncomputable section

open Classical Nat Int Real ENNReal NNReal

namespace SLang

variable {numBins : ℕ+} {n : ℕ} {Δ : ℕ+}

def realLinearQuery (q : Fin numBins → ℤ) (D : List (Fin numBins)) : ℤ :=
  (D.map q).sum

def realLinearQueryReal (q : Fin numBins → ℤ) (A : Fin numBins → NNReal) : ℝ :=
  ∑ b, (q b : ℝ) * (A b : ℝ)

def realScore (q : Fin numBins → ℤ) (A : Fin numBins → NNReal) (D : List (Fin numBins)) : ℤ :=
  |realLinearQuery q D - ⌊realLinearQueryReal q A⌋|

def realMWUpdate (q : Fin numBins → ℤ) (m : ℤ) (A : Fin numBins → NNReal) :
    Fin numBins → NNReal :=
  let err : ℝ := (m : ℝ) - realLinearQueryReal q A
  let unnorm : Fin numBins → ℝ := fun b => (A b : ℝ) * Real.exp ((q b : ℝ) * err / 2)
  let total : ℝ := ∑ b, unnorm b
  fun b => Real.toNNReal (unnorm b / total)

def realInit (numBins : ℕ+) : Fin numBins → NNReal :=
  fun _ => 1

theorem realLinearQuery_sens (q : Fin numBins → ℤ)
    (Hbound : ∀ b, |q b| ≤ (Δ : ℤ)) : sensitivity (realLinearQuery q) Δ := by
  intro l₁ l₂ Hn
  have qnat : ∀ k : Fin numBins, (q k).natAbs ≤ (Δ : ℕ) := fun k => by
    have := Hbound k; rw [Int.abs_eq_natAbs] at this; exact_mod_cast this
  cases Hn with
  | @Addition a b k h1 h2 => subst h1 h2; simp [realLinearQuery]; exact qnat _
  | @Deletion a b k h1 h2 => subst h1 h2; simp [realLinearQuery]; exact qnat _

lemma natAbs_abs_sub_abs_le {a b : ℤ} : (|a| - |b|).natAbs ≤ (a - b).natAbs := by
  zify; exact abs_abs_sub_abs_le_abs_sub a b

theorem realScore_sens (q : Fin numBins → ℤ) (A : Fin numBins → NNReal)
    (Hbound : ∀ b, |q b| ≤ (Δ : ℤ)) : sensitivity (realScore q A) Δ := by
  intro l₁ l₂ Hn
  have hQ : (realLinearQuery q l₁ - realLinearQuery q l₂).natAbs ≤ (Δ : ℕ) :=
    realLinearQuery_sens (Δ := Δ) q Hbound l₁ l₂ Hn
  set c : ℤ := ⌊realLinearQueryReal q A⌋
  show (|realLinearQuery q l₁ - c| - |realLinearQuery q l₂ - c|).natAbs ≤ (Δ : ℕ)
  refine le_trans natAbs_abs_sub_abs_le ?_
  rw [show realLinearQuery q l₁ - c - (realLinearQuery q l₂ - c) =
        realLinearQuery q l₁ - realLinearQuery q l₂ from by ring]
  exact hQ

def realMWUpdater (q : Fin (n+1) → Fin numBins → ℤ)
    (Hbound : ∀ i b, |q i b| ≤ (Δ : ℤ)) :
    SyntheticUpdater (Fin numBins) n Δ (Fin numBins → NNReal) (realInit numBins) where
  queries i := realLinearQuery (q i)
  scoreFn A i := realScore (q i) A
  update A i m := realMWUpdate (q i) m A
  queries_sens i := realLinearQuery_sens (q i) (Hbound i)
  scoreFn_sens A i := realScore_sens (q i) A (Hbound i)

end SLang

end
