/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import SampCert.DifferentialPrivacy.Abstract
import SampCert.DifferentialPrivacy.Pure.System
import SampCert.DifferentialPrivacy.Queries.ReportNoisyMax.Code

/-!
# MWEM mechanism (Hardt 2012)

Each round selects a query via Report-Noisy-Max, releases a noisy answer via the
Laplace mechanism, and post-processes the synthetic state. The synthetic state
type and update rule are abstracted as a `SyntheticUpdater`, so the privacy
proof works uniformly over any choice of updater (real-valued multiplicative
weights, rational, integer, identity, etc.).
-/

noncomputable section

namespace SLang

variable {X : Type}

structure SyntheticUpdater (X : Type) (n : ℕ) (Δ : ℕ+) (State : Type) (init : State) where
  queries      : Fin (n+1) → List X → ℤ
  scoreFn      : State → Fin (n+1) → List X → ℤ
  update       : State → Fin (n+1) → ℤ → State
  queries_sens : ∀ i, sensitivity (queries i) Δ
  scoreFn_sens : ∀ A i, sensitivity (scoreFn A i) Δ

variable {n : ℕ} {Δ : ℕ+} {State : Type} {init : State}

def mwemRound (U : SyntheticUpdater X n Δ State init) (ε₁ ε₂ : ℕ+) (A : State) :
    Mechanism X (Fin (n+1) × ℤ) :=
  privComposeAdaptive
    (privReportNoisyMax n (U.scoreFn A) Δ ε₁ ε₂)
    (fun i => privNoisedQueryPure (U.queries i) Δ ε₁ ε₂)

def mwem (U : SyntheticUpdater X n Δ State init) (ε₁ ε₂ : ℕ+) :
    ℕ → State → Mechanism X (List (Fin (n+1) × ℤ))
  | 0,     _ => privConst []
  | T+1,   A =>
    privPostProcess
      (privComposeAdaptive (mwemRound U ε₁ ε₂ A)
        (fun im => mwem U ε₁ ε₂ T (U.update A im.1 im.2)))
      (fun (im, hist) => im :: hist)

end SLang

end
