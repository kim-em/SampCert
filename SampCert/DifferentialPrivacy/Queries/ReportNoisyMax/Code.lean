/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import SampCert.DifferentialPrivacy.Abstract
import SampCert.DifferentialPrivacy.Pure.System

/-!
# Report Noisy Max (Laplace variant)

Selection mechanism: given a finite, nonempty family of integer-valued queries
each of sensitivity `Δ`, draw independent discrete Laplace noise per query and
return the index of the largest noised score. This is `(ε₁/ε₂)`-DP independent
of the number of candidates.
-/

noncomputable section

namespace SLang

variable {T : Type}

/--
Sample independent Laplace noise for each of `n+1` queries, returning the joint
vector of noised values. Implemented as a fold over `Fin (n+1)`.
-/
def privNoisedFamily (n : ℕ) (s : Fin (n+1) → List T → ℤ) (Δ ε₁ ε₂ : ℕ+) (l : List T) :
    PMF (Fin (n+1) → ℤ) :=
  match n with
  | 0 =>
    (privNoisedQueryPure (s 0) (2 * Δ) ε₁ ε₂ l).bind (fun z => PMF.pure (fun _ => z))
  | Nat.succ n' =>
    (privNoisedFamily n' (fun i => s i.castSucc) Δ ε₁ ε₂ l).bind (fun rest =>
      (privNoisedQueryPure (s (Fin.last (n'+1))) (2 * Δ) ε₁ ε₂ l).bind (fun last =>
        PMF.pure (fun i => if h : i.val < n'+1 then rest ⟨i.val, h⟩ else last)))

/--
Argmax of a function `Fin (n+1) → ℤ`, returning the largest `i` achieving the
maximum (ties broken by taking the larger index).
-/
def Fin.argmax (n : ℕ) (f : Fin (n+1) → ℤ) : Fin (n+1) :=
  match n with
  | 0 => 0
  | Nat.succ n' =>
    let prev := Fin.argmax n' (fun i => f i.castSucc)
    let last : Fin (n'+2) := Fin.last (n'+1)
    if f last < f prev.castSucc
      then prev.castSucc
      else last

/--
Report-Noisy-Max with discrete Laplace noise.

Given `n+1` candidate queries `s : Fin (n+1) → List T → ℤ` each of sensitivity
`Δ`, sample independent Laplace noise (scaled to `(2Δ * ε₂) / ε₁`) for each, and
return the index of the largest noised value.

The mechanism is `(ε₁/ε₂)`-DP regardless of `n`.
-/
def privReportNoisyMax (n : ℕ) (s : Fin (n+1) → List T → ℤ) (Δ ε₁ ε₂ : ℕ+) (l : List T) :
    PMF (Fin (n+1)) :=
  (privNoisedFamily n s Δ ε₁ ε₂ l).bind (fun noised => PMF.pure (Fin.argmax n noised))

end SLang

end
