/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Egbert Rijke
-/

import types.nat

open nat eq equiv sigma sigma.ops

namespace seq_colim

  definition seq_diagram [class] (A : ℕ → Type) : Type := Π⦃n⦄, A n → A (succ n)
  -- structure seq_diagram [class] (A : ℕ → Type) : Type :=
  -- (f : Πn, A n → A (succ n))

  structure Seq_diagram : Type :=
    (carrier : ℕ → Type)
    (struct : seq_diagram carrier)

  protected abbreviation Mk [constructor] := Seq_diagram.mk
  attribute Seq_diagram.carrier [coercion]
  attribute Seq_diagram.struct [instance] [priority 10000] [coercion]

  variables {A : ℕ → Type} [f : seq_diagram A]
  variables {n : ℕ} (a : A n)
  include f

  definition rep (k : ℕ) (a : A n) : A (n + k) :=
  by induction k;exact a;exact f v_0

  definition rep_f (k : ℕ) (a : A n) : rep k (f a) =[succ_add n k] rep (succ k) a :=
  begin
    induction k with k IH,
    { esimp [succ_add], constructor},
    { esimp [succ_add,add_succ], apply to_fun !pathover_compose,
      exact apo f IH}
  end

  definition f_rep (k : ℕ) (a : A n) : f (rep k a) = rep (succ k) a := idp

  variable (A)
  definition shift_diag [instance] [unfold-full] : seq_diagram (λn, A (succ n)) :=
  λn a, f a

  definition kshift_diag [instance] [unfold-full] [priority 800] (k : ℕ)
    : seq_diagram (λn, A (k + n)) :=
  λn a, f a

  definition arrow_left_diag [instance] [unfold-full] (X : Type)
    : seq_diagram (λn, X → A n) :=
  λn g x, f (g x)

  variable {A}
  section over
  variable (P : Π⦃n⦄, A n → Type)

  definition seq_diagram_over [class] : Type := Π⦃n⦄ {a : A n}, P a → P (f a)

  variable [g : seq_diagram_over P]
  include g
  definition seq_diagram_of_over [instance] {n : ℕ} (a : A n)
    : seq_diagram (λk, P (rep k a)) :=
  λk p, g p

  definition seq_diagram_sigma [instance] : seq_diagram (λn, Σ(x : A n), P x) :=
  λn v, ⟨f v.1, g v.2⟩

  theorem rep_f_equiv (k : ℕ) : P (rep (succ k) a) ≃ P (rep k (f a)) :=
  equiv_of_eq (apo011 P _ (rep_f k a))⁻¹

  end over

end seq_colim
