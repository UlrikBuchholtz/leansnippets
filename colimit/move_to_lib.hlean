/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Egbert Rijke
-/

-- these definitions and theorems should be moved to the HoTT library

import types.nat

open eq
open nat
open is_trunc
open function
namespace my

definition add.assoc (n m : ℕ) : Πk, (n + m) + k = n + (m + k) :=
nat.rec (by reflexivity) (λk, ap succ)

definition zero_add' : Πn : ℕ, n = 0 + n :=
nat.rec idp (λn, ap succ)

definition is_hset_elim_triv (D : Type) [H : is_hset D] (x : D)
  : is_hset.elim (refl x) (refl x) = idp :=
begin
  apply is_hset.elim
end

definition pathover_ap_compose {A A₁ A₂ : Type} (B₂ : A₂ → Type)
  (g : A₁ → A₂) (f : A → A₁) {a a₂ : A} (p : a = a₂)
  {b : B₂ (g (f a))} {b₂ : B₂ (g (f a₂))} (q : b =[p] b₂)
  : pathover_ap B₂ (g ∘ f) q =[ap_compose g f p]
    pathover_ap B₂ g (pathover_ap (B₂ ∘ g) f q) :=
by induction q; constructor

variables {A A' : Type} {B B' : A → Type} {C : Π⦃a⦄, B a → Type}
          {a a₂ a₃ a₄ : A} {p p' : a = a₂} {p₂ : a₂ = a₃} {p₃ : a₃ = a₄}
          {b b' : B a} {b₂ b₂' : B a₂} {b₃ : B a₃} {b₄ : B a₄}
          {c : C b} {c₂ : C b₂}

  definition change_path_pathover (q : p = p') (r : b =[p] b₂) : r =[q] change_path q r :=
  begin
    induction q,
    apply pathover_idp_of_eq,
    reflexivity
  end

  definition tro_functor (s : p = p') {q : b =[p] b₂} {q' : b =[p'] b₂}
    (t : q =[s] q') (c : C b) : q ▸o c = q' ▸o c :=
  by induction t; reflexivity

  definition pathover_idp_of_eq_tro (q : b = b') (c : C b)
    : pathover_idp_of_eq q ▸o c = transport (λy, C y) q c :=
  by induction q; reflexivity

  definition apo011_invo {C : Type} (f : Πx, B x → C) (q : b =[p] b₂)
    : apo011 f p⁻¹ q⁻¹ᵒ = (apo011 f p q)⁻¹ :=
  by induction q; reflexivity

  definition apdo_ap {D : Type} (g : D → A) (f : Πa, B a) {d d₂ : D} (p : d = d₂)
    : apdo f (ap g p) = pathover_ap B g (apdo (λx, f (g x)) p) :=
  by induction p; reflexivity

  definition cast_apo011 {P : Πa, B a → Type} {Ha : a = a₂} (Hb : b =[Ha] b₂) (p : P a b) :
    cast (apo011 P Ha Hb) p = Hb ▸o p :=
  by induction Hb; reflexivity

  definition fn_tro_eq_tro_fn {C' : Π ⦃a : A⦄, B a → Type} (q : b =[p] b₂)
    (f : Π⦃a : A⦄ (b : B a), C b → C' b) (c : C b) : f b₂ (q ▸o c) = (q ▸o (f b c)) :=
  by induction q;reflexivity

  -- TODO: prove for generalized apo
  definition apo_tro (C : Π⦃a⦄, B' a → Type) (f : Π⦃a⦄, B a → B' a) (q : b =[p] b₂)
    (c : C (f b)) : apo f q ▸o c = q ▸o c :=
  by induction q; reflexivity

  definition pathover_ap_tro {B' : A' → Type} (C : Π⦃a'⦄, B' a' → Type) (f : A → A')
    {b : B' (f a)} {b₂ : B' (f a₂)} (q : b =[p] b₂) (c : C b) : pathover_ap B' f q ▸o c = q ▸o c :=
  by induction q; reflexivity

  definition pathover_ap_invo_tro {B' : A' → Type} (C : Π⦃a'⦄, B' a' → Type) (f : A → A')
    {b : B' (f a)} {b₂ : B' (f a₂)} (q : b =[p] b₂) (c : C b₂)
    : (pathover_ap B' f q)⁻¹ᵒ ▸o c = q⁻¹ᵒ ▸o c :=
  by induction q; reflexivity

  -- TODO: prove for generalized apo
  definition apo_invo (f : Πa, B a → B' a) {Ha : a = a₂} (Hb : b =[Ha] b₂)
      : (apo f Hb)⁻¹ᵒ = apo f Hb⁻¹ᵒ :=
  by induction Hb; reflexivity

--not used

  definition pathover_ap_invo {B' : A' → Type} (f : A → A') {p : a = a₂}
    {b : B' (f a)} {b₂ : B' (f a₂)} (q : b =[p] b₂)
    : pathover_ap B' f q⁻¹ᵒ =[ap_inv f p] (pathover_ap B' f q)⁻¹ᵒ :=
  by induction q; exact idpo

  definition apo_np {B' : A' → Type} (f : A → A') (g : Πx, B' (f x)) (Ha : a = a₂)
   : g a =[Ha] g a₂ :=
  by induction Ha; exact idpo

  definition apo_np_tro {B' : A' → Type} (f : A → A') (g : Πx, B' (f x)) (Ha : a = a₂)
    (D : Π⦃x'⦄, B' x' → Type) (d : D (g a)) : apo_np f g Ha ▸o d = Ha ▸ d :=
  by induction Ha; reflexivity

end my
