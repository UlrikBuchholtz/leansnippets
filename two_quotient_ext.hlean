/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Floris van Doorn
-/

import hit.circle

open quotient eq circle sum sigma equiv function

section
variables {A B C : Type} {f : A → B} {a a' a₁ a₂ a₃ a₄ : A} {b b' : B}

-- move to square

  definition top_deg_square (l : a₁ = a₂) (b : a₂ = a₃) (r : a₄ = a₃) : square (l ⬝ b ⬝ r⁻¹) b l r :=
  by induction r;induction b;induction l;constructor

  definition square_inv2 {p₁ p₂ p₃ p₄ : a = a'}
    {t : p₁ = p₂} {b : p₃ = p₄} {l : p₁ = p₃} {r : p₂ = p₄} (s : square t b l r)
    : square (inverse2 t) (inverse2 b) (inverse2 l) (inverse2 r) :=
  by induction s;constructor

  definition square_con2 {p₁ p₂ p₃ p₄ : a₁ = a₂} {q₁ q₂ q₃ q₄ : a₂ = a₃}
    {t₁ : p₁ = p₂} {b₁ : p₃ = p₄} {l₁ : p₁ = p₃} {r₁ : p₂ = p₄}
    {t₂ : q₁ = q₂} {b₂ : q₃ = q₄} {l₂ : q₁ = q₃} {r₂ : q₂ = q₄}
    (s₁ : square t₁ b₁ l₁ r₁) (s₂ : square t₂ b₂ l₂ r₂)
      : square (t₁ ◾ t₂) (b₁ ◾ b₂) (l₁ ◾ l₂) (r₁ ◾ r₂) :=
  by induction s₂;induction s₁;constructor

  definition eq_tVl_of_square {t : a₁ = a₂} {b : a₃ = a₄} {l : a₁ = a₃} {r : a₂ = a₄}
    (s : square t b l r) : t⁻¹ ⬝ l = r ⬝ b⁻¹ :=
  by induction s;constructor

-- move to types.eq

  definition ap_weakly_constant [unfold-c 8] {A B : Type} {f : A → B} {b : B} (p : Πx, f x = b)
    {x y : A} (q : x = y) : ap f q = p x ⬝ (p y)⁻¹ :=
  by induction q;exact !con.right_inv⁻¹

  theorem ap_weakly_constant_eq {A B : Type} {f : A → B} {b : B} (p : Πx, f x = b)
    {x y : A} (q : x = y) :
      ap_weakly_constant p q =
      eq_con_inv_of_con_eq ((eq_of_square (square_of_pathover (apdo p q)))⁻¹ ⬝
      whisker_left (p x) (ap_constant q b)) :=
  begin
    induction q, esimp, generalize (p x), intro p, cases p, apply idpath idp
  end

  definition inv2_inv {p q : a = a'} (r : p = q) : inverse2 r⁻¹ = (inverse2 r)⁻¹ :=
  by induction r;reflexivity

  definition inv2_con {p p' p'' : a = a'} (r : p = p') (r' : p' = p'')
    : inverse2 (r ⬝ r') = inverse2 r ⬝ inverse2 r' :=
  by induction r';induction r;reflexivity

  definition con2_inv {p₁ q₁ : a₁ = a₂} {p₂ q₂ : a₂ = a₃} (r₁ : p₁ = q₁) (r₂ : p₂ = q₂)
    : (r₁ ◾ r₂)⁻¹ = r₁⁻¹ ◾ r₂⁻¹ :=
  by induction r₁;induction r₂;reflexivity

  theorem eq_con_inv_of_con_eq_whisker_left {A : Type} {a a2 a3 : A}
    {p : a = a2} {q q' : a2 = a3} {r : a = a3} (s' : q = q') (s : p ⬝ q' = r) :
    eq_con_inv_of_con_eq (whisker_left p s' ⬝ s)
      = eq_con_inv_of_con_eq s ⬝ whisker_left r (inverse2 s')⁻¹ :=
  by induction s';induction q;induction s;reflexivity

  theorem right_inv_eq_idp {A : Type} {a : A} {p : a = a} (r : p = idpath a) :
    con.right_inv p = r ◾ inverse2 r :=
  by cases r;reflexivity

-- move to a new file which both imports types.eq and types.cubical.square?

  definition ap_inv2 {p q : a = a'} (r : p = q)
    : square (ap (ap f) (inverse2 r))
             (inverse2 (ap (ap f) r))
             (ap_inv f p)
             (ap_inv f q) :=
  by induction r;exact hrfl

  definition ap_con2 {p₁ q₁ : a₁ = a₂} {p₂ q₂ : a₂ = a₃} (r₁ : p₁ = q₁) (r₂ : p₂ = q₂)
    : square (ap (ap f) (r₁ ◾ r₂))
             (ap (ap f) r₁ ◾ ap (ap f) r₂)
             (ap_con f p₁ p₂)
             (ap_con f q₁ q₂) :=
  by induction r₂;induction r₁;exact hrfl

  theorem ap_con_right_inv_sq {A B : Type} {a1 a2 : A} (f : A → B) (p : a1 = a2) :
    square (ap (ap f) (con.right_inv p))
           (con.right_inv (ap f p))
           (ap_con f p p⁻¹ ⬝ whisker_left _ (ap_inv f p))
           idp :=
  by cases p;apply hrefl

  theorem ap_con_left_inv_sq {A B : Type} {a1 a2 : A} (f : A → B) (p : a1 = a2) :
    square (ap (ap f) (con.left_inv p))
           (con.left_inv (ap f p))
           (ap_con f p⁻¹ p ⬝ whisker_right (ap_inv f p) _)
           idp :=
  by cases p;apply vrefl

  theorem ap_ap_weakly_constant {A B C : Type} (g : B → C) {f : A → B} {b : B}
    (p : Πx, f x = b) {x y : A} (q : x = y) :
    square (ap (ap g) (ap_weakly_constant p q))
           (ap_weakly_constant (λa, ap g (p a)) q)
           (ap_compose g f q)⁻¹
           (!ap_con ⬝ whisker_left _ !ap_inv) :=
  begin
    induction q, esimp, generalize (p x), intro p, cases p, apply ids
--    induction q, rewrite [↑ap_compose,ap_inv], apply hinverse, apply ap_con_right_inv_sq,
  end

  theorem ap_ap_compose {A B C D : Type} (h : C → D) (g : B → C) (f : A → B)
    {x y : A} (p : x = y) :
    square (ap_compose (h ∘ g) f p)
           (ap (ap h) (ap_compose g f p))
           (ap_compose h (g ∘ f) p)
           (ap_compose h g (ap f p)) :=
  by induction p;exact ids

  theorem ap_compose_inv {A B C : Type} (g : B → C) (f : A → B)
    {x y : A} (p : x = y) :
    square (ap_compose g f p⁻¹)
           (inverse2 (ap_compose g f p) ⬝ (ap_inv g (ap f p))⁻¹)
           (ap_inv (g ∘ f) p)
           (ap (ap g) (ap_inv f p)) :=
  by induction p;exact ids

  theorem ap_compose_con (g : B → C) (f : A → B) (p : a₁ = a₂) (q : a₂ = a₃) :
    square (ap_compose g f (p ⬝ q))
           (ap_compose g f p ◾ ap_compose g f q ⬝ (ap_con g (ap f p) (ap f q))⁻¹)
           (ap_con (g ∘ f) p q)
           (ap (ap g) (ap_con f p q)) :=
  by induction q;induction p;exact ids

  theorem ap_compose_natural {A B C : Type} (g : B → C) (f : A → B)
    {x y : A} {p q : x = y} (r : p = q) :
    square (ap (ap (g ∘ f)) r)
           (ap (ap g ∘ ap f) r)
           (ap_compose g f p)
           (ap_compose g f q) :=
  natural_square (ap_compose g f) r

-- definition naturality_apdo {A : Type} {B : A → Type} {a a₂ : A} {f g : Πa, B a}
--   (H : f ~ g) (p : a = a₂)
--   : squareover B vrfl (apdo f p) (apdo g p)
--                       (pathover_idp_of_eq (H a)) (pathover_idp_of_eq (H a₂)) :=
-- by induction p;esimp;exact hrflo

definition naturality_apdo_eq {A : Type} {B : A → Type} {a a₂ : A} {f g : Πa, B a}
  (H : f ~ g) (p : a = a₂)
  : apdo f p = concato_eq (eq_concato (H a) (apdo g p)) (H a₂)⁻¹ :=
begin
  induction p, esimp,
  generalizes [H a, g a], intro ga Ha, induction Ha,
  reflexivity
end

end



namespace two_quotient

  section
  parameters {A : Type}
             (R : A → A → Type)

  -- equivalence closure
  inductive e_closure : A → A → Type :=
  | of_rel : Π{a a'} (r : R a a'), e_closure a a'
  | refl : Πa, e_closure a a
  | symm : Π{a a'} (r : e_closure a a'), e_closure a' a
  | trans : Π{a a' a''} (r : e_closure a a') (r' : e_closure a' a''), e_closure a a''
  open e_closure
  local abbreviation T := e_closure
  variables ⦃a a' : A⦄ {s : R a a'} {r : T a a}

  protected definition e_closure.elim {B : Type} {f : A → B}
    (e : Π⦃a a' : A⦄, R a a' → f a = f a') (t : T a a') : f a = f a' :=
  begin
    induction t,
      exact e r,
      reflexivity,
      exact v_0⁻¹,
      exact v_0 ⬝ v_1
  end

  definition ap_e_closure_elim_h {B C : Type} {f : A → B} {g : B → C}
    (e : Π⦃a a' : A⦄, R a a' → f a = f a')
    {e' : Π⦃a a' : A⦄, R a a' → g (f a) = g (f a')}
    (p : Π⦃a a' : A⦄ (s : R a a'), ap g (e s) = e' s) (t : T a a')
    : ap g (e_closure.elim e t) = e_closure.elim e' t :=
  begin
    induction t,
      apply p,
      reflexivity,
      exact ap_inv g (e_closure.elim e r) ⬝ inverse2 v_0,
      exact ap_con g (e_closure.elim e r) (e_closure.elim e r') ⬝ (v_0 ◾ v_1)
  end

  definition ap_e_closure_elim {B C : Type} {f : A → B} (g : B → C)
    (e : Π⦃a a' : A⦄, R a a' → f a = f a') (t : T a a')
    : ap g (e_closure.elim e t) = e_closure.elim (λa a' r, ap g (e r)) t :=
  ap_e_closure_elim_h e (λa a' s, idp) t

  definition ap_e_closure_elim_h_eq {B C : Type} {f : A → B} {g : B → C}
    (e : Π⦃a a' : A⦄, R a a' → f a = f a')
    {e' : Π⦃a a' : A⦄, R a a' → g (f a) = g (f a')}
    (p : Π⦃a a' : A⦄ (s : R a a'), ap g (e s) = e' s) (t : T a a')
    : ap_e_closure_elim_h e p t =
      ap_e_closure_elim g e t ⬝ ap (λx, e_closure.elim x t) (eq_of_homotopy3 p) :=
  begin
    fapply homotopy3.rec_on p,
    intro q, esimp at q, induction q,
    esimp, rewrite eq_of_homotopy3_id
  end

  theorem ap_ap_e_closure_elim_h {B C D : Type} {f : A → B}
    {g : B → C} (h : C → D)
    (e : Π⦃a a' : A⦄, R a a' → f a = f a')
    {e' : Π⦃a a' : A⦄, R a a' → g (f a) = g (f a')}
    (p : Π⦃a a' : A⦄ (s : R a a'), ap g (e s) = e' s) (t : T a a')
    : square (ap (ap h) (ap_e_closure_elim_h e p t))
             (ap_e_closure_elim_h e (λa a' s, ap_compose h g (e s)) t)
             (ap_compose h g (e_closure.elim e t))⁻¹
             (ap_e_closure_elim_h e' (λa a' s, (ap (ap h) (p s))⁻¹) t) :=
  begin
    induction t,
    { unfold [ap_e_closure_elim_h,e_closure.elim],
      apply square_of_eq, exact !con.right_inv ⬝ !con.left_inv⁻¹},
    { apply ids},
    { rewrite [↑e_closure.elim,↓e_closure.elim e r,
               ↑ap_e_closure_elim_h,
               ↓ap_e_closure_elim_h e p r,
               ↓ap_e_closure_elim_h e (λa a' s, ap_compose h g (e s)) r,
               ↓ap_e_closure_elim_h e' (λa a' s, (ap (ap h) (p s))⁻¹) r,
               ap_con (ap h)],
      refine (transpose !ap_compose_inv)⁻¹ᵛ ⬝h _,
      rewrite [con_inv,inv_inv,-inv2_inv],
      exact !ap_inv2 ⬝v square_inv2 v_0},
    { rewrite [↑e_closure.elim,↓e_closure.elim e r, ↓e_closure.elim e r',
               ↑ap_e_closure_elim_h,
               ↓ap_e_closure_elim_h e p r,
               ↓ap_e_closure_elim_h e (λa a' s, ap_compose h g (e s)) r,
               ↓ap_e_closure_elim_h e' (λa a' s, (ap (ap h) (p s))⁻¹) r,
               ↓ap_e_closure_elim_h e p r',
               ↓ap_e_closure_elim_h e (λa a' s, ap_compose h g (e s)) r',
               ↓ap_e_closure_elim_h e' (λa a' s, (ap (ap h) (p s))⁻¹) r',
               ap_con (ap h)],
      refine (transpose !ap_compose_con)⁻¹ᵛ ⬝h _,
      rewrite [con_inv,inv_inv,con2_inv],
      refine !ap_con2 ⬝v square_con2 v_0 v_1},
  end

  theorem ap_ap_e_closure_elim {B C D : Type} {f : A → B}
    (g : B → C) (h : C → D)
    (e : Π⦃a a' : A⦄, R a a' → f a = f a') (t : T a a')
    : square (ap (ap h) (ap_e_closure_elim g e t))
             (ap_e_closure_elim_h e (λa a' s, ap_compose h g (e s)) t)
             (ap_compose h g (e_closure.elim e t))⁻¹
             (ap_e_closure_elim h (λa a' r, ap g (e r)) t) :=
  !ap_ap_e_closure_elim_h

  parameter (Q : Π⦃a⦄, T a a → Type)


  local abbreviation B := A ⊎ Σ(a : A) (r : T a a), Q r

  inductive pre_two_quotient_rel : B → B → Type :=
  | pre_Rmk {} : Π⦃a a'⦄ (r : R a a'), pre_two_quotient_rel (inl a) (inl a')
  --BUG: if {} not provided, the alias for pre_Rmk is wrong

  definition pre_two_quotient := quotient pre_two_quotient_rel

  open pre_two_quotient_rel
  local abbreviation C := quotient pre_two_quotient_rel
  protected definition j [constructor] (a : A) : C := class_of pre_two_quotient_rel (inl a)
  protected definition pre_aux [constructor] (q : Q r) : C :=
  class_of pre_two_quotient_rel (inr ⟨a, r, q⟩)
  protected definition e (s : R a a') : j a = j a' := eq_of_rel _ (pre_Rmk s)
  protected definition et (t : T a a') : j a = j a' := e_closure.elim e t
  protected definition f [unfold-c 7] (q : Q r) : S¹ → C :=
  circle.elim (j a) (et r)

  protected definition pre_rec [unfold-c 8] {P : C → Type}
    (Pj : Πa, P (j a)) (Pa : Π⦃a : A⦄ ⦃r : T a a⦄ (q : Q r), P (pre_aux q))
    (Pe : Π⦃a a' : A⦄ (s : R a a'), Pj a =[e s] Pj a') (x : C) : P x :=
  begin
    induction x with p,
    { induction p,
      { apply Pj},
      { induction a with a1 a2, induction a2, apply Pa}},
    { induction H, esimp, apply Pe},
  end

  protected definition pre_elim [unfold-c 8] {P : Type} (Pj : A → P)
    (Pa : Π⦃a : A⦄ ⦃r : T a a⦄, Q r → P) (Pe : Π⦃a a' : A⦄ (s : R a a'), Pj a = Pj a') (x : C)
    : P :=
  pre_rec Pj Pa (λa a' s, pathover_of_eq (Pe s)) x

  protected theorem rec_e {P : C → Type}
    (Pj : Πa, P (j a)) (Pa : Π⦃a : A⦄ ⦃r : T a a⦄ (q : Q r), P (pre_aux q))
    (Pe : Π⦃a a' : A⦄ (s : R a a'), Pj a =[e s] Pj a') ⦃a a' : A⦄ (s : R a a')
    : apdo (pre_rec Pj Pa Pe) (e s) = Pe s :=
  !rec_eq_of_rel

  protected theorem elim_e {P : Type} (Pj : A → P) (Pa : Π⦃a : A⦄ ⦃r : T a a⦄, Q r → P)
    (Pe : Π⦃a a' : A⦄ (s : R a a'), Pj a = Pj a') ⦃a a' : A⦄ (s : R a a')
    : ap (pre_elim Pj Pa Pe) (e s) = Pe s :=
  begin
    apply eq_of_fn_eq_fn_inv !(pathover_constant (e s)),
    rewrite [▸*,-apdo_eq_pathover_of_eq_ap,↑pre_elim,rec_e],
  end

  protected definition elim_et {P : Type} (Pj : A → P) (Pa : Π⦃a : A⦄ ⦃r : T a a⦄, Q r → P)
    (Pe : Π⦃a a' : A⦄ (s : R a a'), Pj a = Pj a') ⦃a a' : A⦄ (t : T a a')
    : ap (pre_elim Pj Pa Pe) (et t) = e_closure.elim Pe t :=
  ap_e_closure_elim_h e (elim_e Pj Pa Pe) t

  inductive two_quotient_rel : C → C → Type :=
  | Rmk {} : Π{a : A} {r : T a a} (q : Q r) (x : circle), two_quotient_rel (f q x) (pre_aux q)

  open two_quotient_rel
  definition two_quotient := quotient two_quotient_rel
  local abbreviation D := two_quotient
  local abbreviation i := class_of two_quotient_rel
  definition incl0 (a : A) : D := i (j a)
  definition aux (q : Q r) : D := i (pre_aux q)
  definition incl1 (s : R a a') : incl0 a = incl0 a' := ap i (e s)
  definition inclt (t : T a a') : incl0 a = incl0 a' := e_closure.elim incl1 t
  -- "wrong" version inclt, which is ap i (p ⬝ q) instead of ap i p ⬝ ap i q
  -- it is used in the proof, because inclt is easier to work with
  definition incltw (t : T a a') : incl0 a = incl0 a' := ap i (et t)

  definition inclt_eq_incltw (t : T a a') : inclt t = incltw t :=
  (ap_e_closure_elim i e t)⁻¹

  definition incl2' (q : Q r) (x : S¹) : i (f q x) = aux q :=
  eq_of_rel two_quotient_rel (Rmk q x)

  definition incl2w (q : Q r) : incltw r = idp :=
  (ap02 i (elim_loop (j a) (et r))⁻¹) ⬝
  (ap_compose i (f q) loop)⁻¹ ⬝
  ap_weakly_constant (incl2' q) loop ⬝
  !con.right_inv

  definition incl2 (q : Q r) : inclt r = idp :=
  inclt_eq_incltw r ⬝ incl2w q

  local attribute two_quotient f i incl0 aux incl1 incl2' inclt [reducible]
  local attribute i aux incl0 [constructor]
  --TO CONSIDER: should all definitions about pre-structure be reducible?
  protected definition elim {P : Type} (P0 : A → P)
    (P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a = P0 a')
    (P2 : Π⦃a : A⦄ ⦃r : T a a⦄ (q : Q r), e_closure.elim P1 r = idp)
    (x : D) : P :=
  begin
    induction x,
    { refine (pre_elim _ _ _ a),
      { exact P0},
      { intro a r q, exact P0 a},
      { exact P1}},
    { exact abstract begin induction H, induction x,
      { exact idpath (P0 a)},
      { unfold f, apply pathover_eq, apply hdeg_square,
        exact abstract ap_compose (pre_elim P0 _ P1) (f q) loop ⬝
              ap _ !elim_loop ⬝
              !elim_et ⬝
              P2 q ⬝
              !ap_constant⁻¹ end
} end end},
  end
  local attribute elim [unfold-c 8]

  protected definition elim_on {P : Type} (x : D) (P0 : A → P)
    (P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a = P0 a')
    (P2 : Π⦃a : A⦄ ⦃r : T a a⦄ (q : Q r), e_closure.elim P1 r = idp)
     : P :=
  elim P0 P1 P2 x

  definition elim_incl1 {P : Type} {P0 : A → P}
    {P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a = P0 a'}
    (P2 : Π⦃a : A⦄ ⦃r : T a a⦄ (q : Q r), e_closure.elim P1 r = idp)
    ⦃a a' : A⦄ (s : R a a') : ap (elim P0 P1 P2) (incl1 s) = P1 s :=
  (ap_compose (elim P0 P1 P2) i (e s))⁻¹ ⬝ !elim_e

  definition elim_inclt {P : Type} {P0 : A → P}
    {P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a = P0 a'}
    (P2 : Π⦃a : A⦄ ⦃r : T a a⦄ (q : Q r), e_closure.elim P1 r = idp)
    ⦃a a' : A⦄ (t : T a a') : ap (elim P0 P1 P2) (inclt t) = e_closure.elim P1 t :=
  ap_e_closure_elim_h incl1 (elim_incl1 P2) t

  definition elim_incltw {P : Type} {P0 : A → P}
    {P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a = P0 a'}
    (P2 : Π⦃a : A⦄ ⦃r : T a a⦄ (q : Q r), e_closure.elim P1 r = idp)
    ⦃a a' : A⦄ (t : T a a') : ap (elim P0 P1 P2) (incltw t) = e_closure.elim P1 t :=
  (ap_compose (elim P0 P1 P2) i (et t))⁻¹ ⬝ !elim_et

  theorem elim_inclt_eq_elim_incltw {P : Type} {P0 : A → P}
    {P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a = P0 a'}
    (P2 : Π⦃a : A⦄ ⦃r : T a a⦄ (q : Q r), e_closure.elim P1 r = idp)
    ⦃a a' : A⦄ (t : T a a')
    : elim_inclt P2 t = ap (ap (elim P0 P1 P2)) (inclt_eq_incltw t) ⬝ elim_incltw P2 t :=
  begin
    unfold [elim_inclt,elim_incltw,inclt_eq_incltw,et],
    refine !ap_e_closure_elim_h_eq ⬝ _,
    rewrite [ap_inv,-con.assoc],
    xrewrite [eq_tVl_of_square (ap_ap_e_closure_elim i (elim P0 P1 P2) e t)],
    rewrite [↓incl1,con.assoc], apply whisker_left,
    rewrite [↑[elim_et,elim_incl1],+ap_e_closure_elim_h_eq,con_inv,↑[i,function.compose]],
    rewrite [-con.assoc (_ ⬝ _),con.assoc _⁻¹,con.left_inv,▸*,-ap_inv,-ap_con],
    apply ap (ap _),
    krewrite [-eq_of_homotopy3_inv,-eq_of_homotopy3_con]
  end

  definition elim_incl2'_incl0 {P : Type} {P0 : A → P}
    {P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a = P0 a'}
    (P2 : Π⦃a : A⦄ ⦃r : T a a⦄ (q : Q r), e_closure.elim P1 r = idp)
    ⦃a : A⦄ ⦃r : T a a⦄ (q : Q r) : ap (elim P0 P1 P2) (incl2' q base) = idpath (P0 a) :=
  !elim_eq_of_rel

  -- set_option pp.implicit true
  theorem elim_incl2w {P : Type} (P0 : A → P)
    (P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a = P0 a')
    (P2 : Π⦃a : A⦄ ⦃r : T a a⦄ (q : Q r), e_closure.elim P1 r = idp)
    ⦃a : A⦄ ⦃r : T a a⦄ (q : Q r)
    : square (ap02 (elim P0 P1 P2) (incl2w q)) (P2 q) (elim_incltw P2 r) idp :=
  begin
    esimp [incl2w,ap02],
    rewrite [+ap_con (ap _),▸*],
    xrewrite [-ap_compose (ap _) (ap i)],
    rewrite [+ap_inv],
    xrewrite [eq_top_of_square
               ((ap_compose_natural (elim P0 P1 P2) i (elim_loop (j a) (et r)))⁻¹ʰ⁻¹ᵛ ⬝h
               (ap_ap_compose (elim P0 P1 P2) i (f q) loop)⁻¹ʰ⁻¹ᵛ ⬝h
               ap_ap_weakly_constant (elim P0 P1 P2) (incl2' q) loop ⬝h
               ap_con_right_inv_sq (elim P0 P1 P2) (incl2' q base)),
               ↑[elim_incltw]],
    apply whisker_tl,
    rewrite [ap_weakly_constant_eq],
    xrewrite [naturality_apdo_eq (λx, !elim_eq_of_rel) loop],
    rewrite [↑elim_2,rec_loop,square_of_pathover_concato_eq,square_of_pathover_eq_concato,
            eq_of_square_vconcat_eq,eq_of_square_eq_vconcat],
    apply eq_vconcat,
    { apply ap (λx, _ ⬝ eq_con_inv_of_con_eq ((_ ⬝ x ⬝ _)⁻¹ ⬝ _) ⬝ _),
      transitivity _, apply ap eq_of_square,
        apply to_right_inv !pathover_eq_equiv_square (hdeg_square (elim_1 P A R Q P0 P1 a r q P2)),
      transitivity _, apply eq_of_square_hdeg_square,
      unfold elim_1, reflexivity},
    rewrite [+con_inv,whisker_left_inv,+inv_inv,-whisker_right_inv,
             con.assoc (whisker_left _ _),con.assoc _ (whisker_right _ _),▸*,
             whisker_right_con_whisker_left _ !ap_constant],
    xrewrite [-con.assoc _ _ (whisker_right _ _)],
    rewrite [con.assoc _ _ (whisker_left _ _),idp_con_whisker_left,▸*,
             con.assoc _ !ap_constant⁻¹,con.left_inv],
    xrewrite [eq_con_inv_of_con_eq_whisker_left,▸*],
    rewrite [+con.assoc _ _ !con.right_inv,
             right_inv_eq_idp (
               (λ(x : ap (elim P0 P1 P2) (incl2' q base) = idpath
               (elim P0 P1 P2 (class_of two_quotient_rel (f q base)))), x)
                (elim_incl2'_incl0 P2 q)),
             ↑[whisker_left]],
    xrewrite [con2_con_con2],
    rewrite [idp_con,↑elim_incl2'_incl0,con.left_inv,whisker_right_inv,↑whisker_right],
    xrewrite [con.assoc _ _ (_ ◾ _)],
    rewrite [con.left_inv,▸*,-+con.assoc,con.assoc _⁻¹,↑[elim,function.compose],con.left_inv,
             ▸*,↑j,con.left_inv,idp_con],
    apply square_of_eq, reflexivity
  end

  theorem elim_incl2 {P : Type} (P0 : A → P)
    (P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a = P0 a')
    (P2 : Π⦃a : A⦄ ⦃r : T a a⦄ (q : Q r), e_closure.elim P1 r = idp)
    ⦃a : A⦄ ⦃r : T a a⦄ (q : Q r)
    : square (ap02 (elim P0 P1 P2) (incl2 q)) (P2 q) (elim_inclt P2 r) idp :=
  begin
    rewrite [↑incl2,↑ap02,ap_con,elim_inclt_eq_elim_incltw],
    apply whisker_tl,
    apply elim_incl2w
  end

end
namespace e_closure
  infix `⬝r`:75 := e_closure.trans
  postfix `⁻¹ʳ`:(max+10) := e_closure.symm
end e_closure
end two_quotient

--attribute two_quotient.j [constructor] --TODO
attribute /-two_quotient.rec-/ two_quotient.elim [unfold-c 8] [recursor 8]
--attribute two_quotient.elim_type [unfold-c 9]
attribute /-two_quotient.rec_on-/ two_quotient.elim_on [unfold-c 5]
--attribute two_quotient.elim_type_on [unfold-c 6]