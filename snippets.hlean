import hit.pushout types.nat.basic

/---------------------------------------------------------------------------------------------------
  show that type quotient preserves equivalence
---------------------------------------------------------------------------------------------------/
namespace type_quotient
  open equiv.ops equiv
  universe variables u v
  variables {A B : Type.{u}} {R : A → A → Type.{v}} {S : B → B → Type.{v}}

  definition type_quotient_equiv (f : A ≃ B) (g : Π(a a' : A), R a a' ≃ S (f a) (f a'))
    : type_quotient R ≃ type_quotient S :=
  begin
    revert S g, eapply (equiv.rec_on_ua_idp f), esimp, intro S g,
    have H : R = S,
      by intros, apply eq_of_homotopy, intro a, apply eq_of_homotopy, intro a',
         eapply (equiv.rec_on_ua_idp (g a a')), reflexivity,
    cases H, reflexivity
  end
end type_quotient

/---------------------------------------------------------------------------------------------------
  test of pushouts: show that the pushout of the diagram
    1 <- 0 -> 1
  is equivalent to 2.
---------------------------------------------------------------------------------------------------/
namespace pushout
  open equiv is_equiv unit bool
  private definition unit_of_empty (u : empty) : unit := star

  example : pushout unit_of_empty unit_of_empty ≃ bool :=
  begin
    fapply equiv.MK,
    { intro x, induction x with u u c,
        exact ff,
        exact tt,
        cases c},
    { intro b, cases b,
        exact (!inl ⋆),
        exact (!inr ⋆)},
    { intro b, cases b,
        reflexivity,
        reflexivity},
    { intro x, induction x with u u c,
        cases u, reflexivity,
        cases u, reflexivity,
        cases c},
  end

end pushout

/---------------------------------------------------------------------------------------------------
  (part of) encode-decode proof to characterize the equality type of the natural numbers
  this is not needed in the library, since we use Hedberg's Theorem to show that the natural numbers
  is a set
---------------------------------------------------------------------------------------------------/
namespace nat
  open unit eq is_trunc
  protected definition code (n m : ℕ) : Type₀ :=
  begin
    revert m,
    induction n with n IH,
    { intro m, cases m,
      { exact unit},
      { exact empty}},
    { intro m, cases m with m,
      { exact empty},
      { exact IH m}},
  end

  protected definition encode {n m : ℕ} (p : n = m) : nat.code n m :=
  begin
    revert m p,
    induction n with n IH,
    { intro m p, cases m,
      { exact star},
      { contradiction}},
    { intro m p, cases m with m,
      { contradiction},
      { rewrite [↑nat.code, ↓nat.code n m], apply IH, injection p, assumption}},
  end

  protected definition decode {n m : ℕ} (q : nat.code n m) : n = m :=
  begin
    revert m q,
    induction n with n IH,
    { intro m q, cases m,
      { reflexivity},
      { contradiction}},
    { intro m q, cases m with m,
      { contradiction},
      { exact ap succ (!IH q)}},
  end

  definition is_hprop_code (n m : ℕ) : is_hprop (nat.code n m) :=
  begin
    apply is_hprop.mk, revert m,
    induction n with n IH,
    { intro m p q, cases m,
      { cases p, cases q, reflexivity},
      { contradiction}},
    { intro m p q, cases m with m,
      { contradiction},
      { exact IH m p q}},
  end
  local attribute is_hprop_code [instance]
end nat

/---------------------------------------------------------------------------------------------------
  (part of) encode-decode proof to characterize < on nat, to show that it is a mere proposition
  in types.nat.hott there is a simpler proof
---------------------------------------------------------------------------------------------------/

namespace nat
namespace lt
  open unit is_trunc
  protected definition code (n m : ℕ) : Type₀ :=
  begin
    revert m,
    induction n with n IH,
    { intro m, cases m,
      { exact empty},
      { exact unit}},
    { intro m, cases m with m,
      { exact empty},
      { exact IH m}},
  end

  protected definition encode {n m : ℕ} (p : n < m) : lt.code n m :=
  begin
    revert m p,
    induction n with n IH,
    { intro m p, cases m,
      { exfalso, exact !lt.irrefl p},
      { exact star}},
    { intro m p, cases m with m,
      { exfalso, apply !not_lt_zero p},
      { rewrite [↑lt.code, ↓lt.code n m], apply IH, apply lt_of_succ_lt_succ p}},
  end

  protected definition decode {n m : ℕ} (q : lt.code n m) : n < m :=
  begin
    revert m q,
    induction n with n IH,
    { intro m q, cases m,
      { contradiction},
      { apply zero_lt_succ}},
    { intro m q, cases m with m,
      { contradiction},
      { exact succ_lt_succ (!IH q)}},
  end

  definition is_hprop_code (n m : ℕ) : is_hprop (lt.code n m) :=
  begin
    apply is_hprop.mk, revert m,
    induction n with n IH,
    { intro m p q, cases m,
      { contradiction},
      { cases p, cases q, reflexivity}},
    { intro m p q, cases m with m,
      { contradiction},
      { exact IH m p q}},
  end
  local attribute is_hprop_code [instance]

end lt
end nat
