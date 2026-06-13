/-
Copyright (c) 2026 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/

import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.RingQuot
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NoncommRing

/-!
# Milnor-Witt K-theory

In this file, we define the Milnor-Witt K-theory of a field `F` as a quotient
of the free ℤ-algebra on symbols `l x` for `x : F` and `η` by the so-called
Milnor-Witt relations.

For now, `KMilnorWitt F` is only defined as a ring: we do not endow it with a grading,
and we do not address its `GW(F)`-algebra structure.
-/
--TODO :
-- Better simps lemmas?
-- Better namespacing?


section PreKMW
/-! We first need to set up some boilerplate in order to define KMilnorWitt:
namely, the type of generators in KMilnorWitt, and the free ℤ-algebra on
the generators -/

/- The type of generators of KMilnorWitt. Note that [0] is a generator.
Though it will be set to zero in the quotient. -/
inductive KMilnorWittGenerator (F : Type*) where
  | η : KMilnorWittGenerator F
  | l (x : F) : KMilnorWittGenerator F

abbrev PreKMW (F : Type*) := FreeAlgebra ℤ (KMilnorWittGenerator F)
@[pp_nodot]
abbrev PreKMW.S {F : Type*} : KMilnorWittGenerator F → PreKMW F := FreeAlgebra.ι _

variable {F : Type*} [Field F]

/-- The symbol in `PreKMW` corresponding to a generator `x` for `x : F`. -/
def pf (x : F) : PreKMW F := PreKMW.S <| KMilnorWittGenerator.l x

/-- The symbol in `PreKMW` corresponding to the generator `η`. -/
def pη : PreKMW F := PreKMW.S KMilnorWittGenerator.η

variable (F) in
/-- The inductive relation on elements of PreKMW that defines the
Milnor-Witt relations. The quotient of `PreKMW` by this relation will be
the Milnor-Witt K-theory of `F`. -/
inductive milnorWittRel : PreKMW F → PreKMW F → Prop
  | zero : milnorWittRel (pf 0) 0
  | steinberg (x : F) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
      milnorWittRel ((pf x) * pf (1 - x)) 0
  | eta (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    milnorWittRel (pf (a * b)) ((pf a) + (pf b) + pη * (pf a) * (pf b))
  | center (a : F) (ha : a ≠ 0) : milnorWittRel (pη * (pf a)) ((pf a) *pη)
  | hyperbolic : milnorWittRel (pη * pη * (pf (-1))) (-2 * pη)

end PreKMW

/-- The Milnor-Witt K-theory of F. For now, we only define it over fields.
It is the quotient of the free ℤ-algebra on `KMilnorWittGenerator` by the
relations given by `milnorWittRel`.

Impl. details: this is made irreducible, and has to be unsealed in a few
boilerplate lemmas that builds universal properties, after these, there is usually
no need to unseal it. -/
@[irreducible]
def KMilnorWitt (F : Type*) [Field F] := RingQuot <| milnorWittRel F
  deriving Ring

variable {F : Type*} [Field F]

namespace KMilnorWitt

unseal KMilnorWitt in
/-- The symbol `η` in `KMilnorWitt F`. This is the image in
`KMilnorWitt F` of the corresponding generator. -/
@[irreducible] def η : KMilnorWitt F := RingQuot.mkRingHom _ pη

unseal KMilnorWitt in
/-- The symbol `⦃a⦄` in `KMilnorWitt F`. This is the image in
`KMilnorWitt F` of the corresponding generator. -/
@[irreducible] def S : F → KMilnorWitt F :=  RingQuot.mkRingHom _ ∘ pf

@[inherit_doc S]
scoped notation :max "⦃" a "⦄" => S a -- ⟦a⟧ already taken.

unseal KMilnorWitt in
lemma S_apply {a : F} : ⦃a⦄ = RingQuot.mkRingHom _ (pf a) := by unfold S; rfl

-- TODO: make this a regular def or an abbrev
/-- The hyperbolic element. By definition, this is `η * ⦃-1⦄ + 2`. -/
irreducible_def hyperbolic : KMilnorWitt F := η * ⦃-1⦄ + 2

-- TODO: make this a regular def or an abbrev
/-- The symbol `⟪a⟫`. It is of degree 0, and corresponds to the generator
`a` in the Grothendieck-Witt ring. -/
irreducible_def L (a : F) : KMilnorWitt F := 1 + η * ⦃a⦄

scoped notation :max "⟪" a "⟫" => L a

-- TODO: make this a regular def
/-- The element -⟪(-1  :F)⟫ is the commutativity factor in `KMilnorWitt` -/
irreducible_def ε : KMilnorWitt F := - ⟪(-1 : F)⟫

unseal KMilnorWitt in
/- A basic induction principle on KMilnorWitt -/
@[elab_as_elim, induction_eliminator]
lemma induction {P : KMilnorWitt F → Prop}
  (h_grade0 : ∀ (n : ℤ), P n)
  (h_grade1 : ∀ (a : F), P ⦃a⦄)
  (h_grade2 : P η)
  (h_mul : ∀ a b, (P a) → (P b) → P (a * b))
  (h_add : ∀ a b, (P a) → (P b) → P (a + b))
  (a : KMilnorWitt F) :
  P a := by
    obtain ⟨x, rfl⟩ := RingQuot.mkRingHom_surjective _ a
    induction x using FreeAlgebra.induction with
    | grade0 r => simpa using h_grade0 r
    | grade1 x => cases x with
      | η => simpa [η] using h_grade2
      | l t => simpa [S] using h_grade1 t
    | mul a b ha hb => simpa using h_mul _ _ ha hb
    | add a b ha hb => simpa using h_add _ _ ha hb

unseal KMilnorWitt in
/-- The "zeroth" Milnor-Witt relation in `KMilnorWitt` : ⦃0⦄ = 0.
Normally, this relation does not appear because `0 : F` is not considered as
a valid generator, however, we included it as a way to avoid carrying `≠ 0`
parameters all over the place. -/
@[simp, grind =]
lemma S_zero : ⦃(0 : F)⦄ = 0 := by
  rw [S]
  suffices c : milnorWittRel F (pf (0 : F)) 0 by
    simpa using RingQuot.mkRingHom_rel c
  exact .zero

alias MW0 := S_zero

unseal KMilnorWitt in
@[simp, grind =]
lemma steinberg (a : F) : ⦃a⦄ * ⦃1 - a⦄ = 0 := by
  by_cases h0 : a = 0
  · rw [h0, MW0, zero_mul]
  by_cases h1 : a = 1
  · rw [h1, sub_self, MW0, mul_zero]
  suffices c : milnorWittRel F (pf a * pf (1 - a)) 0 by
    simpa [S] using RingQuot.mkRingHom_rel c
  exact .steinberg a h0 h1

alias MW1 := steinberg

unseal KMilnorWitt in
@[simp, grind =]
lemma S_mul {a : F} {b : F} (ha : a ≠ 0 := by grind) (hb : b ≠ 0 := by grind) :
    ⦃a * b⦄ = ⦃a⦄ + ⦃b⦄ + η * ⦃a⦄ * ⦃b⦄ := by
  suffices c : milnorWittRel F (pf (a * b)) ((pf a) + (pf b) + pη * (pf a)* (pf b)) by
    simpa [S, η] using RingQuot.mkRingHom_rel c
  exact .eta a b ha hb

alias MW2 := S_mul

unseal KMilnorWitt in
lemma η_mul_S (a : F) : η * ⦃a⦄ = ⦃a⦄ * η := by
  by_cases h : a = 0
  · simp [h]
  suffices c : milnorWittRel F (pη * (pf a)) ((pf a) * pη) by
    simpa [S, η] using RingQuot.mkRingHom_rel c
  exact .center a h

alias MW3 := η_mul_S

-- TODO: rename
@[simp, grind _=_]
lemma η_mul_comm (X : KMilnorWitt F) : η * X = X * η := by
  induction X with
  | h_grade0 => rw [Int.commute_cast]
  | h_grade1 => grind [MW3]
  | h_grade2 => grind
  | h_mul a b ha hb => grind
  | h_add a b ha hb => rw [mul_add, add_mul, ha, hb]

@[simp, grind _=_]
lemma η_mul_comm_assoc (X Y : KMilnorWitt F) : X * η * Y = X * Y * η := by
  grind [mul_assoc]

unseal KMilnorWitt in
@[simp, grind =]
lemma η_mul_hyperbolic : η * hyperbolic = (0 : KMilnorWitt F) := by
  simp only [hyperbolic_def, S, η]
  suffices c : milnorWittRel F (pη * pη * pf (-1)) (-2 * pη : PreKMW F) by
    have : η * η * ⦃(-1 : F)⦄ = (-2) * η := by
      have : (RingQuot.mkRingHom (@milnorWittRel F _)) 2 = 2 := map_intCast ..
      simpa [S, η, this, ← neg_mul] using RingQuot.mkRingHom_rel c
    rw [mul_add, ← mul_assoc]
    simp only [S, η] at this
    rw [this]
    noncomm_ring
  exact .hyperbolic

alias MW4 := η_mul_hyperbolic

section lift

unseal KMilnorWitt in
/-- Part of the universal property of `KMilnorWittGenerator F` as a ring:
a ring homomorphism `KMilnorWittGenerator F →+* R` consists of the data of a
function `f : KMilnorWittGenerator F` such that the image satisfies the Milnor-Witt
relations. -/
@[no_expose]
def lift {R : Type*} [Ring R] (f : KMilnorWittGenerator F → R)
    (mw0 : f (.l 0) = 0)
    (mw1 : ∀ (x : F), (x ≠ 0) → (x ≠ 1) → f (.l x) * f (.l (1 - x)) = 0)
    (mw2 : ∀ (a b : F),
      (a ≠ 0) → (b ≠ 0) → f (.l (a * b)) = f (.l a) + f (.l b) + f .η * f (.l a) * f (.l b))
    (mw3 : ∀ (a : F), f .η * f (.l a) = f (.l a) * f .η)
    (mw4 : f .η * f .η * f (.l (-1)) = -2 * f .η) :
    KMilnorWitt F →+* R :=
  RingQuot.lift
    { val := (FreeAlgebra.lift ℤ f).toRingHom
      property := by
        intro x y h
        cases h with
        | zero => simpa [pf] using mw0
        | steinberg x hx0 hx1 => simpa [pf] using mw1 x hx0 hx1
        | eta a b ha hb => simpa [pf, pη, add_assoc, mul_assoc] using mw2 a b ha hb
        | center a ha => simpa [pf, pη] using mw3 a
        | hyperbolic => simpa [pf, pη,
            dsimp% map_ofNat (FreeAlgebra.lift ℤ f).toRingHom 2] using mw4 }

unseal KMilnorWitt in
@[simp, grind =]
lemma lift_apply_η {R : Type*} [Ring R] (f : KMilnorWittGenerator F → R)
    {mw0 : f (.l 0) = 0}
    {mw1 : ∀ (x : F), (x ≠ 0) → (x ≠ 1) → f (.l x) * f (.l (1 - x)) = 0}
    {mw2 : ∀ (a b : F),
      (a ≠ 0) → (b ≠ 0) → f (.l (a * b)) = f (.l a) + f (.l b) + f .η * f (.l a) * f (.l b)}
    {mw3 : ∀ (a : F), f .η * f (.l a) = f (.l a) * f .η}
    {mw4 : f .η * f .η * f (.l (-1)) = -2 * f .η} :
    lift f mw0 mw1 mw2 mw3 mw4 η = f .η := by
  simp only [lift, η]
  generalize_proofs h
  have := RingQuot.lift_mkRingHom_apply ((FreeAlgebra.lift ℤ) f).toRingHom h pη
  dsimp [pη, PreKMW.S] at this ⊢
  rw [FreeAlgebra.lift_ι_apply] at this
  exact this

unseal KMilnorWitt in
@[simp, grind =]
lemma lift_apply_S {R : Type*} [Ring R] (f : KMilnorWittGenerator F → R)
    {mw0 : f (.l 0) = 0}
    {mw1 : ∀ (x : F), (x ≠ 0) → (x ≠ 1) → f (.l x) * f (.l (1 - x)) = 0}
    {mw2 : ∀ (a b : F),
      (a ≠ 0) → (b ≠ 0) → f (.l (a * b)) = f (.l a) + f (.l b) + f .η * f (.l a) * f (.l b)}
    {mw3 : ∀ (a : F), f .η * f (.l a) = f (.l a) * f .η}
    {mw4 : f .η * f .η * f (.l (-1)) = -2 * f .η}
    (a : F) :
    lift f mw0 mw1 mw2 mw3 mw4 ⦃a⦄ = f (.l a) := by
  simp only [lift, S]
  generalize_proofs h
  have := RingQuot.lift_mkRingHom_apply ((FreeAlgebra.lift ℤ) f).toRingHom h (pf a)
  dsimp [pf, PreKMW.S] at this ⊢
  rw [FreeAlgebra.lift_ι_apply] at this
  exact this

end lift

@[simp]
lemma S_mul_eq_S_add_L_mul {a b : F} (ha : a ≠ 0 := by grind) (hb : b ≠ 0 := by grind) :
    ⦃a * b⦄ = ⦃a⦄ + ⟪a⟫ * ⦃b⦄ := by
  rw [MW2, L, add_mul, one_mul, add_assoc]

@[simp]
lemma S_mul_eq_mul_L_add {a b : F} (ha : a ≠ 0 := by grind) (hb : b ≠ 0 := by grind) :
    ⦃a * b⦄ = ⦃a⦄ * ⟪b⟫ + ⦃b⦄ := by
  rw [MW2 ha hb, L_def]
  simp only [η_mul_comm, η_mul_comm_assoc]
  noncomm_ring

@[simp, grind =]
lemma L_mul {a b : F} (ha : a ≠ 0 := by grind) (hb : b ≠ 0 := by grind) :
    ⟪a * b⟫ = ⟪a⟫ * ⟪b⟫ := by
  simp only [L, MW2 ha hb, η_mul_comm]
  noncomm_ring

@[simp, grind =]
lemma L_zero : ⟪(0 : F)⟫ = 1 := by
  simp [L_def]

@[simp, grind =]
lemma L_one : ⟪(1 : F)⟫ = 1 := by
  have H : (⟪(1 : F)⟫ - 1) * (⟪-1⟫ + 1) = 0 := by
    simp only [L_def]
    calc
      _ = η * ⦃(1 : F)⦄ * (2 + η * ⦃-1⦄) := by grind
      _ = ⦃1⦄ * (η * hyperbolic) := by rw [hyperbolic_def]; grind
      _ = 0 := by grind [MW4]
  rw [left_distrib, mul_one, sub_eq_add_neg, right_distrib, ← L_mul] at H
  simp only [mul_neg, mul_one, neg_mul, one_mul, add_neg_cancel, zero_add, add_neg_eq_zero] at H
  exact H

lemma L_minus_one (a : F) : ⟪a⟫ - 1 = η * ⦃a⦄ := by grind [L_def]

@[simp, grind =]
lemma S_one : ⦃(1 : F)⦄ = 0 := by
  have T : ⦃(1 :F)⦄ = ⦃1⦄ + ⟪1⟫ * ⦃1⦄ := by
    nth_rewrite 1 [← mul_one 1]
    rw [S_mul_eq_S_add_L_mul]
  simpa using T

instance (a : F) : Invertible ⟪a⟫ where
  invOf := L a⁻¹
  invOf_mul_self := by
    by_cases H : a = 0
    · grind
    · rw [← L_mul]
      simp [H]
  mul_invOf_self := by
    by_cases H : a = 0
    · grind
    · rw [← L_mul]
      simp [H]

lemma invOf_L (a : F) : ⅟⟪a⟫ = ⟪a⁻¹⟫ := rfl

@[simp, grind =]
lemma L_inv_mul_self (a : F) : ⟪a⁻¹⟫ * ⟪a⟫ = 1 := by simp [← invOf_L]

@[simp, grind =]
lemma L_mul_self_inv (a : F) : ⟪a⟫ * ⟪a⁻¹⟫ = 1 := by simp [← invOf_L]

lemma S_div {a b : F} (ha : a ≠ 0 := by grind) (hb : b ≠ 0 := by grind) :
    ⦃a / b⦄ = ⦃a⦄ - ⟪a / b⟫ * ⦃b⦄ := by
  have t : a = a * b⁻¹ * b := by simp [hb]
  have ht : a * b⁻¹ ≠ 0 := mul_ne_zero ha (inv_ne_zero hb)
  nth_rw 2 [t]
  simp [S_mul_eq_S_add_L_mul ht hb, div_eq_mul_inv]

@[grind _=_]
lemma S_inv (a : F) : ⦃a⁻¹⦄ = - ⟪a⁻¹⟫ * ⦃a⦄ := by
  by_cases h : a = 0
  · simp [h]
  · have H := S_div (one_ne_zero) h
    rw [S_one, zero_sub] at H
    grind

@[grind _=_]
lemma L_mul_S (a b : F) : ⟪a⟫ * ⦃b⦄ = ⦃b⦄ * ⟪a⟫ := by
  by_cases ha : a = 0
  · simp [ha, L_zero]
  · by_cases hb : b = 0
    · simp [hb]
    rw [← add_left_cancel_iff (a := ⦃a⦄)]
    rw [← S_mul_eq_S_add_L_mul, add_comm, ← S_mul_eq_mul_L_add, mul_comm]

@[grind _=_]
lemma L_center (a : F) (X : KMilnorWitt F) : ⟪a⟫ * X = X * ⟪a⟫ := by
  induction X with
  | h_grade0 n => rw [Int.commute_cast]
  | h_grade1 X => refine L_mul_S a X
  | h_grade2 => rw [← η_mul_comm]
  | h_mul u v hu hv => rw [mul_assoc, ← hv, ← mul_assoc _ u v, hu, ← mul_assoc]
  | h_add a b ha hb => rw [mul_add, ha, hb, add_mul]

lemma IsMulCentral_L (a : F) : IsMulCentral ⟪a⟫ where
  comm x := by grind [Commute, SemiconjBy]
  left_assoc := by grind
  right_assoc := by grind

lemma L_center_assoc (a : F) (X Y : KMilnorWitt F) : (X * (⟪a⟫ * Y)) = ⟪a⟫ * (X * Y) := by
  rw [← mul_assoc, ← L_center, mul_assoc]

@[grind _=_]
lemma ε_mul_comm (X : KMilnorWitt F) : ε * X = X * ε := by rw [ε, neg_mul, L_center, mul_neg]

lemma L_neg_one_add_one_eq_hyperbolic : hyperbolic = ⟪(-1 : F)⟫ + 1 := by
  simp only [L_def, hyperbolic_def]
  grind

@[grind _=_]
lemma hyperbolic_mul_comm (X : KMilnorWitt F) : hyperbolic * X = X * hyperbolic :=
  calc
    _ = (⟪-1⟫ + 1) * X := by rw [L_neg_one_add_one_eq_hyperbolic]
    _ = ⟪-1⟫ * X + 1 * X := by rw [add_mul]
    _ = X * ⟪-1⟫ + X * 1 := by simp [L_center]
    _ = X * (⟪-1⟫ + 1) := by grind
    _ = X * hyperbolic := by rw [L_neg_one_add_one_eq_hyperbolic]

@[grind =]
lemma S_mul_S_neg (a : F) : ⦃a⦄ * ⦃-a⦄ = 0 := by
  -- Discharge the easy cases first
  by_cases! h0 : a = 0; case pos => simp [h0]
  by_cases! h1 : a = 1; case pos => simp [S_one, h1]
  calc
    _ = ⦃a⦄ * ⦃((1 - a) / (1 - a⁻¹))⦄ := by grind
    _ = ⦃a⦄ * (⦃1 - a⦄ - ⟪- a⟫ * ⦃1 - a⁻¹⦄) := by rw [S_div]; grind
    _ = ⦃a⦄ * ⦃1 - a⦄ - ⦃a⦄ * ⟪-a⟫ * ⦃1 - a⁻¹⦄ := by noncomm_ring
    _ = - ⦃a⦄ * ⟪-a⟫ * ⦃1 - a⁻¹⦄ := by rw [MW1]; noncomm_ring
    _ = - ⟪-a⟫ * ⦃a⦄ * ⦃1 - a⁻¹⦄ := by rw [← L_center]; grind
    _ = - ⟪-a⟫ * ⦃a⁻¹⁻¹⦄ * ⦃1 - a⁻¹⦄ := by rw [inv_inv]
    _ = -⟪-a⟫ * -⟪a⁻¹⁻¹⟫ * (⦃a⁻¹⦄ * ⦃1 - a⁻¹⦄) := by rw [S_inv]; noncomm_ring
    _ = 0 := by simp

@[grind =]
lemma S_neg {a : F} (ha : a ≠ 0) : ⦃-a⦄ = ⦃a⦄ + ⟪a⟫ * ⦃-1⦄ := by
  rw [← one_mul a, ← neg_mul]
  grind [S_mul_eq_mul_L_add]

lemma S_neg' {a : F} (ha : a ≠ 0) : ⦃-a⦄ = ⦃-1⦄ + ⟪-1⟫ * ⦃a⦄ := by
  rw [← mul_one (-a), neg_mul, mul_comm, ← neg_mul, S_mul_eq_S_add_L_mul]

@[grind =]
lemma S_neg_mul_S (a : F) : ⦃-a⦄ * ⦃a⦄ = 0 := by
  have h := S_mul_S_neg (-a)
  rw [neg_neg] at h
  exact h

@[simp, grind =]
lemma ε_mul_ε : ε * ε = (1 : KMilnorWitt F) := by
  rw [ε, mul_neg, neg_mul, ← L_mul]
  simp [L_one]

lemma ε_mul_eq_iff (x y : KMilnorWitt F) : ε * x = y ↔ x = ε * y := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · grind [mul_assoc]
  · grind [mul_assoc]

@[simps]
instance invertibleε : Invertible (ε : KMilnorWitt F) where
  invOf := ε
  invOf_mul_self := ε_mul_ε
  mul_invOf_self := ε_mul_ε

lemma ε_mul_S_minus_one : ε * ⦃(-1 : F)⦄ = ⦃-1⦄ := by
  rw [ε, neg_mul]; symm; rw [← add_eq_zero_iff_eq_neg, ← S_one]
  suffices j : (1 : F) = (-1) * (-1) by
    rw [j, S_mul_eq_S_add_L_mul]
    all_goals {simp}
  simp

lemma S_mul_S_self (a : F) : ⦃a⦄ * ⦃a⦄ = ε * ⦃a⦄ * ⦃-1⦄ := by
  by_cases h0 : a = 0
  · grind
  by_cases h1 : a = 1
  · simp [h1, S_one]
  suffices ε * ⦃a⦄ * ⦃a⦄ = ⦃a⦄ * ⦃-1⦄ by rw [mul_assoc, ← ε_mul_eq_iff, ← mul_assoc, this]
  calc
    _ = ⦃a⦄ * ε * ⦃a⦄ + ⦃a⦄ * ⦃-a⦄          := by simp [S_mul_S_neg, ε_mul_comm]
    _ = ⦃a⦄ * (ε * ⦃a⦄ + ⦃-a⦄)              := by noncomm_ring
    _ = ⦃a⦄ * (ε * ⦃a⦄ + ⦃-1⦄ + ⟪-1⟫ * ⦃a⦄)   := by grind [S_neg']
    _ = ⦃a⦄ * (ε * ⦃a⦄ + ⟪-1⟫ * ⦃a⦄ + ⦃-1⦄) := by noncomm_ring
    _ = ⦃a⦄ * ((ε + ⟪-1⟫) * ⦃a⦄ + ⦃-1⦄)     := by congr 4; rw [add_mul]
    _ = ⦃a⦄ * (0 * ⦃a⦄ + ⦃-1⦄)              := by congr 4; simp [ε]
    _ = ⦃a⦄ * ⦃-1⦄                          := by simp

lemma S_mul_S_self' (a : F) : ⦃a⦄ * ⦃a⦄ = ε * ⦃-1⦄ * ⦃a⦄ := by
  by_cases h0 : a = 0
  · grind
  by_cases h1 : a = 1
  · grind only [S_one] -- grind throws some weird error ?
  suffices ε * ⦃a⦄ * ⦃a⦄ = ⦃-1⦄ * ⦃a⦄ by rw [mul_assoc, ← ε_mul_eq_iff, ← mul_assoc, this]
  calc
    _ = ε * ⦃a⦄ * ⦃a⦄ + 0                    := by rw [add_zero]
    _ = ε * ⦃a⦄ * ⦃a⦄ + ⦃-a⦄ * ⦃a⦄           := by rw [S_neg_mul_S]
    _ = (ε * ⦃a⦄ + ⦃-a⦄) * ⦃a⦄               := by rw [add_mul]
    _ = (ε * ⦃a⦄ + ⦃-1⦄ + ⟪-1⟫ * ⦃a⦄) * ⦃a⦄  := by rwa [add_assoc, S_neg']
    _ = ((ε + ⟪-1⟫) * ⦃a⦄ + ⦃-1⦄) * ⦃a⦄      := by noncomm_ring
    _ = (0 * ⦃a⦄ + ⦃-1⦄) * ⦃a⦄               := by simp [ε]
    _ = ⦃-1⦄ * ⦃a⦄                           := by simp

lemma S_mul_S_self_eq_S_neg_one_mul_S (a : F) : ⦃a⦄ * ⦃a⦄ = ⦃-1⦄ * ⦃a⦄ := by
  calc ⦃a⦄ * ⦃a⦄ = ε * ⦃-1⦄ * ⦃a⦄     := by exact S_mul_S_self' a
             _ = ⦃-1⦄ * ⦃a⦄       := by rw [ε_mul_S_minus_one]

lemma S_mul_S_self_eq_S_mul_S_neg_one (a : F) : ⦃a⦄ * ⦃a⦄ = ⦃a⦄ * ⦃-1⦄ := by
  calc ⦃a⦄ * ⦃a⦄ = ε * ⦃a⦄ * ⦃-1⦄   := by exact S_mul_S_self a
             _ = ⦃a⦄ * ε * ⦃-1⦄   := by rw [ε_mul_comm]
             _ = ⦃a⦄ * ⦃-1⦄       := by rw [mul_assoc, ε_mul_S_minus_one]

lemma L_mul_S_self (a : F) : ⟪a⟫ * ⦃a⦄ = ⟪-1⟫ * ⦃a⦄ := by
  by_cases h : a = 0; case pos => simp [h]
  simp only [L_def]
  rw [add_mul, add_mul]
  congr 1
  rw [mul_assoc, mul_assoc]
  congr 1
  exact S_mul_S_self_eq_S_neg_one_mul_S a

lemma L_mul_S_eq_diff {a : F} {b : F} (ha : a ≠ 0 := by grind) (hb : b ≠ 0 := by grind) :
    ⟪a⟫ * ⦃b⦄ = ⦃a * b⦄ - ⦃a⦄ := by
  rw [eq_sub_iff_add_eq, add_comm]
  exact (S_mul_eq_S_add_L_mul ha hb).symm

-- TODO: rename
lemma L_mul_self (a : F) : ⟪a * a⟫ = 1 := by
  by_cases ha : a = 0; case pos => simp [ha]
  suffices h : η * ⦃a * a⦄ = 0 by
    rw [η_mul_comm] at h
    simp [L_def, h]
  calc
    _ = η * (⦃a⦄ + ⦃a⦄ + η * ⦃a⦄ * ⦃a⦄)  := by rw [MW2]
    _ = η * (⦃a⦄ + ⦃a⦄ + η * ⦃-1⦄ * ⦃a⦄) := by grind [S_mul_S_self_eq_S_neg_one_mul_S]
    _ = η * hyperbolic * ⦃a⦄             := by rw [hyperbolic_def]; noncomm_ring
    _ = 0 * ⦃a⦄                          := by rw [MW4]
    _ = 0                                := by rw [zero_mul]

lemma L_pow_two (a : F) : ⟪a ^ 2⟫ = 1 := by
  rw [pow_two a]
  exact L_mul_self a

lemma L_mul_mul_self {a : F} (b : F) (ha : a ≠ 0 := by grind) : ⟪b * a * a⟫ = ⟪b⟫ := by
  by_cases h : b = 0; case pos => simp [h]
  grind [mul_assoc, L_mul_self]

lemma L_mul_pow_two (b : F) {a : F} (ha : a ≠ 0) : ⟪b * a^2⟫ = ⟪b⟫ := by
  rw [pow_two, ← mul_assoc]
  exact L_mul_mul_self b ha

@[deprecated (since := "")]
alias L_mul_mul_self' := L_mul_pow_two

lemma hyperbolic_sum {a : F} (ha : a ≠ 0 := by grind) : ⟪a⟫ + ⟪-a⟫ = hyperbolic := by
  rw [hyperbolic]
  suffices h : L a + ⟪-a⟫ = ⟪-1⟫ + 1 by
    conv_rhs at h => rw [L, add_comm, ← add_assoc, one_add_one_eq_two, add_comm]
    exact h
  -- Reduce the goal to an auxiliary computation
  suffices h : (⟪a⟫ - 1) * (⟪-a⟫ - 1) = 0 by
    rw [← sub_eq_zero]
    calc
      _ = ⟪a⟫ + ⟪-a⟫ - (⟪-1 * a * a⟫ + 1)  := by rw [L_mul_mul_self];
      _ = ⟪a⟫ + ⟪-a⟫ - (⟪-a * a⟫ + 1)      := by rw [neg_one_mul]
      _ = ⟪a⟫ + ⟪-a⟫ - (⟪a⟫ * ⟪-a⟫ + 1)    := by rw [L_mul, L_center]
      _ = ⟪a⟫ + ⟪-a⟫ - ⟪a⟫ * ⟪-a⟫ - 1      := by rw [sub_sub]
      _ = ⟪a⟫ - ⟪a⟫ * ⟪-a⟫ + ⟪-a⟫ - 1      := by rw [sub_add_eq_add_sub]
      _ = ⟪a⟫ * (1 - ⟪-a⟫) + ⟪-a⟫ - 1      := by rw [mul_sub, mul_one]
      _ = ⟪a⟫ * (1 - ⟪-a⟫) - (1 - ⟪-a⟫)    := by rw [sub_sub_eq_add_sub]
      _ = (⟪a⟫ - 1) * (1 - ⟪-a⟫)           := by rw [sub_mul, one_mul]
      _ = - ((⟪a⟫ - 1) * (⟪-a⟫ - 1))       := by rw [← mul_neg, neg_sub]
      _ = 0                                := by rw [h, neg_zero]
  -- Perform the auxiliary computation
  calc
    _ = (η * ⦃a⦄) * (η * ⦃-a⦄)    := by simp_rw [L_minus_one]
    _ = (η * ⦃a⦄) * (⦃-a⦄ * η)    := by rw [← η_mul_comm]
    _ = η * ((⦃a⦄ * ⦃-a⦄) * η)    := by noncomm_ring
    _ = 0                         := by rw [S_mul_S_neg, zero_mul, mul_zero]

lemma ε_comm_S (a b : F) : ⦃a⦄ * ⦃b⦄ = ε * ⦃b⦄ * ⦃a⦄ := by
  by_cases ha : a = 0
  · grind
  by_cases hb : b = 0
  · grind
  symm
  calc
    _ = ⟪-1⟫ * ⟪-1⟫ * ε * ⦃b⦄ * ⦃a⦄                  := by simp [← L_mul,L_one]
    _ = ⟪-1⟫ * ε * ⦃b⦄ * (⟪-1⟫ * ⦃a⦄)                := by rw [L_center_assoc]; noncomm_ring
    _ = ε * (⟪-1⟫ * ⦃b⦄) * (⟪-1⟫ * ⦃a⦄)              := by grind [L_center_assoc, mul_assoc]
    _ = ε * (⟪b⟫ * ⦃b⦄) * (⟪a⟫ * ⦃a⦄)                := by simp_rw [L_mul_S_self]
    _ = ε * ⟪a⟫ * ⦃b⦄ * ⟪b⟫ * ⦃a⦄                    := by simp_rw [mul_assoc]
                                                           congr 1
                                                           simp_rw [L_center_assoc _ ⦃_⦄ ⦃_⦄,
                                                            ← mul_assoc]
                                                           rw [L_center]
    _ = - ⟪-a⟫ * ⦃b⦄ * ⟪b⟫ * ⦃a⦄                     := by rw [ε, neg_mul, ← L_mul, neg_one_mul]
    _ = -(⟪-a⟫ * ⦃b⦄) * (⟪b⟫ * ⦃a⦄)                  := by rw [neg_mul, mul_assoc]
    _ = -(⦃-a * b⦄ - ⦃-a⦄) * (⟪b⟫ * ⦃a⦄)             := by rw [L_mul_S_eq_diff]
    _ = ⦃-a⦄ * (⟪b⟫ * ⦃a⦄) - ⦃-a * b⦄ * (⟪b⟫ * ⦃a⦄)  := by noncomm_ring
    _ = - ⦃-a * b⦄ * (⟪b⟫ * ⦃a⦄)                     := by rw [L_center_assoc,
                                                               S_neg_mul_S,
                                                               mul_zero,
                                                               zero_sub,
                                                               ← neg_mul]
    _ = - ⦃-a * b⦄ * (⦃b * a⦄ - ⦃b⦄)                 := by rw [L_mul_S_eq_diff]
    _ = ⦃-a * b⦄ * ⦃b⦄                               := by rw [mul_sub]
                                                           simp_rw [neg_mul]
                                                           rw [mul_comm b a, S_neg_mul_S, neg_zero,
                                                               zero_sub, neg_neg]
    _ = ((⦃a * b⦄ + ⟪a * b⟫ * ⦃-1⦄)) * ⦃b⦄           := by rw [neg_mul, S_neg]
                                                           grind
    _ = ⦃a * b⦄ * ⦃b⦄ + ⟪a * b⟫ * ⦃-1⦄ * ⦃b⦄         := by rw [add_mul]
    _ = ⦃a * b⦄ * ⦃b⦄ + ⟪a * b⟫ * ⦃b⦄ * ⦃b⦄          := by rw [mul_assoc,
                                                          ← S_mul_S_self_eq_S_neg_one_mul_S,
                                                          ← mul_assoc]
    _ = (⦃a * b⦄ + ⟪a * b⟫ * ⦃b⦄) * ⦃b⦄              := by rw [← add_mul]
    _ = ⦃a * b * b⦄ * ⦃b⦄                            := by rw [← S_mul_eq_S_add_L_mul]
    _ = (⦃a⦄ + ⟪a⟫ * ⦃b * b⦄) * ⦃b⦄                  := by rw [mul_assoc, S_mul_eq_S_add_L_mul]
    _ = ⦃a⦄ * ⦃b⦄ + ⟪a⟫ * ⦃b * b⦄ * ⦃b⦄              := by rw [add_mul]
    _ = ⦃a⦄ * ⦃b⦄ + ⟪a⟫ * ⦃(-b) * (-b)⦄ * ⦃b⦄        := by simp
    _ = ⦃a⦄ * ⦃b⦄ + ⟪a⟫ * (⦃-b⦄ + ⟪-b⟫ * ⦃-b⦄) * ⦃b⦄ := by rw [S_mul_eq_S_add_L_mul]
    _ = ⦃a⦄ * ⦃b⦄ + 0                                := by simp [mul_assoc, add_mul, mul_assoc,
                                                               S_neg_mul_S]
    _ = ⦃a⦄ * ⦃b⦄                                    := by rw [add_zero]

section pow

variable (F) in
/-- The element noted $n_{\epsilon}$ (when n > 0). -/
abbrev ε' (n : ℕ) := ∑ i ∈ Finset.Icc 1 n, ⟪(-1 : F) ^ (i - 1)⟫

lemma ε'_zero : ε' F 0 = 0 := by
  simp [ε']

lemma ε'_one : ε' F 1 = 1 := by
  simp [ε']

variable (F) in
lemma ε'_central (n : ℕ) : IsMulCentral (ε' F n) where
  comm a := by
    dsimp [ε']
    apply Commute.sum_left
    intro i _
    grind [commute_iff_eq]
  left_assoc := by grind
  right_assoc := by grind

variable (F) in
lemma ε'_succ (n : ℕ) : ε' F (n + 1) = (ε' F n) * ⟪(-1 : F)⟫ + 1 := by
  dsimp [ε']
  have : Finset.Icc 1 (n + 1) = {1} ∪ Finset.Icc 2 (n + 1) := by grind
  rw [Finset.sum_mul, this]
  rw [Finset.sum_congr
    (f := fun i ↦ ⟪(-1) ^ (i - 1)⟫ * ⟪-1⟫)
    (g := fun i ↦ ⟪(-1) ^ i⟫)
    (h := (rfl : Finset.Icc 1 n = _))]
  · have : Finset.Icc 2 (n + 1) = (Finset.Icc 1 n).image (· + 1) := by
      ext i
      simp only [Finset.mem_Icc, Finset.mem_image]
      constructor
      · intro hi1
        use (i - 1)
        grind
      · grind
    simp [this]
    grind
  · intro i hi
    rw [Finset.mem_Icc] at hi
    rw [← L_mul (by grind [neg_one_pow_eq_ite])]
    congr
    grind [neg_one_pow_eq_ite]

/-- Under the assumption that -1 is a square, there is a formula for [a ^ n] in terms
of [a]. -/
lemma S_pow
    (a : F) (n : ℕ) (ha : a ≠ 0) :
    ⦃a ^ n⦄ = (ε' F n) * ⦃a⦄ := by
  induction n with
  | zero => simp [ε']
  | succ n ih =>
    calc
      _ = ⦃a ^ n⦄ + ⦃a⦄ + η * ⦃a ^ n⦄ * ⦃a⦄ := by
        have ha : a ^ n ≠ 0 := by grind [pow_eq_zero_iff']
        rw [pow_add, pow_one, S_mul (a := a ^n) (b := a)]
      _ = (ε' F n) * ⦃a⦄ + ⦃a⦄ + η * (ε' F n) * ⦃a⦄ * ⦃a⦄ := by grind
      _ = (ε' F n) * ⦃a⦄ + ⦃a⦄ + (ε' F n) * η * ⦃- 1⦄ * ⦃a⦄ := by
        grind [((ε'_central F n).comm η).eq, S_mul_S_self_eq_S_neg_one_mul_S a]
      _ = ((ε' F n) + 1 + (ε' F n) * η * ⦃- 1⦄) * ⦃a⦄ := by grind
      _ = ((ε' F n) * (1 + η * ⦃- 1⦄) + 1) * ⦃a⦄ := by grind
      _ = ((ε' F n) * ⟪(-1 : F)⟫ + 1) * ⦃a⦄ := by grind [L_def]
      _ = (ε' F (n + 1)) * ⦃a⦄ := by rw [ε'_succ F n]

lemma L_inv_eq (a : F) (ha : a ≠ 0) :
    ⟪a⁻¹⟫ = ⟪a⟫ := by
  have : Invertible ⟪a⟫ := instInvertibleL a
  apply_fun (⟪a⟫ * ·)
  · simp only [L_mul_self_inv]; rw [← L_mul, L_mul_self]
  · intro x y hxy
    grind [mul_left_inj_of_invertible ⟪a⟫]

lemma S_inv' (a : F) (ha : a ≠ 0) :
    ⦃a⁻¹⦄ = ε * (ε' F 1) * ⦃a⦄ := by
  rw [S_inv, ε'_one, L_inv_eq _ ha, L_def, neg_mul,
    add_mul, mul_assoc, S_mul_S_self_eq_S_neg_one_mul_S]
  suffices h : - (1 + η * ⦃(-1 : F)⦄) * ⦃a⦄ = ε * ⦃a⦄ by
    rw [neg_mul, add_mul] at h
    grind
  congr
  simp [ε, L]

lemma S_zpow_neg (a : Fˣ) (n : ℕ) :
    ⦃(a ^ (- n : ℤ) : F)⦄ = ε * (ε' F n) * ⦃(a : F)⦄ := by
  rw [zpow_neg, zpow_natCast, ← inv_pow, S_pow _ _ (by simp), S_inv' _ (by simp),
    ε'_one, mul_one]
  grind

end pow

end KMilnorWitt

section GW_to_KMilnorWitt

open KMilnorWitt

/-! In this section, we check that the symbols `⟪u⟫` satisfy the relations for the
Grothendieck-Witt ring.
When it will be defined, this will define a map from `GrothendieckWitt F` to `KMilnorWitt F`. -/

variable {F : Type*} [Field F]

alias L_GW1 := KMilnorWitt.L_mul_pow_two

-- TODO: rename
lemma L_GW2 {a : F} (ha : a ≠ 0 := by grind) : ⟪a⟫ + ⟪-a⟫ = 1 + ⟪-1⟫ := by
  rw [← L_one, hyperbolic_sum, hyperbolic_sum]

lemma L_add_L (u v : F)
    (hu : u ≠ 0 := by grind) (hv : v ≠ 0 := by grind) (huv : u + v ≠ 0 := by grind) :
    ⟪u⟫ + ⟪v⟫ = ⟪u + v⟫ + ⟪u * v * (u + v)⟫ := by
  wlog h : (u + v = 1) with H
  · apply_fun fun x => x * ⟪(u + v)⁻¹⟫
    · dsimp;
      rw [mul_add]
      set U := u/(u + v) with hU; set V := v / (u + v) with hV
      have HUV1 : U * V * (U + V) = u * v * ((u + v)⁻¹)^2 := by grind [pow_two]
      have HUPV : U + V = 1 := by grind
      have H2 : ⟪U⟫ + ⟪V⟫ = ⟪U + V⟫ + ⟪U * V * (U + V)⟫ :=
        H U V (by grind) (by grind) (by grind) HUPV
      conv_rhs => rw [add_mul]; arg 1; equals 1 => simp
      rw [add_mul, @L_center _ _ u _, @L_center _ _ v _]
      conv_rhs => rw [L_center]
      rw [← L_mul, ← L_mul, ← L_mul]
      simp_rw [← div_eq_inv_mul]
      rw [show (u * v * u + u * v * v) / (u + v) = u * v by field_simp, ← hU, ← hV]
      have HLUV : ⟪u * v⟫ = ⟪U * V * (U + V)⟫ := by grind [L_mul_pow_two]
      have HLUPV : 1 = ⟪U + V⟫ := by rw [HUPV, L_one]
      rw [HLUV, HLUPV]
      exact H2
    · intros x y hxy
      apply_fun fun x => x * ⟪u + v⟫ at hxy
      rw [mul_assoc, mul_assoc] at hxy;
      simpa using hxy
  · obtain rfl : v = 1 - u := by simp [← h]
    have : u * (1 - u) * u + u * (1 - u) * (1 - u) = u * (1 - u) := by grind
    simp_rw [mul_add, L_def, this]
    rw [MW2, mul_assoc, steinberg u, h, S_one]
    noncomm_ring

end GW_to_KMilnorWitt
