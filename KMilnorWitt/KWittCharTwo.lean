/-
Copyright (c) 2026 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/

import KMilnorWitt.KWitt
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Witt K-theory of a field of characteristic 2

The main purpose of this file is to verify the key point in the proof of
Theorem 3.12 in [arXiv:2306.16985]: that the degree k part of the
Witt K-theory of a field `F` of characteristic 2 is zero if the
rank of F as a vector space over its subfield of squares is finite and less
than 2^k.

Since we do not formalize the graded algebra structure Witt K-theory,
we prove here that for any list `L` of non-zero elements of `F` of length `≥ k + 1`,
if the dimension of `F` as a `Square F`-vector space is `≤ 2^k`,
then `(L.map C).prod = 0`, where `C : F → KWitt F` is the function that takes an element
of `F` to the corresponding generator in `KWitt F`. Since the degree `k` part is spanned by
such products, this formalizes our claim.
-/

variable {F : Type*} [Field F]
namespace KWitt
section CharTwo

variable [CharP F 2]

@[simp, grind =]
lemma C_mul_C_self_charTwo (a : F) : C a * C a = 0 := by
  conv_lhs => arg 2; rw [← (CharTwo.neg_eq a)]
  rw [C_mul_C_neg]

@[simp, grind =]
lemma W1_charTwo (a : F) : C a * C (1 + a) = 0 := by
  rw [← CharTwo.sub_eq_add]
  exact W1 a

lemma C_mul_C_eq_C_mul_C_prod (a : F) (b : F) : C a * C b = C a * C (a * b) := by
  by_cases ha : a = 0
  · grind
  by_cases hb : b = 0
  · grind
  grind [mul_add]

lemma C_mul_eq_C_mul_C_mul_pfister_norm (a b t u : F)
    (ht : t ≠ 0 := by grind) (hu : u ≠ 0 := by grind) :
    C a * C b = C a * C (b * (u^2 + a * t^2)) := by
  by_cases h : (u^2 + a * t^2) = 0
  · rw [← CharTwo.sub_eq_add, sub_eq_zero] at h
    by_cases ha : a = 0
    · grind
    simp [← C_mul_pow_two a ht, ← h, C_pow_two]
  · by_cases hb : b = 0
    · grind
    suffices H : C a * C (u^2 + a * t^2) = 0 by grind
    have calc_1 : u^2 + a * t^2 = (1 + a * (t / u)^2) * u^2 := by grind
    grind [C_mul_pow_two a (v := t / u)]

-- TODO: cleanup
lemma C_mul_C_eq_C_norm_mul (a b u v : F) (hu : u ≠ 0 := by grind) (hv : v ≠ 0 := by grind) :
    C a * C b = C (a * u^2 + b * v^2) * C (a * b) := by
  set c := a * u^2 + b * v^2 with hc
  by_cases ha : a = 0
  · grind
  by_cases hb : b = 0
  · grind
  by_cases hc2 : c = 0
  · rw [hc2, W0, zero_mul]
    have hb2 : b * v^2 = a * u^2 := by
      rw [← sub_eq_zero, CharTwo.sub_eq_add, add_comm, ← hc]; exact hc2
    rw [← (C_mul_pow_two b hv), hb2, C_mul_pow_two _ hu]
    exact C_mul_C_self_charTwo a
  · have calc_c: c = a * u^2 * (1 + a * b * (v / (a * u))^2) := by
      rw [hc, mul_add, mul_one, add_right_inj, div_pow, mul_pow, mul_comm a, mul_assoc, mul_div,
          mul_div, ← mul_assoc a (a * b), ← mul_assoc a a, ← pow_two, mul_div, div_eq_inv_mul,
          ← mul_assoc (u^2), ← mul_assoc (u^2), mul_comm (u^2) (a^2), mul_assoc (a^2 * u^2),
          inv_mul_cancel_left₀]
      grind
    rw [calc_c, W2, add_mul, add_mul, C_mul_pow_two,
      ← C_mul_C_eq_C_mul_C_prod, mul_assoc _ _ (C (a * b))]
    suffices cal_2 : C (1 + a * b*((v/(a * u))^2)) * C (a * b) = 0 by simp [cal_2]
    rw [← C_mul_pow_two (a * b) (v := v / (a * u)), mul_comm (C _),
      W1_charTwo (a * b * (v/(a * u))^2)]

lemma C_mul_C_eq_C_add_mul_C_mul (a : F) (b : F) : (C a) * (C b) = C (a + b) * C (a * b) := by
  have calc1 := C_mul_C_eq_C_norm_mul a b 1 1
  rwa [one_pow, mul_one, mul_one] at calc1

end CharTwo

section KWEquiv
/-- An inductive relation on list of elements of `F` that expresses that the corresponding products
of generators are equal in `KWitt F` (see `KWEquiv.map_C_prod_eq_of_KWEquiv` below).

This relation is what we need to set up a "chain lemma"-type of argument to
show that over a field of characteristic 2, sufficiently large products of generators vanish when
the field has finite dimension over its subfield of squares. -/
inductive KWEquiv : List F → List F → Prop where
  | nil : KWEquiv .nil .nil
  | sq (a : F) (u : F) (hu : u ≠ 0) : KWEquiv [a] [a * u^2]
  | prepend {l1 : List F} {l2 : List F} (k : KWEquiv l1 l2) (l3 : List F) :
    KWEquiv (l3 ++ l1) (l3 ++ l2)
  | append {l1 : List F} {l2 : List F} (k : KWEquiv l1 l2) (l3 : List F) :
    KWEquiv (l1 ++ l3) (l2 ++ l3)
  | swap a b : KWEquiv [a, b] [b, a]
  | add_cons_mul (a : F) (b : F) : KWEquiv [a, b] [a + b, a * b]
  | cons_mul (a : F) (b : F) : KWEquiv [a, b] [a, a * b]
  | mul_pfister_norm
      (a : F) (b : F) (t : F) (u : F) (ht : t ≠ 0 := by grind) (hu : u ≠ 0 := by grind) :
      KWEquiv [a, b] [a, b * (u^2 + a * t^2)]
  | norm_mul (a : F) (b : F) (u : F) (v : F) (hu : u ≠ 0 := by grind) (hv : v ≠ 0 := by grind) :
    KWEquiv [a, b] [a * u^2 + b * v^2, a * b]
  | symm : ∀ x y, KWEquiv x y → KWEquiv y x
  | trans {x : List F} {y : List F} {z : List F} : KWEquiv x y → KWEquiv y z → KWEquiv x z
  | refl : ∀ x, KWEquiv x x

attribute [grind .] KWEquiv.nil KWEquiv.swap KWEquiv.add_cons_mul KWEquiv.cons_mul
attribute [grind =>] KWEquiv.append KWEquiv.prepend
attribute [grind =>] KWEquiv.mul_pfister_norm KWEquiv.norm_mul
attribute [grind →, trans] KWEquiv.trans
attribute [symm, grind →] KWEquiv.symm
attribute [refl, grind .] KWEquiv.refl

instance : Trans (α := List F) KWEquiv KWEquiv KWEquiv where
  trans := KWEquiv.trans

@[inherit_doc KWEquiv]
infixr:50 " ≃ᴋᴡ " => KWEquiv

@[grind →]
lemma KWEquiv_length (L1 : List F) (L2 : List F) (h : L1 ≃ᴋᴡ L2) : L1.length = L2.length := by
  induction h with grind

namespace KWEquiv

/-- If `[a₁, …, aₙ] ≃ᴋᴡ [b₁, …, bₙ]`, then `(C a₁) * … * (C aₙ) = (C b₁) * … * (C bₙ)`. -/
@[grind →]
lemma map_C_prod_eq_of_KWEquiv [CharP F 2] {L1 : List F} {L2 : List F} (h : L1 ≃ᴋᴡ L2) :
    (List.map C L1).prod = (List.map C L2).prod := by
  induction h with
  | add_cons_mul a b =>
    simp only [List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one]
    rw [C_mul_C_eq_C_add_mul_C_mul a b]
  | mul_pfister_norm a b t u ht hu => grind [C_mul_eq_C_mul_C_mul_pfister_norm]
  | norm_mul a b u v hu hv => grind [C_mul_C_eq_C_norm_mul]
  | cons_mul a b => grind [C_mul_C_eq_C_mul_C_prod]
  | sq a u hu => grind
  | nil => simp only
  | prepend => grind
  | append  => grind
  | swap a b => grind
  | @trans l1 l2 l3 _ _ h1 h2 => grind
  | symm l1 l2 _ h => grind
  | refl _ => rfl

@[grind =>]
lemma cons {l1 : List F} {l2 : List F} (h : l1 ≃ᴋᴡ l2) (a : F) :
    a :: l1 ≃ᴋᴡ a :: l2 := by
  simpa using h.prepend [a]

lemma append_left (L1 : List F) (L2 : List F) (L3 : List F) (k : L1 ≃ᴋᴡ L2) :
    L3 ++ L1 ≃ᴋᴡ L3 ++ L2 := by
  induction L3 with grind

lemma cons_equiv_append_singleton (L1 : List F) (t : F) : t :: L1 ≃ᴋᴡ L1 ++ [t] := by
  induction L1 with
  | nil         => exact KWEquiv.refl [t]
  | cons u l h  =>
    have h₁ : (u :: t :: l) ≃ᴋᴡ (t :: u :: l) := by exact (swap u t).append l
    exact (h₁.symm).trans <| h.cons u

@[grind .]
lemma reverse (L1 : List F) : L1 ≃ᴋᴡ L1.reverse := by
  induction L1 with
  | nil        => rfl
  | cons u l h =>
    simp only [List.reverse_cons]
    exact (h.cons u).trans <| cons_equiv_append_singleton l.reverse u

@[grind =>]
lemma swap_top (a : F) (b : F) (l : List F) : a::b::l ≃ᴋᴡ b::a::l := (swap a b).append l

end KWEquiv

/-- An helper inductive predicate on lists that isolates a class of lists of elements of
`F` such that the product of the corresponding generators is zero in `KWitt F`. -/
@[grind]
inductive KWEquiv₀ : (l : List F) → Prop where
  | zero : KWEquiv₀ [0]
  | one : KWEquiv₀ [1]
  | double (a : F) : KWEquiv₀ [a, a]
  | of_KWEquiv {l₁ : List F} {l₂ : List F} :
    (KWEquiv₀ l₁) → (KWEquiv l₁ l₂) → KWEquiv₀ l₂
  | append {l₁ : List F} (h : KWEquiv₀ l₁) (l₂ : List F) : KWEquiv₀ (l₁ ++ l₂)

namespace KWEquiv₀

lemma zero_cons (l : List F) : KWEquiv₀ (0::l) := KWEquiv₀.zero.append l

lemma one_cons (l : List F) : KWEquiv₀ (1::l) := KWEquiv₀.one.append l

lemma self_self_cons (a : F) (l : List F) : KWEquiv₀ (a::a::l) :=
  (KWEquiv₀.double a).append l

@[grind =>]
lemma cons {l : List F} (h : KWEquiv₀ l) (a : F) : KWEquiv₀ (a::l) := by
  suffices hh : KWEquiv₀ (l ++ [a]) by
    exact hh.of_KWEquiv (KWEquiv.cons_equiv_append_singleton l a).symm
  exact h.append [a]

lemma of_suffix {l₁ : List F} (h : KWEquiv₀ l₁) {l₂ : List F} (hl₂ : l₁ <:+ l₂) :
    KWEquiv₀ l₂ := by
  obtain ⟨l, hl⟩ := hl₂
  induction l generalizing l₂ with grind

lemma map_C_prod_eq_zero [CharP F 2] {l : List F} (h : KWEquiv₀ l) : (l.map C).prod = 0 := by
  induction h with
  | zero => simp [W0]
  | one => simp [C_one]
  | double a => simp
  | append _ _ hr => simp [hr]
  | of_KWEquiv h h' hr => rwa [← h'.map_C_prod_eq_of_KWEquiv]

end KWEquiv₀

end KWEquiv

section squareField
-- TODO: generalize to all char, not just 2.
-- the ring of squares is a subfield
def Square (F : Type*) [Field F] [CharP F 2] : Subfield F := (frobenius F 2).fieldRange

instance {F : Type*} [Field F] [CharP F 2] : Field (↥(Square F)) :=
  (Square F).toField

namespace Square

variable {F : Type*} [Field F] [CharP F 2]

@[simp]
lemma mem_iff (x : F) : x ∈ (Square F) ↔ (∃ v, v^2 = x) := by
  unfold Square
  simp only [RingHom.mem_fieldRange]
  rfl

lemma square_iff (x : Square F) : ∃ (v : F), v^2 = x := by
  exact x.prop

@[simps! (attr := grind .)]
def mk (a : F) : Square F := ⟨a^2, ⟨a, by tauto⟩⟩

@[grind .]
lemma ne_zero_iff (c : Square F) : (c ≠ 0) ↔ (c.val ≠ 0) := by
  constructor
  · intro h
    simp only [ne_eq, ZeroMemClass.coe_eq_zero]
    exact h
  · simp

@[simp, grind =>]
lemma mk_ne_zero {a : F} (h : a ≠ 0 := by grind) : Square.mk a ≠ 0 := by grind

@[simps! (attr := grind .)]
def inclusion : Square F →+* F := (Square F).subtype

@[simp]
lemma smul_def (a : F) (c : Square F) : c • a = c.val * a := rfl

end Square

variable {F : Type*} [Field F]

lemma KWEquiv.square_smul [CharP F 2] (a : F) (c : Square F) (hc : c ≠ 0 := by grind) :
    [a] ≃ᴋᴡ [c • a] := by
  simp only [Square.smul_def]
  obtain ⟨c, ⟨v, rfl⟩⟩ := c
  simp only [frobenius, RingHom.coe_mk, powMonoidHom_apply]
  rw [mul_comm]
  exact KWEquiv.sq a v (by grind)

section nonemptyProducts

/-!
In this section, we provide a lot of boilerplate for the following construction: given a list `l`
of elements of a field F, there is a finite set of all nonempty products of elements of `l`.

There are many ways to define such a set. In what follows, we provide several variants
of the definitions, each with their pros and cons:
- `nonemptyProducts` defines the set inductively.
- `nonemptyProductsList` defines a list that enumerates all possible elements of `nonemptyProducts`:
  it is convenient to have such an explicit enumeration to compute the cardinal of that set.
- `nonemptyProducts'` is an intermediate abbrev to link the inductive definition from
  `nonemptyProducts` with the set obtained from the list `nonemptyProductsList`.

We could also consider a function that takes as input a function
`f : Fin (l.length) → Fin 1`, and maps it to the product of all l[i] ^ (f i), and
define the set of finite products as the range of this function, but at the end of the day,
working with big operators like this is not the most convenient, so we do not go with that route.
-/

/-- Given `l : List F`, `nonemptyProducts l` is the set of elements of `f` that are
finite nonempty products of elements of l.
It is defined inductively rather than by extension. -/
@[grind]
def nonemptyProducts [DecidableEq F] : List F → Finset F
  | List.nil      => ∅
  | List.cons a l =>
    insert a (nonemptyProducts l) ∪
      if ha : a = 0 then {0} else
      Finset.map ⟨(a * ·), by intros x y hxy; grind⟩ (nonemptyProducts l)

/-- Given `l : List F`, `nonemptyProductsList l` is the list of elements of finite products of
elements of l. -/
@[grind]
def nonemptyProductsList (l : List F) : List F :=
  match l with
  | List.nil => List.nil
  | List.cons a l => a:: (nonemptyProductsList l) ++ List.map (a * ·) (nonemptyProductsList l)

@[grind =>]
lemma nonemptyProductsList_ne_nil (l : List F) (hl : l ≠ []) :
    nonemptyProductsList l ≠ [] := by
  cases l with grind

lemma list_ne_nil_of_nonemptyProductsList_ne_nil (l : List F) :
    (nonemptyProductsList l ≠ []) → l ≠ [] := by cases l with grind

lemma nonemptyProductsList_length (l : List F) :
    (nonemptyProductsList l).length = 2 ^ l.length - 1 := by
  induction l with grind

lemma nonemptyProductsList_head (l : List F) (hl : l ≠ []) :
   (nonemptyProductsList l).head (by grind) = l.head hl := by
 cases l with grind

/-- An alternative description of nonemptyProducts -/
abbrev nonemptyProducts' [DecidableEq F] (l : List F) : Finset F :=
  (nonemptyProductsList l).toFinset

lemma nonemptyProducts'_card_of_nodup [DecidableEq F] (l : List F) :
    (nonemptyProductsList l).Nodup →
    (nonemptyProducts' l).card = 2 ^ l.length - 1 := by
  intro h
  dsimp [nonemptyProducts']
  convert List.toFinset_card_of_nodup h
  symm
  exact nonemptyProductsList_length l

/-- The list `nonemptyProductsList` actually enumerates all elements of `nonemptyProducts`. -/
theorem nonemptyProducts_eq_nonemptyProducts' [DecidableEq F] (l : List F) :
    nonemptyProducts' l = nonemptyProducts l := by
  induction l with
  | nil => dsimp [nonemptyProducts', nonemptyProductsList, nonemptyProducts]
  | cons a l h =>
    simp only [nonemptyProducts', nonemptyProductsList, List.cons_append, List.toFinset_cons,
      List.toFinset_append, nonemptyProducts, Finset.insert_union] at h ⊢
    rw [h]
    split_ifs with ha
    · subst ha
      ext a
      simp only [← h, zero_mul, List.map_const', Finset.mem_insert, Finset.mem_union,
        List.mem_toFinset, List.mem_replicate, ne_eq, List.length_eq_zero_iff,
        Finset.union_singleton, true_or, Finset.insert_eq_of_mem]
      grind
    · congr 2
      ext x
      simp [← h]

lemma mem_nonemptyProducts_of_mem_nonemptyProductsList [DecidableEq F] {l : List F} {a : F}
    (ha : a ∈ nonemptyProductsList l) : a ∈ nonemptyProducts l := by
  rw [← List.mem_toFinset, ← Finset.mem_coe] at ha
  rw [← nonemptyProducts_eq_nonemptyProducts']
  exact ha

lemma mem_nonemptyProducts_iff_mem_nonemptyProductsList [DecidableEq F] {l : List F} {a : F} :
    a ∈ nonemptyProductsList l ↔ a ∈ nonemptyProducts l := by
  refine ⟨fun ha => ?_, fun ha => ?_⟩
  · rw [← List.mem_toFinset, ← Finset.mem_coe] at ha
    rwa [← nonemptyProducts_eq_nonemptyProducts']
  · rw [← nonemptyProducts_eq_nonemptyProducts'] at ha
    simpa [nonemptyProducts'] using ha

lemma nonemptyProductsList_nonzero (l : List F) (hl : (∀ x ∈ l, x ≠ 0)) :
    ∀ x ∈ (nonemptyProductsList l), x ≠ 0 := by
  induction l with grind

lemma nonemptyProducts_nonzero [DecidableEq F] (l : List F) (hl : ∀ x ∈ l, x ≠ 0) :
    ∀ x ∈ (nonemptyProducts l), x ≠ 0 := by
  suffices ∀ x ∈ (nonemptyProductsList l), x ≠ 0 by
    grind [mem_nonemptyProducts_iff_mem_nonemptyProductsList]
  exact nonemptyProductsList_nonzero l hl

/-- A technical lemma describing the "reasons" for which the list of finite products of a list
would acquire duplicates -/
lemma not_nodup_nonemptyProductsList_cons (l : List F) (a : F) (ha : a ≠ 0)
    (hlnz : ∀ x ∈ l, x ≠ 0) (hl' : (nonemptyProductsList l).Nodup)
    (h : ¬ (nonemptyProductsList (a::l)).Nodup) :
    a ∈ nonemptyProductsList l ∨
      (1 ∈ nonemptyProductsList l) ∨
      (a = 1) ∨
      (∃ x ∈ (nonemptyProductsList l), ∃ y ∈ (nonemptyProductsList l), x ≠ y ∧ a * x = y) := by
  dsimp [nonemptyProductsList] at h
  simp only [List.nodup_cons, List.mem_append, List.mem_map, not_and_or, not_not] at h
  by_cases ha' : a ∈ nonemptyProductsList l
  · grind
  · grind [nonemptyProductsList_nonzero]

lemma mem_nonemptyProducts_of_ne_nil [DecidableEq F] (l : List F) (hl : l ≠ []) :
    l.prod ∈ nonemptyProducts l := by
  revert hl
  induction l with
  | nil => tauto
  | cons a l hl =>
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, List.prod_cons, forall_const]
    dsimp only [nonemptyProducts] at *
    cases l with
    | nil => simp [List.prod_nil, mul_one]
    | cons b l =>
      simp only [ne_eq, List.prod_cons] at hl
      apply Finset.mem_union_right
      split_ifs with ha
      · grind
      · rw [Finset.mem_map]
        use (b :: l).prod
        simp [hl]

lemma exists_prefix_of_not_nonemptyProductsList_nodup
    (l : List F) (hl : ∀ x ∈ l, x ≠ 0) (hl' : l.Nodup)
    (h : ¬ (nonemptyProductsList l).Nodup) :
    ∃ (l₀ : List F), ∃ (a : F), a::l₀ <:+ l ∧
      (nonemptyProductsList l₀ ).Nodup ∧ ¬(nonemptyProductsList (a::l₀)).Nodup := by
  induction l with grind

open scoped List
/- TODO: can this Prop be taken as the definition of `nonemptyProducts` instead?
It might be better to work with, but loses some of the inductive part. -/
/-- By design, any element of `nonemptyProducts l` is the product of elements over some sublist -/
lemma exists_eq_prod_of_mem_nonemptyProducts [DecidableEq F] (l : List F) (hl : l ≠ []) (x : F)
    (hf : x ∈ nonemptyProducts l) :
    ∃ (L₀ : List F), L₀ <+ l ∧ x = L₀.prod := by
  induction l generalizing x with
  | nil => grind
  | cons a l ih =>
    rw [← mem_nonemptyProducts_iff_mem_nonemptyProductsList] at hf
    simp only [nonemptyProductsList, List.cons_append, List.mem_cons, List.mem_append,
      List.mem_map] at hf
    obtain rfl | hx | ⟨y, hy, rfl⟩ := hf
    · use [x]; grind
    · cases l with
      | nil => grind
      | cons head tail =>
        have := ih (by simp) _ (by rwa [← mem_nonemptyProducts_iff_mem_nonemptyProductsList])
        grind
    · cases l with
      | nil => grind
      | cons head tail =>
        obtain ⟨L, hL, rfl⟩ :=
          ih (by simp) y (by rwa [← mem_nonemptyProducts_iff_mem_nonemptyProductsList])
        use a:: L
        grind

lemma nonemptyProducts_subset_cons [DecidableEq F] (l : List F) (a : F) :
    nonemptyProducts l ⊆ nonemptyProducts (a::l) := by
  grind

lemma mem_nonemptyProducts_of_ne_nil' [DecidableEq F] (l l' : List F) (hl : l ≠ [])
    (hll' : l <+ l') :
    l.prod ∈ nonemptyProducts l' := by
  induction hll' with
  | slnil => grind
  | cons a h ih => grind
  | @cons_cons l₁ l₂ a h ih =>
    cases l₁ with
    | nil => grind
    | cons head tail =>
      have := ih (by simp)
      simp only [List.prod_cons] at this
      rw [← mem_nonemptyProducts_iff_mem_nonemptyProductsList]
      simp only [nonemptyProductsList, List.cons_append, List.prod_cons, List.mem_cons,
        List.mem_append, List.mem_map, mul_eq_mul_left_iff]
      exact .inr <| .inr <|
        ⟨head * tail.prod, (by rwa [mem_nonemptyProducts_iff_mem_nonemptyProductsList]), by grind⟩

lemma nonemptyProductsList_perm_of_perm {l l' : List F} (hll' : l ~ l') :
    nonemptyProductsList l' ~ nonemptyProductsList l := by
  classical
  induction hll' with
  | nil => grind
  | cons x _ _ => grind
  | swap x y l₀ =>
    simp only [nonemptyProductsList, List.cons_append, List.map_cons,
      List.map_append, List.map_map,
      comp_mul_left, List.append_assoc]
    grind
  | trans _ _ _ _ => grind

@[grind →]
lemma nonemptyProducts_eq_of_perm [DecidableEq F] {l l' : List F} (hll' : l ~ l') :
    nonemptyProducts l' = nonemptyProducts l := by
  ext x
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← mem_nonemptyProducts_iff_mem_nonemptyProductsList] at h ⊢
    have := nonemptyProductsList_perm_of_perm hll'
    grind
  · rw [← mem_nonemptyProducts_iff_mem_nonemptyProductsList] at h ⊢
    have := nonemptyProductsList_perm_of_perm hll'
    grind

lemma mem_nonemptyProducts_of_ne_nil'' [DecidableEq F] (l l' : List F) (hl : l ≠ [])
    (hll' : l <+~ l') :
    l.prod ∈ nonemptyProducts l' := by
  rw [List.subperm_iff] at hll'
  obtain ⟨L₀, hL₀, hL₀'⟩ := hll'
  rw [nonemptyProducts_eq_of_perm hL₀]
  exact mem_nonemptyProducts_of_ne_nil' l L₀ hl hL₀'

@[simp, grind =]
lemma nonemptyProductsList_singleton [DecidableEq F] (a : F) :
    nonemptyProducts [a] = {a} := by
  grind

@[simp, grind =]
lemma nonemptyProducts_pair [DecidableEq F] (a b : F) :
    nonemptyProducts [a, b] = {a, b, a * b} := by
  dsimp [nonemptyProducts]
  split_ifs
  · grind
  · ext
    dsimp
    simp only [Finset.map_insert, Function.Embedding.coeFn_mk, Finset.map_singleton, mul_zero,
      Finset.union_insert, Finset.insert_union, Finset.union_idempotent, Finset.mem_insert,
      Finset.mem_singleton]
    grind
  · grind
  · ext
    dsimp
    simp only [Function.Embedding.coeFn_mk, Finset.map_singleton,
      Finset.insert_union, Finset.mem_insert, Finset.mem_singleton]
    grind
end nonemptyProducts

lemma nonemptyProducts_span_subset [CharP F 2] [DecidableEq F] (l : List F) (a : F) :
    Submodule.span (Square F) (nonemptyProducts l : Set F) ≤
      Submodule.span (Square F) (nonemptyProducts (a::l) : Set F) :=
  Submodule.span_mono (nonemptyProducts_subset_cons l a)

lemma exists_mem_prod [CharP F 2] [DecidableEq F] (a : F) (l : List F) (y : F)
    (hy : y ∈ Submodule.span (Square F) { a * x | x ∈ nonemptyProducts l}) :
    ∃ z ∈ Submodule.span (Square F) (nonemptyProducts l), y = z * a := by
    induction hy using Submodule.span_induction with
    | mem x h =>
      rw [Set.mem_setOf_eq] at h
      obtain ⟨z, ⟨h₁, h₂⟩⟩ := h
      use z
      constructor
      · apply Submodule.subset_span
        exact h₁
      · rw [mul_comm]
        tauto
    | smul x₀ x₁ _ h =>
      obtain ⟨z, h₁, rfl⟩ := h
      exact ⟨x₀ • z, Submodule.smul_mem _ _ h₁, by simp [mul_assoc]⟩
    | zero =>
      use 0
      simp
    | add x₀ _ x₁ _ hx₀r hx₁r =>
      obtain ⟨z₀, ⟨hz₀, hz₀r⟩⟩ := hx₀r
      obtain ⟨z₁, ⟨hz₁, hz₁r⟩⟩ := hx₁r
      use z₀ + z₁
      constructor
      · exact Submodule.add_mem _ hz₀ hz₁
      · rw [hz₀r, hz₁r, add_mul]

/-- Given any element in a list, it can be "bubbled" as the head of the list
through the `≃ᴋᴡ`-relation -/
lemma exists_KWEquiv_cons_of_mem (L : List F) (a : F) (h : a ∈ L) :
    ∃ l : List F, a::l ≃ᴋᴡ L := by
  induction L with
  | nil => tauto
  | cons b l₁ hr =>
    cases h with
    | head => use l₁
    | tail _ ha =>
      specialize hr ha
      obtain ⟨l, hl⟩ := hr
      use b::l
      calc a::b::l ≃ᴋᴡ  b::a::l := KWEquiv.swap_top _ _ _
           _       ≃ᴋᴡ  b::l₁   := hl.cons b

lemma prod_eq_zero_of_non_nodup (l : List F) (hl : ¬ l.Nodup) : KWEquiv₀ l := by
  induction l with
  | nil => simp only [List.nodup_nil, not_true] at hl
  | cons a l h =>
    simp only [List.nodup_cons, not_and] at hl
    by_cases ha : a ∈ l
    · by_cases hl' : l.Nodup
      · obtain ⟨l₁, hl₁⟩ := exists_KWEquiv_cons_of_mem l a ha
        suffices he : KWEquiv₀ (a::a::l₁) by
          apply he.of_KWEquiv
          exact hl₁.cons a
        exact KWEquiv₀.self_self_cons a l₁
      · grind
    · grind

lemma prod_zero_of_prod_suffix_eq_zero {l : List F} {l₁ : List F} (h : l₁ <:+ l)
    (hl₁ : (l₁.map C).prod = 0) :
    (l.map C).prod = 0 := by
  rcases h with ⟨t, ht⟩
  grind

@[grind →]
lemma KWEquiv₀.of_zero_mem {l : List F} (hl : 0 ∈ l) : KWEquiv₀ l := by
  obtain ⟨l₁, hl₁⟩ := exists_KWEquiv_cons_of_mem l 0 hl
  apply KWEquiv₀.of_KWEquiv _ hl₁
  exact KWEquiv₀.zero_cons _

theorem KWEquiv.mul_square_add
  (a s z : F) (l : List F) :
  a :: z :: l ≃ᴋᴡ a * (s ^ 2 + z) :: z :: l := by
  by_cases ht_z : s = 0
  · subst_vars
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add]
    calc a::z::l
      _ ≃ᴋᴡ z::a::l        := KWEquiv.swap_top a z l
      _ ≃ᴋᴡ z::(z * a)::l  := (KWEquiv.cons_mul z a).append l
      _ ≃ᴋᴡ (z * a)::z::l  := KWEquiv.swap_top _ _ _
      _ ≃ᴋᴡ (a * z)::z::l  := by rw [mul_comm]
  · calc a::z::l
    _ ≃ᴋᴡ z::a::l                        := KWEquiv.swap_top a z l
    _ ≃ᴋᴡ z::(a * (s^2 + z * (1^2)))::l  := (mul_pfister_norm z a 1 s).append l
    _ ≃ᴋᴡ z::(a * (s^2 + z))::l          := by grind
    _ ≃ᴋᴡ (a * (s^2 + z))::z::l          := KWEquiv.swap_top _ _ _

-- TODO: split off some cases/sub-computations to make the proof shorter
/- Given any (nonzero) element of `F` that can be represented
as a (squares F)-linear combination of finite products of elements of a list `L`, then
it is the head of a list which is `≃ᴋᴡ`-equivalent to L.
This is a "chain lemma" in some sense. -/
theorem exists_KWEquiv_cons_of_mem_span_nonemptyProducts
    [CharP F 2] [DecidableEq F] (L : List F) (hL : L ≠ []) (c : F) (hc : c ≠ 0)
    (h : c ∈ Submodule.span (Square F) (nonemptyProducts L)) :
    ∃ (L' : List F), KWEquiv L (c :: L') := by
  induction L generalizing c with
  | nil => grind
  | cons a l hr =>
    by_cases hl : l = []
    · use []
      rw [hl] at h ⊢
      simp only [nonemptyProductsList_singleton, Finset.coe_singleton,
        Submodule.mem_span_singleton] at h
      rcases h with ⟨⟨x, v, rfl⟩, rfl⟩
      dsimp [frobenius]
      grind [Square.smul_def, KWEquiv.sq a v]
    · replace hr := hr hl
      dsimp only [nonemptyProducts] at *
      rw [Finset.coe_union, Submodule.span_union, Submodule.mem_sup] at h
      rcases h with ⟨x₁, hx, y₀, hy₀, rfl⟩
      have hx :
          ∃ t, ∃ z ∈ Submodule.span ↥(Square F) ↑(nonemptyProducts l), x₁ = t ^ 2 * a + z := by
        simpa [Submodule.mem_span_insert] using hx
      obtain ⟨s, t, ht, rfl⟩ := hx
      by_cases ha : a = 0
      · subst ha
        simp only [↓reduceDIte, Finset.coe_singleton, Submodule.span_zero_singleton,
          Submodule.mem_bot] at hy₀
        subst hy₀
        simp only [mul_zero, zero_add, add_zero, ne_eq] at hc ⊢
        obtain ⟨L₀, hL₀⟩ := hr t hc ht
        grind [KWEquiv.swap_top 0 t L₀]
      · replace hy₀ : y₀ ∈ Submodule.span ↥(Square F) { a * x | x ∈ nonemptyProducts l } := by
          convert hy₀
          split_ifs
          ext; simp
        obtain ⟨z, hz₁, rfl⟩ := exists_mem_prod a l y₀ hy₀
        rw [show s ^ 2 * a + t + z * a = t + a * (s^2 + z) by ring]
        by_cases hy_z : s^2 + z = 0
        · simp only [hy_z, mul_zero, add_zero]
          obtain ⟨L₀, hL₀⟩ := hr t (by grind) (by grind)
          use a::L₀
          exact (hL₀.cons a).trans <| KWEquiv.swap_top _ _ _
        · have : a::l ≃ᴋᴡ a * (s^2 + z)::l := by
            by_cases hz_z : z = 0
            · subst_vars
              simpa using (KWEquiv.sq a s (by grind)).append l
            · obtain ⟨L₀, hL₀⟩ := hr z hz_z hz₁
              have := hL₀.cons _|>.trans <| KWEquiv.mul_square_add a s z L₀
              grind
          by_cases hx_z : t = 0
          · grind
          · obtain ⟨L₀, hL₀⟩ := hr t hx_z ht
            set y := s^2 + z
            use (a * y * t)::L₀
            calc a::l
              _ ≃ᴋᴡ (a * y)::l                   := this
              _ ≃ᴋᴡ (a * y)::t::L₀               := hL₀.cons (a * y)
              _ ≃ᴋᴡ (a * y + t)::(a * y * t)::L₀ := (KWEquiv.add_cons_mul (a * y) t).append L₀
              _ ≃ᴋᴡ (t + a * y)::(a * y * t)::L₀ := by grind

open List in
lemma List.perm_of_diff_eq_nil {α : Type*} [BEq α] [LawfulBEq α] {l l' : List α}
    (h₁ : l.diff l' = []) (h₂ : l'.diff l = []) : l ~ l' := by
  rw [List.perm_iff_count]
  intro a
  grind [List.count_diff, congr(count a $h₁)]

variable [CharP F 2]
open _root_.List in
lemma List.prod_mem_square
    [DecidableEq F] (l : List F)
    (hl : ∀ x : F, l.count x % 2 = 0) :
    l.prod ∈ Square F := by
  induction h : l.length using Nat.strongRec generalizing l with
  | ind n ih =>
    by_cases hl : l = []
    · simp [hl]
    · simp only [Square.mem_iff] at ih ⊢
      let a := l.head hl
      let l' := l.diff [a, a]
      have : (l' ++ [a,a] : Multiset F) = l := by
        ext b
        simp [l', List.count_erase, List.count_cons]
        grind
      have hl' : 0 < l.length := List.length_pos_of_ne_nil hl
      obtain ⟨v₁, hv₁⟩ := ih (n - 2) (by grind) l'
        (by simp only [diff_cons, diff_nil, count_erase, beq_iff_eq, l']; grind)
        (by
          have : l.head hl ∈ l.erase (l.head hl) := by
            simp only [← count_pos_iff, count_erase_self, tsub_pos_iff_lt]
            grind
          simp only [diff_cons, diff_nil, length_erase, head_mem, h, l', a]
          grind)
      use v₁ * a
      rw [← Multiset.prod_coe, ← this]
      simp only [Multiset.prod_coe, prod_append, prod_cons, prod_nil, mul_one]
      grind

open _root_.List in
-- TODO: cleanup
-- TODO: better docstring
/-- Given any element of nonemptyProducts l, there is a "complement" also in the set -/
lemma mul_eq_smul_square_of_mem_nonemptyProducts [DecidableEq F] (l : List F) (x y : F)
    (hx : x ∈ nonemptyProducts l) (hy : y ∈ nonemptyProducts l) (hxy : x ≠ y) :
    ∃ (t : Square F), ∃ z ∈ nonemptyProducts l, x * y = t • z := by
  by_cases hl : l = []
  · grind
  · obtain ⟨Lx, hLx, rfl⟩ := exists_eq_prod_of_mem_nonemptyProducts l (by grind) _ hx
    obtain ⟨Ly, hLy, rfl⟩ := exists_eq_prod_of_mem_nonemptyProducts l (by grind) _ hy
    rw [← List.prod_append]
    /- At this point, we want that `(Lx ++ Ly).prod = t * z` for some square `t` and
    some `z` in `nonemptyProducts`.
    This is best done using multisets: `t` can be taken as the product over the sum of
    the bag intersections of `Lx` and `Ly`, which lifts the multiset intersection to lists. -/
    let L₀ := Lx.bagInter Ly ++ Ly.bagInter Lx
    have hL₀ : L₀.prod ∈ Square F := List.prod_mem_square _ (by grind [List.count_bagInter])
    let t : Square F := ⟨_, hL₀⟩
    use t
    let L₁ := Lx.diff Ly ++ Ly.diff Lx
    have h : L₁ <+~ l := by grind [List.count_diff, List.subperm_iff_count]
    have : (Lx ++ Ly).prod = t • L₁.prod := by
      dsimp [t]
      rw [← List.prod_append]
      suffices h : (Multiset.ofList (Lx ++ Ly)) = (Multiset.ofList (L₀ ++ L₁)) by
        apply_fun (·.prod) at h
        simpa using h
      ext
      dsimp [L₁, L₀]
      simp only [Multiset.coe_count, List.count_append, List.append_assoc, List.count_bagInter,
        List.count_diff]
      grind
    suffices hL₁' : L₁.prod ∈ nonemptyProducts l by
      exact ⟨L₁.prod, hL₁', this⟩
    have hL₁ : L₁ ≠ [] := by
      intro hL₁
      rw [hL₁] at this
      dsimp [L₁] at hL₁
      simp only [List.append_eq_nil_iff] at hL₁
      obtain ⟨hLxy, hLxy'⟩ := hL₁
      suffices abs : Lx ~ Ly by
        grind [abs.prod_eq]
      exact List.perm_of_diff_eq_nil hLxy hLxy'
    exact mem_nonemptyProducts_of_ne_nil'' _ _ hL₁ h

lemma mul_mem_span_nonemptyProducts [DecidableEq F] (l : List F) (x y : F)
    (hx : x ∈ nonemptyProducts l) (hy : y ∈ nonemptyProducts l) (hxy : x ≠ y) :
    x * y ∈ Submodule.span (Square F) (nonemptyProducts l) := by
  obtain ⟨t, z, hz, htz⟩ := mul_eq_smul_square_of_mem_nonemptyProducts l x y hx hy hxy
  rw [htz]
  exact Submodule.smul_mem _ _ <| Submodule.subset_span hz

lemma one_mem_span_nonemptyProducts_of_not_linearIndependent [DecidableEq F]
    (l : List F) (_ : l ≠ [])
    (hl₁ : ∀ x ∈ l, x ≠ 0)
    (hl₂ : ¬ LinearIndependent (Square F) (fun x : nonemptyProducts l => (x : F))) :
    1 ∈ Submodule.span (Square F) (nonemptyProducts l : Set F) := by
  rw [not_linearIndependent_iff] at hl₂
  obtain ⟨s, g, hs, t, hi₀, hi₁⟩ := hl₂
  rw [← (Finset.add_sum_erase (a := t) _ _ hi₀)] at hs
  apply_fun (· * ↑t) at hs
  -- helping field_simp below
  have := nonemptyProducts_nonzero _ hl₁
  have : (t : F) ≠ 0 := by grind
  have : (g t : F) ≠ 0 := by grind
  rw [zero_mul, add_mul] at hs
  suffices h : (g t) • (t : F) * t ∈ Submodule.span (Square F) (nonemptyProducts l) by
    have h₀ := Submodule.span (Square F) (nonemptyProducts l : Set F) |>.smul_mem
      (g t * Square.mk (t : F))⁻¹ h
    convert h₀
    dsimp
    field_simp
  rw [add_eq_zero_iff_eq_neg] at hs
  rw [hs]
  apply Submodule.neg_mem
  rw [Finset.sum_mul]
  apply Submodule.sum_mem
  intro y hy
  rw [smul_mul_assoc]
  apply Submodule.smul_mem
  simp only [Finset.mem_erase, ne_eq] at hy
  obtain ⟨hy₁, hy₂⟩ := hy
  apply mul_mem_span_nonemptyProducts <;> grind

-- TODO: This proof is too long, extract lemmas and cleanup
/-- If the list of finite products of `l` has duplicates, then it is KW-zero-equiv. -/
lemma KWEquiv₀_of_not_nodup_nonemptyProductsList
    (l : List F) (hl : l.Nodup) (hl' : ∀ x ∈ l, x ≠ 0)
    (hfpl : ¬ (nonemptyProductsList l).Nodup) : KWEquiv₀ l := by
  classical
  obtain ⟨l₀, a, h₀, h₁, h₂⟩ := exists_prefix_of_not_nonemptyProductsList_nodup l hl' hl hfpl
  apply KWEquiv₀.of_suffix _ h₀
  have ha : a ≠ 0 := hl' _ <| List.IsSuffix.mem (by simp) h₀
  have hl₀ : ∀ x ∈ l₀, x ≠ 0 := by grind
  obtain ha₀ | h_one_in | ha_eq_one | ⟨x, hx, y, hy, hxy, haxy⟩ :=
      not_nodup_nonemptyProductsList_cons l₀ a ha hl₀ h₁ h₂
  · have hl₀' : l₀ ≠ [] := list_ne_nil_of_nonemptyProductsList_ne_nil l₀ (List.ne_nil_of_mem ha₀)
    have ha₀' : a ∈ Submodule.span (Square F) (nonemptyProducts l₀ : Set F) := by
      apply Submodule.subset_span
      rw [← nonemptyProducts_eq_nonemptyProducts' l₀]
      dsimp only [nonemptyProducts']
      simp only [List.coe_toFinset, Set.mem_setOf_eq, ha₀]
    obtain ⟨l₁, hl₁⟩ := exists_KWEquiv_cons_of_mem_span_nonemptyProducts l₀ hl₀' a ha ha₀'
    suffices he : KWEquiv₀ (a::a::l₁) by grind
    exact KWEquiv₀.self_self_cons a l₁
  · have h_one' : 1 ∈ Submodule.span (Square F) (nonemptyProducts l₀ : Set F) := by
      apply Submodule.subset_span
      rw [← nonemptyProducts_eq_nonemptyProducts' l₀]
      dsimp only [nonemptyProducts']
      simp only [List.coe_toFinset, Set.mem_setOf_eq, h_one_in]
    have hl₀' : l₀ ≠ [] :=
      list_ne_nil_of_nonemptyProductsList_ne_nil l₀ <| List.ne_nil_of_mem h_one_in
    obtain ⟨l₁, hl₁⟩ :=
      exists_KWEquiv_cons_of_mem_span_nonemptyProducts l₀ hl₀' 1 (one_ne_zero) h_one'
    exact .cons (.of_KWEquiv (.one_cons l₁) hl₁.symm) _
  · rw [ha_eq_one]
    exact KWEquiv₀.one_cons l₀
  · have hl₀' : l₀ ≠ [] := list_ne_nil_of_nonemptyProductsList_ne_nil l₀ (List.ne_nil_of_mem hx)
    have ha' : a ∈ Submodule.span (Square F) (nonemptyProducts l₀) := by
      apply_fun (fun t => t * x) at haxy
      have hx' := mem_nonemptyProducts_of_mem_nonemptyProductsList hx
      have hy' := mem_nonemptyProducts_of_mem_nonemptyProductsList hy
      obtain ⟨t, z, hz, htz⟩ := mul_eq_smul_square_of_mem_nonemptyProducts l₀ x y hx' hy' hxy
      rw [← mul_comm x y, htz] at haxy
      suffices ha' : a = (t / Square.mk x) • z by
        rw [ha']
        apply Submodule.smul_mem
        apply Submodule.subset_span
        exact hz
      · have hxnz := (nonemptyProductsList_nonzero l₀ hl₀ x hx)
        apply_fun (Square.mk x • ·)
        · dsimp only
          rw [smul_smul]
          simp only [Square.smul_def, Square.mk_coe, Subfield.coe_mul,
            Subfield.coe_div] at htz haxy ⊢
          grind
        · exact smul_right_injective F (Square.mk_ne_zero hxnz)
    obtain ⟨l₁, hl₁⟩ := exists_KWEquiv_cons_of_mem_span_nonemptyProducts l₀ hl₀' a ha ha'
    suffices he : KWEquiv₀ (a::a::l₁) from he.of_KWEquiv (hl₁.cons a).symm
    exact .self_self_cons a l₁

-- TODO: split cases into sub-lemmas

/-- If the dimension of F as a vector space over it subfield of square is less than 2^n, then
any list of length n + 1 is zero-equivalent. -/
theorem KWEquiv₀_of_finrank_le_two_pow (n : Nat) (l : List F)
    (hl : l.length = n + 1)
    [FiniteDimensional (Square F) F]
    (hd : Module.finrank (Square F) F ≤ 2 ^ n) : KWEquiv₀ l := by
  classical
  by_cases hl' : ∀ x ∈ l, x ≠ 0
  · by_cases hl_nodup : l.Nodup
    · by_cases hfpl : (nonemptyProductsList l).Nodup
      · set b := (fun x : nonemptyProducts l => (↑x : F))
        obtain _ | n := n
        · simp only [zero_add, pow_zero] at hl hd
          obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hl
          refine KWEquiv₀.of_KWEquiv (l₁ := [1]) .one ?_
          rw [finrank_le_one_iff] at hd
          obtain ⟨v, hv⟩ := hd
          obtain ⟨cₐ, rfl⟩ := hv a
          obtain ⟨c₁, hc⟩ := hv 1
          by_cases hcₐz : cₐ = 0
          · grind [zero_smul]
          by_cases hc₁z : c₁ = 0
          · simp only [hc₁z, zero_smul, zero_ne_one] at hc
          calc [1]
            _ ≃ᴋᴡ [c₁ • v]  := by rw [← hc]
            _ ≃ᴋᴡ [v]       := by exact (KWEquiv.square_smul v c₁ hc₁z).symm
            _ ≃ᴋᴡ [cₐ • v]  := (KWEquiv.square_smul v cₐ hcₐz)
        · have h_lindep : ¬ LinearIndependent (Square F) b := by
            intro h
            have card_hyp := LinearIndependent.fintype_card_le_finrank h
            rw [Fintype.card_coe, ← nonemptyProducts_eq_nonemptyProducts',
              nonemptyProducts'_card_of_nodup l hfpl, hl] at card_hyp
            grind
          obtain ⟨l₀, hl₀⟩ : ∃ l₀, l ≃ᴋᴡ 1 :: l₀ :=
            exists_KWEquiv_cons_of_mem_span_nonemptyProducts l (by grind) 1 one_ne_zero <|
              one_mem_span_nonemptyProducts_of_not_linearIndependent l (by grind) hl' h_lindep
          exact .of_KWEquiv (.one_cons _) hl₀.symm
      · exact KWEquiv₀_of_not_nodup_nonemptyProductsList l hl_nodup hl' hfpl
    · exact prod_eq_zero_of_non_nodup l hl_nodup
  · grind

/-- If `F` is a field such that the dimention of `F` over its subfield of squares is less than
`2^n`, then for any list of length `≥ n + 1` of elements of `F`, the corresponding product of
generators in `KWitt F` is zero.
This proves (though we don’t have the grading to formally state it yet) that for all `k > n + 1`,
the degree `k` part of `KWitt F` is the zero group. -/
theorem map_C_prod_eq_zero_of_finrank_le_two_pow (n : ℕ) (l : List F) (hl : l.length ≥ n + 1)
    [FiniteDimensional (Square F) F]
    (hd : Module.finrank (Square F) F ≤ 2 ^ n) :
    (l.map C).prod = 0 := by
  rw [← l.take_append_drop (n + 1), List.map_append, List.prod_append]
  suffices H : (List.map C (List.take (n + 1) l)).prod = 0 by grind
  exact (KWEquiv₀_of_finrank_le_two_pow n (l.take (n +1)) (by grind) hd).map_C_prod_eq_zero

end squareField

end KWitt
