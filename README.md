# Milnor Witt K-theory and Witt K-theory of Fields

This repository contains a formalized companion to the paper [Milnor-Witt K-theory and Witt K-theory of a field](https://arxiv.org/abs/2306.16985).
It contains a formalization of the definition of the Milnor-Witt K-theory of a field as a ring, as well as some of the computations done in the article. We also formalize the Grothendieck-Witt ring of a field through its presentation with generators and relations.
We formalize one of the technical point of Theorem 3.12 from *loc. cit*: that the classical proof that the powers of the fundamental ideal in the Witt ring of a field of characteristic 2 that is of finite-dimensional over its subfield of squares vanish for large enough power ``just works'' for Witt K-theory as well. This is the subject of the file [`KMilnorWitt/KWittCharTwo.lean`](KMilnorWitt/KWittCharTwo.lean).

## Repo overview

```
.
├── KMilnorWitt
│   ├── Basic.lean
│   ├── GrothendieckWitt.lean
│   ├── KWittCharTwo.lean
│   └── KWitt.lean
├── KMilnorWitt.lean
├── lakefile.toml
├── lake-manifest.json
├── lean-toolchain
├── LICENSE
└── README.md
```

- [`KMilnorWitt/Basic.lean`](KMilnorWitt/Basic.lean): define Milnor-Witt K-theory of a field, provide some computational lemmas about it. Show that the symbols `1 + η ⟦a⟧` satisfy the necessary relations to define a ring morphism from `GrothendieckWitt F` to `KMilnorWitt F`.
- [`KMilnorWitt/GrothendieckWitt.lean`](KMilnorWitt/GrothendieckWitt.lean): define `GW F` via generators and relations. Construct the `rank` morphism `GW F →+* ℤ`.
- [`KMilnorWitt/KWitt.lean`](KMilnorWitt/KWitt.lean): define `KWitt F` as a quotient of `KMilnorWitt F`. Provide some computations.
- [`KMilnorWitt/KWittCharTwo.lean`](KMilnorWitt/KWittCharTwo.lean): study `KWitt F` when `F` is of characteristic 2. Show that a product of `n + 1` generators in `KWitt F` when `F` is of characteristic 2 and such that the dimension of `F` over its subfield of squares is less than or equal to `2^n`.


## TODOs and future possible directions

Although the formalization in this repo verifies one of the key point of the proof of Theorem 3.12 of [arXiv:2306.16985](https://arxiv.org/abs/2306.16985), many more elements would need to be added before being able to formalize the full of the argument from start to end (and even conditionally on Kato’s result that we use as input in the theorem).

- Gradings: we currently only formalize `KMilnorWitt F` and its quotient as rings, but we do not put any graded ring structure on them. Such grading would follow naturally from suitable grading on free algebras, as well as the fact that taking a `RingQuot` of a graded algebra with respect to an "homogeneous" relation induces a grading on the quotient algebra.
- Milnor K-theory as a quotient of `KMilnorWitt F`.
- Witt ring and the fundamental ideal.
- Milnor’s map from `KMilnor` modulo 2 to the graded of the powers of the fundamental ideal.
- Reduction to the case of finitely generated fields over their prime fields: Theorem 3.12 of [arXiv:2306.16985](https://arxiv.org/abs/2306.16985) uses a continuity property for `KWitt F` that allows to reduce some statements to the case where `F`: it would be nice to formalize this kind of reduction to verify more of the proof of theorem 3.12.
- `p`-basis: for a field `F` of characteristic 2 that is finitely generated over its prime subfield, the assumption that `F` is finite dimensional over its subfield of square holds: it would be nice to formalize this. A general reference would be [Bourbaki, Algebra, Ch. V, n°1 & n°2, § 13](https://link.springer.com/book/10.1007/978-3-540-34499-5).
- Link with symmetric bilinear forms: we only formalize `GW F` via a presentation by generators and relations, which makes computations easy, but we currently do not link the theory of symmetric bilinear forms with the object we define here.
