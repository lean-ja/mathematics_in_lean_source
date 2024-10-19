-- BOTH:
import Mathlib.RingTheory.Ideal.QuotientOperations
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.ZMod.Quotient
import MIL.Common

noncomputable section

/- TEXT:
.. _rings:

TEXT. -/
/- OMIT:
Rings
-----

OMIT. -/
/- TEXT:
環
-----

.. index:: ring (algebraic structure)

TEXT. -/
/- OMIT:
Rings, their units, morphisms and subrings
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

OMIT. -/
/- TEXT:
環，単位元，射，部分間
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

TEXT. -/
/- OMIT:
The type of ring structures on a type ``R`` is ``Ring R``. The variant where multiplication is
assumed to be commutative is ``CommRing R``. We have already seen that the ``ring`` tactic will
prove any equality that follows from the axioms of a commutative ring.
OMIT. -/
/- TEXT:
型 ``R`` 上の環構造の型は ``Ring R`` です．乗法が可換であることを仮定するバージョンは ``CommRing R`` です．これまですでに， ``ring`` タクティクによって可換環の公理から導かれるあらゆる等式を証明することを見てきました．
EXAMPLES: -/
-- QUOTE:
example {R : Type*} [CommRing R] (x y : R) : (x + y) ^ 2 = x ^ 2 + y ^ 2 + 2 * x * y := by ring
-- QUOTE.

/- OMIT:
More exotic variants do not require that the addition on ``R`` forms a group but only an additive
monoid. The corresponding type classes are ``Semiring R`` and ``CommSemiring R``.
The type of natural numbers is an important instance of ``CommSemiring R``, as is any type
of functions taking values in the natural numbers.
Another important example is the type of ideals in a ring, which will be discussed below.
The name of the ``ring`` tactic is doubly misleading, since it assumes commutativity but works
in semirings as well. In other words, it applies to any ``CommSemiring``.
OMIT. -/
/- TEXT:
より独特な変種として， ``R`` 上の足し算が群を形成する必要がなく，加法的なモノイドであるようなものがあります．これに対応する型クラスは ``Semiring R`` と ``CommSemiring R`` です．自然数の型は ``CommSemiring R`` の重要な例であり，自然数に値を取る関数の型も同様にこれに属します．もう一つの重要な例は，後述する環のイデアルの型です． ``ring`` タクティクという名前は二重にミスリーディングを生んでいます．というのも，これは可換性を仮定していますが，半環でも機能するからです．言い換えればこのタクティクはどんな ``CommSemiring`` に対しても適用できます．
EXAMPLES: -/
-- QUOTE:
example (x y : ℕ) : (x + y) ^ 2 = x ^ 2 + y ^ 2 + 2 * x * y := by ring
-- QUOTE.

/- OMIT:
There are also versions of the ring and semiring classes that do not assume the existence of a
multiplicative unit or
the associativity of multiplication. We will not discuss those here.

OMIT. -/
/- TEXT:
また乗法について単位元の存在や結合性を仮定しない環や半環のクラスもあります．ここではそれらについては触れません．

TEXT. -/
/- OMIT:
Some concepts that are traditionally taught in an introduction to ring theory are actually about
the underlying multiplicative monoid.
A prominent example is the definition of the units of a ring. Every (multiplicative) monoid ``M``
has a predicate ``IsUnit : M → Prop`` asserting existence of a two-sided inverse, a
type ``Units M`` of units with notation ``Mˣ``, and a coercion to ``M``.
The type ``Units M`` bundles an invertible element with its inverse as well as properties than ensure
that each is indeed the inverse of the other.
This implementation detail is relevant mainly when defining computable functions. In most
situations one can use ``IsUnit.unit {x : M} : IsUnit x → Mˣ`` to build a unit.
In the commutative case, one also has ``Units.mkOfMulEqOne (x y : M) : x * y = 1 → Mˣ``
which builds ``x`` seen as unit.
OMIT. -/
/- TEXT:
環論の入門として伝統的に教えられているいくつかの概念は，実はその根底にある乗法的モノイドに関するものです．顕著な例は環の単位元の定義です．すべての（乗法的）モノイド ``M`` は左右の逆元の存在を保証する述語 ``IsUnit : M → Prop`` と， ``Mˣ`` という表記で ``M`` に強制される単位元の型 ``Units M`` を持ちます．型 ``Units M`` は可逆元とその逆元を束ねたものであり，それぞれが実際にお互いの逆元であることを保証する性質でもあります．この実装の詳細は主に計算可能な関数を定義する時に関係します．ほとんどの場合， ``IsUnit.unit {x : M} : IsUnit x → Mˣ`` を使って単位元を作ることができます．可換の場合は， ``Units.mkOfMulEqOne (x y : M) : x * y = 1 → Mˣ`` で ``x`` を単位元と見なして利用することもできます．
EXAMPLES: -/
-- QUOTE:
example (x : ℤˣ) : x = 1 ∨ x = -1 := Int.units_eq_one_or x

example {M : Type*} [Monoid M] (x : Mˣ) : (x : M) * x⁻¹ = 1 := Units.mul_inv x

example {M : Type*} [Monoid M] : Group Mˣ := inferInstance
-- QUOTE.

/- OMIT:
The type of ring morphisms between two (semi)-rings ``R`` and ``S`` is ``RingHom R S``,
with notation ``R →+* S``.
OMIT. -/
/- TEXT:
二つの（半）環 ``R`` と ``S`` の間の環の射の型は ``RingHom R S`` であり， ``R →+* S`` と表記されます．
EXAMPLES: -/
-- QUOTE:
example {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (x y : R) :
    f (x + y) = f x + f y := f.map_add x y

example {R S : Type*} [Ring R] [Ring S] (f : R →+* S) : Rˣ →* Sˣ :=
  Units.map f
-- QUOTE.

/- OMIT:
The isomorphism variant is ``RingEquiv``, with notation ``≃+*``.

OMIT. -/
/- TEXT:
これの同型版は ``RingEquiv`` で， ``≃+*`` と表記されます．

TEXT. -/
/- OMIT:
As with submonoids and subgroups, there is a ``Subring R`` type for subrings of a ring ``R``,
but this type is a lot less useful than the type of subgroups since one cannot quotient a ring by
a subring.
OMIT. -/
/- TEXT:
部分モノイドや部分群と同様に，環 ``R`` の部分環を表す ``Subring R`` 型が存在しますが，この部分環によって環の商を取ることができないため，部分群の型よりもはるかに使い勝手が悪いです．
EXAMPLES: -/
-- QUOTE:
example {R : Type*} [Ring R] (S : Subring R) : Ring S := inferInstance
-- QUOTE.

/- OMIT:
Also notice that ``RingHom.range`` produces a subring.

OMIT. -/
/- TEXT:
また ``RingHom.range`` が部分環を生成することにも注目してください．

TEXT. -/
/- OMIT:
Ideals and quotients
^^^^^^^^^^^^^^^^^^^^

OMIT. -/
/- TEXT:
イデアルと商
^^^^^^^^^^^^^^^^^^^^

TEXT. -/
/- OMIT:
For historical reasons, Mathlib only has a theory of ideals for commutative rings.
(The ring library was originally developed to make quick progress toward the foundations of modern
algebraic geometry.) So in this section we will work with commutative (semi)rings.
Ideals of ``R`` are defined as submodules of ``R`` seen as ``R``-modules. Modules will
be covered later in a chapter on linear algebra, but this implementation detail can mostly be
safely ignored since most (but not all) relevant lemmas are restated in the special context of
ideals. But anonymous projection notation won't always work as expected. For instance,
one cannot replace ``Ideal.Quotient.mk I`` by ``I.Quotient.mk`` in the snippet below because there
are two ``.``s and so it will parse as ``(Ideal.Quotient I).mk``; but ``Ideal.Quotient`` by itself
doesn't exist.
OMIT. -/
/- TEXT:
歴史的な理由から，Mathlibには可換環のイデアルの理論しかありません．（環のライブラリはもともと現代の代数幾何学の基礎用として急ピッチで開発されたものです．）そのため本節では可換環を取り扱うこととします． ``R`` のイデアルは ``R`` の部分加群として定義されます．加群はのちに線形代数の章で扱われますが，イデアルの特別な文脈において関連する補題の（全てではありませんが）ほとんどが再述されるため，この実装の詳細はほとんど無視しても大丈夫です．しかし，匿名の射影記法は常に期待通りに機能するわけではありません．例えば，以下のコード片では ``Ideal.Quotient.mk I`` を ``I.Quotient.mk`` で置き換えることはできません．というのもここでは ``.`` が2つあるため，これは ``(Ideal.Quotient I).mk`` とパースされてしまい， ``Ideal.Quotient`` 自体は存在しないからです．
EXAMPLES: -/
-- QUOTE:
example {R : Type*} [CommRing R] (I : Ideal R) : R →+* R ⧸ I :=
  Ideal.Quotient.mk I

example {R : Type*} [CommRing R] {a : R} {I : Ideal R} :
    Ideal.Quotient.mk I a = 0 ↔ a ∈ I :=
  Ideal.Quotient.eq_zero_iff_mem
-- QUOTE.

/- OMIT:
The universal property of quotient rings is ``Ideal.Quotient.lift``.
OMIT. -/
/- TEXT:
商環の普遍性は ``Ideal.Quotient.lift`` です．
EXAMPLES: -/
-- QUOTE:
example {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (f : R →+* S)
    (H : I ≤ RingHom.ker f) : R ⧸ I →+* S :=
  Ideal.Quotient.lift I f H
-- QUOTE.

/- OMIT:
In particular it leads to the first isomorphism theorem for rings.
OMIT. -/
/- TEXT:
特に，これは環についての第一同型定理を導きます．
EXAMPLES: -/
-- QUOTE:
example {R S : Type*} [CommRing R] [CommRing S](f : R →+* S) :
    R ⧸ RingHom.ker f ≃+* f.range :=
  RingHom.quotientKerEquivRange f
-- QUOTE.

/- OMIT:
Ideals form a complete lattice structure with the inclusion relation, as well as a semiring
structure. These two structures interact nicely.
OMIT. -/
/- TEXT:
イデアルは包含関係において完備束構造を形成し，また半環構造も持ちます．この2つの構造はうまく相互作用します．
EXAMPLES: -/
section
-- QUOTE:
variable {R : Type*} [CommRing R] {I J : Ideal R}

-- EXAMPLES:
example : I + J = I ⊔ J := rfl

example {x : R} : x ∈ I + J ↔ ∃ a ∈ I, ∃ b ∈ J, a + b = x := by
  simp [Submodule.mem_sup]

example : I * J ≤ J := Ideal.mul_le_left

example : I * J ≤ I := Ideal.mul_le_right

example : I * J ≤ I ⊓ J := Ideal.mul_le_inf
-- QUOTE.

end

/- OMIT:
One can use ring morphisms to push ideals forward and pull them back using ``Ideal.map`` and
``Ideal.comap``, respectively. As usual,
the latter is more convenient to use since it does not involve an existential quantifier.
This explains why it is used to state the condition that allows us to build morphisms between
quotient rings.
OMIT. -/
/- TEXT:
イデアルを押し出したり引き戻したりするにはそれぞれ ``Ideal.map`` と ``Ideal.comap`` を使います．いつものように，後者の方が存在量化子を伴わないため便利です．そのため，これは商環の間の射を構築するための条件として用いられています．
EXAMPLES: -/
-- QUOTE:
example {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (H : I ≤ Ideal.comap f J) : R ⧸ I →+* S ⧸ J :=
  Ideal.quotientMap J f H
-- QUOTE.

/- OMIT:
One subtle point is that the type ``R ⧸ I`` really depends on ``I``
(up to definitional equality), so having a proof that two ideals ``I`` and ``J`` are equal is not
enough to make the corresponding quotients equal. However, the universal properties do provide
an isomorphism in this case.
OMIT. -/
/- TEXT:
微妙な点として，型 ``R ⧸ I`` は実際に ``I`` に（定義上の同値を除いて）依存するため，2つのイデアル ``I`` と ``J`` が等しいことを証明するだけでは対応する商を等しくすることができません．しかし，普遍性はこの場合に同型性を提供します．
EXAMPLES: -/
-- QUOTE:
example {R : Type*} [CommRing R] {I J : Ideal R} (h : I = J) : R ⧸ I ≃+* R ⧸ J :=
  Ideal.quotEquivOfEq h
-- QUOTE.

/- OMIT:
We can now present the Chinese remainder isomorphism as an example. Pay attention to the difference
between the indexed infimum symbol ``⨅`` and the big product of types symbol ``Π``. Depending on
your font, those can be pretty hard to distinguish.
OMIT. -/
/- TEXT:
ここで中国の剰余における同型を紹介しましょう．添字付けられた上限記号 ``⨅`` と型についての大きな積記号 ``Π`` の違いに注意してください．フォントによっては区別が難しいかもしれません．
EXAMPLES: -/
-- QUOTE:
example {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] (f : ι → Ideal R)
    (hf : ∀ i j, i ≠ j → IsCoprime (f i) (f j)) : (R ⧸ ⨅ i, f i) ≃+* Π i, R ⧸ f i :=
  Ideal.quotientInfRingEquivPiQuotient f hf
-- QUOTE.

/- OMIT:
The elementary version of the Chinese remainder theorem, a statement about ``ZMod``, can be easily
deduced from the previous one:
OMIT. -/
/- TEXT:
``ZMod`` に関する記述としての初等版である中国の剰余定理は前のものから簡単に導くことができます．
BOTH: -/
-- QUOTE:
open BigOperators PiNotation

-- EXAMPLES:
example {ι : Type*} [Fintype ι] (a : ι → ℕ) (coprime : ∀ i j, i ≠ j → (a i).Coprime (a j)) :
    ZMod (∏ i, a i) ≃+* Π i, ZMod (a i) :=
  ZMod.prodEquivPi a coprime
-- QUOTE.

/- OMIT:
As a series of exercises, we will reprove the Chinese remainder theorem in the general case.

OMIT. -/
/- TEXT:
一連の演習問題として，中国の剰余定理を一般的なケースで再現します．

TEXT. -/
/- OMIT:
We first need to define the map appearing in the theorem, as a ring morphism, using the
universal property of quotient rings.
OMIT. -/
/- TEXT:
まず商環の普遍性を用いて，定理に登場する写像を環の射として定義する必要があります．
BOTH: -/
section
-- QUOTE:
variable {ι R : Type*} [CommRing R]
open Ideal Quotient Function

#check Pi.ringHom
#check ker_Pi_Quotient_mk

-- OMIT: /-- The homomorphism from ``R ⧸ ⨅ i, I i`` to ``Π i, R ⧸ I i`` featured in the Chinese
-- OMIT:   Remainder Theorem. -/
/-- ``R ⧸ ⨅ i, I i`` から ``Π i, R ⧸ I i`` への準同型は中国の剰余定理によって特徴づけられる -/
def chineseMap (I : ι → Ideal R) : (R ⧸ ⨅ i, I i) →+* Π i, R ⧸ I i :=
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  Ideal.Quotient.lift (⨅ i, I i) (Pi.ringHom fun i : ι ↦ Ideal.Quotient.mk (I i))
    (by simp [← RingHom.mem_ker, ker_Pi_Quotient_mk])
-- QUOTE.
-- BOTH:

/- OMIT:
Make sure the following next two lemmas can be proven by ``rfl``.
OMIT. -/
/- TEXT:
次の2つの補題が ``rfl`` で証明できることを確認してください．
BOTH: -/
-- QUOTE:
lemma chineseMap_mk (I : ι → Ideal R) (x : R) :
    chineseMap I (Quotient.mk _ x) = fun i : ι ↦ Ideal.Quotient.mk (I i) x :=
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  rfl
-- BOTH:

lemma chineseMap_mk' (I : ι → Ideal R) (x : R) (i : ι) :
    chineseMap I (mk _ x) i = mk (I i) x :=
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  rfl
-- QUOTE.
-- BOTH:

/- OMIT:
The next lemma proves the easy half of the Chinese remainder theorem, without any assumption on
the family of ideals. The proof is less than one line long.
OMIT. -/
/- TEXT:
次の補題はイデアルの族を仮定することなく，中国の剰余定理の半分のうち簡単なほうを証明します．証明は1行にも満たないものになります．
EXAMPLES: -/
-- QUOTE:
#check injective_lift_iff

-- BOTH:
lemma chineseMap_inj (I : ι → Ideal R) : Injective (chineseMap I) := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  rw [chineseMap, injective_lift_iff, ker_Pi_Quotient_mk]
-- QUOTE.
-- BOTH:

/- OMIT:
We are now ready for the heart of the theorem, which will show the surjectivity
of our ``chineseMap``. First we need to know the different ways one can express the coprimality
(also called co-maximality assumption). Only the first two will be needed below.
OMIT. -/
/- TEXT:
これで ``chineseMap`` の全射性を示す定理の核心に入る準備が整いました．まず，互いに素（co-maximality仮定とも呼ばれます）を表すさまざまな方法を知っておく必要があります．以下では最初の2つだけが必要です．
EXAMPLES: -/
-- QUOTE:
#check IsCoprime
#check isCoprime_iff_add
#check isCoprime_iff_exists
#check isCoprime_iff_sup_eq
#check isCoprime_iff_codisjoint
-- QUOTE.

/- OMIT:
We take the opportunity to use induction on ``Finset``. Relevant lemmas on ``Finset`` are given
below.
Remember that the ``ring`` tactic works for semirings and that the ideals of a ring form a semiring.
OMIT. -/
/- TEXT:
この機会に ``Finset`` に対する帰納法を使ってみることにしましょう．以下は ``Finset`` に関連する補題です． ``ring`` タクティクは半環にも機能し，環のイデアルは半環を形成することを思い出してください．
EXAMPLES: -/
-- QUOTE:
#check Finset.mem_insert_of_mem
#check Finset.mem_insert_self

-- BOTH:
theorem isCoprime_Inf {I : Ideal R} {J : ι → Ideal R} {s : Finset ι}
    (hf : ∀ j ∈ s, IsCoprime I (J j)) : IsCoprime I (⨅ j ∈ s, J j) := by
  classical
  simp_rw [isCoprime_iff_add] at *
  induction s using Finset.induction with
  | empty =>
      simp
  | @insert i s _ hs =>
      rw [Finset.iInf_insert, inf_comm, one_eq_top, eq_top_iff, ← one_eq_top]
      set K := ⨅ j ∈ s, J j
      calc
/- EXAMPLES:
        1 = I + K                  := sorry
        _ = I + K * (I + J i)      := sorry
        _ = (1 + K) * I + K * J i  := sorry
        _ ≤ I + K ⊓ J i            := sorry
SOLUTIONS: -/
        1 = I + K                  := (hs fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)).symm
        _ = I + K * (I + J i)      := by rw [hf i (Finset.mem_insert_self i s), mul_one]
        _ = (1 + K) * I + K * J i  := by ring
        _ ≤ I + K ⊓ J i            := by gcongr ; apply mul_le_left ; apply mul_le_inf

-- QUOTE.

/- OMIT:
We can now prove surjectivity of the map appearing in the Chinese remainder theorem.
OMIT. -/
/- TEXT:
これで中国の剰余定理に登場する写像の全射性を証明することができます．
BOTH: -/
-- QUOTE:
lemma chineseMap_surj [Fintype ι] {I : ι → Ideal R}
    (hI : ∀ i j, i ≠ j → IsCoprime (I i) (I j)) : Surjective (chineseMap I) := by
  classical
  intro g
  choose f hf using fun i ↦ Ideal.Quotient.mk_surjective (g i)
  have key : ∀ i, ∃ e : R, mk (I i) e = 1 ∧ ∀ j, j ≠ i → mk (I j) e = 0 := by
    intro i
    have hI' : ∀ j ∈ ({i} : Finset ι)ᶜ, IsCoprime (I i) (I j) := by
/- EXAMPLES:
      sorry
SOLUTIONS: -/
      intros j hj
      exact hI _ _ (by simpa [ne_comm, isCoprime_iff_add] using hj)
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    rcases isCoprime_iff_exists.mp (isCoprime_Inf hI') with ⟨u, hu, e, he, hue⟩
    replace he : ∀ j, j ≠ i → e ∈ I j := by simpa using he
    refine ⟨e, ?_, ?_⟩
    · simp [eq_sub_of_add_eq' hue, map_sub, eq_zero_iff_mem.mpr hu]
    · exact fun j hj ↦ eq_zero_iff_mem.mpr (he j hj)
-- BOTH:
  choose e he using key
  use mk _ (∑ i, f i * e i)
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  ext i
  rw [chineseMap_mk', map_sum, Fintype.sum_eq_single i]
  · simp [(he i).1, hf]
  · intros j hj
    simp [(he j).2 i hj.symm]
-- QUOTE.
-- BOTH:

/- OMIT:
Now all the pieces come together in the following:
OMIT. -/
/- TEXT:
これですべてのピースを次のようにまとめます：
BOTH: -/
-- QUOTE:
noncomputable def chineseIso [Fintype ι] (f : ι → Ideal R)
    (hf : ∀ i j, i ≠ j → IsCoprime (f i) (f j)) : (R ⧸ ⨅ i, f i) ≃+* Π i, R ⧸ f i :=
  { Equiv.ofBijective _ ⟨chineseMap_inj f, chineseMap_surj hf⟩,
    chineseMap f with }
-- QUOTE.

end

/- OMIT:
Algebras and polynomials
^^^^^^^^^^^^^^^^^^^^^^^^

OMIT. -/
/- TEXT:
代数と多項式
^^^^^^^^^^^^^^^^^^^^^^^^

TEXT. -/
/- OMIT:
Given a commutative (semi)ring ``R``, an *algebra over* ``R`` is a semiring ``A`` equipped
with a ring morphism whose image commutes with every element of ``A``. This is encoded as
a type class ``Algebra R A``.
The morphism from ``R`` to ``A`` is called the structure map and is denoted
``algebraMap R A : R →+* A`` in Lean.
Multiplication of ``a : A`` by ``algebraMap R A r`` for some ``r : R`` is called the scalar
multiplication of ``a`` by ``r`` and denoted by ``r • a``.
Note that this notion of algebra is sometimes called an *associative unital algebra* to emphasize the
existence of more general notions of algebra.

OMIT. -/
/- TEXT:
ある可換（半）環 ``R`` が与えられた時， ``R`` **上の代数** （algebra over ``R`` ）は，半環 ``A`` と ``A`` の各元に対して像が可換になる環の射からなります．これは型クラス ``Algebra R A`` としてエンコードされます． ``R`` から ``A`` への射は構造写像と呼ばれ， ``algebraMap R A : R →+* A`` と表記されます．ある ``r : R`` について ``a : A`` と ``algebraMap R A r`` の乗算は ``a`` と ``r`` のスカラー倍と呼ばれ， ``r • a`` と表記されます．このような代数の概念は，より一般的な代数の概念の存在を強調するために **結合的単位代数** （associative unital algebra）と呼ばれることがあります．

TEXT. -/
/- OMIT:
The fact that ``algebraMap R A`` is ring morphism packages together a lot of properties of scalar
multiplication, such as the following:
OMIT. -/
/- TEXT:
``algebraMap R A`` が環の射であるという事実には以下のようなスカラー倍の多くの性質が内臓されています：
EXAMPLES: -/
-- QUOTE:
example {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (r r' : R) (a : A) :
    (r + r') • a = r • a + r' • a :=
  add_smul r r' a

example {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (r r' : R) (a : A) :
    (r * r') • a = r • r' • a :=
  mul_smul r r' a
-- QUOTE.

/- OMIT:
The morphisms between two ``R``-algebras ``A`` and ``B`` are ring morphisms
which commute with scalar multiplication by elements of ``R``. They are bundled morphisms
with type ``AlgHom R A B``, which is denoted by ``A →ₐ[R] B``.

OMIT. -/
/- TEXT:
2つの ``R`` 代数 ``A`` と ``B`` の間の射は， ``R`` の要素によるスカラー倍について可換な環の射です．これらは ``AlgHom R A B`` 型を持つ束縛射であり， ``A →ₐ[R] B`` と表記されます．

TEXT. -/
/- OMIT:
Important examples of non-commutative algebras include algebras of endomorphisms and
algebras of square matrices, both of which will be covered in the chapter on linear algebra.
In this chapter we will discuss one of the most important examples of a commutative algebra,
namely, polynomial algebras.

OMIT. -/
/- TEXT:
非可換環の重要な例として，自己同型の代数と正方行列の代数が挙げられますが，これらは線形代数の章で扱います．本章では可換環論の最も重要な例で，すなわち多項式代数について述べます．

TEXT. -/
/- OMIT:
The algebra of univariate polynomials with coefficients in ``R`` is called ``Polynomial R``,
which can be written as ``R[X]`` as soon as one opens the ``Polynomial`` namespace.
The algebra structure map from ``R`` to ``R[X]`` is denoted by ``C``,
which stands for "constant" since the corresponding
polynomial functions are always constant. The indeterminate is denoted by ``X``.
OMIT. -/
/- TEXT:
``R`` に係数を持つ一変数多項式の代数は ``Polynomial R`` と呼ばれ， ``Polynomial`` 名前空間を開くだけで ``R[X]`` と書くことができます． ``R`` から ``R[X]`` への代数構造写像は ``C`` と表記されます．これは対応する多項式関数が常に定数関数になることから「定数（constant）」を意味しています．不定元は ``X`` で表されます．
EXAMPLES: -/
section Polynomials
-- QUOTE:
open Polynomial

example {R : Type*} [CommRing R] : R[X] := X

example {R : Type*} [CommRing R] (r : R) := X - C r
-- QUOTE.

/- OMIT:
In the first example above, it is crucial that we give Lean the expected type since it cannot be
determined from the body of the definition. In the second example, the target polynomial
algebra can be inferred from our use of ``C r`` since the type of ``r`` is known.

OMIT. -/
/- TEXT:
上記の最初の例では定義の本体から型を決定することができないため，Leanに期待される型を与えることが重要です．二つ目の例では， ``r`` の型がわかっているため， ``C r`` の使用から大昌となる多項式代数を推測することができます．

TEXT. -/
/- OMIT:
Because ``C`` is a ring morphism from ``R`` to ``R[X]``, we can use all ring morphisms lemmas
such as ``map_zero``, ``map_one``, ``map_mul``, and ``map_pow`` before computing in the ring
``R[X]``. For example:
OMIT. -/
/- TEXT:
``C`` は ``R`` から ``R[X]`` への環の射であるため，環 ``R[X]`` で計算をする前に ``map_zero`` や ``map_one`` ， ``map_mul`` ， ``map_pow`` などの環の射についての補題を使うことができます．例えば：
EXAMPLES: -/
-- QUOTE:
example {R : Type*} [CommRing R] (r : R) : (X + C r) * (X - C r) = X ^ 2 - C (r ^ 2) := by
  rw [C.map_pow]
  ring
-- QUOTE.

/- OMIT:
You can access coefficients using ``Polynomial.coeff``
OMIT. -/
/- TEXT:
係数にアクセスするには ``Polynomial.coeff`` を使うことができます．
EXAMPLES: -/
-- QUOTE:
example {R : Type*} [CommRing R] (r:R) : (C r).coeff 0 = r := by simp

example {R : Type*} [CommRing R] : (X ^ 2 + 2 * X + C 3 : R[X]).coeff 1 = 2 := by simp
-- QUOTE.

/- OMIT:
Defining the degree of a polynomial is always tricky because of the special case of the zero
polynomial. Mathlib has two variants: ``Polynomial.natDegree : R[X] → ℕ`` assigns degree
``0`` to the zero polynomial, and ``Polynomial.degree : R[X] → WithBot ℕ`` assigns ``⊥``.
In the latter, ``WithBot ℕ`` can be seen as ``ℕ ∪ {-∞}``, except that ``-∞`` is denoted ``⊥``,
the same symbol as the bottom element in a complete lattice. This special value is used as the
degree of the zero polynomial, and it is absorbent for addition. (It is almost absorbent for
multiplication, except that ``⊥ * 0 = 0``.)

OMIT. -/
/- TEXT:
多項式の次数の定義は零多項式という特殊なケースがあるため常に厄介です．Mathlibには2つのバリエーションがあります： ``Polynomial.natDegree : R[X] → ℕ`` は零多項式に次数 ``0`` を割り当てたもの，そして ``Polynomial.degree : R[X] → WithBot ℕ`` は ``⊥`` を割り当てたものです．後者では， ``WithBot ℕ`` は ``ℕ ∪ {-∞}`` と見なすことができますが， ``-∞`` は ``⊥`` と表記されます．この特別な値は零多項式の次数として使われ，加法について吸収的です．（掛け算に対しては ``⊥ * 0 = 0`` を除いてほぼ吸収的です．）

TEXT. -/
/- OMIT:
Morally speaking, the ``degree`` version is the correct one. For instance, it allows us to state
the expected formula for the degree of a product (assuming the base ring has no zero divisor).
OMIT. -/
/- TEXT:
理屈上は ``degree`` のバージョンが正しいです．例えば，積の次数について（ベースの環が零因子を持たないと仮定した場合に）期待される公式を述べることができます．
EXAMPLES: -/
-- QUOTE:
example {R : Type*} [Semiring R] [NoZeroDivisors R] {p q : R[X]} :
    degree (p * q) = degree p + degree q :=
  Polynomial.degree_mul
-- QUOTE.

/- OMIT:
Whereas the version for ``natDegree`` needs to assume non-zero polynomials.
OMIT. -/
/- TEXT:
一方， ``natDegree`` 用のバージョンでは非零多項式を仮定する必要があります．
EXAMPLES: -/
-- QUOTE:
example {R : Type*} [Semiring R] [NoZeroDivisors R] {p q : R[X]} (hp : p ≠ 0) (hq : q ≠ 0) :
    natDegree (p * q) = natDegree p + natDegree q :=
  Polynomial.natDegree_mul hp hq
-- QUOTE.

/- OMIT:
However, ``ℕ`` is much nicer to use than ``WithBot ℕ``, so Mathlib makes both versions available
and provides lemmas to convert between them. Also, ``natDegree`` is the more convenient definition
to use when computing the degree of a composition. Composition of polynomial is ``Polynomial.comp``
and we have:
OMIT. -/
/- TEXT:
しかし， ``ℕ`` よりも ``WithBot ℕ`` の方が使いやすいため，Mathlibでは両方のバージョンを利用できるようにし，両者を変換するための定理を提供しています．また，合成の次数を計算する際には ``natDegree`` の方が便利です．多項式の合成は ``Polynomial.comp`` であり，次のようになります：
EXAMPLES: -/
-- QUOTE:
example {R : Type*} [Semiring R] [NoZeroDivisors R] {p q : R[X]} :
    natDegree (comp p q) = natDegree p * natDegree q :=
  Polynomial.natDegree_comp
-- QUOTE.

/- OMIT:
Polynomials give rise to polynomial functions: any polynomial can be evaluated on ``R``
using ``Polynomial.eval``.
OMIT. -/
/- TEXT:
多項式は多項式関数を生み出します：任意の多項式は ``Polynomial.eval`` を使って ``R`` 上で評価することができます．
EXAMPLES: -/
-- QUOTE:
example {R : Type*} [CommRing R] (P: R[X]) (x : R) := P.eval x

example {R : Type*} [CommRing R] (r : R) : (X - C r).eval r = 0 := by simp
-- QUOTE.

/- OMIT:
In particular, there is a predicate, ``IsRoot``, that holds for elements ``r`` in ``R`` where a
polynomial vanishes.
OMIT. -/
/- TEXT:
特に，多項式が消失する ``R`` 内の要素 ``r`` に対して成り立つ ``IsRoot`` という述語があります．
EXAMPLES: -/
-- QUOTE:
example {R : Type*} [CommRing R] (P : R[X]) (r : R) : IsRoot P r ↔ P.eval r = 0 := Iff.rfl
-- QUOTE.

/- OMIT:
We would like to say that, assuming ``R`` has no zero divisor, a polynomial has at most as many
roots as its degree, where the roots are counted with multiplicities.
But once again the case of the zero polynomial is painful.
So Mathlib defines ``Polynomial.roots`` to send a polynomial ``P`` to a multiset,
i.e. the finite set that is defined to be empty if ``P`` is zero and the roots of ``P``,
with multiplicities, otherwise. This is defined only when the underlying ring is a domain
since otherwise the definition does not have good properties.
OMIT. -/
/- TEXT:
``R`` が零因子を持たないと仮定すると，重根の重複もカウントすると多項式は次数と同じ数の根を持つことになります．しかし，零多項式のケースはまたしても辛いものがあります．そこでMathlibは ``Polynomial.roots`` を定義しており，多項式 ``P`` を多集合，つまり ``P`` が0の場合は空，それ以外の場合は重根も含めた ``P`` の根として定義した有限集合に送るようにしています．これはベースの環が始域である場合にのみ定義されます．というのもそうでない場合は定義は良い性質を持たないからです．
EXAMPLES: -/
-- QUOTE:
example {R : Type*} [CommRing R] [IsDomain R] (r : R) : (X - C r).roots = {r} :=
  roots_X_sub_C r

example {R : Type*} [CommRing R] [IsDomain R] (r : R) (n : ℕ):
    ((X - C r) ^ n).roots = n • {r} :=
  by simp
-- QUOTE.

/- OMIT:
Both ``Polynomial.eval`` and ``Polynomial.roots`` consider only the coefficients ring. They do not
allow us to say that ``X ^ 2 - 2 : ℚ[X]`` has a root in ``ℝ`` or that ``X ^ 2 + 1 : ℝ[X]`` has a root in
``ℂ``. For this, we need ``Polynomial.aeval``, which will evaluate ``P : R[X]`` in any ``R``-algebra.
More precisely, given a semiring ``A`` and an instance of ``Algebra R A``, ``Polynomial.aeval`` sends
every element of ``a`` along the ``R``-algebra morphism of evaluation at ``a``. Since ``AlgHom``
has a coercion to functions, one can apply it to a polynomial.
But ``aeval`` does not have a polynomial as an argument, so one cannot use dot notation like in
``P.eval`` above.
OMIT. -/
/- TEXT:
``Polynomial.eval`` と ``Polynomial.roots`` はどちらも係数環のみを考慮します． ``X ^ 2 - 2 : ℚ[X]`` が ``ℝ`` に根を持つ，あるいは ``X ^ 2 + 1 : ℝ[X]`` が ``ℂ`` に根を持つことを言えません．このため，任意の ``R`` 代数において ``P : R[X]`` を評価する ``Polynomial.aeval`` が必要です．より正確には，半環 ``A`` と ``Algebra R A`` のインスタンスが与えられた時， ``Polynomial.aeval`` は ``a`` の各元を ``a`` での ``R`` 代数の評価射に沿って送ります． ``AlgHom`` は関数に対する強制機能を持っているため，多項式に適用をすることができます．しかし， ``aeval`` は多項式を引数に取らないため，上記の ``P.eval`` のようなドット記法は使うことができません．
EXAMPLES: -/
-- QUOTE:
example : aeval Complex.I (X ^ 2 + 1 : ℝ[X]) = 0 := by simp

-- QUOTE.
/- OMIT:
The function corresponding to ``roots`` in this context is ``aroots`` which takes a polynomial
and then an algebra and outputs a multiset (with the same caveat about the zero polynomial as
for ``roots``).
OMIT. -/
/- TEXT:
この文脈で ``roots`` に対応する関数は ``aroots`` であり，これは多項式と代数を受け取り，多集合を出力します（ ``roots`` と同じように零多項式についての注意点があります）．
EXAMPLES: -/
-- QUOTE:
open Complex Polynomial

example : aroots (X ^ 2 + 1 : ℝ[X]) ℂ = {Complex.I, -I} := by
  suffices roots (X ^ 2 + 1 : ℂ[X]) = {I, -I} by simpa [aroots_def]
  have factored : (X ^ 2 + 1 : ℂ[X]) = (X - C I) * (X - C (-I)) := by
    have key : (C I * C I : ℂ[X]) = -1 := by simp [← C_mul]
    rw [C_neg]
    linear_combination key
  have p_ne_zero : (X - C I) * (X - C (-I)) ≠ 0 := by
    intro H
    apply_fun eval 0 at H
    simp [eval] at H
  simp only [factored, roots_mul p_ne_zero, roots_X_sub_C]
  rfl

-- OMIT: Mathlib knows about D'Alembert-Gauss theorem: ``ℂ`` is algebraically closed.
-- MathlibはD'Alembert-Gaussの定理を知っています： ``ℂ`` は代数的に閉じています．
example : IsAlgClosed ℂ := inferInstance

-- QUOTE.
/- OMIT:
More generally, given an ring morphism ``f : R →+* S`` one can evaluate ``P : R[X]`` at a point
in ``S`` using ``Polynomial.eval₂``. This one produces an actual function from ``R[X]`` to ``S``
since it does not assume the existence of a ``Algebra R S`` instance, so dot notation works as
you would expect.
OMIT. -/
/- TEXT:
より一般的には，環の射 ``f : R →+* S`` が与えられると， ``P : R[X]`` を ``S`` の点で ``Polynomial.eval₂`` によって評価することができます．これは ``R[X]`` から ``S`` への実際の関数を生成するもので， ``Algebra R S`` インスタンスの存在を仮定していないためドット記法は期待通りに機能します．
EXAMPLES: -/
-- QUOTE:
#check (Complex.ofReal : ℝ →+* ℂ)

example : (X ^ 2 + 1 : ℝ[X]).eval₂ Complex.ofReal Complex.I = 0 := by simp
-- QUOTE.

/- OMIT:
Let us end by mentioning multivariate polynomials briefly. Given a commutative semiring ``R``,
the ``R``-algebra of polynomials with coefficients in ``R`` and indeterminates indexed by
a type ``σ`` is ``MVPolynomial σ R``. Given ``i : σ``, the corresponding polynomial is
``MvPolynomial.X i``. (As usual, one can open the ``MVPolynomial`` namespace to shorten this
to ``X i``.)
For instance, if we want two indeterminates we can use
``Fin 2`` as ``σ`` and write the polynomial defining the unit circle in :math:`\mathbb{R}^2`` as:
OMIT. -/
/- TEXT:
最後に多変数多項式について簡単に触れておきましょう．可換環 ``ℝ`` が与えられた時， ``R`` に係数と型 ``σ`` で添字付けられた不定元を持つ多項式の ``R`` 代数は ``MVPolynomial σ R`` です． ``i : σ`` が与えられた時，対応する多項式は ``MvPolynomial.X i`` です．（いつものように， ``MVPolynomial`` 名前空間を開くことでこれを ``X i`` と短縮することができます．）例えば，2つの不定元が欲しい場合， ``Fin 2`` を ``σ`` として使い， :math:`\mathbb{R}^2`` の単位円を定義する多項式を次のように書くことができます．
EXAMPLES: -/
-- QUOTE:
open MvPolynomial

def circleEquation : MvPolynomial (Fin 2) ℝ := X 0 ^ 2 + X 1 ^ 2 - 1
-- QUOTE.

/- OMIT:
Recall that function application has a very high precedence so the expression above is read as
``(X 0) ^ 2 + (X 1) ^ 2 - 1``.
We can evaluate it to make sure the point with coordinates :math:`(1, 0)` is on the circle.
Recall the ``![...]`` notation denotes elements of ``Fin n → X`` for some natural number ``n``
determined by the number of arguments and some type ``X`` determined by the type of arguments.
OMIT. -/
/- TEXT:
関数の適用は非常に高い優先度を持つため，上の式は ``(X 0) ^ 2 + (X 1) ^ 2 - 1`` と読めることを思い出してください．これを評価して座標 :math:`(1, 0)` の点が円上にあることを確認することができます．この ``![...]`` 記法は，引数の数によって決まる自然数 ``n`` と引数の型によって決まる ``X`` の ``Fin n → X`` の要素を表すことを思い出してください．
EXAMPLES: -/
-- QUOTE:
example : MvPolynomial.eval ![0, 1] circleEquation = 0 := by simp [circleEquation]
-- QUOTE.

end Polynomials
