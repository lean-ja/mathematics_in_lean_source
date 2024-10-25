-- BOTH:
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Charpoly.Basic

import MIL.Common

/- TEXT:
.. index:: vector subspace

TEXT. -/
/- OMIT:
Subspaces and quotients
-----------------------

OMIT. -/
/- TEXT:
部分空間と商空間
-----------------------

TEXT. -/
/- OMIT:
Subspaces
^^^^^^^^^

OMIT. -/
/- TEXT:
部分空間
^^^^^^^^^

TEXT. -/
/- OMIT:
Just as linear maps are bundled, a linear subspace of ``V`` is also a bundled structure consisting of
a set in ``V``, called the carrier of the subspace, with the relevant closure properties.
Again the word module appears instead of vector space because of the more general context that
Mathlib actually uses for linear algebra.
OMIT. -/
/- TEXT:
線形写像が束ねられているように， ``V`` の線形部分空間も束ねられた構造であり，部分空間の台集合と呼ばれる ``V`` の集合から構成され，関連する閉方の性質を持ちます．ここでもベクトル空間の代わりに加群の言葉が出てきますが，これはMathlibが線形代数により一般的な文脈を使用しているためです．
EXAMPLES: -/
-- QUOTE:

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

example (U : Submodule K V) {x y : V} (hx : x ∈ U) (hy : y ∈ U) :
    x + y ∈ U :=
  U.add_mem hx hy

example (U : Submodule K V) {x : V} (hx : x ∈ U) (a : K) :
    a • x ∈ U :=
  U.smul_mem a hx

-- QUOTE.

/- OMIT:
In the example above, it is important to understand that ``Submodule K V`` is the type of ``K``-linear
subspaces of ``V``, rather than a predicate ``IsSubmodule U`` where ``U`` is an element of ``Set V``.
``Submodule K V`` is endowed with a coercion to ``Set V`` and a membership predicate on ``V``.
See :numref:`section_hierarchies_subobjects` for an explanation of how and why this is done.

OMIT. -/
/- TEXT:
上の例では， ``Submodule K V`` は ``V`` の ``K`` 上の線形部分空間の型であり， ``U`` が ``Set V`` の元である ``IsSubmodule U`` という述語ではないことを理解することが重要です． ``Submodule K V`` は ``Set V`` への強制子と ``V`` への所属についての述語を持ちます．この方法と理由については :numref:`section_hierarchies_subobjects` を参照してください．

TEXT. -/
/- OMIT:
Of course, two subspaces are the same if and only if they have the same elements. This fact
is registered for use with the ``ext`` tactic, which can be used to prove two subspaces are
equal in the same way it is used to prove that two sets are equal.

OMIT. -/
/- TEXT:
もちろん，2つの部分空間が同じであるのは，同じ要素を持つ場合に限ります．この事実は ``ext`` タクティクで使用するために登録されており，2つの集合が等しいことを証明するのと同じように，2つの部分空間が等しいことを証明するために使用することができます．

TEXT. -/
/- OMIT:
To state and prove, for example, that ``ℝ`` is a ``ℝ``-linear subspace of ``ℂ``,
what we really want is to construct a term of type ``Submodule ℝ ℂ`` whose projection to
``Set ℂ`` is ``ℝ``, or, more precisely, the image of ``ℝ`` in ``ℂ``.
OMIT. -/
/- TEXT:
例えば， ``ℝ`` が ``ℂ`` の ``ℝ`` 上の線形部分空間であることを述べて証明するために実際に必要なものは， ``Set ℂ`` への射影が ``ℝ`` （より正確には ``ℂ`` 中の像 ``ℝ`` ）である ``Submodule ℝ ℂ`` 型の項を構成することです．
EXAMPLES: -/
-- QUOTE:
noncomputable example : Submodule ℝ ℂ where
  carrier := Set.range ((↑) : ℝ → ℂ)
  add_mem' := by
    rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
    use n + m
    simp
  zero_mem' := by
    use 0
    simp
  smul_mem' := by
    rintro c - ⟨a, rfl⟩
    use c*a
    simp

-- QUOTE.

/- OMIT:
The prime at the end of proof fields in ``Submodule`` are analogous to the one in ``LinearMap``.
Those fields are stated in terms of the ``carrier`` field because they are defined before the
``MemberShip`` instance. They are then superseded by ``Submodule.add_mem``, ``Submodule.zero_mem``
and ``Submodule.smul_mem`` that we saw above.

OMIT. -/
/- TEXT:
``Submodule`` の証明フィールドの末尾についているプライムは ``LinearMap`` のものと似ています．これらのフィールドは ``MemberShip`` インスタンスの前に定義されているため， ``carrier`` フィールドを使って記述されています．この記述の後では，これらのフィールドは ``Submodule.add_mem`` と ``Submodule.zero_mem`` ， ``Submodule.smul_mem`` に取って代わられます．

TEXT. -/
/- OMIT:
As an exercise in manipulating subspaces and linear maps, you will define the pre-image of
a subspace by a linear map (of course we will see below that Mathlib already knows about this).
Remember that ``Set.mem_preimage`` can be used to rewrite a statement involving
membership and preimage. This is the only lemma you will need in addition to the lemmas
discussed above about ``LinearMap`` and ``Submodule``.
OMIT. -/
/- TEXT:
部分空間と線形写像の操作の演習として，線形写像による部分空間の逆像を定義しましょう（もちろん，Mathlibがこのことを知っていることは後で見ます）． ``Set.mem_preimage`` は所属と逆像を含む文を書き換えるのに使うことができることを覚えておいてください．必要な補題は今のこれと， ``LinearMap`` と ``Submodule`` について上述した補題だけです．
BOTH: -/
-- QUOTE:
def preimage {W : Type*} [AddCommGroup W] [Module K W] (φ : V →ₗ[K] W) (H : Submodule K W) :
    Submodule K V where
  carrier := φ ⁻¹' H
  zero_mem' := by
/- EXAMPLES:
    dsimp
    sorry
SOLUTIONS: -/
    dsimp
    rw [Set.mem_preimage, map_zero]
    exact H.zero_mem
-- BOTH:
  add_mem' := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    rintro a b ha hb
    rw [Set.mem_preimage, map_add]
    apply H.add_mem <;> assumption
-- BOTH:
  smul_mem' := by
/- EXAMPLES:
    dsimp
    sorry
SOLUTIONS: -/
    dsimp
    rintro a v hv
    rw [Set.mem_preimage, map_smul]
    exact H.smul_mem a hv
-- BOTH:
-- QUOTE.

/- OMIT:
Using type classes, Mathlib knows that a subspace of a vector space inherits a vector space structure.
OMIT. -/
/- TEXT:
型クラスを使うことで，Mathlibはベクトル空間の部分空間がベクトル空間の構造を継承することを知っています．
EXAMPLES: -/
-- QUOTE:
example (U : Submodule K V) : Module K U := inferInstance
-- QUOTE.

/- OMIT:
This example is subtle. The object ``U`` is not a type, but Lean automatically coerces it to
a type by interpreting it as a subtype of ``V``.
So the above example can be restated more explicitly as:
OMIT. -/
/- TEXT:
この例は微妙です．オブジェクト ``U`` は型ではありませんが，Leanはそれを ``V`` の部分型と解釈することで，自動的に型に強制しています．つまり，上の例はより明確に次のように言い換えることができます：
EXAMPLES: -/
-- QUOTE:
example (U : Submodule K V) : Module K {x : V // x ∈ U} := inferInstance
-- QUOTE.

/- OMIT:

Complete lattice structure and internal direct sums
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

OMIT. -/
/- TEXT:
完備束構造と内部直和
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

TEXT. -/
/- OMIT:
An important benefit of having a type ``Submodule K V`` instead of a predicate
``IsSubmodule : Set V → Prop`` is that one can easily endow ``Submodule K V`` with additional structure.
Importantly, it has the structure of a complete lattice structure with respect to
inclusion. For instance, instead of having a lemma stating that an intersection of
two subspaces of ``V`` is again a subspace, we
use the lattice operation ``⊓`` to construct the intersection. We can then apply arbitrary
lemmas about lattices to the construction.

OMIT. -/
/- TEXT:
述語 ``IsSubmodule : Set V → Prop`` の代わりに ``Submodule K V`` 型を持つことの重要な利点は， ``Submodule K V`` に追加の構造を簡単に与えられることです．重要なものとしては，包含に関して完備束構造を持つことです．例えば， ``V`` の2つの部分空間の共通部分が再び部分空間であるという補題を持つ代わりに，束の演算 ``⊓`` を使って共通部分を構成します．そして，束に関する任意の補題をこの構成に適用することができます．

TEXT. -/
/- OMIT:
Let us check that the set underlying the infimum of two subspaces is indeed, by definition,
their intersection.
OMIT. -/
/- TEXT:
ここで，2つの部分空間の下限の台集合が定義上確かにそれらの共通部分であることを確認しましょう．
EXAMPLES: -/
-- QUOTE:
example (H H' : Submodule K V) :
    ((H ⊓ H' : Submodule K V) : Set V) = (H : Set V) ∩ (H' : Set V) := rfl
-- QUOTE.

/- OMIT:
It may look strange to have a different notation for what amounts to the intersection of the
underlying sets, but the correspondence does not carry over to the supremum operation and set
union, since a union of subspaces is not, in general, a subspace.
Instead one needs to use the subspace generated by the union, which is done
using ``Submodule.span``.
OMIT. -/
/- TEXT:
台集合の共通部分に相当するものに対して異なる表記をするのは奇妙に見えるかもしれませんが，部分空間の合併は一般的に部分空間ではないため，この対応関係は上限演算や集合の合併には引き継がれません．代わりに合併によって生成される部分空間を使用する必要があり，これは ``Submodule.span`` を使用して行われます．
EXAMPLES: -/
-- QUOTE:
example (H H' : Submodule K V) :
    ((H ⊔ H' : Submodule K V) : Set V) = Submodule.span K ((H : Set V) ∪ (H' : Set V)) := by
  simp [Submodule.span_union]
-- QUOTE.

/- OMIT:
Another subtlety is that ``V`` itself does not have type ``Submodule K V``,
so we need a way to talk about ``V`` seen as a subspace of ``V``.
This is also provided by the lattice structure: the full subspace is the top element of
this lattice.
OMIT. -/
/- TEXT:
もう1つの微妙な点は， ``V`` 自身は ``Submodule K V`` という型を持たないため， ``V`` の部分空間として見た ``V`` について語る方法が必要だということです．これは束の構造によって提供されます：完全な部分空間はこの束の一番上の要素です．
EXAMPLES: -/
-- QUOTE:
example (x : V) : x ∈ (⊤ : Submodule K V) := trivial
-- QUOTE.

/- OMIT:
Similarly the bottom element of this lattice is the subspace whose only element is the
zero element.
OMIT. -/
/- TEXT:
同じように，この束のボトムの要素は，唯一の要素が零元である部分空間です．
EXAMPLES: -/
-- QUOTE:
example (x : V) : x ∈ (⊥ : Submodule K V) ↔ x = 0 := Submodule.mem_bot K
-- QUOTE.

/- OMIT:
In particular we can discuss the case of subspaces that are in (internal) direct sum.
In the case of two subspaces, we use the general purpose predicate ``IsCompl``
which makes sense for any bounded partially ordered type.
In the case of general families of subspaces we use ``DirectSum.IsInternal``.

OMIT. -/
/- TEXT:
特に，（内部）直和の中の部分空間の場合について議論することができます．部分空間が2つの場合，任意の有界な半順序型に対して意味を為す汎用的な述語 ``IsCompl`` を使用します．一般的な部分空間の族である場合は， ``DirectSum.IsInternal`` を使用します．
EXAMPLES: -/
-- QUOTE:

-- OMIT: If two subspaces are in direct sum then they span the whole space.
-- 2つの部分空間が直和である場合，それらで空間全体が張られます．
example (U V : Submodule K V) (h : IsCompl U V) :
  U ⊔ V = ⊤ := h.sup_eq_top

-- OMIT: If two subspaces are in direct sum then they intersect only at zero.
-- 2つの部分空間が直和である場合，それらは0でのみ交わります．
example (U V : Submodule K V) (h : IsCompl U V) :
  U ⊓ V = ⊥ := h.inf_eq_bot

section
open DirectSum
variable {ι : Type*} [DecidableEq ι]

-- OMIT: If subspaces are in direct sum then they span the whole space.
-- 部分空間が直和である場合，それらで空間全体が張られます．
example (U : ι → Submodule K V) (h : DirectSum.IsInternal U) :
  ⨆ i, U i = ⊤ := h.submodule_iSup_eq_top

-- OMIT: If subspaces are in direct sum then they pairwise intersect only at zero.
-- 部分空間が直和である場合，それらは0でのみ交わります．
example {ι : Type*} [DecidableEq ι] (U : ι → Submodule K V) (h : DirectSum.IsInternal U)
    {i j : ι} (hij : i ≠ j) : U i ⊓ U j = ⊥ :=
  (h.submodule_independent.pairwiseDisjoint hij).eq_bot

-- OMIT: Those conditions characterize direct sums.
-- これらの条件は直和で特徴づけられています．
#check DirectSum.isInternal_submodule_iff_independent_and_iSup_eq_top

-- OMIT: The relation with external direct sums: if a family of subspaces is
-- OMIT: in internal direct sum then the map from their external direct sum into `V`
-- OMIT: is a linear isomorphism.
-- 外部直和との関係：ある部分空間の族が内部直和にある場合，その外部直和からの `V` への写像は線形同型です．
noncomputable example {ι : Type*} [DecidableEq ι] (U : ι → Submodule K V)
    (h : DirectSum.IsInternal U) : (⨁ i, U i) ≃ₗ[K] V :=
  LinearEquiv.ofBijective (coeLinearMap U) h
end
-- QUOTE.

/- OMIT:

Subspace spanned by a set
^^^^^^^^^^^^^^^^^^^^^^^^^

OMIT. -/
/- TEXT:
集合で張られた部分空間
^^^^^^^^^^^^^^^^^^^^^^^^^

TEXT. -/
/- OMIT:
In addition to building subspaces out of existing subspaces, we can build them out
of any set ``s`` using ``Submodule.span K s`` which builds the smallest subspace
containing ``s``.
On paper it is common to use that this space is made of all linear combinations of elements of
``s``.
But it is often more efficient to use its universal property expressed by ``Submodule.span_le``,
and the whole theory of Galois connections.


OMIT. -/
/- TEXT:
既存の部分空間から部分空間を構築するだけでなく，集合 ``s`` を含む最小の部分空間を構築する ``Submodule.span K s`` を使って，任意の集合 ``s`` から部分空間を構築することもできます．紙の上では，この空間は ``s`` の要素のすべての線形結合で構成されることが一般的です．しかし，多くの場合 ``Submodule.span_le`` で表される普遍性とガロア接続の理論全体を使用する方が効率的です．
EXAMPLES: -/
-- QUOTE:
example {s : Set V} (E : Submodule K V) : Submodule.span K s ≤ E ↔ s ⊆ E :=
  Submodule.span_le

example : GaloisInsertion (Submodule.span K) ((↑) : Submodule K V → Set V) :=
  Submodule.gi K V
-- QUOTE.
/- OMIT:

When those are not enough, one can use the relevant induction principle
``Submodule.span_induction`` which ensures a property holds for every element of the
span of ``s`` as long as it holds on ``zero`` and elements of ``s`` and is stable under
sum and scalar multiplication. As usual with such lemmas, Lean sometimes needs help
to figure out the predicate we are interested in.

OMIT. -/
/- TEXT:
これらでは十分ではない場合，関連した帰納的原理 ``Submodule.span_induction`` を使うことができます．これは，ある性質が ``zero`` と ``s`` の要素で成り立ち，直和とスカラー倍で保たれる限り， ``s`` のスパンのすべての要素で成り立つことを保証するものです．このような補題の常として，Leanは関心のある述語を理解するために利用者の助けを必要とすることがあります．

TEXT. -/
/- OMIT:
As an exercise, let us reprove one implication of ``Submodule.mem_sup``.
Remember that you can use the `module` tactic to close goals that follow from
the axioms relating the various algebraic operations on ``V``.
OMIT. -/
/- TEXT:
演習として， ``Submodule.mem_sup`` の片方の含意を再証明してみましょう． ``V`` 上の様々な代数演算に関連する公理から従うゴールを閉じるために ``module`` というタクティクが使えることを覚えておいてください．
EXAMPLES: -/
-- QUOTE:

example {S T : Submodule K V} {x : V} (h : x ∈ S ⊔ T) :
    ∃ s ∈ S, ∃ t ∈ T, x = s + t  := by
  rw [← S.span_eq, ← T.span_eq, ← Submodule.span_union] at h
  apply Submodule.span_induction h (p := fun x ↦ ∃ s ∈ S, ∃ t ∈ T, x = s + t)
/- EXAMPLES:
  · sorry
  · sorry
  · sorry
  · sorry
SOLUTIONS: -/
  · rintro x (hx|hx)
    · use x, hx, 0, T.zero_mem
      module
    · use 0, S.zero_mem, x, hx
      module
  · use 0, S.zero_mem, 0, T.zero_mem
    module
  · rintro - - ⟨s, hs, t, ht, rfl⟩ ⟨s', hs', t', ht', rfl⟩
    use s + s', S.add_mem hs hs', t + t', T.add_mem ht ht'
    module
  · rintro a - ⟨s, hs, t, ht, rfl⟩
    use a • s, S.smul_mem a hs, a • t, T.smul_mem a ht
    module

-- QUOTE.
/- OMIT:

Pushing and pulling subspaces
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

OMIT. -/
/- TEXT:
部分空間の押し出しと引き戻し
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

TEXT. -/
/- OMIT:
As promised earlier, we now describe how to push and pull subspaces by linear maps.
As usual in Mathlib, the first operation is called ``map`` and the second one is called
``comap``.
OMIT. -/
/- TEXT:
以前の約束通り，線形写像による部分空間の押し出しと引き戻しの方法を説明しましょう．Mathlibの常として，1つ目の操作は ``map`` と呼ばれ，2つ目の操作は ``comap`` と呼ばれます．
EXAMPLES: -/
-- QUOTE:

section

variable {W : Type*} [AddCommGroup W] [Module K W] (φ : V →ₗ[K] W)

variable (E : Submodule K V) in
#check (Submodule.map φ E : Submodule K W)

variable (F : Submodule K W) in
#check (Submodule.comap φ F : Submodule K V)
-- QUOTE.

/- OMIT:
Note those live in the ``Submodule`` namespace so one can use dot notation and write
``E.map φ`` instead of ``Submodule.map φ E``, but this is pretty awkward to read (although some
Mathlib contributors use this spelling).

OMIT. -/
/- TEXT:
これらは ``Submodule`` 名前空間の中に存在するため， ``Submodule.map φ E`` の代わりにドット記法を使って ``E.map φ`` と書くこともできますが，これは大変読みにくいものになります（Mathlibのコントリビュータの中にはこの書き方を使う人もいます）．

TEXT. -/
/- OMIT:
In particular the range and kernel of a linear map are subspaces. Those special cases are important
enough to get declarations.
OMIT. -/
/- TEXT:
特に，線形写像の範囲と核は部分空間です．これらの特殊ケースはあえて宣言する必要があるほど重要です．
EXAMPLES: -/
-- QUOTE:
example : LinearMap.range φ = .map φ ⊤ := LinearMap.range_eq_map φ

example : LinearMap.ker φ = .comap φ ⊥ := Submodule.comap_bot φ -- or `rfl`
-- QUOTE.


/- OMIT:
Note that we cannot write ``φ.ker`` instead of ``LinearMap.ker φ`` because ``LinearMap.ker`` also
applies to classes of maps preserving more structure, hence it does not expect an argument
whose type starts with ``LinearMap``, hence dot notation doesn’t work here.
However we were able to use the other flavor of dot notation in the right-hand side. Because
Lean expects a term with type ``Submodule K V`` after elaborating the left-hand side, it interprets
``.comap`` as ``Submodule.comap``.

OMIT. -/
/- TEXT:
``LinearMap.ker φ`` の代わりに ``φ.ker`` と書けないことに注意してください．というのも ``LinearMap.ker`` はより多くの構造を保存する写像のクラスにも適用されるため，型が ``LinearMap`` で始まる引数を想定しておらず，そのためドット記法はここでは使えません．しかし，右辺ではドット記法の他の方法を使うことができます．Leanは左辺をエラボレートした後には ``Submodule K V`` という型を持つ項を期待するため， ``.comap`` を ``Submodule.comap`` と解釈します．

TEXT. -/
/- OMIT:
The following lemmas give the key relations between those submodule and the properties of ``φ``.
OMIT. -/
/- TEXT:
以下の補題は，これらの部分加群と ``φ`` の性質との間の重要な関係を与えます．
EXAMPLES: -/
-- QUOTE:

open Function LinearMap

example : Injective φ ↔ ker φ = ⊥ := ker_eq_bot.symm

example : Surjective φ ↔ range φ = ⊤ := range_eq_top.symm
-- QUOTE.
/- OMIT:
As an exercise, let us prove the Galois connection property for ``map`` and ``comap``.
One can use the following lemmas but this is not required since they are true by definition.
OMIT. -/
/- TEXT:
演習として， ``map`` と ``comap`` のガロア接続の性質を証明してみましょう．以下の補題を使うこともできますが，定義上真であるためこれは必須ではありません．
EXAMPLES: -/
-- QUOTE:

#check Submodule.mem_map_of_mem
#check Submodule.mem_map
#check Submodule.mem_comap

example (E : Submodule K V) (F : Submodule K W) :
    Submodule.map φ E ≤ F ↔ E ≤ Submodule.comap φ F := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  constructor
  · intro h x hx
    exact h ⟨x, hx, rfl⟩
  · rintro h - ⟨x, hx, rfl⟩
    exact h hx
-- QUOTE.

/- OMIT:
Quotient spaces
^^^^^^^^^^^^^^^

OMIT. -/
/- TEXT:
商空間
^^^^^^^^^^^^^^^

TEXT. -/
/- OMIT:
Quotient vector spaces use the general quotient notation (typed with ``\quot``, not the ordinary
``/``).
The projection onto a quotient space is ``Submodule.mkQ`` and the universal property is
``Submodule.liftQ``.
OMIT. -/
/- TEXT:
商ベクトル空間は一般的な商記法（通常の ``/`` ではなく ``\quot`` と打ち込みます）を使用します．商空間への射影は ``Submodule.mkQ`` で，普遍性は ``Submodule.liftQ`` です．
EXAMPLES: -/
-- QUOTE:

variable (E : Submodule K V)

example : Module K (V ⧸ E) := inferInstance

example : V →ₗ[K] V ⧸ E := E.mkQ

example : ker E.mkQ = E := E.ker_mkQ

example : range E.mkQ = ⊤ := E.range_mkQ

example (hφ : E ≤ ker φ) : V ⧸ E →ₗ[K] W := E.liftQ φ hφ

example (F : Submodule K W) (hφ : E ≤ .comap φ F) : V ⧸ E →ₗ[K] W ⧸ F := E.mapQ F φ hφ

noncomputable example : (V ⧸ LinearMap.ker φ) ≃ₗ[K] range φ := φ.quotKerEquivRange

-- QUOTE.
/- OMIT:
As an exercise, let us prove the correspondence theorem for subspaces of quotient spaces.
Mathlib knows a slightly more precise version as ``Submodule.comapMkQRelIso``.
OMIT. -/
/- TEXT:
演習問題として，商空間の部分空間の対応定理を証明しましょう．Mathlibはこの事実をもう少し正確なバージョンである ``Submodule.comapMkQRelIso`` として知っています．
EXAMPLES: -/
-- QUOTE:

open Submodule

#check Submodule.map_comap_eq
#check Submodule.comap_map_eq

example : Submodule K (V ⧸ E) ≃ { F : Submodule K V // E ≤ F } where
/- EXAMPLES:
  toFun := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry
SOLUTIONS: -/
  toFun F := ⟨comap E.mkQ F, by
    conv_lhs => rw [← E.ker_mkQ, ← comap_bot]
    gcongr
    apply bot_le⟩
  invFun P := map E.mkQ P
  left_inv P := by
    dsimp
    rw [Submodule.map_comap_eq, E.range_mkQ]
    exact top_inf_eq P
  right_inv := by
    intro P
    ext x
    dsimp only
    rw [Submodule.comap_map_eq, E.ker_mkQ, sup_of_le_left]
    exact P.2
-- QUOTE.
