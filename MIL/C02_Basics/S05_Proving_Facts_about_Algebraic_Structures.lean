-- BOTH:
import MIL.Common
import Mathlib.Topology.MetricSpace.Basic

/- OMIT:
Proving Facts about Algebraic Structures
----------------------------------------

OMIT. -/
/- TEXT:
.. _proving_facts_about_algebraic_structures:

代数構造についての事実の証明
----------------------------

.. index:: order relation, partial order

TEXT. -/
/- OMIT:
In :numref:`proving_identities_in_algebraic_structures`,
we saw that many common identities governing the real numbers hold
in more general classes of algebraic structures,
such as commutative rings.
We can use any axioms we want to describe an algebraic structure,
not just equations.
For example, a *partial order* consists of a set with a
binary relation that is reflexive and transitive,
like ``≤`` on the real numbers.
Lean knows about partial orders:
OMIT. -/
/- TEXT:
:numref:`proving_identities_in_algebraic_structures` では，実数上で成り立つ多くの一般的な恒等式が，可換環のようなより一般的な代数的構造のクラスでも成り立つことを確認しました．等式だけでなく，代数的構造を記述するために必要な公理はなんでも表現することができます．例えば *半順序* は実数上の ``≤`` のような，集合上の反射的で推移的な二項関係のことです．Leanはこの半順序を表現できます:
TEXT. -/
section
-- QUOTE:
variable {α : Type*} [PartialOrder α]
variable (x y z : α)

-- EXAMPLES:
#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
-- QUOTE.

/- OMIT:
Here we are adopting the Mathlib convention of using
letters like ``α``, ``β``, and ``γ``
(entered as ``\a``, ``\b``, and ``\g``)
for arbitrary types.
The library often uses letters like ``R`` and ``G``
for the carries of algebraic structures like rings and groups,
respectively,
but in general Greek letters are used for types,
especially when there is little or no structure
associated with them.

OMIT. -/
/- TEXT:
ここではMathlibの慣例に則り ``α`` や ``β`` ， ``γ`` （ ``\a`` ， ``\b`` ， ``\g`` と入力します）等の文字で任意の型を表すものとします．Mathlibでは環や群のような代数的構造の台集合を表す際にそれぞれ ``R`` や ``G`` をよく使いますが，一般的な型，特にその型に構造が入っていない場合にはギリシャ文字が使われます．

TEXT. -/
/- OMIT:
Associated to any partial order, ``≤``,
there is also a *strict partial order*, ``<``,
which acts somewhat like ``<`` on the real numbers.
Saying that ``x`` is less than ``y`` in this order
is equivalent to saying that it is less-than-or-equal to ``y``
and not equal to ``y``.
OMIT. -/
/- TEXT:
一般の半順序 ``≤`` に関連して，実数上における ``<`` のような働きをする *狭義半順序* ``<`` も存在します．この順序関係において ``x`` が ``y`` より小さいというのは ``y`` 以下でかつ ``y`` と等しくないということと同じです．
TEXT. -/
-- QUOTE:
#check x < y
#check (lt_irrefl x : ¬x < x)
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
  lt_iff_le_and_ne
-- QUOTE.

end

/- OMIT:
In this example, the symbol ``∧`` stands for "and,"
the symbol ``¬`` stands for "not," and
``x ≠ y`` abbreviates ``¬ (x = y)``.
In :numref:`Chapter %s <logic>`, you will learn how to use
these logical connectives to *prove* that ``<``
has the properties indicated.

OMIT. -/
/- TEXT:
この例では，記号 ``∧`` は「かつ」を表し， ``¬`` は「否定」を， ``x ≠ y`` は ``¬ (x = y)`` の省略形をそれぞれ表しています．:numref:`Chapter %s <logic>` では，これらの論理結合子を用いて ``<`` が上記で示された性質を持っていることを *証明* する方法を学びます．

.. index:: lattice

TEXT. -/
/- OMIT:
A *lattice* is a structure that extends a partial
order with operations ``⊓`` and ``⊔`` that are
analogous to ``min`` and ``max`` on the real numbers:
OMIT. -/
/- TEXT:
半順序集合の構造に加えて，実数上の ``min`` と ``max`` に対応するような演算子 ``⊓`` と ``⊔`` を持つ構造を *束* と呼びます:
TEXT. -/
-- BOTH:
section
-- QUOTE:
variable {α : Type*} [Lattice α]
variable (x y z : α)

-- EXAMPLES:
#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)
-- QUOTE.

/- OMIT:
The characterizations of ``⊓`` and ``⊔`` justify calling them
the *greatest lower bound* and *least upper bound*, respectively.
You can type them in VS code using ``\glb`` and ``\lub``.
The symbols are also often called then *infimum* and
the *supremum*,
and Mathlib refers to them as ``inf`` and ``sup`` in
theorem names.
To further complicate matters,
they are also often called *meet* and *join*.
Therefore, if you work with lattices,
you have to keep the following dictionary in mind:

OMIT. -/
/- TEXT:
``⊓`` と ``⊔`` はその特徴からそれぞれ *最大下界* と *最小上界* と呼ばれます．VSCodeでは ``\glb`` と ``\lub`` と打ち込むことで使用できます．またこれらの記号はしばしば *下限* と *上限* と呼ばれ，Mathlibの定理名では ``inf`` や ``sup`` と書かれます．さらにややこしいことに，これらは *交わり* と *結び* とも呼ばれます．そのため，束を扱う際には以下の辞書を頭に入れておく必要があります:

TEXT. -/
/- OMIT:
* ``⊓`` is the *greatest lower bound*, *infimum*, or *meet*.

OMIT. -/
/- TEXT:
* ``⊓`` は *最大下界* ， *下限* ， *交わり* のこと

TEXT. -/
/- OMIT:
* ``⊔`` is the *least upper bound*, *supremum*, or *join*.

OMIT. -/
/- TEXT:
* ``⊔`` は *最小上界* ， *上限* ， *結び* のこと

TEXT. -/
/- OMIT:
Some instances of lattices include:

OMIT. -/
/- TEXT:
束の例としては以下のようなものがあります:

TEXT. -/
/- OMIT:
* ``min`` and ``max`` on any total order, such as the integers or real numbers with ``≤``

OMIT. -/
/- TEXT:
* 整数や実数上の ``≤`` のような任意の全順序での ``min`` と ``max``．

TEXT. -/
/- OMIT:
* ``∩`` and ``∪`` on the collection of subsets of some domain, with the ordering ``⊆``

OMIT. -/
/- TEXT:
* 部分集合のあつまりにおける順序 ``⊆`` での ``∩`` と ``∪``．

TEXT. -/
/- OMIT:
* ``∧`` and ``∨`` on boolean truth values, with ordering ``x ≤ y`` if either ``x`` is false or ``y`` is true

OMIT. -/
/- TEXT:
* 真偽値について ``x ≤ y`` を ``x`` が偽か ``y`` が真である [#f2]_ という関係としたときの ``∧`` と ``∨``．

TEXT. -/
/- OMIT:
* ``gcd`` and ``lcm`` on the natural numbers (or positive natural numbers), with the divisibility ordering, ``∣``

OMIT. -/
/- TEXT:
* 自然数（やもしくは正の整数）についての整除関係 ``∣`` による半順序での ``gcd`` と ``lcm``．

TEXT. -/
/- OMIT:
* the collection of linear subspaces of a vector space,
  where the greatest lower bound is given by the intersection,
  the least upper bound is given by the sum of the two spaces,
  and the ordering is inclusion

OMIT. -/
/- TEXT:
* ベクトル空間の線形部分空間のあつまりも包含関係を半順序として束になります: 最大下界は共通部分で与えられ，最小上界は2つの空間の和で与えられます．

TEXT. -/
/- OMIT:
* the collection of topologies on a set (or, in Lean, a type),
  where the greatest lower bound of two topologies consists of
  the topology that is generated by their union,
  the least upper bound is their intersection,
  and the ordering is reverse inclusion

OMIT. -/
/- TEXT:
* ある集合（もしくはLeanではTypeのこと）上の位相のあつまりは，包含関係の逆を順序として束になります: 2つの位相の最大下界はその和から生成される位相で，最小上界はその2つの共通部分です．

TEXT. -/
/- OMIT:
You can check that, as with ``min`` / ``max`` and ``gcd`` / ``lcm``,
you can prove the commutativity and associativity of the infimum and supremum
using only their characterizing axioms,
together with ``le_refl`` and ``le_trans``.
OMIT. -/
/- TEXT:
``min`` / ``max`` と ``gcd`` / ``lcm`` と同様に，下限と上限の可換性と結合性をそれらの公理と ``le_refl`` と ``le_trans`` を用いて証明することができます．
TEXT. -/
-- QUOTE:
example : x ⊓ y = y ⊓ x := by
  sorry

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  sorry

example : x ⊔ y = y ⊔ x := by
  sorry

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example : x ⊓ y = y ⊓ x := by
  apply le_antisymm
  repeat'
    apply le_inf
    · apply inf_le_right
    apply inf_le_left

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  · apply le_inf
    · apply le_trans
      apply inf_le_left
      apply inf_le_left
    apply le_inf
    · apply le_trans
      apply inf_le_left
      apply inf_le_right
    apply inf_le_right
  apply le_inf
  · apply le_inf
    · apply inf_le_left
    apply le_trans
    apply inf_le_right
    apply inf_le_left
  apply le_trans
  apply inf_le_right
  apply inf_le_right

example : x ⊔ y = y ⊔ x := by
  apply le_antisymm
  repeat'
    apply sup_le
    · apply le_sup_right
    apply le_sup_left

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  apply le_antisymm
  · apply sup_le
    · apply sup_le
      apply le_sup_left
      · apply le_trans
        apply @le_sup_left _ _ y z
        apply le_sup_right
    apply le_trans
    apply @le_sup_right _ _ y z
    apply le_sup_right
  apply sup_le
  · apply le_trans
    apply @le_sup_left _ _ x y
    apply le_sup_left
  apply sup_le
  · apply le_trans
    apply @le_sup_right _ _ x y
    apply le_sup_left
  apply le_sup_right

/- OMIT:
You can find these theorems in the Mathlib as ``inf_comm``, ``inf_assoc``,
``sup_comm``, and ``sup_assoc``, respectively.

OMIT. -/
/- TEXT:
これらの定理はそれぞれ ``inf_comm`` ， ``inf_assoc`` ， ``sup_comm`` ， ``sup_assoc`` という名前でMathlib中に定義されています．

TEXT. -/
/- OMIT:
Another good exercise is to prove the *absorption laws*
using only those axioms:
OMIT. -/
/- TEXT:
これらの公理のみを用いて *吸収則* を証明するのもまたいい演習となるでしょう:
TEXT. -/
-- QUOTE:
theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  sorry

theorem absorb2 : x ⊔ x ⊓ y = x := by
  sorry
-- QUOTE.

-- SOLUTIONS:
theorem absorb1αα : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  · apply inf_le_left
  apply le_inf
  · apply le_refl
  apply le_sup_left

theorem absorb2αα : x ⊔ x ⊓ y = x := by
  apply le_antisymm
  · apply sup_le
    · apply le_refl
    apply inf_le_left
  apply le_sup_left

-- BOTH:
end

/- OMIT:
These can be found in Mathlib with the names ``inf_sup_self`` and ``sup_inf_self``.

OMIT. -/
/- TEXT:
これらの定理はMathlib中に ``inf_sup_self`` と ``sup_inf_self`` という名前で存在します．

TEXT. -/
/- OMIT:
A lattice that satisfies the additional identities
``x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z)`` and
``x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z)``
is called a *distributive lattice*. Lean knows about these too:
OMIT. -/
/- TEXT:
束の中でも追加で ``x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z)`` と ``x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z)`` を満たすものを *分配束* と呼びます．Leanはこれらも表現できます:
TEXT. -/
-- BOTH:
section
-- QUOTE:
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
-- QUOTE.
end

/- OMIT:
The left and right versions are easily shown to be
equivalent, given the commutativity of ``⊓`` and ``⊔``.
It is a good exercise to show that not every lattice
is distributive
by providing an explicit description of a
nondistributive lattice with finitely many elements.
It is also a good exercise to show that in any lattice,
either distributivity law implies the other:
OMIT. -/
/- TEXT:
``⊓`` と ``⊔`` の可換性を用いることで上記の左と右のバージョンが等価であることは簡単に示せます．ここで有限個の元を持つ分配的ではない束を明示的に記述することで，すべての束が分配的ではないことを示すのは良い演習になります．そして任意の束で ``⊓`` と ``⊔`` のどちらかの分配則がもう片方を包含することを示すのも良い演習になるでしょう:
TEXT. -/
-- BOTH:
section
-- QUOTE:
variable {α : Type*} [Lattice α]
variable (a b c : α)

-- EXAMPLES:
example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  sorry

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  rw [h, @inf_comm _ _ (a ⊔ b), absorb1, @inf_comm _ _ (a ⊔ b), h, ← sup_assoc, @inf_comm _ _ c a,
    absorb2, inf_comm]

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  rw [h, @sup_comm _ _ (a ⊓ b), absorb2, @sup_comm _ _ (a ⊓ b), h, ← inf_assoc, @sup_comm _ _ c a,
    absorb1, sup_comm]

-- BOTH:
end

/- OMIT:
It is possible to combine axiomatic structures into larger ones.
For example, a *strict ordered ring* consists of a commutative ring together
with a partial order on the carrier
satisfying additional axioms that say that the ring operations
are compatible with the order:
OMIT. -/
/- TEXT:
公理に基づく構造をより大きい構造に組み込むことも可能です．例えば *狭義順序環* は半順序が定義された可換環であり，かつその順序が環の和と積に対して整合的であるという追加の公理を満たすものです:
TEXT. -/
-- BOTH:
section
-- QUOTE:
variable {R : Type*} [StrictOrderedRing R]
variable (a b c : R)

-- EXAMPLES:
#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)
-- QUOTE.

/- OMIT:
:numref:`Chapter %s <logic>` will provide the means to derive the following from ``mul_pos``
and the definition of ``<``:
OMIT. -/
/- TEXT:
:numref:`Chapter %s <logic>` では以下の定理を ``mul_pos`` と ``<`` の定義から導く方法を学びます:
TEXT. -/
-- QUOTE:
#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)
-- QUOTE.

/- OMIT:
It is then an extended exercise to show that many common facts
used to reason about arithmetic and the ordering on the real
numbers hold generically for any ordered ring.
Here are a couple of examples you can try,
using only properties of rings, partial orders, and the facts
enumerated in the last two examples:
OMIT. -/
/- TEXT:
ここまでの内容からさらに発展問題として，実数上の算術と順序についての推論に使われるよくある事実の多くが任意の順序環で一般的に成り立つことが示せます．ここでは環と半順序の性質，そして最後の2つの例で使われている事実だけを用いていくつかの例を示しましょう:
TEXT. -/
-- QUOTE:
example (h : a ≤ b) : 0 ≤ b - a := by
  sorry

example (h: 0 ≤ b - a) : a ≤ b := by
  sorry

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  sorry
-- QUOTE.

-- SOLUTIONS:
theorem aux1 (h : a ≤ b) : 0 ≤ b - a := by
  rw [← sub_self a, sub_eq_add_neg, sub_eq_add_neg, add_comm, add_comm b]
  apply add_le_add_left h

theorem aux2 (h : 0 ≤ b - a) : a ≤ b := by
  rw [← add_zero a, ← sub_add_cancel b a, add_comm (b - a)]
  apply add_le_add_left h

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  have h1 : 0 ≤ (b - a) * c := mul_nonneg (aux1 _ _ h) h'
  rw [sub_mul] at h1
  exact aux2 _ _ h1

-- BOTH:
end

/- OMIT:
Finally, here is one last example.
A *metric space* consists of a set equipped with a notion of
distance, ``dist x y``,
mapping any pair of elements to a real number.
The distance function is assumed to satisfy the following axioms:
OMIT. -/
/- TEXT:
.. index:: metric space

最後にもう一つ例を挙げましょう． *距離空間* とは，集合とその集合上の距離と呼ばれる，任意の2つの要素 ``x, y`` から実数 ``dist x y`` を対応させる写像の組のことです．距離関数は以下の公理を満たすものとします:
TEXT. -/
-- BOTH:
section
-- QUOTE:
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

-- EXAMPLES:
#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)
-- QUOTE.

/- OMIT:
Having mastered this section,
you can show that it follows from these axioms that distances are
always nonnegative:
OMIT. -/
/- TEXT:
本節をマスターすれば，これらの公理から距離が常に非負であることを示すことができます:
TEXT. -/
-- QUOTE:
example (x y : X) : 0 ≤ dist x y := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (x y : X) : 0 ≤ dist x y :=by
  have : 0 ≤ dist x y + dist y x := by
    rw [← dist_self x]
    apply dist_triangle
  linarith [dist_comm x y]

-- BOTH:
end

/- OMIT:
We recommend making use of the theorem ``nonneg_of_mul_nonneg_left``.
As you may have guessed, this theorem is called ``dist_nonneg`` in Mathlib.
OMIT. -/
/- TEXT:
この証明を行うに当たって ``nonneg_of_mul_nonneg_left`` という定理を利用することをお勧めします．またお察しの通り，上記の定理 ``0 ≤ dist x y`` はMathlibでは ``dist_nonneg`` と呼ばれています．

.. [#f2] 訳注: つまり ``x → y`` のことです
TEXT. -/
