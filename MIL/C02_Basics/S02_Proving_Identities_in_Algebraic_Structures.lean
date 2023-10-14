-- BOTH:
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Real.Basic
import MIL.Common

/- TEXT:
.. _proving_identities_in_algebraic_structures:
TEXT. -/
/- OMIT:

Proving Identities in Algebraic Structures
------------------------------------------
OMIT. -/
/- TEXT:
代数的構造における恒等性の証明
----------------------------
.. index:: ring (algebraic structure)

TEXT. -/
/- OMIT:
Mathematically, a ring consists of a collection of objects,
:math:`R`, operations :math:`+` :math:`\times`, and constants :math:`0`
and :math:`1`, and an operation :math:`x \mapsto -x` such that:

OMIT. -/
/- TEXT:
数学的に，環は対象の集まりである:math:`R`と演算子:math:`+` :math:`\times`，定数:math:`0`，:math:`1`，
そして演算子:math:`x \mapsto -x`から構成され，以下を満たします:

TEXT. -/
/- OMIT:
* :math:`R` with :math:`+` is an *abelian group*, with :math:`0`
  as the additive identity and negation as inverse.
* Multiplication is associative with identity :math:`1`,
  and multiplication distributes over addition.

OMIT. -/
/- TEXT:
* :math:`R`と:math:`+`は*アーベル群*で，:math:`0`は加法の単位元，減算が逆元になります．
* 乗法は単位元:math:`1`について結合的で，また乗法は加法に対して分配されます．

TEXT. -/
/- OMIT:
In Lean, the collection of objects is represented as a *type*, ``R``.
The ring axioms are as follows:
OMIT. -/
/- TEXT:
Leanでは対象のあつまりは*型*として表現され，環は``R``と表記します．
環の公理は以下のようになります．

TEXT. -/
section
-- QUOTE:
variable (R : Type*) [Ring R]

#check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))
#check (add_comm : ∀ a b : R, a + b = b + a)
#check (zero_add : ∀ a : R, 0 + a = a)
#check (add_left_neg : ∀ a : R, -a + a = 0)
#check (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))
#check (mul_one : ∀ a : R, a * 1 = a)
#check (one_mul : ∀ a : R, 1 * a = a)
#check (mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)
#check (add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c)
-- QUOTE.

end

/- OMIT:
You will learn more about the square brackets in the first line later,
but for the time being,
suffice it to say that the declaration gives us a type, ``R``,
and a ring structure on ``R``.
Lean then allows us to use generic ring notation with elements of ``R``,
and to make use of a library of theorems about rings.

OMIT. -/
/- TEXT:
上記の1行目に出てきた角括弧については後ほど学びますが，
今のところはこの書き方で型``R``に対して環の構造が与えられるようにする定義だと思ってもらえれば十分です．
これによりLeanは``R``の元について環の一般的な記法を使うことが出来るようにし，ライブラリ中の環についての定理も使えるようになります．

TEXT. -/
/- OMIT:
The names of some of the theorems should look familiar:
they are exactly the ones we used to calculate with the real numbers
in the last section.
Lean is good not only for proving things about concrete mathematical
structures like the natural numbers and the integers,
but also for proving things about abstract structures,
characterized axiomatically, like rings.
Moreover, Lean supports *generic reasoning* about
both abstract and concrete structures,
and can be trained to recognized appropriate instances.
So any theorem about rings can be applied to concrete rings
like the integers, ``ℤ``, the rational numbers,  ``ℚ``,
and the complex numbers ``ℂ``.
It can also be applied to any instance of an abstract
structure that extends rings,
such as any ordered ring or any field.

OMIT. -/
/- TEXT:
これらの定理の中にはなじみ深い名前のものもあるでしょう，それもそのはずで，これらはまさに前章で実数について計算したものと同じだからです．
Leanは実際の自然数や整数のような数学構造について証明をするだけでなく，環のような公理的に特徴づけられた抽象構造の証明にも長けています．
さらに，Leanは抽象と具象の構造どちらに対しても*一般的な推論*のサポートを備えており，適切なインスタンスを認識できるように調節できます．
そのため環についての定理を整数``Z``や有理数``Q``，複素数``C``のような具体的な環に適用することができます．
またさらに任意の順序環や体などの拡張された環構造のインスタンスに適用することもできます．

.. index:: commutative ring

TEXT. -/
/- OMIT:
Not all important properties of the real numbers hold in an
arbitrary ring, however.
For example, multiplication on the real numbers
is commutative,
but that does not hold in general.
If you have taken a course in linear algebra,
you will recognize that, for every :math:`n`,
the :math:`n` by :math:`n` matrices of real numbers
form a ring in which commutativity usually fails. If we declare ``R`` to be a
*commutative* ring, in fact, all the theorems
in the last section continue to hold when we replace
``ℝ`` by ``R``.
OMIT. -/
/- TEXT:
しかし，実数の重要な性質がすべて任意の環で成り立つわけではありません．
例えば実数の乗算は可換ですが，これは一般の環では成り立ちません．
線形代数の講義を受けたことがある人なら，実数の :math:`n` 行列が :math:`n` × :math:`n` の環を形成し，
その環では通常可換性が成り立たないことがわかります．
もし ``R`` を*可換*環であると宣言すれば，実際に ``ℝ`` を ``R`` に置き換えても，前節の定理はすべて成り立ち続ける．
TEXT. -/
section
-- QUOTE:
variable (R : Type*) [CommRing R]
variable (a b c d : R)

example : c * b * a = b * (a * c) := by ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring
-- QUOTE.

end

/- OMIT:
We leave it to you to check that all the other proofs go through unchanged.
Notice that when a proof is short, like ``by ring`` or ``by linarith``
or ``by sorry``,
it is common (and permissible) to put it on the same line as
the ``by``.
Good proof-writing style should strike a balance between concision and readability.

OMIT. -/
/- TEXT:
他のすべての証明が変更されずに通過することを確認するのは読者のために残しましょう．
``by ring`` や ``by linarith`` や ``by sorry`` のように証明が短い場合，証明は ``by`` と同じ行に書くのが一般的です（また許可されています）．
良い証明文の書き方は，簡潔さと読みやすさのバランスを取ることです．

TEXT. -/
/- OMIT:
The goal of this section is to strengthen the skills
you have developed in the last section
and apply them to reasoning axiomatically about rings.
We will start with the axioms listed above,
and use them to derive other facts.
Most of the facts we prove are already in Mathlib.
We will give the versions we prove the same names
to help you learn the contents of the library
as well as the naming conventions.

OMIT. -/
/- TEXT:
このセクションの目的は，前回のセクションで身につけたスキルを強化し，環についての公理的推論に応用することです．
上に挙げた公理から始め，それを使って他の事実を導きます．
本書で証明する事実のほとんどはすでにMathlibにあります．
Mathlibの内容と命名規則を学ぶのに役立つように，証明するものに同じ名前を付けます．

.. index:: namespace, open, command ; open

TEXT. -/
/- OMIT:
Lean provides an organizational mechanism similar
to those used in programming languages:
when a definition or theorem ``foo`` is introduced in a *namespace*
``bar``, its full name is ``bar.foo``.
The command ``open bar`` later *opens* the namespace,
which allows us to use the shorter name ``foo``.
To avoid errors due to name clashes,
in the next example we put our versions of the library
theorems in a new namespace called ``MyRing.``

OMIT. -/
/- TEXT:
Leanは一般的なプログラミング言語で使われるものと似たようなコードの組織化のメカニズムを提供します．
定義や定理 ``foo`` が *名前空間* ``bar`` に導入されると，その完全な名前は ``bar.foo`` となります．
コマンド ``open bar`` で名前空間を *開く*ことで，より短い名前 ``foo`` を使うことができます．
名前の衝突によるエラーを避けるために，次の例ではライブラリの定理を ``MyRing.`` という新しい名前空間に置きます．

TEXT. -/
/- OMIT:
The next example shows that we do not need ``add_zero`` or ``add_right_neg``
as ring axioms, because they follow from the other axioms.
OMIT. -/
/- TEXT:
次の例は，``add_zero`` や ``add_right_neg`` が他の公理に従うことから，環の公理として必要ないことを示しています．
TEXT. -/
-- QUOTE:
namespace MyRing
variable {R : Type*} [Ring R]

theorem add_zero (a : R) : a + 0 = a := by rw [add_comm, zero_add]

theorem add_right_neg (a : R) : a + -a = 0 := by rw [add_comm, add_left_neg]

#check MyRing.add_zero
#check add_zero

end MyRing
-- QUOTE.

/- OMIT:
The net effect is that we can temporarily reprove a theorem in the library,
and then go on using the library version after that.
But don't cheat!
In the exercises that follow, take care to use only the
general facts about rings that we have proved earlier in this section.

OMIT. -/
/- TEXT:
このように名前空間を分けることの正味の効果は，ライブラリにある定理を一時的に再現し，その後はライブラリのバージョンを使い続けることができるということです．
しかし，ごまかしは禁物です！
この後の練習問題では，このセクションで先に証明した環に関する一般的な事実だけを使うように注意しましょう．

TEXT. -/
/- OMIT:
(If you are paying careful attention, you may have noticed that we
changed the round brackets in ``(R : Type*)`` for
curly brackets in ``{R : Type*}``.
This declares ``R`` to be an *implicit argument*.
We will explain what this means in a moment,
but don't worry about it in the meanwhile.)

Here is a useful theorem:
OMIT. -/
/- TEXT:
(注意深く見ていれば，``(R : Type*)`` の丸括弧を ``{R : Type*}`` の中括弧に変更したことに気づいたかもしれません．
これは ``R`` が *暗黙の引数* であることを宣言しています．
これが何を意味するかは後ほど説明しますが，ひとまずは気にしないでください)

以下に便利な定理を示します．
TEXT. -/
-- BOTH:
namespace MyRing
variable {R : Type*} [Ring R]

-- EXAMPLES:
-- QUOTE:
theorem neg_add_cancel_left (a b : R) : -a + (a + b) = b := by
  rw [← add_assoc, add_left_neg, zero_add]
-- QUOTE.

/- OMIT:
Prove the companion version:
OMIT. -/
-- Prove these:
-- QUOTE:
theorem add_neg_cancel_right (a b : R) : a + b + -b = a := by
  sorry
-- QUOTE.

-- SOLUTIONS:
theorem add_neg_cancel_rightαα (a b : R) : a + b + -b = a := by
  rw [add_assoc, add_right_neg, add_zero]

/- OMIT:
Use these to prove the following:
OMIT. -/
-- QUOTE:
theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  sorry

theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c := by
  sorry
-- QUOTE.

-- SOLUTIONS:
theorem add_left_cancelαα {a b c : R} (h : a + b = a + c) : b = c := by
  rw [← neg_add_cancel_left a b, h, neg_add_cancel_left]

theorem add_right_cancelαα {a b c : R} (h : a + b = c + b) : a = c := by
  rw [← add_neg_cancel_right a b, h, add_neg_cancel_right]

/- OMIT:
With enough planning, you can do each of them with three rewrites.

.. index:: implicit argument

We will now explain the use of the curly braces.
Imagine you are in a situation where you have ``a``, ``b``, and ``c``
in your context,
as well as a hypothesis ``h : a + b = a + c``,
and you would like to draw the conclusion ``b = c``.
In Lean, you can apply a theorem to hypotheses and facts just
the same way that you can apply them to objects,
so you might think that ``add_left_cancel a b c h`` is a
proof of the fact ``b = c``.
But notice that explicitly writing ``a``, ``b``, and ``c``
is redundant, because the hypothesis ``h`` makes it clear that
those are the objects we have in mind.
In this case, typing a few extra characters is not onerous,
but if we wanted to apply ``add_left_cancel`` to more complicated expressions,
writing them would be tedious.
In cases like these,
Lean allows us to mark arguments as *implicit*,
meaning that they are supposed to be left out and inferred by other means,
such as later arguments and hypotheses.
The curly brackets in ``{a b c : R}`` do exactly that.
So, given the statement of the theorem above,
the correct expression is simply ``add_left_cancel h``.

To illustrate, let us show that ``a * 0 = 0``
follows from the ring axioms.
OMIT. -/
-- QUOTE:
theorem mul_zero (a : R) : a * 0 = 0 := by
  have h : a * 0 + a * 0 = a * 0 + 0 := by
    rw [← mul_add, add_zero, add_zero]
  rw [add_left_cancel h]
-- QUOTE.

/- OMIT:
.. index:: have, tactics ; have

We have used a new trick!
If you step through the proof,
you can see what is going on.
The ``have`` tactic introduces a new goal,
``a * 0 + a * 0 = a * 0 + 0``,
with the same context as the original goal.
The fact that the next line is indented indicates that Lean
is expecting a block of tactics that serves to prove this
new goal.
The indentation therefore promotes a modular style of proof:
the indented subproof establishes the goal
that was introduced by the ``have``.
After that, we are back to proving the original goal,
except a new hypothesis ``h`` has been added:
having proved it, we are now free to use it.
At this point, the goal is exactly the result of ``add_left_cancel h``.

.. index:: apply, tactics ; apply, exact, tactics ; exact

We could equally well have closed the proof with
``apply add_left_cancel h`` or ``exact add_left_cancel h``.
The ``exact`` tactic takes as argument a proof term which completely proves the
current goal, without creating any new goal. The ``apply`` tactic is a variant
whose argument is not necessarily a complete proof. The missing pieces are either
inferred automatically by Lean or become new goals to prove.
While the ``exact`` tactic is technically redundant since it is strictly less powerful
than ``apply``, it makes proof scripts slightly clearer to
human readers and easier to maintain when the library evolves.

Remember that multiplication is not assumed to be commutative,
so the following theorem also requires some work.
OMIT. -/
-- QUOTE:
theorem zero_mul (a : R) : 0 * a = 0 := by
  sorry
-- QUOTE.

-- SOLUTIONS:
theorem zero_mulαα (a : R) : 0 * a = 0 := by
  have h : 0 * a + 0 * a = 0 * a + 0 := by rw [← add_mul, add_zero, add_zero]
  rw [add_left_cancel h]

/- OMIT:
By now, you should also be able replace each ``sorry`` in the next
exercise with a proof,
still using only facts about rings that we have
established in this section.
OMIT. -/
-- QUOTE:
theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
  sorry

theorem eq_neg_of_add_eq_zero {a b : R} (h : a + b = 0) : a = -b := by
  sorry

theorem neg_zero : (-0 : R) = 0 := by
  apply neg_eq_of_add_eq_zero
  rw [add_zero]

theorem neg_neg (a : R) : - -a = a := by
  sorry
-- QUOTE.

-- SOLUTIONS:
theorem neg_eq_of_add_eq_zeroαα {a b : R} (h : a + b = 0) : -a = b := by
  rw [← neg_add_cancel_left a b, h, add_zero]

theorem eq_neg_of_add_eq_zeroαα {a b : R} (h : a + b = 0) : a = -b := by
  symm
  apply neg_eq_of_add_eq_zero
  rw [add_comm, h]

theorem neg_zeroαα : (-0 : R) = 0 := by
  apply neg_eq_of_add_eq_zero
  rw [add_zero]

theorem neg_negαα (a : R) : - -a = a := by
  apply neg_eq_of_add_eq_zero
  rw [add_left_neg]

-- BOTH:
end MyRing

/- OMIT:
We had to use the annotation ``(-0 : R)`` instead of ``0`` in the third theorem
because without specifying ``R``
it is impossible for Lean to infer which ``0`` we have in mind,
and by default it would be interpreted as a natural number.

In Lean, subtraction in a ring is provably equal to
addition of the additive inverse.
OMIT. -/
-- Examples.
section
variable {R : Type*} [Ring R]

-- QUOTE:
example (a b : R) : a - b = a + -b :=
  sub_eq_add_neg a b
-- QUOTE.

end

/- OMIT:
On the real numbers, it is *defined* that way:
OMIT. -/
-- QUOTE:
example (a b : ℝ) : a - b = a + -b :=
  rfl

example (a b : ℝ) : a - b = a + -b := by
  rfl
-- QUOTE.

/- OMIT:
.. index:: rfl, reflexivity, tactics ; refl and reflexivity, definitional equality

The proof term ``rfl`` is short for "reflexivity".
Presenting it as a proof of ``a - b = a + -b`` forces Lean
to unfold the definition and recognize both sides as being the same.
The ``rfl`` tactic does the same.
This is an instance of what is known as a *definitional equality*
in Lean's underlying logic.
This means that not only can one rewrite with ``sub_eq_add_neg``
to replace ``a - b = a + -b``,
but in some contexts, when dealing with the real numbers,
you can use the two sides of the equation interchangeably.
For example, you now have enough information to prove the theorem
``self_sub`` from the last section:
OMIT. -/
-- BOTH:
namespace MyRing
variable {R : Type*} [Ring R]

-- EXAMPLES:
-- QUOTE:
theorem self_sub (a : R) : a - a = 0 := by
  sorry
-- QUOTE.

-- SOLUTIONS:
theorem self_subαα (a : R) : a - a = 0 := by
  rw [sub_eq_add_neg, add_right_neg]

/- OMIT:
Show that you can prove this using ``rw``,
but if you replace the arbitrary ring ``R`` by
the real numbers, you can also prove it
using either ``apply`` or ``exact``.

Lean knows that ``1 + 1 = 2`` holds in any ring.
With a bit of effort,
you can use that to prove the theorem ``two_mul`` from
the last section:
OMIT. -/
-- QUOTE:
-- BOTH:
theorem one_add_one_eq_two : 1 + 1 = (2 : R) := by
  norm_num

-- EXAMPLES:
theorem two_mul (a : R) : 2 * a = a + a := by
  sorry
-- QUOTE.

-- SOLUTIONS:
theorem two_mulαα (a : R) : 2 * a = a + a := by
  rw [← one_add_one_eq_two, add_mul, one_mul]

-- BOTH:
end MyRing

/- OMIT:
.. index:: group (algebraic structure)

We close this section by noting that some of the facts about
addition and negation that we established above do not
need the full strength of the ring axioms, or even
commutativity of addition. The weaker notion of a *group*
can be axiomatized as follows:
OMIT. -/
section
-- QUOTE:
variable (A : Type*) [AddGroup A]

#check (add_assoc : ∀ a b c : A, a + b + c = a + (b + c))
#check (zero_add : ∀ a : A, 0 + a = a)
#check (add_left_neg : ∀ a : A, -a + a = 0)
-- QUOTE.

end

/- OMIT:
It is conventional to use additive notation when
the group operation is commutative,
and multiplicative notation otherwise.
So Lean defines a multiplicative version as well as the
additive version (and also their abelian variants,
``AddCommGroup`` and ``CommGroup``).
OMIT. -/
-- BOTH:
section
-- QUOTE:
variable {G : Type*} [Group G]

-- EXAMPLES:
#check (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
#check (one_mul : ∀ a : G, 1 * a = a)
#check (mul_left_inv : ∀ a : G, a⁻¹ * a = 1)
-- QUOTE.

/- OMIT:
If you are feeling cocky, try proving the following facts about
groups, using only these axioms.
You will need to prove a number of helper lemmas along the way.
The proofs we have carried out in this section provide some hints.
OMIT. -/
-- BOTH:
namespace MyGroup

-- EXAMPLES:
-- QUOTE:
theorem mul_right_inv (a : G) : a * a⁻¹ = 1 := by
  sorry

theorem mul_one (a : G) : a * 1 = a := by
  sorry

theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  sorry
-- QUOTE.

-- SOLUTIONS:
theorem mul_right_invαα (a : G) : a * a⁻¹ = 1 := by
  have h : (a * a⁻¹)⁻¹ * (a * a⁻¹ * (a * a⁻¹)) = 1 := by
    rw [mul_assoc, ← mul_assoc a⁻¹ a, mul_left_inv, one_mul, mul_left_inv]
  rw [← h, ← mul_assoc, mul_left_inv, one_mul]

theorem mul_oneαα (a : G) : a * 1 = a := by
  rw [← mul_left_inv a, ← mul_assoc, mul_right_inv, one_mul]

theorem mul_inv_revαα (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  rw [← one_mul (b⁻¹ * a⁻¹), ← mul_left_inv (a * b), mul_assoc, mul_assoc, ← mul_assoc b b⁻¹,
    mul_right_inv, one_mul, mul_right_inv, mul_one]

-- BOTH:
end MyGroup

end

/- OMIT:
.. index:: group (tactic), tactics ; group, tactics ; noncomm_ring, tactics ; abel

Explicitly invoking those lemmas is tedious, so Mathlib provides
tactics similar to `ring` in order to cover most uses: `group`
is for non-commutative multiplicative groups, `abel` for abelian
additive groups, and `noncomm_ring` for non-commutative rings.
It may seem odd that the algebraic structures are called
`Ring` and `CommRing` while the tactics are named
`noncomm_ring` and `ring`. This is partly for historical reasons,
but also for the convenience of using a shorter name for the
tactic that deals with commutative rings, since it is used more often.
OMIT. -/
