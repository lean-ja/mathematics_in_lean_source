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

代数的構造における等式の証明
-------------------------------

.. index:: ring (algebraic structure)

TEXT. -/
/- OMIT:
Mathematically, a ring consists of a collection of objects,
:math:`R`, operations :math:`+` :math:`\times`, and constants :math:`0`
and :math:`1`, and an operation :math:`x \mapsto -x` such that:

OMIT. -/
/- TEXT:
数学的に，環は対象の集まりである :math:`R` と演算子 :math:`+` :math:`\times`，定数 :math:`0`，:math:`1`，そして演算子 :math:`x \mapsto -x` の集まりであって，以下を満たすようなものです:

TEXT. -/
/- OMIT:
* :math:`R` with :math:`+` is an *abelian group*, with :math:`0`
  as the additive identity and negation as inverse.
* Multiplication is associative with identity :math:`1`,
  and multiplication distributes over addition.

OMIT. -/
/- TEXT:
* :math:`R` は :math:`+` に関して :math:`0` を加法の単位元，減算を逆元とする *アーベル群* ．
* 乗法に関して結合法則が成り立ち， :math:`1` が単位元になる．また乗法と加法に関して分配法則が成り立つ．

TEXT. -/
/- OMIT:
In Lean, the collection of objects is represented as a *type*, ``R``.
The ring axioms are as follows:
OMIT. -/
/- TEXT:
Leanでは環の対象の集まりは *型* ``R`` として表すことができます．環の公理は以下のようになります．

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
上記の1行目に出てきた角括弧については後ほど学びますが，今のところはこの宣言で型 ``R`` に対して環の構造が与えられることさえ理解していただければ十分です．これによりLean上で ``R`` の元について環の一般的な記法を使うことが可能になり，ライブラリ中の環についての定理も使えるようになります．

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
これらの定理の名前の中には見覚えがあるものもあるでしょう．それもそのはずで，これらはまさに前章で実数について示したものと同じだからです．Leanは自然数や整数のような具体的な数学的構造についての証明だけでなく，環のような公理的に特徴づけられた抽象的構造についての証明にも長けています．さらに，Leanは抽象的な構造または具体的な構造のどちらに対しても *一般的な推論(generic reasoning)* をサポートしており，適切なインスタンスを認識できます．そのため環についての定理を整数 ``ℤ`` や有理数 ``ℚ`` ，複素数 ``ℂ`` のような具体的な環に適用することができます．またさらに順序環や体などの環より特殊な抽象的構造の任意のインスタンスに適用することもできます．

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
しかし，実数のすべての重要な性質が任意の環で成り立つわけではありません．例えば実数の乗算は可換ですが，これは一般の環では成り立ちません．線形代数の講義を受けたことがある人ならご存じだと思いますが，実数の :math:`n` × :math:`n` 行列全体は環をなし，この環では通常可換性が成り立ちません．もし ``R`` を *可換* 環であると宣言すれば，実際に ``ℝ`` を ``R`` に置き換えても，前節の定理はすべて成り立ちます．
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
他のすべての証明が変更なしで通ることを確認するのは読者にお任せします．``by ring`` や ``by linarith`` や ``by sorry`` のように証明が短い場合，証明は ``by`` と同じ行に書くのが一般的です（また文法的にも問題ありません）．簡潔さと読みやすさのバランスを取ることが，証明のスタイルを整えるコツです．

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
この節のゴールは，前節で身につけたスキルを強化し，環についての公理的推論に応用することです．上に挙げた公理から始め，それを使って他の事実を導きます．本書で証明する事実のほとんどは既にMathlibにあります．Mathlibの内容と命名規則を学ぶのに役立つように，本書で証明するものにも同じ名前を付けます．

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
Leanは一般的なプログラミング言語で使われるものと同様の *名前空間* によるコードの組織化のメカニズムを提供します．例えば定義や定理 ``foo`` が名前空間 ``bar`` に導入されると，その完全な名前は ``bar.foo`` となります．コマンド ``open bar`` で名前空間を *開く* ことができ，より短い名前 ``foo`` を使えるようになります．名前の衝突によるエラーを避けるために，次の例ではライブラリの定理を ``MyRing`` という新しい名前空間に置きます．

TEXT. -/
/- OMIT:
The next example shows that we do not need ``add_zero`` or ``add_right_neg``
as ring axioms, because they follow from the other axioms.
OMIT. -/
/- TEXT:
次の例は，``add_zero`` や ``add_right_neg`` が他の公理から従うことから，環の公理として必要ないことを示しています．
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
このように名前空間を分けることの正味の効果は，ライブラリにある定理を一時的に再定義できることです．その後はライブラリにあるバージョンを使い続けることができます．しかし，ごまかしは禁物です！この後の練習問題では，この節で前もって証明する環に関する一般的な事実だけを使うように注意してください．

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
(注意深い読者なら，``(R : Type*)`` の丸括弧を ``{R : Type*}`` の中括弧に変更したことに気づかれたかもしれません．これは ``R`` が *暗黙の引数* であることを宣言しています．これが何を意味するかは後ほど説明しますが，ひとまずは気にしないでください)

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
/- TEXT:
類似した以下の定理を証明してください:
TEXT. -/
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
/- TEXT:
これらを以下の証明に用いてください:
TEXT. -/
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

OMIT. -/
/- TEXT:
この2つの証明はそれぞれ3回の書き換えにまとめることが可能です．

.. index:: implicit argument

TEXT. -/
/- OMIT:
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

OMIT. -/
/- TEXT:
ここで中括弧の使い方について説明しましょう．例えば証明のコンテキストに ``a`` ， ``b`` ， ``c`` ，仮定 ``h : a + b = a + c`` があり，結論 ``b = c`` を導きたいとしましょう．Leanでは，定理を ``a`` や ``b`` 等の対象に適用するのと同じように仮定や事実に適用することができるため，``add_left_cancel a b c h`` が ``b = c`` の証明になると思われるかもしれません．しかし， ``a`` ， ``b`` ， ``c`` を明示的に書くことは引数の与え過ぎであることに注意してください．なぜなら，仮定 ``h`` を見るだけで，どういう対象を想定しているか判断できるからです．今回の場合，数文字書くかどうか程度ですので大した負担にはなりませんが，``add_left_cancel`` をさらに複雑な式に適用していく場合には面倒になることでしょう．このような場合のためにLeanでは引数を *暗黙* のものとしてマークすることができます．つまり，その引数は省略され，それを用いている後続の引数や仮定などから推測されるということです．これがまさに ``{a b c : R}`` で中括弧にしている理由です．よって，上記の定理の内容から考えると正しい式は ``add_left_cancel h`` とシンプルなものとなります．

TEXT. -/
/- OMIT:
To illustrate, let us show that ``a * 0 = 0``
follows from the ring axioms.
OMIT. -/
/- TEXT:
このことを説明するために，環の公理から ``a * 0 = 0`` が成り立つことを示しましょう．
TEXT. -/
-- QUOTE:
theorem mul_zero (a : R) : a * 0 = 0 := by
  have h : a * 0 + a * 0 = a * 0 + 0 := by
    rw [← mul_add, add_zero, add_zero]
  rw [add_left_cancel h]
-- QUOTE.

/- OMIT:
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

OMIT. -/
/- TEXT:
.. index:: have, tactics ; have

ここでは新しいワザを使っています！ステップごとにinfoviewを見ていけば，この証明で何が起こっているかわかるでしょう．ここで ``have`` タクティクは元のゴールと同じコンテキストに新しいゴール ``a * 0 + a * 0 = a * 0 + 0`` を導入しています．この次の行でインデントが1段深くなっていますが，そこにタクティクのブロックを続けると，その内容が新しいゴールの証明と解釈されます．このインデントにより，証明のモジュール化が促進されます．つまり，インデントされた部分が ``have`` で導入されたゴールの証明になります．インデントを抜けると，新しい仮定 ``h`` が追加され，自由に利用できる状態で元のゴールの証明が再開します．この時点で，ゴールはちょうど ``add_left_cancel h`` が使える状態となります．

.. index:: apply, tactics ; apply, exact, tactics ; exact

TEXT. -/
/- OMIT:
We could equally well have closed the proof with
``apply add_left_cancel h`` or ``exact add_left_cancel h``.
The ``exact`` tactic takes as argument a proof term which completely proves the
current goal, without creating any new goal. The ``apply`` tactic is a variant
whose argument is not necessarily a complete proof. The missing pieces are either
inferred automatically by Lean or become new goals to prove.
While the ``exact`` tactic is technically redundant since it is strictly less powerful
than ``apply``, it makes proof scripts slightly clearer to
human readers and easier to maintain when the library evolves.

OMIT. -/
/- TEXT:
上記の証明の終わりに ``rw`` を用いていますが，代わりに ``apply add_left_cancel h`` もしくは ``exact add_left_cancel h`` で証明を終えることもできます．``exact`` タクティクは引数として与えられた証明項をそのまま使って現在のゴールを証明しようとします．新たなゴールを生成することはありません．これに対し ``apply`` タクティクの引数は完全な証明である必要はありません．証明の足りない部分はLeanにより自動的に推測されるか，新たなゴールとなります． ``exact`` は ``apply`` よりも真に弱いので， ``exact`` を使うのは技術的には冗長です． しかし ``exact`` を使うことで証明のコードが少し読みやすくなりますし，ライブラリが変更されたときの保守も容易になります．

TEXT. -/
/- OMIT:
Remember that multiplication is not assumed to be commutative,
so the following theorem also requires some work.
OMIT. -/
/- TEXT:
ところで乗算は可換であるとは仮定されていないことを思い出してください．このため次の定理は公理から直接導かれず，証明にもひと工夫必要になります．
TEXT. -/
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
/- TEXT:
ここまでくれば，次の演習問題でも各 ``sorry`` を証明に置き換えることができるでしょう．この節で示した環に関する事実だけを用います．
TEXT. -/
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

OMIT. -/
/- TEXT:
ここで3つ目の定理においては単に ``0`` とするのではなく， ``(-0 : R)`` と注釈をつける必要があります．なぜなら ``R`` を指定しなければLeanはどの環での ``0`` を念頭においているかを推測することができず，結果デフォルトの挙動として ``0`` を自然数として解釈してしまうからです．

TEXT. -/
/- OMIT:
In Lean, subtraction in a ring is provably equal to
addition of the additive inverse.
OMIT. -/
/- TEXT:
環においての引き算は加法の逆元との足し算と等しいことがLeanで証明できます．
TEXT. -/
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
/- TEXT:
実数においてはまさにそのように *定義されています* ．
TEXT. -/
-- QUOTE:
example (a b : ℝ) : a - b = a + -b :=
  rfl

example (a b : ℝ) : a - b = a + -b := by
  rfl
-- QUOTE.

/- OMIT:
The proof term  ``rfl`` is short for "reflexivity".
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
/- TEXT:
.. index:: rfl, reflexivity, tactics ; refl and reflexivity, definitional equality

証明項 ``rfl`` は「反射性（reflexivity）」の略です．これを ``a - b = a + -b`` の証明として提示すると，Leanはその定義を展開し，両辺が同じであることを認識します．``rfl`` タクティクもこれと同様です．これは *definitional equality(定義からの等価性)* として知られているLeanの基礎にある論理の一例です．つまり ``sub_eq_add_neg`` を用いて等式 ``a - b = a + -b`` を示せるだけでなく，実数を扱うときなど文脈によってはこの等式の両辺を同じ意味で使うことができます．ここまでの情報で，例えば前節の定理 ``self_sub`` はもう証明できます:

TEXT. -/
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

OMIT. -/
/- TEXT:
``rw`` を用いて証明してみましょう．また ``R`` を任意の環ではなく実数とすれば， ``apply`` または ``exact`` を使っても証明することができます．

TEXT. -/
/- OMIT:
Lean knows that ``1 + 1 = 2`` holds in any ring.
With a bit of effort,
you can use that to prove the theorem ``two_mul`` from
the last section:
OMIT. -/
/- TEXT:
Leanはどんな環でも ``1 + 1 = 2`` が成り立つことを知っています．そしてさらに少し努力すれば，この事実を使って前節の定理 ``two_mul`` を証明することができます:
TEXT. -/
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
/- TEXT:
.. index:: group (algebraic structure)

本節を締めくくるにあたって，上で証明した加算と減算に関する事実の中には，環の公理のすべてを必要とするわけではないものや，加算の可換性さえも必要としないものがあることについて見ていきましょう．この環よりも弱い概念である *群* は次のように公理化できます:
TEXT. -/
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
/- TEXT:
群の演算が可換な場合は加法的表記を使い，そうでない場合は乗法的表記を使うのが一般的です．そのためLeanは加法バージョンの群と同様に乗法バージョンの群も定義しています．（またこれらのアーベリアンなバリエーションである ``AddCommGroup`` と ``CommGroup`` についても定義しています．）
TEXT. -/
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
/- TEXT:
もし腕に自信があるならこれらの公理だけを用いて群に関する以下の事実を証明してみましょう．その過程でいくつか補助的な補題を証明する必要があります．また本節でこれまで行ってきた証明がヒントになります．
TEXT. -/
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
/- TEXT:
.. index:: group (tactic), tactics ; group, tactics ; noncomm_ring, tactics ; abel

これらの補題を明示的に呼び出すのは面倒であるため，Mathlibは上記の補題のほとんどすべての用途をカバーするような `ring` と同じようなタクティクを提供しています:`group` は非可換乗法群， `abel` は加法群，そして `noncomm_ring` は非可換環です．代数的な構造が `Ring` や `CommRing` と呼ばれている一方で，タクティクが `noncomm_ring` と `ring` と名付けられているのは奇妙に感じられるかもしれません．これには歴史的な理由もありますが，可換環を扱う場合のほうが多いため，それに合わせて便宜上短い名前を可換環につけているという理由もあります．
TEXT. -/
