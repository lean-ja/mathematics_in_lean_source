-- BOTH:
import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S03

/- OMIT:
Negation
--------

OMIT. -/
/- TEXT:
.. _negation:

否定
-----

TEXT. -/
/- OMIT:
The symbol ``¬`` is meant to express negation,
so ``¬ x < y`` says that ``x`` is not less than ``y``,
``¬ x = y`` (or, equivalently, ``x ≠ y``) says that
``x`` is not equal to ``y``,
and ``¬ ∃ z, x < z ∧ z < y`` says that there does not exist a ``z``
strictly between ``x`` and ``y``.
In Lean, the notation ``¬ A`` abbreviates ``A → False``,
which you can think of as saying that ``A`` implies a contradiction.
Practically speaking, this means that you already know something
about how to work with negations:
you can prove ``¬ A`` by introducing a hypothesis ``h : A``
and proving ``False``,
and if you have ``h : ¬ A`` and ``h' : A``,
then applying ``h`` to ``h'`` yields ``False``.

OMIT. -/
/- TEXT:
記号 ``¬`` は否定を表すもので， ``¬ x < y`` は ``x`` が ``y`` より小さくないことを表し， ``¬ x = y`` （または ``x ≠ y`` でも同じ意味になります）は ``x`` が ``y`` と等しくないことを表し， ``¬ ∃ z, x < z ∧ z < y`` は ``x`` と ``y`` の間の開区間に ``z`` が存在しないことを表します．Leanでは， ``¬ A`` という表記は ``A → False`` を省略したもので，これは ``A`` から矛盾が導かれるという意味です．実用的には，読者はもう既に否定を扱う方法を知っているとも言えます: ``¬ A`` を証明するにあたっては ``h : A`` を導入してから ``False`` を示せば良く，また ``h : ¬ A`` と ``h' : A`` があれば， ``h'`` に ``h`` を適用することで ``False`` を得ることができます．

TEXT. -/
/- OMIT:
To illustrate, consider the irreflexivity principle ``lt_irrefl``
for a strict order,
which says that we have ``¬ a < a`` for every ``a``.
The asymmetry principle ``lt_asymm`` says that we have
``a < b → ¬ b < a``. Let's show that ``lt_asymm`` follows
from ``lt_irrefl``.
OMIT. -/
/- TEXT:
これを説明するために，狭義順序に対する非反射律 ``lt_irrefl`` を考えてみましょう．これはすべての``a`` に対して ``¬ a < a`` であることを指します．反対称律 ``lt_asymm`` は ``a < b → ¬ b < a`` となることを言います．ここで ``lt_asymm`` が ``lt_irrefl`` から導かれることを示しましょう．
TEXT. -/
-- BOTH:
section
variable (a b : ℝ)

-- EXAMPLES:
-- QUOTE:
example (h : a < b) : ¬b < a := by
  intro h'
  have : a < a := lt_trans h h'
  apply lt_irrefl a this
-- QUOTE.

/- OMIT:
This example introduces a couple of new tricks.
First, when you use ``have`` without providing
a label,
Lean uses the name ``this``,
providing a convenient way to refer back to it.
Because the proof is so short, we provide an explicit proof term.
But what you should really be paying attention to in this
proof is the result of the ``intro`` tactic,
which leaves a goal of ``False``,
and the fact that we eventually prove ``False``
by applying ``lt_irrefl`` to a proof of ``a < a``.

OMIT. -/
/- TEXT:
.. index:: this, have, tactics ; have, from, tactics ; from

この例で初めて使用した新たな技法があります．まず，ラベルを付けずに ``have`` を用いましたが，こうするとLeanが ``this`` という名前を使用します．これはこの対象を後から参照するにあたって便利です．今回の証明はとても短いため，明示的な証明項を用意しています．しかしこの証明において最も注目すべきなのは ``intro`` タクティクによってゴールが ``False`` となっていること，そして ``lt_irrefl`` を ``a < a`` に適用することで最終的に ``False`` を証明していることです．

TEXT. -/
/- OMIT:
Here is another example, which uses the
predicate ``FnHasUb`` defined in the last section,
which says that a function has an upper bound.
OMIT. -/
/- TEXT:
ここで前節で定義した関数が上限を持つことを示す述語 ``FnHasUb`` を用いた別の例を見てみましょう．
TEXT. -/

-- BOTH:
def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a

variable (f : ℝ → ℝ)

-- EXAMPLES:
-- QUOTE:
example (h : ∀ a, ∃ x, f x > a) : ¬FnHasUb f := by
  intro fnub
  rcases fnub with ⟨a, fnuba⟩
  rcases h a with ⟨x, hx⟩
  have : f x ≤ a := fnuba x
  linarith
-- QUOTE.

/- OMIT:
Remember that it is often convenient to use ``linarith``
when a goal follows from linear equations and
inequalities that in the context.

OMIT. -/
/- TEXT:
ゴールがそのコンテキストにおいて線形な等式と不等式から導かれるとき， ``linarith`` を使うとしばしば便利であることを覚えておきましょう．

TEXT. -/
/- OMIT:
See if you can prove these in a similar way:
OMIT. -/
/- TEXT:
以下でも同じように証明できるかやってみましょう:
TEXT. -/
-- QUOTE:
example (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f :=
  sorry

example : ¬FnHasUb fun x ↦ x :=
  sorry
-- QUOTE.

-- SOLUTIONS:
example (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f := by
  rintro ⟨a, ha⟩
  rcases h a with ⟨x, hx⟩
  have := ha x
  linarith

example : ¬FnHasUb fun x ↦ x := by
  rintro ⟨a, ha⟩
  have : a + 1 ≤ a := ha (a + 1)
  linarith

/- OMIT:
Mathlib offers a number of useful theorems for relating orders
and negations:
OMIT. -/
/- TEXT:
Mathlibには順序と否定に関連した便利な定理が多数あります:
TEXT. -/
-- QUOTE:
#check (not_le_of_gt : a > b → ¬a ≤ b)
#check (not_lt_of_ge : a ≥ b → ¬a < b)
#check (lt_of_not_ge : ¬a ≥ b → a < b)
#check (le_of_not_gt : ¬a > b → a ≤ b)
-- QUOTE.

/- OMIT:
Recall the predicate ``Monotone f``,
which says that ``f`` is nondecreasing.
Use some of the theorems just enumerated to prove the following:
OMIT. -/
/- TEXT:
``f`` が減少しないことを表す ``Monotone f`` という述語を思い出してください．今挙げた定理の中からいくつか使って以下を証明してください:
TEXT. -/
-- QUOTE:
example (h : Monotone f) (h' : f a < f b) : a < b := by
  sorry

example (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (h : Monotone f) (h' : f a < f b) : a < b := by
  apply lt_of_not_ge
  intro h''
  apply absurd h'
  apply not_lt_of_ge (h h'')

example (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
  intro h''
  apply absurd h'
  apply not_lt_of_ge
  apply h'' h

/- OMIT:
We can show that the first example in the last snippet
cannot be proved if we replace ``<`` by ``≤``.
Notice that we can prove the negation of a universally
quantified statement by giving a counterexample.
Complete the proof.
OMIT. -/
/- TEXT:
もし ``<`` を ``≤`` で置き換えると，すぐ上の1つ目の例の否定が証明できます．全称量化子のついた命題の否定は，反例を示すことで証明できることに注意してください．この証明を完成させてみましょう．
TEXT. -/
-- QUOTE:
example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
  intro h
  let f := fun x : ℝ ↦ (0 : ℝ)
  have monof : Monotone f := by sorry
  have h' : f 1 ≤ f 0 := le_refl _
  sorry
-- QUOTE.

-- SOLUTIONS:
example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
  intro h
  let f := fun x : ℝ ↦ (0 : ℝ)
  have monof : Monotone f := by
    intro a b leab
    rfl
  have h' : f 1 ≤ f 0 := le_refl _
  have : (1 : ℝ) ≤ 0 := h monof h'
  linarith

/- OMIT:
This example introduces the ``let`` tactic,
which adds a *local definition* to the context.
If you put the cursor after the ``let`` command,
in the goal window you will see that the definition
``f : ℝ → ℝ := fun x ↦ 0`` has been added to the context.
Lean will unfold the definition of ``f`` when it has to.
In particular, when we prove ``f 1 ≤ f 0`` with ``le_refl``,
Lean reduces ``f 1`` and ``f 0`` to ``0``.

OMIT. -/
/- TEXT:
.. index:: let, tactics ; let

この例では **局所的な定義** （local definition）をローカルコンテキストに追加する ``let`` タクティクを導入しています． ``let`` コマンドの後ろにカーソルを置くと，ゴールウィンドウに ``f : ℝ → ℝ := fun x ↦ 0`` という定義が追加されていることがわかるでしょう．Leanは必要なときに ``f`` の定義を展開します．特に ``f 1 ≤ f 0`` を ``le_refl`` で証明するとき，Leanは ``f 1`` と ``f 0`` を ``0`` に展開します．

TEXT. -/
/- OMIT:
Use ``le_of_not_gt`` to prove the following:
OMIT. -/
/- TEXT:
``le_of_not_gt`` を用いて以下を証明しましょう:
TEXT. -/
-- QUOTE:
example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  apply le_of_not_gt
  intro h'
  linarith [h _ h']

-- BOTH:
end

/- OMIT:
Implicit in many of the proofs we have just done
is the fact that if ``P`` is any property,
saying that there is nothing with property ``P``
is the same as saying that everything fails to have
property ``P``,
and saying that not everything has property ``P``
is equivalent to saying that something fails to have property ``P``.
In other words, all four of the following implications
are valid (but one of them cannot be proved with what we explained so
far):
OMIT. -/
/- TEXT:
今までの証明の中で暗黙のうちに用いてきた事実として，次の2つがあります．任意の性質 ``P`` について，「性質 ``P`` を満たすものが存在しない」ということは，「すべてのものが性質 ``P`` を持たない」ということと同義であり，また「すべてのものが性質 ``P`` を持つわけではない」ということは，「性質 ``P`` を持たないものが存在する」ということと同義です．言い換えるならば，以下の4つの含意がすべて成立するということです（ただし，そのうちの1つはこれまでに説明した内容では証明できません）:
TEXT. -/
-- BOTH:
section
-- QUOTE:
variable {α : Type*} (P : α → Prop) (Q : Prop)

-- EXAMPLES:
example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  sorry

example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  sorry

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  sorry

example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  intro x Px
  apply h
  use x

example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  rintro ⟨x, Px⟩
  exact h x Px

example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  intro h'
  rcases h with ⟨x, nPx⟩
  apply nPx
  apply h'

/- OMIT:
The first, second, and fourth are straightforward to
prove using the methods you have already seen.
We encourage you to try it.
The third is more difficult, however,
because it concludes that an object exists
from the fact that its nonexistence is contradictory.
This is an instance of *classical* mathematical reasoning.
We can use proof by contradiction
to prove the third implication as follows.
OMIT. -/
/- TEXT:
1つ目と2つ目，そして4つ目はこれまでに見てきた方法でそのまま証明することができます．ぜひ試してみてください．しかし，3つ目はより難しいです．なぜなら「存在しないと仮定すると矛盾する」という事実から何かが存在すると結論付けなければならないからです．これは **古典的な** （classical）数学的推論の一例です．背理法を用いて3つ目の含意を次のように証明することができます．
TEXT. -/
-- QUOTE:
example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  show P x
  by_contra h''
  exact h' ⟨x, h''⟩
-- QUOTE.

/- OMIT:
Make sure you understand how this works.
The ``by_contra`` tactic
allows us to prove a goal ``Q`` by assuming ``¬ Q``
and deriving a contradiction.
In fact, it is equivalent to using the
equivalence ``not_not : ¬ ¬ Q ↔ Q``.
Confirm that you can prove the forward direction
of this equivalence using ``by_contra``,
while the reverse direction follows from the
ordinary rules for negation.
OMIT. -/
/- TEXT:
.. index:: by_contra, tactics ; by_contra and by_contradiction,

これがどのように機能しているかどうかをきちんと理解しておきましょう． ``by_contra`` タクティクは ``¬ Q`` を仮定し，そこから矛盾を導くことでゴール ``Q`` を証明できるようにしてくれます．実のところこれは ``not_not : ¬ ¬ Q ↔ Q`` という同値性を使うのと等価です．この同値の順方向は ``by_contra`` を使って証明することができ，逆方向は通常の否定のルールから導かれることを確認しましょう．
TEXT. -/
-- QUOTE:
example (h : ¬¬Q) : Q := by
  sorry

example (h : Q) : ¬¬Q := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (h : ¬¬Q) : Q := by
  by_contra h'
  exact h h'

example (h : Q) : ¬¬Q := by
  intro h'
  exact h' h

-- BOTH:
end

/- OMIT:
Use proof by contradiction to establish the following,
which is the converse of one of the implications we proved above.
(Hint: use ``intro`` first.)
OMIT. -/
/- TEXT:
背理法を使って上で証明した含意の1つの逆である以下を証明してください．（ヒント: 最初に ``intro`` を用います．）
TEXT. -/
-- BOTH:
section
variable (f : ℝ → ℝ)

-- EXAMPLES:
-- QUOTE:
example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  intro a
  by_contra h'
  apply h
  use a
  intro x
  apply le_of_not_gt
  intro h''
  apply h'
  use x

/- OMIT:
It is often tedious to work with compound statements with
a negation in front,
and it is a common mathematical pattern to replace such
statements with equivalent forms in which the negation
has been pushed inward.
To facilitate this, Mathlib offers a ``push_neg`` tactic,
which restates the goal in this way.
The command ``push_neg at h`` restates the hypothesis ``h``.
OMIT. -/
/- TEXT:
.. index:: push_neg, tactics ; push_neg

否定が先頭についている複合的な命題を扱うのは面倒なことが多く，否定を内側に押し込んだ等価な形に置き換えるのが一般的な数学のパターンです．これを容易にするために，Mathlibはこれをゴールに適用する ``push_neg`` というタクティクを提供しています． ``push_neg at h`` とすると仮定 ``h`` を書き換えます．
TEXT. -/
-- QUOTE:
example (h : ¬∀ a, ∃ x, f x > a) : FnHasUb f := by
  push_neg at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  dsimp only [FnHasUb, FnUb] at h
  push_neg at h
  exact h
-- QUOTE.

/- OMIT:
In the second example, we use dsimp to
expand the definitions of ``FnHasUb`` and ``FnUb``.
(We need to use ``dsimp`` rather than ``rw``
to expand ``FnUb``,
because it appears in the scope of a quantifier.)
You can verify that in the examples above
with ``¬∃ x, P x`` and ``¬∀ x, P x``,
the ``push_neg`` tactic does the expected thing.
Without even knowing how to use the conjunction
symbol,
you should be able to use ``push_neg``
to prove the following:
OMIT. -/
/- TEXT:
2つ目の例では， ``FnHasUb`` と ``FnUb`` の定義を展開するために ``dsimp`` を使っています．（量化子のスコープが現れるため ``FnUb`` を展開するには ``rw`` ではなく ``dsimp`` を用いる必要があります．）上記の ``¬∃ x, P x`` と ``¬∀ x, P x`` の例では， ``push_neg`` タクティクが期待通り動作することを確認できます．連言の記号の使い方を知らずとも， ``push_neg`` を使って次のことが証明できるはずです:
TEXT. -/
-- QUOTE:
example (h : ¬Monotone f) : ∃ x y, x ≤ y ∧ f y < f x := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (h : ¬Monotone f) : ∃ x y, x ≤ y ∧ f y < f x := by
  rw [Monotone] at h
  push_neg  at h
  exact h

/- OMIT:
Mathlib also has a tactic, ``contrapose``,
which transforms a goal ``A → B`` to ``¬B → ¬A``.
Similarly, given a goal of proving ``B`` from
hypothesis ``h : A``,
``contrapose h`` leaves you with a goal of proving
``¬A`` from hypothesis ``¬B``.
Using ``contrapose!`` instead of ``contrapose``
applies ``push_neg`` to the goal and the relevant
hypothesis as well.
OMIT. -/
/- TEXT:
.. index:: contrapose, tactics ; contrapose

Mathlibには ``contrapose`` というタクティクもあり，これは ``A → B`` というゴールを ``¬B → ¬A`` に変換します．同様に，仮定 ``h : A`` から ``B`` を証明するというゴールがある場合， ``contrapose h`` を使うと仮定 ``¬B`` から ``¬A`` を証明するというゴールになります． ``contrapose`` の代わりに ``contrapose!`` を使うと，ゴールとそれに関連する仮定に ``push_neg`` が適用されます．
TEXT. -/
-- QUOTE:
example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  contrapose! h
  exact h

example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := by
  contrapose! h
  use x / 2
  constructor <;> linarith
-- QUOTE.

-- BOTH:
end

/- OMIT:
We have not yet explained the ``constructor`` command
or the use of the semicolon after it,
but we will do that in the next section.

OMIT. -/
/- TEXT:
ここまでまだ ``constructor`` タクティクやその後のセミコロンの使い方について説明していませんが，それは次の節で説明します．

TEXT. -/
/- OMIT:
We close this section with
the principle of *ex falso*,
which says that anything follows from a contradiction.
In Lean, this is represented by ``False.elim``,
which establishes ``False → P`` for any proposition ``P``.
This may seem like a strange principle,
but it comes up fairly often.
We often prove a theorem by splitting on cases,
and sometimes we can show that one of
the cases is contradictory.
In that case, we need to assert that the contradiction
establishes the goal so we can move on to the next one.
(We will see instances of reasoning by cases in
:numref:`disjunction`.)

OMIT. -/
/- TEXT:
本節の最後に，矛盾からはなんでも導かれるという *爆発律(ex falso)* の原理について述べましょう．Leanではこれは ``False.elim`` で表現され，任意の命題 ``P`` に対して ``False → P`` を成立させます．これは奇妙な原理のように思えるかもしれませんが，かなり頻繁に出てきます．定理を証明する際に場合分けを行うのはよくあることですが，その際そのうちの一つのケースが矛盾していることがあります．そのような場合，次のケースに進むために矛盾がゴールを成立させていることを主張する必要があります．（場合分けによる推論の例は :numref:`disjunction` で見ていきます．）

.. index:: exfalso, contradiction, absurd, tactics ; exfalso, tactics ; contradiction

TEXT. -/
/- OMIT:
Lean provides a number of ways of closing
a goal once a contradiction has been reached.
OMIT. -/
/- TEXT:
Leanは矛盾に到達したときゴールを閉じる方法をいくつか用意しています．
TEXT. -/
section
variable (a : ℕ)

-- QUOTE:
example (h : 0 < 0) : a > 37 := by
  exfalso
  apply lt_irrefl 0 h

example (h : 0 < 0) : a > 37 :=
  absurd h (lt_irrefl 0)

example (h : 0 < 0) : a > 37 := by
  have h' : ¬0 < 0 := lt_irrefl 0
  contradiction
-- QUOTE.

end

/- OMIT:
The ``exfalso`` tactic replaces the current goal with
the goal of proving ``False``.
Given ``h : P`` and ``h' : ¬ P``,
the term ``absurd h h'`` establishes any proposition.
Finally, the ``contradiction`` tactic tries to close a goal
by finding a contradiction in the hypotheses,
such as a pair of the form ``h : P`` and ``h' : ¬ P``.
Of course, in this example, ``linarith`` also works.
OMIT. -/
/- TEXT:
``exfalso`` タクティクは現在のゴールを ``False`` を証明するゴールに置き換えます． ``h : P`` と ``h' : ¬ P`` が与えられたとき， ``absurd h h'`` という項は任意の命題を証明します．最後に， ``contradiction`` タクティクは ``h : P`` と ``h' : ¬ P`` の形の仮定の組のような，ローカルコンテキストの矛盾を見つけることによってゴールを閉じようとします．もちろん，この例では ``linarith`` も有効です．
TEXT. -/
