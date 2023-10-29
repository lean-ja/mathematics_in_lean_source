-- BOTH:
import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S01

/- OMIT:
Implication and the Universal Quantifier
----------------------------------------

OMIT. -/
/- TEXT:
.. _implication_and_the_universal_quantifier:

含意と全称記号
---------------

TEXT. -/
/- OMIT:
Consider the statement after the ``#check``:
OMIT. -/
/- TEXT:
以下の ``#check`` コマンドの後ろに続いている命題について考察してみましょう:
TEXT. -/
-- QUOTE:
#check ∀ x : ℝ, 0 ≤ x → |x| = x
-- QUOTE.

/- OMIT:
In words, we would say "for every real number ``x``, if ``0 ≤ x`` then
the absolute value of ``x`` equals ``x``".
We can also have more complicated statements like:
OMIT. -/
/- TEXT:
この命題を日本語にすると「すべての実数 ``x`` に対して，もし ``0 ≤ x`` ならば， ``x`` の絶対値は ``x`` に等しい」ということになります．もっと複雑な命題を表現することもできます:
TEXT. -/
-- QUOTE:
#check ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε
-- QUOTE.
/- OMIT:
In words, we would say "for every ``x``, ``y``, and ``ε``,
if ``0 < ε ≤ 1``, the absolute value of ``x`` is less than ``ε``,
and the absolute value of ``y`` is less than ``ε``,
then the absolute value of ``x * y`` is less than ``ε``."
In Lean, in a sequence of implications there are
implicit parentheses grouped to the right.
So the expression above means
"if ``0 < ε`` then if ``ε ≤ 1`` then if ``|x| < ε`` ..."
As a result, the expression says that all the
assumptions together imply the conclusion.

OMIT. -/
/- TEXT:
この命題は「すべての ``x`` ， ``y`` ， ``ε`` に対して，もし ``0 < ε ≤ 1`` で， ``x`` の絶対値が ``ε`` よりも小さく，``y`` の絶対値も ``ε`` よりも小さいならば， ``x * y`` の絶対値も ``ε`` より小さい」ということになります．Leanにおいて複数の含意がある場合，右側をまとめた暗黙の括弧が存在します．したがって上記の式は「もし ``0 ≤ ε`` ならば，そしてもし ``ε ≤ 1`` ならば，そしてもし ``|x| < ε`` ならば…」を意味します．結果として，この式は上記で並べられた仮定すべてから結論が導かれるということを言っています．

TEXT. -/
/- OMIT:
You have already seen that even though the universal quantifier
in this statement
ranges over objects and the implication arrows introduce hypotheses,
Lean treats the two in very similar ways.
In particular, if you have proved a theorem of that form,
you can apply it to objects and hypotheses in the same way.
We will use as an example the following statement that we will help you to prove a
bit later:
OMIT. -/
/- TEXT:
この命題において，全称記号が対象の範囲を変化させ，含意の矢印が仮説を導入するという異なることをしているにもかかわらず，Leanはこの2つを非常に似た方法で扱っていることはすでにおわかりでしょう．特に，このような形式の定理を証明した場合，その定理を対象にも仮説にも同じように適用することができます．この事の例として，少しあとで証明する以下の命題を用いましょう:
TEXT. -/
-- QUOTE:
theorem my_lemma : ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε :=
  sorry

section
variable (a b δ : ℝ)
variable (h₀ : 0 < δ) (h₁ : δ ≤ 1)
variable (ha : |a| < δ) (hb : |b| < δ)

#check my_lemma a b δ
#check my_lemma a b δ h₀ h₁
#check my_lemma a b δ h₀ h₁ ha hb

end
-- QUOTE.

/- OMIT:
You have also already seen that it is common in Lean
to use curly brackets to make quantified variables implicit
when they can be inferred from subsequent hypotheses.
When we do that, we can just apply a lemma to the hypotheses without
mentioning the objects.
OMIT. -/
/- TEXT:
またLeanにおいて，量化された変数が後続の仮説から推測できる場合に波括弧を使って暗黙の変数にできることも見てきました．この場合，対象について言及することなく仮説に補題を適用することができます．
TEXT. -/
-- QUOTE:
theorem my_lemma2 : ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε :=
  sorry

section
variable (a b δ : ℝ)
variable (h₀ : 0 < δ) (h₁ : δ ≤ 1)
variable (ha : |a| < δ) (hb : |b| < δ)

#check my_lemma2 h₀ h₁ ha hb

end
-- QUOTE.

/- OMIT:
At this stage, you also know that if you use
the ``apply`` tactic to apply ``my_lemma``
to a goal of the form ``|a * b| < δ``,
you are left with new goals that require you to  prove
each of the hypotheses.

OMIT. -/
/- TEXT:
この段階で， ``apply`` タクティクを使って ``my_lemma`` を ``|a * b| < δ`` というゴールに適用すると，``my_lemma`` の引数の仮説が証明しなければならない新たなゴールとして残ることも知っているでしょう．

.. index:: intro, tactics; intro

TEXT. -/
/- OMIT:
To prove a statement like this, use the ``intro`` tactic.
Take a look at what it does in this example:
OMIT. -/
/- TEXT:
このような命題を証明するには， ``intro`` タクティクを使います．このことについて次の例を見てみましょう:
TEXT. -/
-- QUOTE:
theorem my_lemma3 :
    ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε epos ele1 xlt ylt
  sorry
-- QUOTE.

/- OMIT:
We can use any names we want for the universally quantified variables;
they do not have to be ``x``, ``y``, and ``ε``.
Notice that we have to introduce the variables
even though they are marked implicit:
making them implicit means that we leave them out when
we write an expression *using* ``my_lemma``,
but they are still an essential part of the statement
that we are proving.
After the ``intro`` command,
the goal is what it would have been at the start if we
listed all the variables and hypotheses *before* the colon,
as we did in the last section.
In a moment, we will see why it is sometimes necessary to
introduce variables and hypotheses after the proof begins.

OMIT. -/
/- TEXT:
ここで全称量化された変数の名前にはどんな名前でも使うことができます:つまり ``x`` ， ``y`` ， ``ε`` である必要がないのです．ここでこれらの変数が暗黙的な変数であったとしても，変数の導入をしなければならないことに注意してください:変数を暗黙的にすることは式で ``my_lemma`` を *使う* 際にわざわざ書かなくても良いことを意味しますが，その命題を証明する段階ではそれらはその命題の必須な部分であるのです．``intro`` コマンドを実行した後のゴールは，前節でやったようなコロンの前にすべての変数と仮説を列挙した場合の証明の一番初めと同じになっています．このように証明の開始後に変数や仮説を導入する必要性がある理由については後ほど説明します．

TEXT. -/
/- OMIT:
To help you prove the lemma, we will start you off:
OMIT. -/
/- TEXT:
この補題の証明を行うにあたって，手助けとして以下の形から証明を行ってみましょう:
TEXT. -/
-- QUOTE:
-- BOTH:
theorem my_lemma4 :
    ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε epos ele1 xlt ylt
/- EXAMPLES:
  calc
    |x * y| = |x| * |y| := sorry
    _ ≤ |x| * ε := sorry
    _ < 1 * ε := sorry
    _ = ε := sorry

SOLUTIONS: -/
  calc
    |x * y| = |x| * |y| := by apply abs_mul
    _ ≤ |x| * ε := by apply mul_le_mul; linarith; linarith; apply abs_nonneg; apply abs_nonneg;
    _ < 1 * ε := by rw [mul_lt_mul_right epos]; linarith
    _ = ε := by apply one_mul
-- QUOTE.

/- OMIT:
Finish the proof using the theorems
``abs_mul``, ``mul_le_mul``, ``abs_nonneg``,
``mul_lt_mul_right``, and ``one_mul``.
Remember that you can find theorems like these using
Ctrl-space completion (or Cmd-space completion on a Mac).
Remember also that you can use ``.mp`` and ``.mpr``
or ``.1`` and ``.2`` to extract the two directions
of an if-and-only-if statement.

OMIT. -/
/- TEXT:
証明を完成させるために，定理 ``abs_mul`` ， ``mul_le_mul`` ， ``abs_nonneg`` ， ``mul_lt_mul_right`` を用います．Ctrl+スペース（MacではCmd+スペース）での補完を使えば，これらの定理を見つけることができることも覚えてください．また， ``mp`` と ``.mpr`` や ``.1`` と ``.2`` を使って，「〜とき，かつそのときに限る」の2つの方向を抽出できることも覚えておきましょう．

TEXT. -/
/- OMIT:
Universal quantifiers are often hidden in definitions,
and Lean will unfold definitions to expose them when necessary.
For example, let's define two predicates,
``FnUb f a`` and ``FnLb f a``,
where ``f`` is a function from the real numbers to the real
numbers and ``a`` is a real number.
The first says that ``a`` is an upper bound on the
values of ``f``,
and the second says that ``a`` is a lower bound
on the values of ``f``.
OMIT. -/
/- TEXT:
全称量化は定義に隠されていることが多く，Leanは必要なときに定義を展開しそれらの変数を公開します．例えば， ``FnUb f a`` と ``FnLb f a`` という2つの述語を定義しましょう．ここで ``f`` は実数から実数への関数， ``a`` は実数です．前者は ``a`` が ``f`` の値の上界であること， ``a`` が ``f`` の値の下界であることを言います．
BOTH: -/
-- QUOTE:
def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x
-- QUOTE.

/- OMIT:
In the next example, ``fun x ↦ f x + g x`` is the
function that maps ``x`` to ``f x + g x``. Going from the expression ``f x + g x``
to this function is called a lambda abstraction in type theory.
OMIT. -/
/- TEXT:
.. index:: lambda abstraction

次の例での ``fun x ↦ f x + g x`` は ``x`` を ``f x + g x`` にマップする関数です．式 ``f x + g x`` からこの関数を作ることを，型理論ではラムダ抽象と呼びます．
BOTH: -/
section
variable (f g : ℝ → ℝ) (a b : ℝ)

-- EXAMPLES:
-- QUOTE:
example (hfa : FnUb f a) (hgb : FnUb g b) : FnUb (fun x ↦ f x + g x) (a + b) := by
  intro x
  dsimp
  apply add_le_add
  apply hfa
  apply hgb
-- QUOTE.

/- OMIT:
Applying ``intro`` to the goal ``FnUb (fun x ↦ f x + g x) (a + b)``
forces Lean to unfold the definition of ``FnUb``
and introduce ``x`` for the universal quantifier.
The goal is then ``(fun (x : ℝ) ↦ f x + g x) x ≤ a + b``.
But applying ``(fun x ↦ f x + g x)`` to ``x`` should result in ``f x + g x``,
and the ``dsimp`` command performs that simplification.
(The "d" stands for "definitional.")
You can delete that command and the proof still works;
Lean would have to perform that contraction anyhow to make
sense of the next ``apply``.
The ``dsimp`` command simply makes the goal more readable
and helps us figure out what to do next.
Another option is to use the ``change`` tactic
by writing ``change f x + g x ≤ a + b``.
This helps make the proof more readable,
and gives you more control over how the goal is transformed.

OMIT. -/
/- TEXT:
.. index:: dsimp, tactics ; dsimp, change, tactics ; change

ゴール ``FnUb (fun x ↦ f x + g x) (a + b)`` に ``intro`` タクティクを適用すると，Leanは ``FnUb`` の定義を展開し，全称量化した変数として ``x`` を導入します．これによりゴールは ``(fun (x : ℝ) ↦ f x + g x) x ≤ a + b`` となります．しかし， ``(fun x ↦ f x + g x)`` を ``x`` に適用すると ``f x + g x`` となるはずで， ``dsimp`` コマンドはこの単純化を行います．（「d」は「definitional（定義上）」の略です．）このコマンドを削除しても証明は機能します; Leanは次の行の ``apply`` の意味を理解するために，いずれにせよこの短縮を行います．``dsimp`` コマンドは単にゴールを読みやすくし，次に何をすべきかを考える手助けをしてくれます．別の方法として， ``change`` タクティクを用いて ``change f x + g x ≤ a + b`` と書くこともできます．これは証明をより読みやすくし，ゴールがどのように変換されるかをコントロールできるようにします．

TEXT. -/
/- OMIT:
The rest of the proof is routine.
The last two ``apply`` commands force Lean to unfold the definitions
of ``FnUb`` in the hypotheses.
Try carrying out similar proofs of these:
OMIT. -/
/- TEXT:
残りの証明はいつもの流れです．最後の2つの ``apply`` コマンドはLeanに仮説野中の ``FnUb`` の定義を展開させます．これらと同様の証明を行ってみましょう:
TEXT. -/
-- QUOTE:
example (hfa : FnLb f a) (hgb : FnLb g b) : FnLb (fun x ↦ f x + g x) (a + b) :=
  sorry

example (nnf : FnLb f 0) (nng : FnLb g 0) : FnLb (fun x ↦ f x * g x) 0 :=
  sorry

example (hfa : FnUb f a) (hgb : FnUb g b) (nng : FnLb g 0) (nna : 0 ≤ a) :
    FnUb (fun x ↦ f x * g x) (a * b) :=
  sorry
-- QUOTE.

-- SOLUTIONS:
example (hfa : FnLb f a) (hgb : FnLb g b) : FnLb (fun x ↦ f x + g x) (a + b) := by
  intro x
  apply add_le_add
  apply hfa
  apply hgb

example (nnf : FnLb f 0) (nng : FnLb g 0) : FnLb (fun x ↦ f x * g x) 0 := by
  intro x
  apply mul_nonneg
  apply nnf
  apply nng

example (hfa : FnUb f a) (hgb : FnUb g b) (nng : FnLb g 0) (nna : 0 ≤ a) :
    FnUb (fun x ↦ f x * g x) (a * b) := by
  intro x
  apply mul_le_mul
  apply hfa
  apply hgb
  apply nng
  apply nna

-- BOTH:
end

/- OMIT:
Even though we have defined ``FnUb`` and ``FnLb`` for functions
from the reals to the reals,
you should recognize that the definitions and proofs are much
more general.
The definitions make sense for functions between any two types
for which there is a notion of order on the codomain.
Checking the type of the theorem ``add_le_add`` shows that it holds
of any structure that is an "ordered additive commutative monoid";
the details of what that means don't matter now,
but it is worth knowing that the natural numbers, integers, rationals,
and real numbers are all instances.
So if we prove the theorem ``fnUb_add`` at that level of generality,
it will apply in all these instances.
OMIT. -/
/- TEXT:
実数から実数への関数に対して ``FnUb`` と ``FnLb`` を定義しましたが，この定義と証明はもっと一般的です．この定義は終域に順序の概念がある任意の2つの型間の関数でも意味を持ちます．定理 ``add_le_add`` の型を調べると，この定理が「順序付き加法可換モノイド」であればどんな構造でも成り立つことがわかります;この構造が何を意味するのかの詳細は今の段階では重要ではありませんが，自然数，整数，有理数，実数すべてがこの構造のインスタンスであることを知っておいて損はありません．そのため，この一般性のレベルで定理 ``fnUb_add`` を証明すれば，これらのインスタンス全てに適用できます．
TEXT. -/
section
-- QUOTE:
variable {α : Type*} {R : Type*} [OrderedCancelAddCommMonoid R]

#check add_le_add

def FnUb' (f : α → R) (a : R) : Prop :=
  ∀ x, f x ≤ a

theorem fnUb_add {f g : α → R} {a b : R} (hfa : FnUb' f a) (hgb : FnUb' g b) :
    FnUb' (fun x ↦ f x + g x) (a + b) := fun x ↦ add_le_add (hfa x) (hgb x)
-- QUOTE.

end

/- OMIT:
You have already seen square brackets like these in
Section :numref:`proving_identities_in_algebraic_structures`,
though we still haven't explained what they mean.
For concreteness, we will stick to the real numbers
for most of our examples,
but it is worth knowing that Mathlib contains definitions and theorems
that work at a high level of generality.

OMIT. -/
/- TEXT:
このような角括弧はすでに :numref:`proving_identities_in_algebraic_structures` で見たことがあると思いますが，その意味についてはまだ説明していませんでした．実用性を考えて，これからも例としては実数を対象にしていきますが，Mathlibにはより一般性の高い定義や定理が含まれていることは知っておく価値があるでしょう．

.. index:: monotone function

TEXT. -/
/- OMIT:
For another example of a hidden universal quantifier,
Mathlib defines a predicate ``Monotone``,
which says that a function is nondecreasing in its arguments:
OMIT. -/
/- TEXT:
隠された全称量化子のもう一つの例として，Mathlibは関数が引数に対して減少しないことを意味する述語 ``Monotone`` （単調）を定義しています:
TEXT. -/
-- QUOTE:
example (f : ℝ → ℝ) (h : Monotone f) : ∀ {a b}, a ≤ b → f a ≤ f b :=
  @h
-- QUOTE.

/- OMIT:
The property ``Monotone f`` is defined to be exactly the expression
after the colon. We need to put the ``@`` symbol before ``h`` because
if we don't,
Lean expands the implicit arguments to ``h`` and inserts placeholders.

OMIT. -/
/- TEXT:
このように ``Monotone f`` はコロンの後ろの式と全く同じように定義されています．ここで ``h`` の前に ``@`` を置く必要があります．こうしないと，Leanは暗黙の引数を ``h`` に展開し，プレースホルダーを挿入してしまうからです．

TEXT. -/
/- OMIT:
Proving statements about monotonicity
involves using ``intro`` to introduce two variables,
say, ``a`` and ``b``, and the hypothesis ``a ≤ b``.
To *use* a monotonicity hypothesis,
you can apply it to suitable arguments and hypotheses,
and then apply the resulting expression to the goal.
Or you can apply it to the goal and let Lean help you
work backwards by displaying the remaining hypotheses
as new subgoals.
OMIT. -/
/- TEXT:
単調性についての命題の証明では， ``intro`` を使って2つの変数，例えば ``a`` と ``b`` を導入し， ``a ≤ b`` という仮説を立てます．単調性についての仮説を *用いる* ために，適切な引数と仮説に適用し，得られた式をゴールに適用することができます．もしくは直接ゴールに適用し，Leanに残りの仮説を新しいサブゴールとして表示してもらって証明をサポートしてもらうこともできます．
BOTH: -/
section
variable (f g : ℝ → ℝ)

-- EXAMPLES:
-- QUOTE:
example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f x + g x := by
  intro a b aleb
  apply add_le_add
  apply mf aleb
  apply mg aleb
-- QUOTE.

/- OMIT:
When a proof is this short, it is often convenient
to give a proof term instead.
To describe a proof that temporarily introduces objects
``a`` and ``b`` and a hypothesis ``aleb``,
Lean uses the notation ``fun a b aleb ↦ ...``.
This is analogous to the way that an expression
like ``fun x ↦ x^2`` describes a function
by temporarily naming an object, ``x``,
and then using it to describe a value.
So the ``intro`` command in the previous proof
corresponds to the lambda abstraction in the next proof term.
The ``apply`` commands then correspond to building
the application of the theorem to its arguments.
OMIT. -/
/- TEXT:
証明がこれくらい短い場合は，証明の項を直接与えるほうが便利であることが多いです．この際対象 ``a`` と ``b`` ，仮説 ``aleb`` を一時的に導入するような証明を書くためには，Leanでは ``fun a b aleb ↦ ...`` という表記を用います．これは ``fun x ↦ x^2`` のような式が一時的な対象に ``x`` と名付けてそれを用いて関数の値を記述するのと似ています．つまり，前の証明の ``intro`` コマンドは次の証明項のラムダ抽象に対応しています．そして ``apply`` コマンドは定理への引数の適用を構築することに対応しています．
TEXT. -/
-- QUOTE:
example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f x + g x :=
  fun a b aleb ↦ add_le_add (mf aleb) (mg aleb)
-- QUOTE.

/- OMIT:
Here is a useful trick: if you start writing
the proof term ``fun a b aleb ↦ _`` using
an underscore where the rest of the
expression should go,
Lean will flag an error,
indicating that it can't guess the value of that expression.
If you check the Lean Goal window in VS Code or
hover over the squiggly error marker,
Lean will show you the goal that the remaining
expression has to solve.

OMIT. -/
/- TEXT:
ここで便利な小技をご紹介しましょう: 式の残り部分にアンダースコアを使って ``fun a b aleb ↦ _`` 証明項を書き始めると，Leanはその式の値を推測できないことを示すエラーを出します．VSCodeのゴールウィンドウを見るか，四角いエラーマーカーにカーソルを合わせると，Leanが出した残っている未解決のゴールを表示します．

TEXT. -/
/- OMIT:
Try proving these, with either tactics or proof terms:
OMIT. -/
/- TEXT:
ここで次の定理をタクティクか証明項を用いて証明してみましょう:
TEXT. -/
-- QUOTE:
example {c : ℝ} (mf : Monotone f) (nnc : 0 ≤ c) : Monotone fun x ↦ c * f x :=
  sorry

example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f (g x) :=
  sorry
-- QUOTE.

-- SOLUTIONS:
example {c : ℝ} (mf : Monotone f) (nnc : 0 ≤ c) : Monotone fun x ↦ c * f x := by
  intro a b aleb
  apply mul_le_mul_of_nonneg_left _ nnc
  apply mf aleb

example {c : ℝ} (mf : Monotone f) (nnc : 0 ≤ c) : Monotone fun x ↦ c * f x :=
  fun a b aleb ↦ mul_le_mul_of_nonneg_left (mf aleb) nnc

example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f (g x) := by
  intro a b aleb
  apply mf
  apply mg
  apply aleb

example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f (g x) :=
  fun a b aleb ↦ mf (mg aleb)

/- OMIT:
Here are some more examples.
A function :math:`f` from :math:`\Bbb R` to
:math:`\Bbb R` is said to be *even* if
:math:`f(-x) = f(x)` for every :math:`x`,
and *odd* if :math:`f(-x) = -f(x)` for every :math:`x`.
The following example defines these two notions formally
and establishes one fact about them.
You can complete the proofs of the others.
OMIT. -/
/- TEXT:
ここでさらに例を挙げましょう．:math:`\Bbb R` から :math:`\Bbb R` への関数 :math:`f` が *偶関数* であるとはすべての :math:`x` に対して :math:`f(-x) = f(x)` となることを指し， *奇関数* であるとはすべての :math:`x` に対して :math:`f(-x) = -f(x)` となることを指します．以下の例ではこの2つの概念を形式的に定義し，またこれらについての1つの事実を立証します．残りの証明については読者自身で完成させてみましょう．
TEXT. -/
-- QUOTE:
-- BOTH:
def FnEven (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = f (-x)

def FnOdd (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = -f (-x)

-- EXAMPLES:
example (ef : FnEven f) (eg : FnEven g) : FnEven fun x ↦ f x + g x := by
  intro x
  calc
    (fun x ↦ f x + g x) x = f x + g x := rfl
    _ = f (-x) + g (-x) := by rw [ef, eg]


example (of : FnOdd f) (og : FnOdd g) : FnEven fun x ↦ f x * g x := by
  sorry

example (ef : FnEven f) (og : FnOdd g) : FnOdd fun x ↦ f x * g x := by
  sorry

example (ef : FnEven f) (og : FnOdd g) : FnEven fun x ↦ f (g x) := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (of : FnOdd f) (og : FnOdd g) : FnEven fun x ↦ f x * g x := by
  intro x
  calc
    (fun x ↦ f x * g x) x = f x * g x := rfl
    _ = f (-x) * g (-x) := by rw [of, og, neg_mul_neg]


example (ef : FnEven f) (og : FnOdd g) : FnOdd fun x ↦ f x * g x := by
  intro x
  dsimp
  rw [ef, og, neg_mul_eq_mul_neg]

example (ef : FnEven f) (og : FnOdd g) : FnEven fun x ↦ f (g x) := by
  intro x
  dsimp
  rw [og, ← ef]

-- BOTH:
end

/- OMIT:
The first proof can be shortened using ``dsimp`` or ``change``
to get rid of the lambda abstraction.
But you can check that the subsequent ``rw`` won't work
unless we get rid of the lambda abstraction explicitly,
because otherwise it cannot find the patterns ``f x`` and ``g x``
in the expression.
Contrary to some other tactics, ``rw`` operates on the syntactic level,
it won't unfold definitions or apply reductions for you
(it has a variant called ``erw`` that tries a little harder in this
direction, but not much harder).

OMIT. -/
/- TEXT:
.. index:: erw, tactics ; erw

1つ目の証明は ``dsimp`` か ``change`` を用いてラムダ抽象を取り除くことで証明を短くすることができるでしょう．ここで明示的にラムダ抽象を取り除いておかないと後続の証明で ``rw`` がうまく機能しないことを確認できます．これは式中で ``f x`` や ``g x`` のパターンを見つけられないからです．他のタクティクとは異なり， ``rw`` は構文レベルで動作し定義の展開や式の簡約を行ってくれません．（この方向性に関してもう少し頑張ってくれる ``erw`` というタクティクもありますが、これもさほど頑張ってはくれません．）

TEXT. -/
/- OMIT:
You can find implicit universal quantifiers all over the place,
once you know how to spot them.

OMIT. -/
/- TEXT:
さて，一度見分け方さえわかれば暗黙の全称量化子はいたるところで見つけることができます．

TEXT. -/
/- OMIT:
Mathlib includes a good library for manipulating sets. Recall that Lean does not
use foundations based on set theory, so here the word set has its mundane meaning
of a collection of mathematical objects of some given type ``α``.
If ``x`` has type ``α`` and ``s`` has type ``Set α``, then ``x ∈ s`` is a proposition
that asserts that ``x`` is an element of ``s``. If ``y`` has some different type ``β`` then the
expression ``y ∈ s`` makes no sense. Here "makes no sense" means "has no type hence Lean does not
accept it as a well-formed statement". This contrasts with Zermelo-Fraenkel set theory for instance
where ``a ∈ b`` is a well-formed statement for every mathematical objects ``a`` and ``b``.
For instance ``sin ∈ cos`` is a well-formed statement in ZF. This defect of set theoretic
foundations is an important motivation for not using it in a proof assistant which is meant to assist
us by detecting meaningless expressions. In Lean ``sin`` has type ``ℝ → ℝ`` and ``cos`` has type
``ℝ → ℝ`` which is not equal to ``Set (ℝ → ℝ)``, even after unfolding definitions, so the statement
``sin ∈ cos`` makes no sense.
One can also use Lean to work on set theory itself. For instance the independence of the continuum
hypothesis from the axioms of Zermelo-Fraenkel has been formalized in Lean. But such a meta-theory
of set theory is completely beyond the scope of this book.

OMIT. -/
/- TEXT:
Mathlibは集合を操作するにための優れたライブラリを有しています．ところでLeanは集合論を基礎に置いていないことを思い出してください，そのためここで言うところの集合は何かしらの型 ``α`` の数学的対象のあつまりというありふれた意味合いになります．もし ``x`` が型 ``α`` で， ``s`` が ``Set α`` 型であるとき， ``x ∈ s`` は ``x`` が ``s`` の要素であることを主張する命題となります．別の型 ``β`` の ``y`` については，式 ``y ∈ s`` は意味をなしません．ここでいう「意味をなさない」とは「型を持たないため，Leanとして合法な（well-formed）命題として受け入れられない」という意味です．これは例えばツェルメロ-フレンケルの集合論（ZF）では ``a ∈ b`` がすべての数学的対象 ``a`` と ``b`` に対して合法であることと対照的です．例えば ``sin ∈ cos`` もZFでは合法です．この集合論の欠点は無意味な式を検知して証明を支援することを意図した証明支援系として上記の集合論的な基礎を使用しない重要な動機となっています．Leanにおいて ``sin`` は ``ℝ → ℝ`` の型を持ち，``cos`` も ``ℝ → ℝ`` の型であり，これはたとえ定義を展開したとしても ``Set (ℝ → ℝ)`` とは等しくないため，``sin ∈ cos`` という命題は意味をなしません．一方でLeanを使って集合論そのものに取り組むこともできます．例えばZFの公理から連続体仮説が独立していることはLeanで形式化されています．しかしこのような集合論のメタ理論は本書の範囲を完全に超えています．

TEXT. -/
/- OMIT:
If ``s`` and ``t`` are of type ``Set α``,
then the subset relation ``s ⊆ t`` is defined to mean
``∀ {x : α}, x ∈ s → x ∈ t``.
The variable in the quantifier is marked implicit so that
given ``h : s ⊆ t`` and ``h' : x ∈ s``,
we can write ``h h'`` as justification for ``x ∈ t``.
The following example provides a tactic proof and a proof term
justifying the reflexivity of the subset relation,
and asks you to do the same for transitivity.
OMIT. -/
/- TEXT:
もし ``s`` と ``t`` が ``Set α`` 型のとき，部分集合の関係 ``s ⊆ t`` は ``∀ {x : α}, x ∈ s → x ∈ t`` の意味として定義されます．ここで量化された変数は暗黙的とされているため， ``h : s ⊆ t`` と ``h' : x ∈ s`` から ``h h'`` を ``x ∈ t`` の証明として書くことができます．次の例では，部分集合関係の反射性についてタクティクによるものと証明項によるもの両方の証明を示しています．これにならって遷移性について同じことをしてみましょう．
TEXT. -/
-- BOTH:
section

-- QUOTE:
variable {α : Type*} (r s t : Set α)

-- EXAMPLES:
example : s ⊆ s := by
  intro x xs
  exact xs

theorem Subset.refl : s ⊆ s := fun x xs ↦ xs

theorem Subset.trans : r ⊆ s → s ⊆ t → r ⊆ t := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example : r ⊆ s → s ⊆ t → r ⊆ t := by
  intro rsubs ssubt x xr
  apply ssubt
  apply rsubs
  apply xr

theorem Subset.transαα : r ⊆ s → s ⊆ t → r ⊆ t :=
  fun rsubs ssubt x xr ↦ ssubt (rsubs xr)

-- BOTH:
end

/- OMIT:
Just as we defined ``FnUb`` for functions,
we can define ``SetUb s a`` to mean that ``a``
is an upper bound on the set ``s``,
assuming ``s`` is a set of elements of some type that
has an order associated with it.
In the next example, we ask you to prove that
if ``a`` is a bound on ``s`` and ``a ≤ b``,
then ``b`` is a bound on ``s`` as well.
OMIT. -/
/- TEXT:
関数に対して ``FnUb`` を定義したように，``SetUb s a`` を定義することで， ``s`` を順序付けられたある型の要素の集合であると仮定して，``a`` が集合 ``s`` の上界であることを意味するようにできます．次の例で，もし ``a`` が ``s`` の上界であり，かつ ``a ≤ b`` ならば， ``b`` も ``s`` の上界であることを証明しましょう．
TEXT. -/
-- BOTH:
section
-- QUOTE:
variable {α : Type*} [PartialOrder α]
variable (s : Set α) (a b : α)

def SetUb (s : Set α) (a : α) :=
  ∀ x, x ∈ s → x ≤ a

-- EXAMPLES:
example (h : SetUb s a) (h' : a ≤ b) : SetUb s b :=
  sorry
-- QUOTE.

-- SOLUTIONS:
example (h : SetUb s a) (h' : a ≤ b) : SetUb s b := by
  intro x xs
  apply le_trans (h x xs) h'

example (h : SetUb s a) (h' : a ≤ b) : SetUb s b :=
  fun x xs ↦ le_trans (h x xs) h'

-- BOTH:
end

/- OMIT:
We close this section with one last important example.
A function :math:`f` is said to be *injective* if for
every :math:`x_1` and :math:`x_2`,
if :math:`f(x_1) = f(x_2)` then :math:`x_1 = x_2`.
Mathlib defines ``Function.Injective f`` with
``x₁`` and ``x₂`` implicit.
The next example shows that, on the real numbers,
any function that adds a constant is injective.
We then ask you to show that multiplication by a nonzero
constant is also injective, using the lemma name in the example as a source
of inspiration. Recall you should use Ctrl-space completion after guessing the beginning of
a lemma name.
OMIT. -/
/- TEXT:
.. index:: injective function

最後にもう一つ重要な例を挙げて本節を締めくくりましょう．関数 :math:`f` が *単射（injective）* であるとはすべての :math:`x_1` と :math:`x_2` について， :math:`f(x_1) = f(x_2)` なら :math:`x_1 = x_2` であることを指します．Mathlibはこの関係を ``x₁`` と ``x₂`` を暗黙にして ``Function.Injective f`` として定義しています．次の例は実数上で定数を加える関数が単射であることを示しています．この例中の補題名をヒントに0ではない定数を掛ける関数も単射であることを示しましょう．補題名の先頭を推測したらCtrl+スペースによる補完を使えることを思い出してください．
TEXT. -/
-- BOTH:
section

-- QUOTE:
open Function

-- EXAMPLES:
example (c : ℝ) : Injective fun x ↦ x + c := by
  intro x₁ x₂ h'
  exact (add_left_inj c).mp h'

example {c : ℝ} (h : c ≠ 0) : Injective fun x ↦ c * x := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example {c : ℝ} (h : c ≠ 0) : Injective fun x ↦ c * x := by
  intro x₁ x₂ h'
  apply (mul_right_inj' h).mp h'

/- OMIT:
Finally, show that the composition of two injective functions is injective:
OMIT. -/
/- TEXT:
最後に2つの単射な関数の合成も単射であることを示しましょう:
BOTH: -/
-- QUOTE:
variable {α : Type*} {β : Type*} {γ : Type*}
variable {g : β → γ} {f : α → β}

-- EXAMPLES:
example (injg : Injective g) (injf : Injective f) : Injective fun x ↦ g (f x) := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (injg : Injective g) (injf : Injective f) : Injective fun x ↦ g (f x) := by
  intro x₁ x₂ h
  apply injf
  apply injg
  apply h

-- BOTH:
end
