-- BOTH:
import MIL.Common
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Prime

namespace C03S04

/- OMIT:
Conjunction and Iff
-------------------

OMIT. -/
/- TEXT:
.. _conjunction_and_biimplication:

連言と必要十分条件
-------------------

.. index:: constructor, tactics ; constructor

TEXT. -/
/- OMIT:
You have already seen that the conjunction symbol, ``∧``,
is used to express "and."
The ``constructor`` tactic allows you to prove a statement of
the form ``A ∧ B``
by proving ``A`` and then proving ``B``.
OMIT. -/
/- TEXT:
「かつ」を表すのに使われている連言の記号 ``∧`` はもうすでに見てきました． ``constructor`` タクティクを使うことで ``A ∧ B`` という形の命題の証明を ``A`` と ``B`` を証明することに帰着できます．
TEXT. -/
-- QUOTE:
example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y := by
  constructor
  · assumption
  intro h
  apply h₁
  rw [h]
-- QUOTE.

/- OMIT:
In this example, the ``assumption`` tactic
tells Lean to find an assumption that will solve the goal.
Notice that the final ``rw`` finishes the goal by
applying the reflexivity of ``≤``.
The following are alternative ways of carrying out
the previous examples using the anonymous constructor
angle brackets.
The first is a slick proof-term version of the
previous proof,
which drops into tactic mode at the keyword ``by``.
OMIT. -/
/- TEXT:
.. index:: assumption, tactics ; assumption

この例では， ``assumption`` タクティクがLeanにゴールを解決する仮定を見つけるように指示しています．最後の ``rw`` で ``≤`` の反射性を適用してゴールを終了させていることに注意してください．以下は先程の例を無名コンストラクタを用いて解いた別解です．1つ目の例では証明項中で ``by`` キーワードを用いてタクティクモードに入るという技を使用しています．
TEXT. -/
-- QUOTE:
example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y :=
  ⟨h₀, fun h ↦ h₁ (by rw [h])⟩

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y :=
  have h : x ≠ y := by
    contrapose! h₁
    rw [h₁]
  ⟨h₀, h⟩
-- QUOTE.

/- OMIT:
*Using* a conjunction instead of proving one involves unpacking the proofs of the
two parts.
You can use the ``rcases`` tactic for that,
as well as ``rintro`` or a pattern-matching ``fun``,
all in a manner similar to the way they are used with
the existential quantifier.
OMIT. -/
/- TEXT:
連言を証明するのではなく *使う* には，その連言の証明を2つに展開する必要があります．これは存在量化子に対するのと同じように ``rcases`` タクティクや ``rintro`` ， ``fun`` のパターンマッチを使って行うことができます．
TEXT. -/
-- QUOTE:
example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  rcases h with ⟨h₀, h₁⟩
  contrapose! h₁
  exact le_antisymm h₀ h₁

example {x y : ℝ} : x ≤ y ∧ x ≠ y → ¬y ≤ x := by
  rintro ⟨h₀, h₁⟩ h'
  exact h₁ (le_antisymm h₀ h')

example {x y : ℝ} : x ≤ y ∧ x ≠ y → ¬y ≤ x :=
  fun ⟨h₀, h₁⟩ h' ↦ h₁ (le_antisymm h₀ h')
-- QUOTE.

/- OMIT:
In analogy to the ``obtain`` tactic, which we used with the existential
quantifier, there is also a pattern-matching ``have``:
OMIT. -/
/- TEXT:
存在量化子に対して ``obtain`` タクティクで行ったのと同様に ``have`` と無名コンストラクタを組み合わせてパターンマッチをすることができます:
TEXT. -/
-- QUOTE:
example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  have ⟨h₀, h₁⟩ := h
  contrapose! h₁
  exact le_antisymm h₀ h₁
-- QUOTE.

/- OMIT:
In contrast to ``rcases``, here the ``have`` tactic leaves ``h`` in the context.
And even though we won't use them, once again we have the computer scientists'
pattern-matching syntax:
OMIT. -/
/- TEXT:
``rcases`` とは異なり，ここで用いた ``have`` タクティクは ``h`` をローカルコンテキストに残します．また，今後本書では使いませんが，計算機科学におけるパターンマッチ構文を使用する例を今一度挙げましょう:
TEXT. -/
-- QUOTE:
example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  cases h
  case intro h₀ h₁ =>
    contrapose! h₁
    exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  cases h
  next h₀ h₁ =>
    contrapose! h₁
    exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  match h with
    | ⟨h₀, h₁⟩ =>
        contrapose! h₁
        exact le_antisymm h₀ h₁
-- QUOTE.

/- OMIT:
In contrast to using an existential quantifier,
you can also extract proofs of the two components
of a hypothesis ``h : A ∧ B``
by writing ``h.left`` and ``h.right``,
or, equivalently, ``h.1`` and ``h.2``.
OMIT. -/
/- TEXT:
存在量化子の使い方とは対照的に，仮定 ``h : A ∧ B`` の2つの構成要素を取り出すために ``h.left`` と ``h.right`` ，あるいは ``h.1`` と ``h.2`` と書くことができます．
TEXT. -/
-- QUOTE:
example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  intro h'
  apply h.right
  exact le_antisymm h.left h'

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x :=
  fun h' ↦ h.right (le_antisymm h.left h')
-- QUOTE.

/- OMIT:
Try using these techniques to come up with various ways of proving of the following:
OMIT. -/
/- TEXT:
これらのテクニックを使って以下の証明を行う方法をいろいろ考えてみましょう:
TEXT. -/
-- QUOTE:
example {m n : ℕ} (h : m ∣ n ∧ m ≠ n) : m ∣ n ∧ ¬n ∣ m :=
  sorry
-- QUOTE.

-- SOLUTIONS:
example {m n : ℕ} (h : m ∣ n ∧ m ≠ n) : m ∣ n ∧ ¬n ∣ m := by
  rcases h with ⟨h0, h1⟩
  constructor
  · exact h0
  intro h2
  apply h1
  apply Nat.dvd_antisymm h0 h2

/- OMIT:
You can nest uses of ``∃`` and ``∧``
with anonymous constructors, ``rintro``, and ``rcases``.
OMIT. -/
/- TEXT:
``rintro`` と ``rcases`` に無名コンストラクタを渡すことでネストした ``∃`` と ``∧`` を扱うことができます:
TEXT. -/
-- QUOTE:
example : ∃ x : ℝ, 2 < x ∧ x < 4 :=
  ⟨5 / 2, by norm_num, by norm_num⟩

example (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y := by
  rintro ⟨z, xltz, zlty⟩
  exact lt_trans xltz zlty

example (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y :=
  fun ⟨z, xltz, zlty⟩ ↦ lt_trans xltz zlty
-- QUOTE.

/- OMIT:
You can also use the ``use`` tactic:
OMIT. -/
/- TEXT:
``use`` タクティクを使うこともできます:
TEXT. -/
-- QUOTE:
example : ∃ x : ℝ, 2 < x ∧ x < 4 := by
  use 5 / 2
  constructor <;> norm_num

example : ∃ m n : ℕ, 4 < m ∧ m < n ∧ n < 10 ∧ Nat.Prime m ∧ Nat.Prime n := by
  use 5
  use 7
  norm_num

example {x y : ℝ} : x ≤ y ∧ x ≠ y → x ≤ y ∧ ¬y ≤ x := by
  rintro ⟨h₀, h₁⟩
  use h₀
  exact fun h' ↦ h₁ (le_antisymm h₀ h')
-- QUOTE.

/- OMIT:
In the first example, the semicolon after the ``constructor`` command tells Lean to use the
``norm_num`` tactic on both of the goals that result.

OMIT. -/
/- TEXT:
1つ目の例では， ``constructor`` の後ろのセミコロン ``<;>`` によってLeanに2つのゴールのどちらにも ``norm_num`` タクティクを用いるように指示しています．

TEXT. -/
/- OMIT:
In Lean, ``A ↔ B`` is *not* defined to be ``(A → B) ∧ (B → A)``,
but it could have been,
and it behaves roughly the same way.
You have already seen that you can write ``h.mp`` and ``h.mpr``
or ``h.1`` and ``h.2`` for the two directions of ``h : A ↔ B``.
You can also use ``cases`` and friends.
To prove an if-and-only-if statement,
you can uses ``constructor`` or angle brackets,
just as you would if you were proving a conjunction.
OMIT. -/
/- TEXT:
Leanでは ``A ↔ B`` は ``(A → B) ∧ (B → A)`` で定義されて *いません* が，そのような定義であっても良かったはずですし，実際にほぼ同じ振る舞いをします．ここまでですでに ``h : A ↔ B`` のそれぞれの方向を ``h.mp`` と ``h.mpr`` ，もしくは ``h.1`` と ``h.2`` でそれぞれ書けることを見てきました．また ``cases`` とそれに類するものも使えます．「〜ならば…が成り立つ．かつ…が成り立つのは～のときに限る」という命題を証明するには，連言を証明するときと同じように， ``constructor`` や角括弧（無名コンストラクタ）を使うことができます．
TEXT. -/
-- QUOTE:
example {x y : ℝ} (h : x ≤ y) : ¬y ≤ x ↔ x ≠ y := by
  constructor
  · contrapose!
    rintro rfl
    rfl
  contrapose!
  exact le_antisymm h

example {x y : ℝ} (h : x ≤ y) : ¬y ≤ x ↔ x ≠ y :=
  ⟨fun h₀ h₁ ↦ h₀ (by rw [h₁]), fun h₀ h₁ ↦ h₀ (le_antisymm h h₁)⟩
-- QUOTE.

/- OMIT:
The last proof term is inscrutable. Remember that you can
use underscores while writing an expression like that to
see what Lean expects.

OMIT. -/
/- TEXT:
最後の証明項は複雑でよくわからないことになっています．このような式を書くときにアンダースコアを使うと，Leanが何を期待しているかがわかることを覚えておきましょう．

TEXT. -/
/- OMIT:
Try out the various techniques and gadgets you have just seen
in order to prove the following:
OMIT. -/
/- TEXT:
以下を証明するためにこれまでに見てきた様々なテクニックや機能を試してみてください:
TEXT. -/
-- QUOTE:
example {x y : ℝ} : x ≤ y ∧ ¬y ≤ x ↔ x ≤ y ∧ x ≠ y :=
  sorry
-- QUOTE.

-- SOLUTIONS:
example {x y : ℝ} : x ≤ y ∧ ¬y ≤ x ↔ x ≤ y ∧ x ≠ y := by
  constructor
  · rintro ⟨h0, h1⟩
    constructor
    · exact h0
    intro h2
    apply h1
    rw [h2]
  rintro ⟨h0, h1⟩
  constructor
  · exact h0
  intro h2
  apply h1
  apply le_antisymm h0 h2

/- OMIT:
For a more interesting exercise, show that for any
two real numbers ``x`` and ``y``,
``x^2 + y^2 = 0`` if and only if ``x = 0`` and ``y = 0``.
We suggest proving an auxiliary lemma using
``linarith``, ``pow_two_nonneg``, and ``pow_eq_zero``.
OMIT. -/
/- TEXT:
さらに興味深い演習問題として，任意の2つの実数 ``x`` と ``y`` に対して， ``x^2 + y^2 = 0`` が ``x = 0`` と ``y = 0`` の場合にのみ成り立つことを示しましょう．ここでは ``linarith`` ， ``pow_two_nonneg`` ， ``pow_eq_zero`` を使って補助的な補題を証明することをお勧めします．
TEXT. -/
-- QUOTE:
theorem aux {x y : ℝ} (h : x ^ 2 + y ^ 2 = 0) : x = 0 :=
  have h' : x ^ 2 = 0 := by sorry
  pow_eq_zero h'

example (x y : ℝ) : x ^ 2 + y ^ 2 = 0 ↔ x = 0 ∧ y = 0 :=
  sorry
-- QUOTE.

-- SOLUTIONS:
theorem auxαα {x y : ℝ} (h : x ^ 2 + y ^ 2 = 0) : x = 0 :=
  have h' : x ^ 2 = 0 := by linarith [pow_two_nonneg x, pow_two_nonneg y]
  pow_eq_zero h'

example (x y : ℝ) : x ^ 2 + y ^ 2 = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    constructor
    · exact aux h
    rw [add_comm] at h
    exact aux h
  rintro ⟨rfl, rfl⟩
  norm_num

/- OMIT:
In Lean, bi-implication leads a double-life.
You can treat it like a conjunction and use its two
parts separately.
But Lean also knows that it is a reflexive, symmetric,
and transitive relation between propositions,
and you can also use it with ``calc`` and ``rw``.
It is often convenient to rewrite a statement to
an equivalent one.
In the next example, we use ``abs_lt`` to
replace an expression of the form ``|x| < y``
by the equivalent expression ``- y < x ∧ x < y``,
and in the one after that we use ``Nat.dvd_gcd_iff``
to replace an expression of the form ``m ∣ Nat.gcd n k`` by the equivalent expression ``m ∣ n ∧ m ∣ k``.
OMIT. -/
/- TEXT:
Leanでは，必要十分条件には二面性があります．まず，連言のように2つの部分を別々に使うことができます．しかしその一方で，Leanはこれを命題間の反射的，対称的，そして推移的な関係であることも知っており， ``calc`` や ``rw`` と一緒に使うこともできます．命題を同値なものに書き換えることができるのは多くのケースで便利です．次の例では， ``abs_lt`` を使って ``|x| < y`` の形の式を同値な ``- y < x ∧ x < y`` に書き換え，その次の例では ``Nat.dvd_gcd_iff`` を用いて ``m ∣ Nat.gcd n k`` の形の式を同値な ``m ∣ n ∧ m ∣ k`` に置き換えています．
TEXT. -/
section

-- QUOTE:
example (x : ℝ) : |x + 3| < 5 → -8 < x ∧ x < 2 := by
  rw [abs_lt]
  intro h
  constructor <;> linarith

example : 3 ∣ Nat.gcd 6 15 := by
  rw [Nat.dvd_gcd_iff]
  constructor <;> norm_num
-- QUOTE.

end

/- OMIT:
See if you can use ``rw`` with the theorem below
to provide a short proof that negation is not a
nondecreasing function. (Note that ``push_neg`` won't
unfold definitions for you, so the ``rw [Monotone]`` in
the proof of the theorem is needed.)
OMIT. -/
/- TEXT:
以下の定理で ``rw`` を使って，``-1`` 倍する関数が単調増加関数ではないことを簡単に証明できるか試してみましょう．（ ``push_neg`` が定義を展開してくれないため，定理の証明には ``rw [Monotone]`` が必要であることに注意してください．）
BOTH: -/
-- QUOTE:
theorem not_monotone_iff {f : ℝ → ℝ} : ¬Monotone f ↔ ∃ x y, x ≤ y ∧ f x > f y := by
  rw [Monotone]
  push_neg
  rfl

-- EXAMPLES:
example : ¬Monotone fun x : ℝ ↦ -x := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example : ¬Monotone fun x : ℝ ↦ -x := by
  rw [not_monotone_iff]
  use 0, 1
  norm_num

/- OMIT:
The remaining exercises in this section are designed
to give you some more practice with conjunction and
bi-implication. Remember that a *partial order* is a
binary relation that is transitive, reflexive, and
antisymmetric.
An even weaker notion sometimes arises:
a *preorder* is just a reflexive, transitive relation.
For any pre-order ``≤``,
Lean axiomatizes the associated strict pre-order by
``a < b ↔ a ≤ b ∧ ¬ b ≤ a``.
Show that if ``≤`` is a partial order,
then ``a < b`` is equivalent to ``a ≤ b ∧ a ≠ b``:
OMIT. -/
/- TEXT:
本節での最後の演習問題は連言と必要十分条件を練習するためのものです． *半順序* は推移的で反射的で反対称的な二項関係であることを思い出してください．これに対してより弱い概念である *前順序* は単に反射的で推移的な関係のことです．任意の前順序 ``≤`` について，Leanは対応する狭義の前順序 ``a < b`` を ``a < b ↔ a ≤ b ∧ ¬ b ≤ a`` で公理化しています．もし ``≤`` が半順序ならば， ``a < b`` は ``a ≤ b ∧ a ≠ b`` と等価であることを示しましょう:
TEXT. -/
-- BOTH:
section
-- QUOTE:
variable {α : Type*} [PartialOrder α]
variable (a b : α)

-- EXAMPLES:
example : a < b ↔ a ≤ b ∧ a ≠ b := by
  rw [lt_iff_le_not_le]
  sorry
-- QUOTE.

-- SOLUTIONS:
example : a < b ↔ a ≤ b ∧ a ≠ b := by
  rw [lt_iff_le_not_le]
  constructor
  · rintro ⟨h0, h1⟩
    constructor
    · exact h0
    intro h2
    apply h1
    rw [h2]
  rintro ⟨h0, h1⟩
  constructor
  · exact h0
  intro h2
  apply h1
  apply le_antisymm h0 h2

-- BOTH:
end

/- OMIT:
Beyond logical operations, you do not need
anything more than ``le_refl`` and ``le_trans``.
Show that even in the case where ``≤``
is only assumed to be a preorder,
we can prove that the strict order is irreflexive
and transitive.
In the second example,
for convenience, we use the simplifier rather than ``rw``
to express ``<`` in terms of ``≤`` and ``¬``.
We will come back to the simplifier later,
but here we are only relying on the fact that it will
use the indicated lemma repeatedly, even if it needs
to be instantiated to different values.
OMIT. -/
/- TEXT:
.. index:: simp, tactics ; simp

論理演算以外では ``le_refl`` と ``le_trans`` 以外は必要ではありません．ここで ``≤`` が前順序であることだけを仮定したとしても狭義の順序が非反射的で推移的であることを示しましょう．2つ目の例では， ``<`` を ``≤`` と ``¬`` を用いて表現するために便宜上 ``rw`` ではなく単純化のコマンドを用います．この単純化については後ほど説明しますが，ここでは単純化によって指定された補題はたとえ異なる値についてインスタンス化する必要がある場合でも繰り返し使用されるという事実のみを用います．
TEXT. -/
-- BOTH:
section
-- QUOTE:
variable {α : Type*} [Preorder α]
variable (a b c : α)

-- EXAMPLES:
example : ¬a < a := by
  rw [lt_iff_le_not_le]
  sorry

example : a < b → b < c → a < c := by
  simp only [lt_iff_le_not_le]
  sorry
-- QUOTE.

-- SOLUTIONS:
example : ¬a < a := by
  rw [lt_iff_le_not_le]
  rintro ⟨h0, h1⟩
  exact h1 h0

example : a < b → b < c → a < c := by
  simp only [lt_iff_le_not_le]
  rintro ⟨h0, h1⟩ ⟨h2, h3⟩
  constructor
  · apply le_trans h0 h2
  intro h4
  apply h1
  apply le_trans h2 h4

-- BOTH:
end
