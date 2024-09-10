import MIL.Common
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime
/- OMIT:
-- fix this.
-- import Mathlib.Data.Real.Irrational
BOTH: -/

/- OMIT:
Irrational Roots
----------------

OMIT: -/
/- TEXT:
.. _section_irrational_roots:

無理根
-----------

TEXT. -/
/- OMIT:
Let's start with a fact known to the ancient greeks, namely,
that the square root of 2 is irrational.
If we suppose otherwise,
we can write :math:`\sqrt{2} = a / b` as a fraction
in lowest terms. Squaring both sides yields :math:`a^2 = 2 b^2`,
which implies that :math:`a` is even.
If we write :math:`a = 2c`, then we get :math:`4c^2 = 2 b^2`
and hence :math:`b^2 = 2 c^2`.
This implies that :math:`b` is also even, contradicting
the fact that we have assumed that :math:`a / b` has been
reduced to lowest terms.

OMIT: -/
/- TEXT:
古代ギリシャの時代から知られていた事実から初めていきましょう．すなわち2の平方根が無理数であるということです．もしここでそうでないと仮定すると， :math:`\sqrt{2} = a / b` のようにとある既約分数として書くことができます．両辺を2乗すると :math:`a^2 = 2 b^2` となります．これは :math:`a` が偶数であることを意味します．そこで :math:`a = 2c` と書くと :math:`4c^2 = 2 b^2` となり整理して :math:`b^2 = 2 c^2` を得ます．これは :math:`b` も偶数であることを意味し， :math:`a / b` が既約分数という仮定に矛盾します．

TEXT. -/
/- OMIT:
Saying that :math:`a / b` is a fraction in lowest terms means
that :math:`a` and :math:`b` do not have any factors in common,
which is to say, they are *coprime*.
Mathlib defines the predicate ``Nat.coprime m n`` to be ``Nat.gcd m n = 1``.
Using Lean's anonymous projection notation, if ``s`` and ``t`` are
expressions of type ``Nat``, we can write ``s.coprime t`` instead of
``Nat.coprime s t``, and similarly for ``Nat.gcd``.
As usual, Lean will often unfold the definition of ``Nat.coprime`` automatically
when necessary,
but we can also do it manually by rewriting or simplifying with
the identifier ``Nat.coprime``.
The ``norm_num`` tactic is smart enough to compute concrete values.
OMIT. -/
/- TEXT:
:math:`a / b` が既約分数であるということは， :math:`a` と :math:`b` は共通の因数がない，つまり *互いに素* であることを意味します．Mathlibは述語 ``Nat.coprime m n`` を ``Nat.gcd m n = 1`` と定義しています．Leanの無名の射影による記法を使うと， ``s`` と ``t`` が ``Nat`` 型の式であれば， ``Nat.coprime s t`` の代わりに ``s.coprime t`` と書くことができます．これは ``Nat.gcd`` についても同様です．いつものように，Leanはしばしば ``Nat.coptime`` の定義を必要に応じて自動的に展開しますが， ``Nat.coprime`` 識別子を用いて手動で書き換えや単純化することもできます． ``norm_num`` タクティクは具体的な値を計算するにあたって十分な賢さを備えています．
EXAMPLES: -/
-- QUOTE:
#print Nat.coprime

example (m n : Nat) (h : m.coprime n) : m.gcd n = 1 :=
  h

example (m n : Nat) (h : m.coprime n) : m.gcd n = 1 := by
  rw [Nat.coprime] at h
  exact h

example : Nat.coprime 12 7 := by norm_num

example : Nat.gcd 12 8 = 4 := by norm_num
-- QUOTE.

/- OMIT:
We have already encountered the ``gcd`` function in
:numref:`more_on_order_and_divisibility`.
There is also a version of ``gcd`` for the integers;
we will return to a discussion of the relationship between
different number systems below.
There are even a generic ``gcd`` function and generic
notions of ``Prime`` and ``coprime``
that make sense in general classes of algebraic structures.
We will come to understand how Lean manages this generality
in the next chapter.
In the meanwhile, in this section, we will restrict attention
to the natural numbers.

OMIT: -/
/- TEXT:
関数 ``gcd`` についてはすでに :numref:`more_on_order_and_divisibility` で説明しました． ``gcd`` には整数用のバージョンも存在します．このような異なる数体系間の関係については後述します．また ``gcd`` 関数や ``Prime`` ， ``coprime`` にはさらに一般的な概念も存在し，一般的な代数構造で意味を持ちます．Leanがこの一般性をどのように管理しているかについては次の章で説明します．それまでにこの節では自然数に限定して説明しましょう．

TEXT. -/
/- OMIT:
We also need the notion of a prime number, ``Nat.Prime``.
The theorem ``Nat.prime_def_lt`` provides one familiar characterization,
and ``Nat.Prime.eq_one_or_self_of_dvd`` provides another.
OMIT. -/
/- TEXT:
また素数の概念 ``Nat.Prime`` も必要です．定理 ``Nat.prime_def_lt`` は素数についておなじみの特徴を定義します．また ``Nat.Prime.eq_one_or_self_of_dvd`` では別の特徴づけをしています．
EXAMPLES: -/
-- QUOTE:
#check Nat.prime_def_lt

example (p : ℕ) (prime_p : Nat.Prime p) : 2 ≤ p ∧ ∀ m : ℕ, m < p → m ∣ p → m = 1 := by
  rwa [Nat.prime_def_lt] at prime_p

#check Nat.Prime.eq_one_or_self_of_dvd

example (p : ℕ) (prime_p : Nat.Prime p) : ∀ m : ℕ, m ∣ p → m = 1 ∨ m = p :=
  prime_p.eq_one_or_self_of_dvd

example : Nat.Prime 17 := by norm_num

-- commonly used
example : Nat.Prime 2 :=
  Nat.prime_two

example : Nat.Prime 3 :=
  Nat.prime_three
-- QUOTE.

/- OMIT:
In the natural numbers, a prime number has the property that it cannot
be written as a product of nontrivial factors.
In a broader mathematical context, an element of a ring that has this property
is said to be *irreducible*.
An element of a ring is said to be *prime* if whenever it divides a product,
it divides one of the factors.
It is an important property of the natural numbers
that in that setting the two notions coincide,
giving rise to the theorem ``Nat.Prime.dvd_mul``.

OMIT: -/
/- TEXT:
自然数において，素数は自明ではない因数の積として書けないという性質を持っています．より広い数学的な文脈では，この性質を持つ環の元は *既約元* と呼ばれます．環のある元が *素数* であるとは，この元が積を割れる時，必ずその積の因数のいずれかを割ることができることを指します．この2つの概念は一致し，自然数の重要な性質として定理 ``Nat.Prime.dvd_mul`` に集約されます．

TEXT. -/
/- OMIT:
We can use this fact to establish a key property in the argument
above:
if the square of a number is even, then that number is even as well.
Mathlib defines the predicate ``Even`` in ``Data.Nat.Parity``,
but for reasons that will become clear below,
we will simply use ``2 ∣ m`` to express that ``m`` is even.
OMIT. -/
/- TEXT:
この事実は上記で行った議論の重要な性質を確立することができます．すなわちある数の2乗が偶数であれば，その数も偶数であるということです．Mathlibは ``Data.Nat.Parity`` にて述語 ``Even`` を定義していますが，後ほど説明する理由から，ここでは ``m`` が偶数であることを表現するために ``2 ∣ m`` を使用します．
EXAMPLES: -/
-- QUOTE:
#check Nat.Prime.dvd_mul
#check Nat.Prime.dvd_mul Nat.prime_two
#check Nat.prime_two.dvd_mul

-- BOTH:
theorem even_of_even_sqr {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m := by
  rw [pow_two, Nat.prime_two.dvd_mul] at h
  cases h <;> assumption

-- EXAMPLES:
example {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m :=
  Nat.Prime.dvd_of_dvd_pow Nat.prime_two h
-- QUOTE.

/- OMIT:
As we proceed, you will need to become proficient at finding the facts you
need.
Remember that if you can guess the prefix of the name and
you have imported the relevant library,
you can use tab completion (sometimes with ``ctrl-tab``) to find
what you are looking for.
You can use ``ctrl-click`` on any identifier to jump to the file
where it is defined, which enables you to browse definitions and theorems
nearby.
You can also use the search engine on the
`Lean community web pages <https://leanprover-community.github.io/>`_,
and if all else fails,
don't hesitate to ask on
`Zulip <https://leanprover.zulipchat.com/>`_.
OMIT. -/
/- TEXT:
本書を読み進めるにあたって，Mathlibから必要な事実や定理を見つける技量が必要になってきます．もし名前の接頭辞が推測でき，関連するMathlibをimportしているのであれば，タブ補完（ ``Ctrl+タブ`` を使うこともあります）を使って探しているものを見つけることができることを覚えておいてください．任意の識別子を ``Ctrl+クリック`` することでその識別子が定義されているファイルにジャンプすることができます．これでその識別子の定義とその近くにある定理を見ることが可能です．また `LeanのコミュニティのWEBページ <https://leanprover-community.github.io/>`_ にある検索エンジンを使うこともできますし，もし他の方法がうまくいかなかったら遠慮なく `Zulip <https://leanprover.zulipchat.com/>`_ で質問してください．
EXAMPLES: -/
-- QUOTE:
example (a b c : Nat) (h : a * b = a * c) (h' : a ≠ 0) : b = c :=
  -- apply? suggests the following:
  (mul_right_inj' h').mp h
-- QUOTE.

/- OMIT:
The heart of our proof of the irrationality of the square root of two
is contained in the following theorem.
See if you can fill out the proof sketch, using
``even_of_even_sqr`` and the theorem ``Nat.dvd_gcd``.
OMIT. -/
/- TEXT:
2の平方根が無理数であることの証明の核心は次の定理にあります．この証明について ``even_of_even_sqr`` と定理 ``Nat.dvd_gcd`` を使ってby以降を埋めてみましょう．
BOTH: -/
-- QUOTE:
example {m n : ℕ} (coprime_mn : m.coprime n) : m ^ 2 ≠ 2 * n ^ 2 := by
  intro sqr_eq
  have : 2 ∣ m := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    apply even_of_even_sqr
    rw [sqr_eq]
    apply dvd_mul_right
-- BOTH:
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp this
  have : 2 * (2 * k ^ 2) = 2 * n ^ 2 := by
    rw [← sqr_eq, meq]
    ring
  have : 2 * k ^ 2 = n ^ 2 :=
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    (mul_right_inj' (by norm_num)).mp this
-- BOTH:
  have : 2 ∣ n := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    apply even_of_even_sqr
    rw [← this]
    apply dvd_mul_right
-- BOTH:
  have : 2 ∣ m.gcd n := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    apply Nat.dvd_gcd <;>
    assumption
-- BOTH:
  have : 2 ∣ 1 := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    convert this
    symm
    exact coprime_mn
-- BOTH:
  norm_num at this
-- QUOTE.

/- OMIT:
In fact, with very few changes, we can replace ``2`` by an arbitrary prime.
Give it a try in the next example.
At the end of the proof, you'll need to derive a contradiction from
``p ∣ 1``.
You can use ``Nat.Prime.two_le``, which says that
any prime number is greater than or equal to two,
and ``Nat.le_of_dvd``.
OMIT. -/
/- TEXT:
実は僅かな変更でこれまでの議論の ``2`` を任意の素数に置き換えることができます．次の例で試してみましょう．証明の最後で ``p ∣ 1`` から矛盾を導く必要があります．ここで素数が2以上であるという ``Nat.Prime.two_le`` と ``Nat.le_of_dvd`` が使えます．
BOTH: -/
-- QUOTE:
example {m n p : ℕ} (coprime_mn : m.coprime n) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  intro sqr_eq
  have : p ∣ m := by
    apply prime_p.dvd_of_dvd_pow
    rw [sqr_eq]
    apply dvd_mul_right
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp this
  have : p * (p * k ^ 2) = p * n ^ 2 := by
    rw [← sqr_eq, meq]
    ring
  have : p * k ^ 2 = n ^ 2 := by
    apply (mul_right_inj' _).mp this
    exact prime_p.ne_zero
  have : p ∣ n := by
    apply prime_p.dvd_of_dvd_pow
    rw [← this]
    apply dvd_mul_right
  have : p ∣ Nat.gcd m n := by apply Nat.dvd_gcd <;> assumption
  have : p ∣ 1 := by
    convert this
    symm
    exact coprime_mn
  have : 2 ≤ 1 := by
    apply prime_p.two_le.trans
    exact Nat.le_of_dvd zero_lt_one this
  norm_num at this
-- QUOTE.

-- BOTH:
/- OMIT:
Let us consider another approach.
Here is a quick proof that if :math:`p` is prime, then
:math:`m^2 \ne p n^2`: if we assume :math:`m^2 = p n^2`
and consider the factorization of :math:`m` and :math:`n` into primes,
then :math:`p` occurs an even number of times on the left side of the equation
and an odd number of times on the right, a contradiction.
Note that this argument requires that :math:`n` and hence :math:`m`
are not equal to zero.
The formalization below confirms that this assumption is sufficient.

OMIT: -/
/- TEXT:
別のアプローチを考えてみましょう． :math:`p` が素数のときに :math:`m^2 = p n^2` を仮定すると， :math:`m` と :math:`n` の素因数分解を考えることで :math:`p` は方程式の左辺に偶数回，右辺に奇数回出現し，矛盾することから :math:`m^2 \ne p n^2`: となります．ここでこの議論は :math:`n` と :math:`m` が0ではないことを仮定している点に注意してください．この仮定は以下の定式化で十分であることが確認されます．

TEXT. -/
/- OMIT:
The unique factorization theorem says that any natural number other
than zero can be written as the product of primes in a unique way.
Mathlib contains a formal version of this, expressed in terms of a function
``Nat.factors``, which returns the list of
prime factors of a number in nondecreasing order.
The library proves that all the elements of ``Nat.factors n``
are prime, that any ``n`` greater than zero is equal to the
product of its factors,
and that if ``n`` is equal to the product of another list of prime numbers,
then that list is a permutation of ``Nat.factors n``.
OMIT. -/
/- TEXT:
素因数分解の一意性とは，0以外の自然数は素数の積として一意に書けるというものです．Mathlibにはこの定理が正式に含まれており， ``Nat.factors`` という関数で表現され，与えられた数の素因数を小さい順に並べたリストを返します．Mathlibは ``Nat.factors n`` のすべての要素が素数であること，0より大きい ``n`` はその因数の積に等しいこと，そして ``n`` が他の素数のリストの積に等しい場合，そのリストは ``Nat.factors n`` の結果を順列に並べ替えたものであることを証明します．
EXAMPLES: -/
-- QUOTE:
#check Nat.factors
#check Nat.prime_of_mem_factors
#check Nat.prod_factors
#check Nat.factors_unique
-- QUOTE.

/- OMIT:
You can browse these theorems and others nearby, even though we have not
talked about list membership, products, or permutations yet.
We won't need any of that for the task at hand.
We will instead use the fact that Mathlib has a function ``Nat.factorization``,
that represents the same data as a function.
Specifically, ``Nat.factorization n p``, which we can also write
``n.factorization p``, returns the multiplicity of ``p`` in the prime
factorization of ``n``. We will use the following three facts.
OMIT. -/
/- TEXT:
これらの定理や他の定理についてその定義等を見ることができますが，リストの要素の参照や積，順列の話はまだしていません．ですがさしあたって今の問題においてはそれらの知識は不要です．その代わりに，Mathlibには同じデータを関数として表現する関数 ``Nat.factorization`` があることを利用します．具体的には， ``Nat.factorization n p`` (これは ``n.factorization p`` と書くこともできます)は ``n`` の素因数分解における ``p`` の指数を返します．この関数について以下の3つの事実を用います．
BOTH: -/
-- QUOTE:
theorem factorization_mul' {m n : ℕ} (mnez : m ≠ 0) (nnez : n ≠ 0) (p : ℕ) :
    (m * n).factorization p = m.factorization p + n.factorization p := by
  rw [Nat.factorization_mul mnez nnez]
  rfl

theorem factorization_pow' (n k p : ℕ) :
    (n ^ k).factorization p = k * n.factorization p := by
  rw [Nat.factorization_pow]
  rfl

theorem Nat.Prime.factorization' {p : ℕ} (prime_p : p.Prime) :
    p.factorization p = 1 := by
  rw [prime_p.factorization]
  simp
-- QUOTE.

/- OMIT:
In fact, ``n.factorization`` is defined in Lean as a function of finite support,
which explains the strange notation you will see as you step through the
proofs above. Don't worry about this now. For our purposes here, we can use
the three theorems above as a black box.

OMIT: -/
/- TEXT:
上記の証明をステップごとに見ていくと奇妙な表記を見かけるでしょうが，これは ``n.factorization`` はLeanでは有限台として定義されているからです．ひとまず今はこのことを気にする必要はありません．ここでの目的では，上3つの定理の中身を気にせずブラックボックスとして使うことができます．

TEXT. -/
/- OMIT:
The next example shows that the simplifier is smart enough to replace
``n^2 ≠ 0`` by ``n ≠ 0``. The tactic ``simpa`` just calls ``simp``
followed by ``assumption``.

OMIT: -/
/- TEXT:
次の例は ``simp`` を使うことで ``n^2 ≠ 0`` が ``n ≠ 0`` に置き換えられることを示しています． ``simpa`` タクティクはただ単に ``simp`` タクティクのあとに ``assumption`` タクティクを呼んでいるだけです．

TEXT. -/
/- OMIT:
See if you can use the identities above to fill in the missing parts
of the proof.
OMIT: -/
/- TEXT:
証明中の抜けている箇所を埋めてみましょう．
BOTH: -/
-- QUOTE:
example {m n p : ℕ} (nnz : n ≠ 0) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
  intro sqr_eq
  have nsqr_nez : n ^ 2 ≠ 0 := by simpa
  have eq1 : Nat.factorization (m ^ 2) p = 2 * m.factorization p := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    rw [factorization_pow']
-- BOTH:
  have eq2 : (p * n ^ 2).factorization p = 2 * n.factorization p + 1 := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    rw [factorization_mul' prime_p.ne_zero nsqr_nez, prime_p.factorization', factorization_pow',
      add_comm]
-- BOTH:
  have : 2 * m.factorization p % 2 = (2 * n.factorization p + 1) % 2 := by
    rw [← eq1, sqr_eq, eq2]
  rw [add_comm, Nat.add_mul_mod_self_left, Nat.mul_mod_right] at this
  norm_num at this
-- QUOTE.

/- OMIT:
A nice thing about this proof is that it also generalizes. There is
nothing special about ``2``; with small changes, the proof shows that
whenever we write ``m^k = r * n^k``, the multiplicity of any prime ``p``
in ``r`` has to be a multiple of ``k``.

OMIT: -/
/- TEXT:
この証明のいいところは一般化できる点です．ちょっと変えるだけで ``m^k = r * n^k`` と書いたなら， ``r`` の任意の素数 ``p`` の倍数はかならず ``k`` の倍数でなければならないことを示す証明となり， ``k`` は ``2`` である必要はどこにもなくなります．

TEXT. -/
/- OMIT:
To use ``Nat.count_factors_mul_of_pos`` with ``r * n^k``,
we need to know that ``r`` is positive.
But when ``r`` is zero, the theorem below is trivial, and easily
proved by the simplifier.
So the proof is carried out in cases.
The line ``cases r with r`` replaces the goal with two versions:
one in which ``r`` is replaced by ``0``,
and the other in which ``r`` is replaces by ``r.succ``,
the successor of ``r``.
In the second case, we can use the theorem ``r.succ_ne_zero``, which
establishes ``r.succ ≠ 0``.

OMIT: -/
/- TEXT:
``Nat.count_factors_mul_of_pos`` を ``r * n^k`` と一緒に使うには， ``r`` が正であることを知っている必要があります．しかし ``r`` が0の場合，以下の定理は自明であり， ``simp`` で簡単に証明できます．そこで証明は場合分けして行うことにします．一つは ``r`` を ``0`` に置き換えるもので，もう一つは ``r`` を ``r.succ`` に置き換えるものです．後者の場合，定理 ``r.succ_ne_zero`` を使うことができ， ``r.succ ≠ 0`` が成立します．

TEXT. -/
/- OMIT:
Notice also that the line that begins ``have : npow_nz`` provides a
short proof-term proof of ``n^k ≠ 0``.
To understand how it works, try replacing it with a tactic proof,
and then think about how the tactics describe the proof term.

OMIT: -/
/- TEXT:
また ``have : npow_nz`` から始まる行が ``n^k ≠ 0`` の短い証明項の証明になっていることにも注目してください．この項がどのように機能するかを理解するために，これをタクティクによる証明でどのように記述されるかを考えてみましょう．

TEXT. -/
/- OMIT:
See if you can fill in the missing parts of the proof below.
At the very end, you can use ``Nat.dvd_sub'`` and ``Nat.dvd_mul_right``
to finish it off.
OMIT: -/
/- TEXT:
以下の証明の欠けている部分を埋めてみましょう．証明の一番最後は ``Nat.dvd_sub'`` と ``Nat.dvd_mul_right`` で完成させることができます．
BOTH: -/
-- QUOTE:
example {m n k r : ℕ} (nnz : n ≠ 0) (pow_eq : m ^ k = r * n ^ k) {p : ℕ} (prime_p : p.Prime) :
    k ∣ r.factorization p := by
  rcases r with _ | r
  · simp
  have npow_nz : n ^ k ≠ 0 := fun npowz ↦ nnz (pow_eq_zero npowz)
  have eq1 : (m ^ k).factorization p = k * m.factorization p := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    rw [factorization_pow']
-- BOTH:
  have eq2 : (r.succ * n ^ k).factorization p =
      k * n.factorization p + r.succ.factorization p := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    rw [factorization_mul' r.succ_ne_zero npow_nz, factorization_pow', add_comm]
-- BOTH:
  have : r.succ.factorization p = k * m.factorization p - k * n.factorization p := by
    rw [← eq1, pow_eq, eq2, add_comm, Nat.add_sub_cancel]
  rw [this]
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  apply Nat.dvd_sub' <;>
  apply Nat.dvd_mul_right
-- BOTH:
-- QUOTE.

/- OMIT:
There are a number of ways in which we might want to improve on these results.
To start with, a proof that the square root of two is irrational
should say something about the square root of two,
which can be understood as an element of the
real or complex numbers.
And stating that it is irrational should say something about the
rational numbers, namely, that no rational number is equal to it.
Moreover, we should extend the theorems in this section to the integers.
Although it is mathematically obvious that if we could write the square root of
two as a quotient of two integers then we could write it as a quotient
of two natural numbers,
proving this formally requires some effort.

OMIT: -/
/- TEXT:
ここまで行ってきた証明について改善するポイントがいくつかあります．まずはじめに，2の平方根が無理数であることの証明は，2の平方根そのものについて語るべきであり，これは実数または複素数の要素として理解されています．そして2の平方根が無理数であることを証明することは有理数について語るべきであり，すなわち2の平方根に等しい有理数は無いということを示すはずです．さらにこの節の定理を整数に拡張する必要があります．もし2の平方根を2つの整数の商として書くことができれば，自然数の商としても書くことができるのは数学的に明らかですが，これを正式に証明するには多少の努力が必要です．

TEXT. -/
/- OMIT:
In Mathlib, the natural numbers, the integers, the rationals, the reals,
and the complex numbers are represented by separate data types.
Restricting attention to the separate domains is often helpful:
we will see that it is easy to do induction on the natural numbers,
and it is easiest to reason about divisibility of integers when the
real numbers are not part of the picture.
But having to mediate between the different domains is a headache,
one we will have to contend with.
We will return to this issue later in this chapter.

OMIT: -/
/- TEXT:
Mathlibでは，自然数と整数，有理数，実数，複素数はすべて別々のデータ型で表現されます．このように分けられた領域ごとに注意を向けるのはしばしば有用です．例えば自然数に対して帰納法を適用するのは簡単であり，実数をふくまない整数の割り算を推論することも非常に簡単です．しかし，異なる領域にまたがる議論は頭痛の種であり，これは私達が対処しなければならない問題です．この問題については章の後半で触れることにします．

TEXT. -/
/- OMIT:
We should also expect to be able to strengthen the conclusion of the
last theorem to say that the number ``r`` is a ``k``-th power,
since its ``k``-th root is just the product of each prime dividing ``r``
raised to its multiplicity in ``r`` divided by ``k``.
To be able to do that we will need better means for reasoning about
products and sums over a finite set,
which is also a topic we will return to.

OMIT: -/
/- TEXT:
最後の定理については ``r`` は ``k`` 乗された数であるという結論に強化できることを期待するでしょう．なぜなら ``r`` の ``k`` 乗根は ``r`` を分割する各素数の積であり，これらの素数の ``r`` での指数は ``k`` で割ることができるからです．これを可能にするには有限集合上の積と和についての推論のためのより良い手段が必要です．この話題についても後ほど触れます．

TEXT. -/
/- OMIT:
In fact, the results in this section are all established in much
greater generality in Mathlib,
in ``Data.Real.Irrational``.
The notion of ``multiplicity`` is defined for an
arbitrary commutative monoid,
and that it takes values in the extended natural numbers ``enat``,
which adds the value infinity to the natural numbers.
In the next chapter, we will begin to develop the means to
appreciate the way that Lean supports this sort of generality.
OMIT: -/
/- TEXT:
実際，この節の結果はすべてMathlibの ``Data.Real.Irreational`` で遥かに一般的なものとして確立されています． ``multiplicity`` の概念は任意の可換モノイドに対して定義され，そこで使える概念も無限大の値を追加して拡張された自然数 ``enat`` を受け取るようになっています．次の章ではLeanがこのような一般正をサポートする方法を理解するために実際に実装をしていきましょう．
EXAMPLES: -/
#check multiplicity

-- OMIT: TODO: add when available
-- #check irrational_nrt_of_n_not_dvd_multiplicity

-- #check irrational_sqrt_two

-- OMIT:
-- TODO: use this in the later section and then delete here.
#check Rat.num
#check Rat.den

section
variable (r : ℚ)

#check r.num
#check r.den
#check r.pos
#check r.reduced

#check Rat.num_den'

end

-- example (r : ℚ) : r ^ 2 ≠ 2 := by
--   rw [← r.num_div_denom, div_pow]
--   have : (r.denom : ℚ) ^ 2 > 0 := by
--     norm_cast
--     apply pow_pos r.pos
--   have := Ne.symm (ne_of_lt this)
--   intro h
--   field_simp [this]  at h
--   norm_cast  at h
--   sorry
