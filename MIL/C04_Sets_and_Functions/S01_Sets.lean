-- BOTH:
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Prime.Basic
import MIL.Common

/- OMIT:
Sets
----

OMIT. -/
/- TEXT:
.. _sets:

集合
-----

.. index:: set operations

TEXT. -/
/- OMIT:
If ``α`` is any type, the type ``Set α`` consists of sets
of elements of ``α``.
This type supports the usual set-theoretic operations and relations.
For example, ``s ⊆ t`` says that ``s`` is a subset of ``t``,
``s ∩ t`` denotes the intersection of ``s`` and ``t``,
and ``s ∪ t`` denotes their union.
The subset relation can be typed with ``\ss`` or ``\sub``,
intersection can be typed with ``\i`` or ``\cap``,
and union can be typed with ``\un`` or ``\cup``.
The library also defines the set ``univ``,
which consists of all the elements of type ``α``,
and the empty set, ``∅``, which can be typed as ``\empty``.
Given ``x : α`` and ``s : Set α``,
the expression ``x ∈ s`` says that ``x`` is a member of ``s``.
Theorems that mention set membership often include ``mem``
in their name.
The expression ``x ∉ s`` abbreviates ``¬ x ∈ s``.
You can type ``∈`` as ``\in`` or ``\mem`` and ``∉`` as ``\notin``.

OMIT. -/
/- TEXT:
``α`` が型であるとき， ``Set α`` 型は ``α`` の要素からなる集合の集まりです．この型は通常の集合論的な操作や関係をサポートしています．例えば ``s ⊆ t`` は ``s`` が ``t`` の部分集合であること， ``s ∩ t`` は ``s`` と ``t`` の共通部分， ``s ∪ t`` は ``s`` と ``t`` の合併を表します．部分集合の関係は ``\ss`` か ``\sub`` で，共通部分は ``\i`` もしくは ``\cap`` ，合併は ``\un`` か ``\cup`` で入力できます．またMathlibは ``univ`` という集合も定義しています．これは ``α`` のすべての要素からなる集合です．そして ``\empty`` で入力される空集合 ``∅`` も定義しています． ``x : α`` と ``s : Set α`` が与えられた時，式 ``x ∈ s`` は ``x`` が ``s`` のメンバーであることを表します．集合の所属関係に言及する定理は，しばしばその名前に ``mem`` を含みます．式 ``x ∉ s`` は ``¬ x ∈ s`` を省略したものです． ``∈`` は ``\in`` か ``\mem`` で， ``∉`` は ``\notin`` で入力できます．

.. index:: simp, tactics ; simp

TEXT. -/
/- OMIT:
One way to prove things about sets is to use ``rw``
or the simplifier to expand the definitions.
In the second example below, we use ``simp only``
to tell the simplifier to use only the list
of identities we give it,
and not its full database of identities.
Unlike ``rw``, ``simp`` can perform simplifications
inside a universal or existential quantifier.
If you step through the proof,
you can see the effects of these commands.
OMIT. -/
/- TEXT:
集合について証明する一つの方法は， ``rw`` や ``simp`` を使って定義を展開することです．以下の2つ目の例では， ``simp only`` を使うことで ``simp`` がLean内部にある等式についてのデータベース全体ではなく，指定した等式のリストだけを使うようにしています． ``rw`` とは異なり， ``simp`` は全称量化子や存在量化子の中でも単純化を行うことができます．以下の証明を一行ずつたどれば，これらのタクティクの効果を見ることができます．
TEXT. -/
-- BOTH:
section
-- QUOTE:
variable {α : Type*}
variable (s t u : Set α)
open Set

-- EXAMPLES:
example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rw [subset_def, inter_def, inter_def]
  rw [subset_def] at h
  simp only [mem_setOf]
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  simp only [subset_def, mem_inter_iff] at *
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩
-- QUOTE.

/- OMIT:
In this example, we open the ``set`` namespace to have
access to the shorter names for the theorems.
But, in fact, we can delete the calls to ``rw`` and ``simp``
entirely:
OMIT. -/
/- TEXT:
この例では，定理の短い名前にアクセスするために ``Set`` 名前空間を開いています．しかし，実は ``rw`` と ``simp`` の呼び出しは削除することができます．
TEXT. -/
-- QUOTE:
example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  intro x xsu
  exact ⟨h xsu.1, xsu.2⟩
-- QUOTE.

/- OMIT:
What is going on here is known as *definitional reduction*:
to make sense of the ``intro`` command and the anonymous constructors
Lean is forced to expand the definitions.
The following example also illustrate the phenomenon:
OMIT. -/
/- TEXT:
ここで行われたことは **定義に基づく簡約** （definitional reduction）として知られるもので， ``intro`` コマンドとその後の無名コンストラクタの意味が通るようにLeanが定義を自動で展開しています．下記の例でも同じ現象が発生しています:
TEXT. -/
-- QUOTE:
example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  fun x ⟨xs, xu⟩ ↦ ⟨h xs, xu⟩
-- QUOTE.

/- OMIT:
To deal with unions, we can use ``Set.union_def`` and ``Set.mem_union``.
Since ``x ∈ s ∪ t`` unfolds to ``x ∈ s ∨ x ∈ t``,
we can also use the ``cases`` tactic to force a definitional reduction.
OMIT. -/
/- TEXT:
合併を扱うには， ``Set.union_def`` と ``Set.mem_union`` を使うことができます． ``x ∈ s ∪ t`` は ``x ∈ s ∨ x ∈ t`` に展開されるため， ``cases`` タクティクを使って強制的に定義に基づく簡約を行うこともできます．
TEXT. -/
-- QUOTE:
example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  intro x hx
  have xs : x ∈ s := hx.1
  have xtu : x ∈ t ∪ u := hx.2
  rcases xtu with xt | xu
  · left
    show x ∈ s ∩ t
    exact ⟨xs, xt⟩
  · right
    show x ∈ s ∩ u
    exact ⟨xs, xu⟩
-- QUOTE.

/- OMIT:
Since intersection binds tighter than union,
the use of parentheses in the expression ``(s ∩ t) ∪ (s ∩ u)``
is unnecessary, but they make the meaning of the expression clearer.
The following is a shorter proof of the same fact:
OMIT. -/
/- TEXT:
共通部分は合併よりも強く結合するため， ``(s ∩ t) ∪ (s ∩ u)`` という式に括弧を使う必要はありませんが，括弧を使うことで式の意味がより明確になります．以下は同じ事実のより短い証明です:
TEXT. -/
-- QUOTE:
example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  rintro x ⟨xs, xt | xu⟩
  · left; exact ⟨xs, xt⟩
  · right; exact ⟨xs, xu⟩
-- QUOTE.

/- OMIT:
As an exercise, try proving the other inclusion:
OMIT. -/
/- TEXT:
演習問題として，もう一方の包含を証明してみましょう:
BOTH: -/
-- QUOTE:
example : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  rintro x (⟨xs, xt⟩ | ⟨xs, xu⟩)
  · use xs; left; exact xt
  · use xs; right; exact xu
-- QUOTE.

-- BOTH:
/- OMIT:
It might help to know that when using ``rintro``,
sometimes we need to use parentheses around a disjunctive pattern
``h1 | h2`` to get Lean to parse it correctly.

OMIT. -/
/- TEXT:
``rintro`` を使う時，パースが正しく行われるように，選言のパターン ``h1 | h2`` を括弧で囲む必要があることを知っておくと良いでしょう．

TEXT. -/
/- OMIT:
The library also defines set difference, ``s \ t``,
where the backslash is a special unicode character
entered as ``\\``.
The expression ``x ∈ s \ t`` expands to ``x ∈ s ∧ x ∉ t``.
(The ``∉`` can be entered as ``\notin``.)
It can be rewritten manually using ``Set.diff_eq`` and ``dsimp``
or ``Set.mem_diff``,
but the following two proofs of the same inclusion
show how to avoid using them.
OMIT. -/
/- TEXT:
Mathlibでは ``s \ t`` で表される差集合も定義されています．ここでバックスラッシュは ``\\`` で入力される特別なUnicode文字です．式 ``x ∈ s \ t`` は ``x ∈ s ∧ x ∉ t`` に展開されます．（ ``∉`` は ``\notin`` で入力できます．）この定義は ``Set.diff_eq`` や ``dsimp`` や ``Set.mem_diff`` を使って手動で展開することもできますが，使わないこともできます．以下の包含関係に関する命題では，これを避ける方法で２通りの証明を示します．
TEXT. -/
-- QUOTE:
example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  intro x xstu
  have xs : x ∈ s := xstu.1.1
  have xnt : x ∉ t := xstu.1.2
  have xnu : x ∉ u := xstu.2
  constructor
  · exact xs
  intro xtu
  -- x ∈ t ∨ x ∈ u
  rcases xtu with xt | xu
  · show False; exact xnt xt
  · show False; exact xnu xu

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  rintro x ⟨⟨xs, xnt⟩, xnu⟩
  use xs
  rintro (xt | xu) <;> contradiction
-- QUOTE.

/- OMIT:
As an exercise, prove the reverse inclusion:
OMIT. -/
/- TEXT:
演習問題として，反対向きの包含を証明してみましょう:
BOTH: -/
-- QUOTE:
example : s \ (t ∪ u) ⊆ (s \ t) \ u := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  rintro x ⟨xs, xntu⟩
  constructor
  use xs
  · intro xt
    exact xntu (Or.inl xt)
  intro xu
  apply xntu (Or.inr xu)
-- QUOTE.

-- BOTH:
/- OMIT:
To prove that two sets are equal,
it suffices to show that every element of one is an element
of the other.
This principle is known as "extensionality,"
and, unsurprisingly,
the ``ext`` tactic is equipped to handle it.
OMIT. -/
/- TEXT:
2つの集合が等しいことを証明するには，一方の集合のすべての要素がもう片方の集合の要素であることを示せば十分です．この原理は「外延性（extensionality）」として知られており，名前としてはそのまま ``ext`` タクティクでこれを扱うことができます．
TEXT. -/
-- QUOTE:
example : s ∩ t = t ∩ s := by
  ext x
  simp only [mem_inter_iff]
  constructor
  · rintro ⟨xs, xt⟩; exact ⟨xt, xs⟩
  · rintro ⟨xt, xs⟩; exact ⟨xs, xt⟩
-- QUOTE.

/- OMIT:
Once again, deleting the line ``simp only [mem_inter_iff]``
does not harm the proof.
In fact, if you like inscrutable proof terms,
the following one-line proof is for you:
OMIT. -/
/- TEXT:
繰り返しになりますが， ``simp only [mem_inter_iff]`` の行を削除しても証明には影響しません．実際，証明項による難解な証明で構わなければ，次のように1行で証明できます:
TEXT. -/

-- QUOTE:
example : s ∩ t = t ∩ s :=
  Set.ext fun x ↦ ⟨fun ⟨xs, xt⟩ ↦ ⟨xt, xs⟩, fun ⟨xt, xs⟩ ↦ ⟨xs, xt⟩⟩
-- QUOTE.

/- OMIT:
Here is an even shorter proof,
using the simplifier:
OMIT. -/
/- TEXT:
以下は ``simp`` を使ったさらに短い証明です:
TEXT. -/
-- QUOTE:
example : s ∩ t = t ∩ s := by ext x; simp [and_comm]
-- QUOTE.

/- OMIT:
An alternative to using ``ext`` is to use
the theorem ``Subset.antisymm``
which allows us to prove an equation ``s = t``
between sets by proving ``s ⊆ t`` and ``t ⊆ s``.
OMIT. -/
/- TEXT:
``ext`` の代わりに ``s ⊆ t`` と ``t ⊆ s`` の証明から集合間の等式 ``s = t`` を導出する定理 ``Subset.antisymm`` を使うことができます．
TEXT. -/
-- QUOTE:
example : s ∩ t = t ∩ s := by
  apply Subset.antisymm
  · rintro x ⟨xs, xt⟩; exact ⟨xt, xs⟩
  · rintro x ⟨xt, xs⟩; exact ⟨xs, xt⟩
-- QUOTE.

/- OMIT:
Try finishing this proof term:
OMIT. -/
/- TEXT:
これの証明項バージョンを完成させてみましょう:
BOTH: -/
-- QUOTE:
example : s ∩ t = t ∩ s :=
/- EXAMPLES:
    Subset.antisymm sorry sorry
SOLUTIONS: -/
    Subset.antisymm
    (fun x ⟨xs, xt⟩ ↦ ⟨xt, xs⟩) fun x ⟨xt, xs⟩ ↦ ⟨xs, xt⟩
-- QUOTE.

-- BOTH:
/- OMIT:
Remember that you can replace `sorry` by an underscore,
and when you hover over it,
Lean will show you what it expects at that point.

OMIT. -/
/- TEXT:
上記で `sorry` をアンダースコアで書き換えてその上にカーソルを置くと，Leanがその時点で何を期待しているかが表示されることを覚えておいてください．

TEXT. -/
/- OMIT:
Here are some set-theoretic identities you might enjoy proving:
OMIT. -/
/- TEXT:
以下の集合論的な等式の証明は楽しいかもしれません:
TEXT. -/
-- QUOTE:
example : s ∩ (s ∪ t) = s := by
  sorry

example : s ∪ s ∩ t = s := by
  sorry

example : s \ t ∪ t = s ∪ t := by
  sorry

example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example : s ∩ (s ∪ t) = s := by
  ext x; constructor
  · rintro ⟨xs, _⟩
    exact xs
  · intro xs
    use xs; left; exact xs

example : s ∪ s ∩ t = s := by
  ext x; constructor
  · rintro (xs | ⟨xs, xt⟩) <;> exact xs
  · intro xs; left; exact xs

example : s \ t ∪ t = s ∪ t := by
  ext x; constructor
  · rintro (⟨xs, nxt⟩ | xt)
    · left
      exact xs
    · right
      exact xt
  by_cases h : x ∈ t
  · intro
    right
    exact h
  rintro (xs | xt)
  · left
    use xs
  right; exact xt

example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  ext x; constructor
  · rintro (⟨xs, xnt⟩ | ⟨xt, xns⟩)
    · constructor
      left
      exact xs
      rintro ⟨_, xt⟩
      contradiction
    · constructor
      right
      exact xt
      rintro ⟨xs, _⟩
      contradiction
  rintro ⟨xs | xt, nxst⟩
  · left
    use xs
    intro xt
    apply nxst
    constructor <;> assumption
  · right; use xt; intro xs
    apply nxst
    constructor <;> assumption

/- OMIT:
When it comes to representing sets,
here is what is going on underneath the hood.
In type theory, a *property* or *predicate* on a type ``α``
is just a function ``P : α → Prop``.
This makes sense:
given ``a : α``, ``P a`` is just the proposition
that ``P`` holds of ``a``.
In the library, ``Set α`` is defined to be ``α → Prop`` and ``x ∈ s`` is defined to be ``s x``.
In other words, sets are really properties, treated as objects.

OMIT. -/
/- TEXT:
Leanで集合を表現するとき，その裏で何が行われているのか説明しましょう．型理論において，ある型 ``α`` の **性質** （property）や **述語** （predicate）は単なる関数 ``P : α → Prop`` です．これは理にかなっています: ``a : α`` が与えられた時， ``P a`` はまさに ``a`` に対して ``P`` が成り立っているという命題に他ならないからです．Mathlibでは ``Set α`` は ``α → Prop`` と定義され， ``x ∈ s`` は ``s x`` と定義されます．言い換えれば，集合は性質であり，対象として扱われます．

TEXT. -/
/- OMIT:
The library also defines set-builder notation.
The expression ``{ y | P y }`` unfolds to ``(fun y ↦ P y)``,
so ``x ∈ { y | P y }`` reduces to ``P x``.
So we can turn the property of being even into the set of even numbers:
OMIT. -/
/- TEXT:
ライブラリでは集合の内包表記も定義しています．式 ``{ y | P y }`` は ``(fun y ↦ P y)`` に展開されます．したがって， ``x ∈ { y | P y }`` は ``P x`` に簡約されます．これを用いて偶数であるという性質を偶数の集合に変えることができます:
TEXT. -/
-- QUOTE:
def evens : Set ℕ :=
  { n | Even n }

def odds : Set ℕ :=
  { n | ¬Even n }

example : evens ∪ odds = univ := by
  rw [evens, odds]
  ext n
  simp [-Nat.not_even_iff_odd]
  apply Classical.em
-- QUOTE.

/- OMIT:
You should step through this proof and make sure
you understand what is going on.
Note we tell the simplifier to *not* use the lemma
``Nat.not_even_iff`` because we want to keep
``¬ Even n`` in our goal.
Try deleting the line ``rw [evens, odds]``
and confirm that the proof still works.

OMIT. -/
/- TEXT:
この証明を順を追って見て，何が起こっているのか理解してください．そして ``rw [evens, odds]`` の行を削除しても証明がまだ機能することを確認してください．

TEXT. -/
/- OMIT:
In fact, set-builder notation is used to define

OMIT. -/
/- TEXT:
実際，内包表記は以下を定義する際に用いられています．

TEXT. -/
/- OMIT:
- ``s ∩ t`` as ``{x | x ∈ s ∧ x ∈ t}``,
- ``s ∪ t`` as ``{x | x ∈ s ∨ x ∈ t}``,
- ``∅`` as ``{x | False}``, and
- ``univ`` as ``{x | True}``.

OMIT. -/
/- TEXT:
- ``s ∩ t`` は ``{x | x ∈ s ∧ x ∈ t}`` で定義されます．
- ``s ∪ t`` は ``{x | x ∈ s ∨ x ∈ t}`` で定義されます．
- ``∅`` は ``{x | False}`` で定義されます．
- ``univ`` は ``{x | True}`` で定義されます．

TEXT. -/
/- OMIT:
We often need to indicate the type of ``∅`` and ``univ``
explicitly,
because Lean has trouble guessing which ones we mean.
The following examples show how Lean unfolds the last
two definitions when needed. In the second one,
``trivial`` is the canonical proof of ``True`` in the library.
OMIT. -/
/- TEXT:
``∅`` と ``univ`` についてはどの型についてのものなのかをLeanが正しく推論できないため，明示的に型を示す必要があります．以下の例では，Leanが必要に応じて最後の2つの定義をどのように展開するかを示しています．2つ目の例で用いられている ``trivial`` はライブラリにおいて ``True`` の標準的な証明です．
TEXT. -/
-- QUOTE:
example (x : ℕ) (h : x ∈ (∅ : Set ℕ)) : False :=
  h

example (x : ℕ) : x ∈ (univ : Set ℕ) :=
  trivial
-- QUOTE.

/- OMIT:
As an exercise, prove the following inclusion.
Use ``intro n`` to unfold the definition of subset,
and use the simplifier to reduce the
set-theoretic constructions to logic.
We also recommend using the theorems
``Nat.Prime.eq_two_or_odd`` and ``Nat.odd_iff``.
OMIT. -/
/- TEXT:
演習問題として，以下の包含を証明しましょう．その際にはまず ``intro n`` を使って部分集合の定義を展開し，そして単純化を使って集合論的な構成を論理に落とし込みます．また定理 ``Nat.Prime.eq_two_or_odd`` と ``Nat.odd_iff`` を使うことをお勧めします．
TEXT. -/
-- QUOTE:
example : { n | Nat.Prime n } ∩ { n | n > 2 } ⊆ { n | ¬Even n } := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example : { n | Nat.Prime n } ∩ { n | n > 2 } ⊆ { n | ¬Even n } := by
  intro n
  simp
  intro nprime n_gt
  rcases Nat.Prime.eq_two_or_odd nprime with h | h
  · rw [h]
    linarith
  · rw [Nat.odd_iff, h]

/- OMIT:
Be careful: it is somewhat confusing that the library has multiple versions
of the predicate ``Prime``.
The most general one makes sense in any commutative monoid with a zero element.
The predicate ``Nat.Prime`` is specific to the natural numbers.
Fortunately, there is a theorem that says that in the specific case,
the two notions agree, so you can always rewrite one to the other.
OMIT. -/
/- TEXT:
注意：少し混乱するかもしれませんが，Mathlibでは ``Prime`` という述語に複数のバージョンがあります．最も一般的な定義では，零要素を持つ任意の可換モノイドで使うことができます．これに対し ``Nat.Prime`` は自然数専用の述語です．幸いなことに，特定のケースではこの2つの概念が一致するという定理があるため，いつでも一方を他方に書き換えることができます．
TEXT. -/
-- QUOTE:
#print Prime

#print Nat.Prime

example (n : ℕ) : Prime n ↔ Nat.Prime n :=
  Nat.prime_iff.symm

example (n : ℕ) (h : Prime n) : Nat.Prime n := by
  rw [Nat.prime_iff]
  exact h
-- QUOTE.

/- OMIT:
The `rwa` tactic follows a rewrite with the assumption tactic.
OMIT. -/
/- TEXT:
.. index:: rwa, tactics ; rwa

``rwa`` タクティクは ``rw`` に続いて ``assumption`` タクティクを実行します．
TEXT. -/
-- QUOTE:
example (n : ℕ) (h : Prime n) : Nat.Prime n := by
  rwa [Nat.prime_iff]
-- QUOTE.

-- BOTH:
end

/- OMIT:
Lean introduces the notation ``∀ x ∈ s, ...``,
"for every ``x`` in ``s`` .,"
as an abbreviation for  ``∀ x, x ∈ s → ...``.
It also introduces the notation ``∃ x ∈ s, ...,``
"there exists an ``x`` in ``s`` such that .."
These are sometimes known as *bounded quantifiers*,
because the construction serves to restrict their significance
to the set ``s``.
As a result, theorems in the library that make use of them
often contain ``ball`` or ``bex`` in the name.
The theorem ``bex_def`` asserts that ``∃ x ∈ s, ...`` is equivalent
to ``∃ x, x ∈ s ∧ ...,``
but when they are used with ``rintro``, ``use``,
and anonymous constructors,
these two expressions behave roughly the same.
As a result, we usually don't need to use ``bex_def``
to transform them explicitly.
Here is are some examples of how they are used:
OMIT. -/
/- TEXT:
.. index:: bounded quantifiers

Leanでは「 ``s`` のすべての要素 ``x`` について，」を意味する ``∀ x, x ∈ s → ...`` の省略形として ``∀ x ∈ s, ...`` という記法を使用できます．またこれと同じように「 ``s`` の要素である ``x`` が存在し，」に対する ``∃ x ∈ s, ...,`` という記法も使用できます．これらは **束縛量化子** （bounded quantifiers）と呼ばれることがあります．これはこの構文が変数の範囲を集合 ``s`` に限定する役割を果たすからです．このため，これらの記法を用いるライブラリ中の定理の名前にはしばしば ``ball`` や ``bex`` が含まれます． ``∃ x ∈ s, ...`` が ``∃ x, x ∈ s ∧ ...,`` と等価であることは定理 ``bex_def`` で主張されていますが，この定理を用いずとも ``rintro`` と ``use`` ，そして無名コンストラクタを用いることでこの2つの差異をほぼ無視できます．そのため通常 ``bex_def`` を使って明示的に変換する必要はありません．以下は上記の記法の使用例です:
TEXT. -/
-- BOTH:
section

-- QUOTE:
variable (s t : Set ℕ)

-- EXAMPLES:
example (h₀ : ∀ x ∈ s, ¬Even x) (h₁ : ∀ x ∈ s, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  intro x xs
  constructor
  · apply h₀ x xs
  apply h₁ x xs

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ s, Prime x := by
  rcases h with ⟨x, xs, _, prime_x⟩
  use x, xs
-- QUOTE.

/- OMIT:
See if you can prove these slight variations:
OMIT. -/
/- TEXT:
これらの少し異なったバージョンを証明してみましょう:
TEXT. -/
-- QUOTE:
section
variable (ssubt : s ⊆ t)

example (h₀ : ∀ x ∈ t, ¬Even x) (h₁ : ∀ x ∈ t, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  sorry

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ t, Prime x := by
  sorry

end
-- QUOTE.

-- SOLUTIONS:
section
variable (ssubt : s ⊆ t)

example (h₀ : ∀ x ∈ t, ¬Even x) (h₁ : ∀ x ∈ t, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  intro x xs
  constructor
  · apply h₀ x (ssubt xs)
  apply h₁ x (ssubt xs)

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ t, Prime x := by
  rcases h with ⟨x, xs, _, px⟩
  use x, ssubt xs

end

-- BOTH:
end

/- OMIT:
Indexed unions and intersections are
another important set-theoretic construction.
We can model a sequence :math:`A_0, A_1, A_2, \ldots` of sets of
elements of ``α``
as a function ``A : ℕ → Set α``,
in which case ``⋃ i, A i`` denotes their union,
and ``⋂ i, A i`` denotes their intersection.
There is nothing special about the natural numbers here,
so ``ℕ`` can be replaced by any type ``I``
used to index the sets.
The following illustrates their use.
OMIT. -/
/- TEXT:
添字付き集合族の合併と共通部分も集合論では重要な構成です．:math:`A_0, A_1, A_2, \ldots` で表される ``α`` の部分集合の族は，関数 ``A : ℕ → Set α`` でモデル化することができます．ここで ``⋃ i, A i`` は集合族の合併を， ``⋂ i, A i`` は集合族の共通部分を表します．ここで添字に用いられている ``i`` の型として自然数を用いていますが特段自然数の性質を用いているわけではないため， ``ℕ`` は任意の型 ``I`` で置き換えることができます．以下にこれらの使い方を示します．
TEXT. -/
-- BOTH:
section
-- QUOTE:
variable {α I : Type*}
variable (A B : I → Set α)
variable (s : Set α)

open Set

-- EXAMPLES:
example : (s ∩ ⋃ i, A i) = ⋃ i, A i ∩ s := by
  ext x
  simp only [mem_inter_iff, mem_iUnion]
  constructor
  · rintro ⟨xs, ⟨i, xAi⟩⟩
    exact ⟨i, xAi, xs⟩
  rintro ⟨i, xAi, xs⟩
  exact ⟨xs, ⟨i, xAi⟩⟩

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := by
  ext x
  simp only [mem_inter_iff, mem_iInter]
  constructor
  · intro h
    constructor
    · intro i
      exact (h i).1
    intro i
    exact (h i).2
  rintro ⟨h1, h2⟩ i
  constructor
  · exact h1 i
  exact h2 i
-- QUOTE.

/- OMIT:
Parentheses are often needed with an
indexed union or intersection because,
as with the quantifiers,
the scope of the bound variable extends as far as it can.

OMIT. -/
/- TEXT:
添字付き集合族の合併や共通部分の表記ではしばしば括弧を使う必要があります．これは量化子の場合と同様に，Leanが束縛された変数のスコープを可能な限り広げようとするからです．

TEXT. -/
/- OMIT:
Try proving the following identity.
One direction requires classical logic!
We recommend using ``by_cases xs : x ∈ s``
at an appropriate point in the proof.
OMIT. -/
/- TEXT:
次の等式を証明してみましょう．この証明は2方向の包含関係を示すことで行いますが，片方は古典論理が必要となります！適切なところで ``by_cases xs : x ∈ s`` を使うと良いでしょう．
TEXT. -/
-- QUOTE:

example : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by
  ext x
  simp only [mem_union, mem_iInter]
  constructor
  · rintro (xs | xI)
    · intro i
      right
      exact xs
    intro i
    left
    exact xI i
  intro h
  by_cases xs : x ∈ s
  · left
    exact xs
  right
  intro i
  cases h i
  · assumption
  contradiction

/- OMIT:
Mathlib also has bounded unions and intersections,
which are analogous to the bounded quantifiers.
You can unpack their meaning with ``mem_iUnion₂``
and ``mem_iInter₂``.
As the following examples show,
Lean's simplifier carries out these replacements as well.
OMIT. -/
/- TEXT:
またMathlibは束縛された量化子に似た束縛された合併と共通集合を持っています．これらは ``mem_iUnion₂`` と ``mem_iInter₂`` で定義に展開することができます．以下の例で示すように，Leanの ``simp`` タクティクはこれらの置換も行ってくれます．
TEXT. -/
-- QUOTE:
-- BOTH:
def primes : Set ℕ :=
  { x | Nat.Prime x }

-- EXAMPLES:
example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } :=by
  ext
  rw [mem_iUnion₂]
  simp

example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } := by
  ext
  simp

example : (⋂ p ∈ primes, { x | ¬p ∣ x }) ⊆ { x | x = 1 } := by
  intro x
  contrapose!
  simp
  apply Nat.exists_prime_and_dvd
-- QUOTE.

/- OMIT:
Try solving the following example, which is similar.
If you start typing ``eq_univ``,
tab completion will tell you that ``apply eq_univ_of_forall``
is a good way to start the proof.
We also recommend using the theorem ``Nat.exists_infinite_primes``.
OMIT. -/
/- TEXT:
上記と似た次の例題を解いてみましょう．ここで ``eq_univ`` と入力し始めると，タブの補完が ``apply eq_univ_of_forall`` をまず使うことを教えてくれるでしょう．また ``Nat.exists_infinite_primes`` という定理を使うこともお勧めします．
TEXT. -/
-- QUOTE:
example : (⋃ p ∈ primes, { x | x ≤ p }) = univ := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example : (⋃ p ∈ primes, { x | x ≤ p }) = univ := by
  apply eq_univ_of_forall
  intro x
  simp
  rcases Nat.exists_infinite_primes x with ⟨p, pge, primep⟩
  use p, primep

-- BOTH:
end

/- OMIT:
Give a collection of sets, ``s : Set (Set α)``,
their union, ``⋃₀ s``, has type ``Set α``
and is defined as ``{x | ∃ t ∈ s, x ∈ t}``.
Similarly, their intersection, ``⋂₀ s``, is defined as
``{x | ∀ t ∈ s, x ∈ t}``.
These operations are called ``sUnion`` and ``sInter``, respectively.
The following examples show their relationship to bounded union
and intersection.
OMIT. -/
/- TEXT:
集合の集まり ``s : Set (Set α)`` について，これらの合併 ``⋃₀ s`` は型 ``Set α`` を持ち， ``{x | ∃ t ∈ s, x ∈ t}`` と定義されます．同様に共通部分 ``⋂₀ s`` は ``{x | ∀ t ∈ s, x ∈ t}`` で定義されます．これらの演算子はそれぞれ ``sUnion`` と ``sInter`` と呼ばれます．以下の例では束縛された合併と共通部分との関係を示します．
TEXT. -/
section

open Set

-- QUOTE:
variable {α : Type*} (s : Set (Set α))

example : ⋃₀ s = ⋃ t ∈ s, t := by
  ext x
  rw [mem_iUnion₂]
  simp

example : ⋂₀ s = ⋂ t ∈ s, t := by
  ext x
  rw [mem_iInter₂]
  rfl
-- QUOTE.

end

/- OMIT:
In the library, these identities are called
``sUnion_eq_biUnion`` and ``sInter_eq_biInter``.
OMIT. -/
/- TEXT:
Mathlibでは，これらの等式は ``sUnion_eq_biUnion`` と ``sInter_eq_biInter`` と呼ばれています．
TEXT. -/
