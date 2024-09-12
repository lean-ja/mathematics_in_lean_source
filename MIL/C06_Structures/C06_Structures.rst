.. _structures:

構造体
==========

.. Structures
.. ==========

.. Modern mathematics makes essential use of algebraic
.. structures,
.. which encapsulate patterns that can be instantiated in
.. multiple settings.
.. The subject provides various ways of defining such structures and
.. constructing particular instances.

現代の数学では，代数的な構造を本質的に利用しており，この構造はさまざまな状況下でインスタンス化されるパターンを内包しています．このような構造は定義方法と，特定のインスタンスを構築する様々な方法を提供します．

.. Lean therefore provides corresponding ways of
.. defining structures formally and working with them.
.. You have already seen examples of algebraic structures in Lean,
.. such as rings and lattices, which were discussed in
.. :numref:`Chapter %s <basics>`.
.. This chapter will explain the mysterious square bracket annotations
.. that you saw there,
.. ``[Ring α]`` and ``[Lattice α]``.
.. It will also show you how to define and use
.. algebraic structures on your own.

Leanはこのような構造に対する形式的な定義方法と，その扱い方に対応する方法を提供しています．Leanでの代数的な構造の例は :numref:`Chapter %s <basics>` で説明した環や束ですでに見てきました．この章では，そこで見た不思議な角括弧の注釈 ``[Ring α]`` と ``[Lattice α]`` についても説明します．また，代数的構造を自分で定義して使う方法も紹介します．

.. For more technical detail, you can consult `Theorem Proving in Lean <https://leanprover.github.io/theorem_proving_in_lean/>`_,
.. and a paper by Anne Baanen, `Use and abuse of instance parameters in the Lean mathematical library <https://arxiv.org/abs/2202.01629>`_.

技術的詳細を知りたい場合は， `Theorem Proving in Lean <https://leanprover.github.io/theorem_proving_in_lean/>`_ [#f01]_ とAnne Baanenによる記事 `Use and abuse of instance parameters in the Lean mathematical library <https://arxiv.org/abs/2202.01629>`_ にあたるとよいでしょう．

.. [#f01] 訳注: 日本語訳は <https://aconite-ac.github.io/theorem_proving_in_lean4_ja/>
