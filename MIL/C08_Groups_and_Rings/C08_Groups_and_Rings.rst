.. _groups_and_ring:

.. Groups and Rings
.. ================

群と環
========

.. We saw in :numref:`proving_identities_in_algebraic_structures` how to reason about
.. operations in groups and rings. Later, in :numref:`section_algebraic_structures`, we saw how
.. to define abstract algebraic structures, such as group structures, as well as concrete instances
.. such as the ring structure on the Gaussian integers. :numref:`Chapter %s <hierarchies>` explained how
.. hierarchies of abstract structures are handled in Mathlib.

:numref:`proving_identities_in_algebraic_structures` にて群や環の演算を推論する方法を見ました．その後， :numref:`section_algebraic_structures` では群構造などの抽象的な代数構造や，ガウス整数上の環構造のような具体的な例を定義する方法を説明しました． :numref:`Chapter %s <hierarchies>` ではMathlibにおいて抽象的な構造がどのように階層付けられるかを説明しました．

.. In this chapter we work with groups and rings in more detail. We won't be able to
.. cover every aspect of the treatment of these topics in Mathlib, especially since Mathlib is constantly growing.
.. But we will provide entry points to the library and show how the essential concepts are used.
.. There is some overlap with the discussion of
.. :numref:`Chapter %s <hierarchies>`, but here we will focus on how to use Mathlib instead of the design
.. decisions behind the way the topics are treated.
.. So making sense of some of the examples may require reviewing the background from
.. :numref:`Chapter %s <hierarchies>`.

この章では群と環をより詳しく扱います．Mathlibにおけるこれらのトピックの扱いについてすべての面をカバーすることはできません．というのもMathlibは常に成長しているからです．しかし，ライブラリへの入口を提供し，重要な概念がどのように使われているかを紹介します． :numref:`Chapter %s <hierarchies>` の議論と重なる部分もありますが，ここではトピックの扱い方の背後にある設計の理由ではなく，Mathlibの使い方に焦点を当てます．そのため，いくつかの例を理解するためには :numref:`Chapter %s <hierarchies>` の背景を復習する必要があるかもしれません．
