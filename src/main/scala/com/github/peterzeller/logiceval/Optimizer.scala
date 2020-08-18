package com.github.peterzeller.logiceval

import com.github.peterzeller.logiceval.SimpleLogic.Expr

object Optimizer {


  /**
   * narrow the scope of quantifiers to be as small as possible
   *
   *     forall x. A ~> A // if x not free in A
   *     forall x. A && B ~> (forall x. A) && (forall x. B)
   *     forall x. !(A && B)  ~> !((forall x. A) && B)  // if x not free in B
   *     forall x. !(A && B)  ~> !(A && (forall x. B))  // if x not free in A
   */
  def narrowQuantifiers(expr: Expr): Expr = {
    ???
  }

  /**
   * Eliminate quantifiers that are constrained by equality
   *
   * forall x. P [ f(z) != C(x) ]
   * ~> f(z) match { case C(x) => P(x)  }
   *
   */

  /**
   * Restrict quantifiers that are restricted by a set
   *
   * forall x in S1. P [ x in S2 ]
   * ~> forall x in (S1 intersect S2). P(x)
   *
   */

  /**
   * Other ideas:
   *
   * - reverse index in map: Find all calls of a certain shape
   *    (index with trie like structure, special data structure in language)
   */


}
