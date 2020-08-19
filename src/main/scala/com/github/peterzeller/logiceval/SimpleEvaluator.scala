package com.github.peterzeller.logiceval

import com.github.peterzeller.logiceval.SimpleLogic._
import com.github.peterzeller.logiceval.utils.HMap
import shapeless.Id

object SimpleEvaluator {
  def startEval[T](expr: Expr[T], typeEnv: TypeEnv): T =
    eval(expr)(Ctxt(typeEnv))


  class EvalException(msg: String, exc: Throwable = null) extends Exception(msg, exc)

  case class Ctxt(typeEnv: TypeEnv, varValues: HMap[Var, Id] = HMap[Var, Id]()) {
    def +[T](v: (Var[T], T)): Ctxt = copy(varValues = varValues + v)

    def apply[T](v: Var[T]): T =
      varValues.getOrElse(v,
        throw new EvalException(s"Could not find $v in ${varValues.values}"))
  }


  def eval[T](expr: Expr[T])(implicit ctxt: Ctxt): T = expr match {
    case v: Var[T] => ctxt(v)
    case Forall(v, t, body) =>
      t.values(ctxt.typeEnv).forall(x => eval(body)(ctxt + (v -> x)))
    case Neg(negatedExpr) =>
      !eval(negatedExpr)
    case And(left, right) =>
      eval(left) && eval(right)
    case Eq(left, right) =>
      eval(left) == eval(right)
    case IsElem(elem, set) =>
      eval(set).contains(eval(elem))
    case c: ConstructDt[t] =>
      val argsE: List[Any] = c.args.map((e: Expr[_]) => eval(e))
      c.construct(argsE)
    case g: Get[k, v] =>
      val m = eval(g.map)
      val k = eval(g.key)
      m.getOrElse(k, eval(g.default))
    case Pair(a, b) =>
      (eval(a), eval(b))
    case g: Opaque[a, r] =>
      g.func(eval(g.arg))
    case ConstExpr(v) => v
  }


}
