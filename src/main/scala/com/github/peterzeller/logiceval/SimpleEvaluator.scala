package com.github.peterzeller.logiceval

import com.github.peterzeller.logiceval.NarrowingEvaluator.Concrete
import com.github.peterzeller.logiceval.SimpleLogic._

object SimpleEvaluator {
  def startEval(expr: Expr): Value =
    eval(expr)(Ctxt(Map()))


  class EvalException(msg: String, exc: Throwable = null) extends Exception(msg, exc)

  case class Ctxt(varValues: Map[Var, Value]) {
    def +(v: (Var, Value)): Ctxt = copy(varValues = varValues + v)

    def apply(v: Var): Value =
      varValues.getOrElse(v,
        throw new EvalException(s"Could not find $v in ${varValues.values}"))
  }

  def evalB(expr: Expr)(implicit ctxt: Ctxt): Boolean =
    eval(expr) match {
      case BoolVal(value) => value
      case other =>
        throw new EvalException(s"Expected Bool but found $other")
    }

  def evalSet(expr: Expr)(implicit ctxt: Ctxt): Set[Value] =
    eval(expr) match {
      case SetValue(values) => values
      case other =>
        throw new EvalException(s"Expected Set but found $other")
    }


  def eval(expr: Expr)(implicit ctxt: Ctxt): Value = expr match {
    case v: Var => ctxt(v)
    case Forall(v, t, body) =>
      BoolVal(t.values.forall(x => evalB(body)(ctxt + (v -> x))))
    case Neg(negatedExpr) =>
      BoolVal(!evalB(negatedExpr))
    case And(left, right) =>
      BoolVal(evalB(left) && evalB(right))
    case Eq(left, right) =>
      BoolVal(eval(left) == eval(right))
    case IsElem(elem, set) =>
      BoolVal(evalSet(set).contains(eval(elem)))
    case ConstructDt(name, args) =>
      DatatypeValue(name, args.map(eval))
    case Get(map, key) =>
      val m = eval(map)
      val k = eval(key)
      m.getFromMap(k)
    case Opaque(func, args) =>
      func(args.map(eval))
    case ConstExpr(v) => v
  }


}
