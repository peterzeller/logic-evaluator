package com.github.peterzeller.logiceval

import com.github.peterzeller.logiceval.SimpleLogic._
import com.github.peterzeller.logiceval.utils.HMap
import shapeless.Id

object SimpleEvaluator {
  /** global flag for enabling type checks */
  var checked: Boolean = true


  def startEval[T](expr: Expr[T], typeEnv: Env): T =
    eval(expr)(Ctxt(typeEnv))


  class EvalException(msg: String, exc: Throwable = null) extends Exception(msg, exc)

  case class Ctxt(env: Env, varValues: HMap[Var, Id] = HMap[Var, Id]()) {
    def +[T](v: (Var[T], T)): Ctxt = copy(varValues = varValues + v)

    def apply[T](v: Var[T]): T =
      varValues.getOrElse(v,
        throw new EvalException(s"Could not find $v in ${varValues.values}"))
  }


  def eval[T](expr: Expr[T])(implicit ctxt: Ctxt): T = expr match {
    case v: Var[T] => ctxt(v)
    case Forall(v, t, body) =>
      t.values(ctxt.env).forall { x =>
        checkType(t, x)
        eval(body)(ctxt + (v -> x))
      }
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
      val res = c.construct(argsE)
      checkType(c.typ, res)
      res
    case g: Get[k, v] =>
      val m = eval(g.map)
      val k = eval(g.key)
      m.getOrElse(k, eval(g.default))
    case Pair(a, b) =>
      (eval(a), eval(b))
    case g: Opaque[a, r] =>
      val res = g.func(ctxt.env, eval(g.arg))
      checkType(g.resultType, res)
      res
    case c@ConstExpr(v) =>
      checkType(c.typ, v)
      v
  }

  private def checkType[T](t: Type[T], v: Any): Unit = {
    if (checked) {
      assert(t.check(v), s"Value $v (${v.getClass}) is not an instance of $t.")
    }
  }
}
