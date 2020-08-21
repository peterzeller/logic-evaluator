package com.github.peterzeller.logiceval

import com.github.peterzeller.logiceval.SimpleLogic._
import com.github.peterzeller.logiceval.utils.HMap

object TypeCheck {

  case class Ctxt(vars: List[Type[_]] = List()) {
    def withBinding[T](t: Type[T]): Ctxt =
      this.copy(vars = t :: vars)

    def apply[T](b: Bound[T]): Type[T] = vars(b.index).asInstanceOf[Type[T]]

  }

  def calcType[T](expr: Expr[T])(implicit ctxt: Ctxt): Type[T] = expr match {
    case v: Var[T] => throw new Exception(s"Unexpected variable $v")
    case b: Bound[T] => ctxt(b)
    case f: ForallD[_] =>
      BoolType()
    case n: Neg => BoolType()
    case and: And => BoolType()
    case eq: Eq[_] => BoolType()
    case elem: IsElem[_] => BoolType()
    case c: ConstructDt[_] => c.typ
    case g: Get[k, v] =>
      val it = calcType(g.map).asInstanceOf[MapType[k, v]].valueType
      optionType(it).asInstanceOf[Type[T]]
    case Pair(a, b) =>
      PairType(calcType(a), calcType(b))
    case o: Opaque[_, _] =>
      o.resultType
    case c: ConstExpr[_] =>
      c.typ
  }


  def checkType[T](expr: Expr[T])(implicit ctxt: Ctxt): Type[T] = {
    def expect[Q](expr: Expr[Q], t: Type[_])(implicit ctxt: Ctxt): Unit = {
      val at = checkType(expr)(ctxt)
      if (at != t)
        throw new Exception(s"Expected $t but found $at\nin $expr")
    }

    try {
      expr match {
        case v: Var[T] => throw new Exception(s"Unexpected variable $v")
        case b: Bound[T] => ctxt(b)
        case f: ForallD[_] =>
          expect(f.body, BoolType())(ctxt.withBinding(f.typ))
          BoolType()
        case n: Neg =>
          expect(n.negatedExpr, BoolType())
          BoolType()
        case and: And =>
          expect(and.left, BoolType())
          expect(and.right, BoolType())
          BoolType()
        case eq: Eq[_] =>
          val l = checkType(eq.left)
          expect(eq.right, l)
          BoolType()
        case elem: IsElem[_] => BoolType()
          val st = checkType(elem.set)
          st match {
            case SetType(elemType) =>
              expect(elem.elem, elemType)
            case _ =>
              throw new Exception(s"Expeceted set type, but found $st")
          }
          BoolType()
        case c: ConstructDt[_] =>
          val cas = c.typ.cases.find(_.name == c.name)
            .getOrElse(throw new Exception(s"Could not find case ${c.name} in ${c.typ}"))
          if (cas.argTypes.length != c.args.length)
            throw new Exception("Wrong number of args")

          for ((a1, t) <- c.args zip cas.argTypes)
            expect(a1, t)

          c.typ
        case g: Get[k, v] =>
          checkType(g.map) match {
            case MapType(keyType, valueType) =>
              expect(g.key, keyType)
              expect(g.default, valueType)
              valueType.asInstanceOf[Type[T]]
            case other =>
              throw new Exception(s"Expected map type but found $other")
          }
        case Pair(a, b) =>
          PairType(calcType(a), calcType(b))
        case o: Opaque[_, _] =>
          expect(o.arg, o.argType)
          o.resultType
        case c: ConstExpr[_] =>
          c.typ
      }
    } catch {
      case ex: Exception =>
        throw new Exception(s"When checking $expr", ex)
    }
  }


}
