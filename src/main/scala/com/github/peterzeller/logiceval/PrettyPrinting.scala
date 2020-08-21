package com.github.peterzeller.logiceval

import com.github.peterzeller.logiceval.SimpleLogic._
import com.github.peterzeller.logiceval.utils.PrettyPrintDoc._

object PrettyPrinting {

  case class Ctxt(
    vars: List[Var[_]] = List()
  ) {
    def withVar(v: Var[Any]): Ctxt =
      copy(vars = v::vars)

  }

  def paren(p: Boolean, doc: Doc): Doc =
    group(if (p) "(" <> doc <> ")" else doc)

  def printTyp(typ: SimpleLogic.Type[_]): Doc = typ match {
    case SetType(elemType) => "Set[" <> printTyp(elemType) <> "]"
    case MapType(keyType, valueType) => "Set[" <> printTyp(keyType) <> ", " <> printTyp(valueType) <> "]"
    case Datatype(name, cases) =>
      name
    case CustomType(name) =>
      name
    case BoolType() =>
      "Bool"
    case PairType(a, b) =>
      "(" <> printTyp(a) <> ", " <> printTyp(b) <> ")"
  }

  def op(prec1: Int, prec: Int, op: String, left: Expr[_], right: Expr[_])(implicit ctxt: Ctxt): Doc =
    paren(prec1 <= prec, printExpr(left, prec) <> nested(2, lineOrSpace <> op <+> printExpr(right, prec)))

  def printValue(v: Any): Doc = v match {
    case values: Set[t] =>
      "{" <> sep(", ", values.map(printValue)) <> "}"
    case m: Map[k, v] =>
      "{" <> sep(", ", m.toList.map(e => printValue(e._1) <> " ↦ " <> printValue(e._2))) <> "}"
    case _ =>
      v.toString
  }

  def printExpr(e: Expr[_], prec: Int)(implicit ctxt: Ctxt): Doc = e match {
    case SimpleLogic.Var(name) =>
      name
    case Bound(index) =>
      ctxt.vars(index).name
    case SimpleLogic.ForallD(v, typ, body) =>
      paren(prec <= 50, "∀" <> v.name <> ": " <> printTyp(typ) <> nested(2, "." </>
        printExpr(body, 100)(ctxt.withVar(v))))
    case SimpleLogic.Neg(n) =>
      paren(prec <= 10, "¬" <> printExpr(n, 10))
    case SimpleLogic.And(left, right) =>
      op(prec, 20, "∧", left, right)

    case SimpleLogic.Eq(left, right) =>
      op(prec, 15, "=", left, right)
    case SimpleLogic.IsElem(elem, set) =>
      op(prec, 14, "∈", elem, set)
    case SimpleLogic.ConstructDt(_, name, c, args) =>
      group(name <> "(" <> nested(2, line <> sep("," <> lineOrSpace, args.map(printExpr(_, 100)))) <> ")")
    case SimpleLogic.Get(map, key, _) =>
      printExpr(map, 5) <> "[" <> printExpr(key, 100) <> "]"
    case SimpleLogic.Opaque(_, _, func, args) =>
      group(func.toString() <> "(" <> nested(2, printExpr(args, 100)) <> ")")
    case SimpleLogic.ConstExpr(v) =>
      printValue(v)
    case Pair(a, b) =>
      "(" <> printExpr(a, 100) <> ", " <> printExpr(b, 100) <> ")"

  }


}
