package com.github.peterzeller.logiceval

import com.github.peterzeller.logiceval.SimpleLogic._
import com.github.peterzeller.logiceval.utils.PrettyPrintDoc._

object PrettyPrinting {


  def paren(p: Boolean, doc: Doc): Doc =
    group(if (p) "(" <> doc <> ")" else doc)

  def printTyp(typ: SimpleLogic.Type): Doc = typ match {
    case SetType(elemType) => "Set[" <> printTyp(elemType) <> "]"
    case MapType(keyType, valueType) => "Set[" <> printTyp(keyType) <> ", " <> printTyp(valueType) <> "]"
    case Datatype(name, cases) =>
      name
    case CustomType(name, customValues) =>
      name
    case BoolType =>
      "Bool"
  }

  def op(prec1: Int, prec: Int, op: String, left: Expr, right: Expr): Doc =
    paren(prec1 <= prec, printExpr(left, prec) <> nested(2, lineOrSpace <> op <+> printExpr(right, prec)))

  def printValue(v: Value): Doc = v match {
    case BoolVal(value) =>
      value.toString
    case AnyValue(value) =>
      value.toString
    case SetValue(values) =>
      "{" <> sep(", ", values.toList.sorted.map(printValue)) <> "}"
    case MapValue(map, default) =>
      "Map(" <> printValue(default) <> "){" <> sep(", ", map.toList.sorted.map(e => printValue(e._1) <> " ↦ " <> printValue(e._2))) <> "}"
    case DatatypeValue(name, args) =>
      name <> "(" <> sep(", ", args.map(printValue)) <> ")"
  }

  def printExpr(e: Expr, prec: Int): Doc = e match {
    case SimpleLogic.Var(name) =>
      name
    case SimpleLogic.Forall(v, typ, body) =>
      paren(prec <= 50, "∀" <> v.name <> ": " <> printTyp(typ) <> nested(2, "." </> printExpr(body, 100)))
    case SimpleLogic.Neg(n) =>
      paren(prec <= 10, "¬" <> printExpr(n, 10))
    case SimpleLogic.And(left, right) =>
      op(prec, 20, "∧", left, right)

    case SimpleLogic.Eq(left, right) =>
      op(prec, 15, "=", left, right)
    case SimpleLogic.IsElem(elem, set) =>
      op(prec, 14, "∈", elem, set)
    case SimpleLogic.ConstructDt(name, args) =>
      group(name <> "(" <> nested(2, line <> sep("," <> lineOrSpace, args.map(printExpr(_, 100)))) <> ")")
    case SimpleLogic.Get(map, key) =>
      printExpr(map, 5) <> "[" <> printExpr(key, 100) <> "]"
    case SimpleLogic.Opaque(func, args) =>
      group(func.toString() <> "(" <> nested(2, line <> sep("," <> lineOrSpace, args.map(printExpr(_, 100)))) <> ")")
    case SimpleLogic.ConstExpr(v) =>
      printValue(v)

  }


}
