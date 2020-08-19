package com.github.peterzeller.logiceval

import com.github.peterzeller.logiceval.utils.{LazyListUtils, PrettyPrintDoc}

import scala.math.Ordered.orderingToOrdered
import scala.math.Ordering.Implicits.seqOrdering

/**
 * Example logic
 */
object SimpleLogic {

  sealed abstract class Type {
    def print: String = PrettyPrinting.printTyp(this).prettyStr(120)

    def values: Iterable[Value] = this match {
      case SetType(elemType) => ???
      case MapType(keyType, valueType) => ???
      case Datatype(name, cases) =>
        for {
          c <- cases.to(LazyList)
          argList: List[LazyList[Value]] = c.argTypes.map(_.values.to(LazyList))
          args <- LazyListUtils.allCombinations(argList)
        } yield {
          DatatypeValue(c.name, args)
        }
      case CustomType(name, customValues) => customValues
      case BoolType => Set(BoolVal(false), BoolVal(true))
    }
  }

  case class SetType(elemType: Type) extends Type

  case class MapType(keyType: Type, valueType: Type) extends Type

  case class Datatype(name: String, cases: List[DtCase]) extends Type

  case class DtCase(name: String, argTypes: List[Type])

  case class CustomType(name: String, customValues: Set[Value]) extends Type

  object BoolType extends Type {
    override def toString: String = "BoolType"
  }


  sealed abstract class Expr {
    def doc: PrettyPrintDoc.Doc = PrettyPrinting.printExpr(this, 100)

    override def toString: String = doc.prettyStr(120)

    def freeVars: Set[Var] = this match {
      case v: Var => Set(v)
      case Forall(v, typ, body) =>
        body.freeVars - v
      case Neg(negatedExpr) =>
        negatedExpr.freeVars
      case And(left, right) =>
        left.freeVars ++ right.freeVars
      case Eq(left, right) =>
        left.freeVars ++ right.freeVars
      case IsElem(elem, set) =>
        elem.freeVars ++ set.freeVars
      case ConstructDt(name, args) =>
        args.view.flatMap(_.freeVars).toSet
      case Get(map, key) =>
        map.freeVars ++ key.freeVars
      case Opaque(func, args) =>
        args.view.flatMap(_.freeVars).toSet
      case ConstExpr(v) =>
        Set()
    }
  }

  case class Var(name: String) extends Expr

  case class Forall(v: Var, typ: Type, body: Expr) extends Expr

  case class Neg(negatedExpr: Expr) extends Expr

  case class And(left: Expr, right: Expr) extends Expr

  case class Eq(left: Expr, right: Expr) extends Expr

  case class IsElem(elem: Expr, set: Expr) extends Expr

  case class ConstructDt(name: String, args: List[Expr]) extends Expr

  case class Get(map: Expr, key: Expr) extends Expr

  case class Opaque(func: List[Value] => Value, args: List[Expr]) extends Expr

  case class ConstExpr(v: Value) extends Expr


  sealed abstract class Value extends Ordered[Value] {
    def getFromMap(k: Value): Value = this match {
      case MapValue(map, default) =>
        map.getOrElse(k, default)
      case other => throw new Exception(s"unhandled case $other")
    }

    def boolVal: Boolean = this match {
      case BoolVal(value) => value
      case other => throw new Exception(s"unhandled case $other")
    }


    override def compare(that: Value): Int = {
      this match {
        case BoolVal(value) =>
          that match {
            case BoolVal(value2) =>
              value compare value2
            case _ => -1
          }
        case AnyValue(value) =>
          that match {
            case BoolVal(value2) => 1
            case AnyValue(value2) =>
              try {
                value.asInstanceOf[Comparable[Any]].compareTo(value2)
              } catch {
                case _: Throwable =>
                  value.toString compare value2.toString
              }
            case _ => -1
          }
        case SetValue(values) =>
          that match {
            case BoolVal(value2) => 1
            case AnyValue(value2) => 1
            case SetValue(values2) =>
              values.toList compare values2.toList
            case MapValue(map2, default2) => -1
            case DatatypeValue(name2, args2) => -1
          }
        case MapValue(map, default) =>
          that match {
            case BoolVal(value2) => 1
            case AnyValue(value2) => 1
            case SetValue(values2) => 1
            case MapValue(map2, default2) =>
              (map.toList, default) compare (map2.toList, default2)
            case DatatypeValue(name2, args2) => -1
          }
        case DatatypeValue(name, args) =>
          that match {
            case BoolVal(value2) =>1
            case AnyValue(value2) =>1
            case SetValue(values2) =>1
            case MapValue(map2, default2) =>1
            case DatatypeValue(name2, args2) =>
              (name, args) compare (name2, args2)
          }
      }
    }
  }

  case class BoolVal(value: Boolean) extends Value

  case class AnyValue(value: Any) extends Value

  case class SetValue(values: Set[Value]) extends Value

  case class MapValue(map: Map[Value, Value], default: Value) extends Value

  case class DatatypeValue(name: String, args: List[Value]) extends Value


}
