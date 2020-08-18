package com.github.peterzeller.logiceval

import com.github.peterzeller.logiceval.utils.LazyListUtils

/**
 * Example logic
 */
object SimpleLogic {

  sealed abstract class Type {
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

  object BoolType extends Type


  sealed abstract class Expr

  case class Var(name: String) extends Expr

  case class Forall(v: Var, typ: Type, body: Expr) extends Expr

  case class Neg(negatedExpr: Expr) extends Expr

  case class And(left: Expr, right: Expr) extends Expr

  case class Eq(left: Expr, right: Expr) extends Expr

  case class IsElem(elem: Expr, set: Expr) extends Expr

  case class ConstructDt(name: String, args: List[Expr]) extends Expr

  case class Domain(map: Expr) extends Expr

  case class Get(map: Expr, key: Expr) extends Expr

  case class Opaque(func: List[Value] => Value, args: List[Expr]) extends Expr

  case class ConstExpr(v: Value) extends Expr


  sealed abstract class Value {
    def boolVal: Boolean = this match {
      case BoolVal(value) => value
      case other => throw new Exception(s"unhandled case $other")
    }
  }

  case class BoolVal(value: Boolean) extends Value

  case class AnyValue(value: Any) extends Value

  case class SetValue(values: Set[Value]) extends Value

  case class MapValue(map: Map[Value, Value]) extends Value

  case class DatatypeValue(name: String, args: List[Value]) extends Value


}
