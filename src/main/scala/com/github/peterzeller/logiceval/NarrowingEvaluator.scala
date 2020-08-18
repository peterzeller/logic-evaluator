package com.github.peterzeller.logiceval

import com.github.peterzeller.logiceval.NarrowingEvaluator.SymbolicValue
import com.github.peterzeller.logiceval.SimpleLogic._

import scala.annotation.tailrec

object NarrowingEvaluator {

  def startEval(expr: Expr): Value =
      eval(expr)(Ctxt(Map()))


  sealed abstract class SymbolicValue {
    /** variables that this symbolic value depends on */
    def variables: Set[Var] = this match {
      case AnyValue(variable) => Set(variable)
      case Concrete(value) => Set()
      case NotEqVal(variable, value) => Set(variable)
      case NotInSetValue(variable, set) => Set(variable)
      case SymbolicDatatypeValue(name, args) => args.view.flatMap(_.variables).toSet
    }
  }

  case class AnyValue(variable: Var) extends SymbolicValue

  case class Concrete(value: Value) extends SymbolicValue

  case class NotEqVal(variable: Var, value: Value) extends SymbolicValue

  case class NotInSetValue(variable: Var, set: Set[Value]) extends SymbolicValue

  case class SymbolicDatatypeValue(name: String, args: List[SymbolicValue]) extends SymbolicValue {
    // must not be a concrete value
    require(variables.nonEmpty)
  }

  /** smart constructor */
  def SymDatatypeValue(name: String, args: List[SymbolicValue]): SymbolicValue =
    if (args.forall(_.isInstanceOf[Concrete]))
      Concrete(DatatypeValue(name, args.map(_.asInstanceOf[Concrete].value)))
    else
      SymbolicDatatypeValue(name, args)


  sealed case class NarrowException(variable: Var, cause: NarrowCause) extends Exception

  sealed abstract class NarrowCause

  case class EqExc(value: Value) extends NarrowCause

  case class InSetExc(setValue: Set[Value]) extends NarrowCause

  object MustBeConcrete extends NarrowCause

  case class NarrowDatatype(index: Int, cause: NarrowCause) extends NarrowCause


  class EvalException(msg: String, exc: Throwable = null) extends Exception(msg, exc)

  case class Ctxt(varValues: Map[Var, SymbolicValue]) {
    def +(v: (Var, SymbolicValue)): Ctxt = copy(varValues = varValues + v)

    def apply(v: Var): SymbolicValue =
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

  def evalMap(expr: Expr)(implicit ctxt: Ctxt): Map[Value, Value] =
    eval(expr) match {
      case MapValue(values) => values
      case other =>
        throw new EvalException(s"Expected Map but found $other")
    }

  def tryEval(expr: Expr)(implicit ctxt: Ctxt): Either[NarrowException, Value] =
    try {
      Right(eval(expr))
    } catch {
      case n: NarrowException =>
        Left(n)
    }

  def eval(expr: Expr)(implicit ctxt: Ctxt): Value = {
    evalS(expr) match {
      case Concrete(value) => value
      case other =>
        throw NarrowException(other.variables.head, MustBeConcrete)
    }
  }

  def evalS(expr: Expr)(implicit ctxt: Ctxt): SymbolicValue = expr match {
    case v: Var => ctxt(v)
    case Forall(v, set, body) =>
      val setV: Iterable[Value] = set.values

      def evalBody(value: SymbolicValue): Boolean = {
        evalB(body)(ctxt + (v -> value))
      }

      def loop(values: LazyList[SymbolicValue]): Boolean = {
        for (value <- values) {
          try {
            val res = evalBody(value)
            if (!res)
              return false
          } catch {
            case NarrowException(va, cause) if va == v =>
              cause match {
                case EqExc(value) =>
                  // if value is checked for equality, check once with equal and once with not equal
                  return loop(LazyList(Concrete(value), NotEqVal(v, value)))
                case InSetExc(setValue) =>
                  // if value is checked in a set, try with symbolic value not in set and all values in set
                  val v1 = setValue.to(LazyList)
                  val v2 =
                    setV match {
                      case s: Set[Value] =>
                        v1.filter(s.contains)
                      case _ =>
                        v1
                    }
                  return loop(LazyList(NotInSetValue(v, setValue)) ++ v2.map(Concrete))
                case MustBeConcrete =>
                  // if the value must be concrete, try all possible values
                  // TODO if type is a datatype, don't generate symbolic DatatypeValue
                  return loop(setV.to(LazyList).map(Concrete))
                case NarrowDatatype(index, cause) =>
                  // TODO refine datatype
                  return loop(setV.to(LazyList).map(Concrete))
              }
          }
        }
        true
      }

      // first try with a symbolic value
      Concrete(BoolVal(loop(LazyList[SymbolicValue](AnyValue(v)))))
    case Neg(negatedExpr) =>
      Concrete(BoolVal(!evalB(negatedExpr)))
    case And(left, right) =>
      Concrete(BoolVal(evalB(left) && evalB(right)))
    case Eq(left, right) =>


      def checkEq(left: SymbolicValue, right: SymbolicValue): Boolean = {
        (left, right) match {
          case (SymbolicDatatypeValue(name1, args1), SymbolicDatatypeValue(name2, args2)) =>
            if (name1 == name2 && args1.length == args2.length) {
              args1.zip(args2).forall { case (a1, a2) => checkEq(a1, a2) }
            } else {
              false
            }
          case (Concrete(x), Concrete(y)) =>
            x == y
          case (Concrete(x), AnyValue(v)) =>
            throw NarrowException(v, EqExc(x))
          case (AnyValue(v), Concrete(x)) =>
            throw NarrowException(v, EqExc(x))
          case (x, y) =>
            throw NarrowException(x.variables.head, MustBeConcrete)
        }
      }

      val leftV = evalS(left)
      val rightV = evalS(right)

      Concrete(BoolVal(checkEq(leftV, rightV)))
    case IsElem(elem, set) =>
      val elemV = evalS(elem)
      val setV = evalSet(set)

      val res = {
        elemV match {
          case Concrete(x) =>
            setV.contains(x)
          case AnyValue(variable) =>
            throw NarrowException(variable, InSetExc(setV))
          case NotInSetValue(variable, s) if setV.subsetOf(s) =>
            // notin s, therefore not in setV
            false
          case other =>
            throw NarrowException(other.variables.head, MustBeConcrete)
        }
      }


      Concrete(BoolVal(res))
    case ConstructDt(name, args) =>
      SymDatatypeValue(name, args.map(evalS))
    case Domain(map) =>
      Concrete(SetValue(evalMap(map).keySet))
    case Get(map, key) =>
      val m = evalMap(map)
      val k = eval(key)
      Concrete(m.getOrElse(k, throw new EvalException(s"Could not find $k in map $m")))
    case Opaque(func, args) =>
      Concrete(func(args.map(eval)))
    case ConstExpr(v) => Concrete(v)
  }


}
