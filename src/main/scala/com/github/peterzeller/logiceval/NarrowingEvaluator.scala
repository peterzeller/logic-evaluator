package com.github.peterzeller.logiceval

import com.github.peterzeller.logiceval.NarrowingEvaluator.SymbolicValue
import com.github.peterzeller.logiceval.SimpleLogic._
import com.github.peterzeller.logiceval.utils.HMap

import scala.annotation.tailrec
import scala.collection.{AbstractIterable, View, immutable, mutable}

object NarrowingEvaluator {

  def startEval[T](expr: Expr[T]): T =
    eval(expr)(Ctxt())


  sealed abstract class SymbolicValue[T] {
    /** variables that this symbolic value depends on */
    def variables: Set[Var[_]] = this match {
      case AnyValue(variable) => Set(variable)
      case Concrete(value) => Set()
      case NotEqVal(variable, value) => Set(variable)
      case NotInSetValue(variable, set) => Set(variable)
      case SymbolicDatatypeValue(name, args) => args.view.flatMap(_.variables).toSet
    }

    def isConcrete: Boolean = this.isInstanceOf[Concrete[_]]

    def concreteVal: T = this.asInstanceOf[Concrete[T]].value

  }

  case class AnyValue[T](variable: Var[T]) extends SymbolicValue[T]

  case class Concrete[T](value: T) extends SymbolicValue[T]

  case class NotEqVal[T](variable: Var[T], value: T) extends SymbolicValue[T]

  case class NotInSetValue[T](variable: Var[T], set: Set[T]) extends SymbolicValue[T]

  case class SymbolicDatatypeValue[T](name: String, args: List[SymbolicValue[_]]) extends SymbolicValue[T] {
    // must not be a concrete value
    require(variables.nonEmpty)
  }

  /** smart constructor */
  def SymDatatypeValue[T](name: String, c: List[Any] => T, args: List[SymbolicValue[_]]): SymbolicValue[T] =
    if (args.forall(_.isConcrete))
      Concrete(c(args.map(_.concreteVal)))
    else
      SymbolicDatatypeValue(name, args)


  sealed case class NarrowException[T](variable: Var[T], cause: NarrowCause[T]) extends Exception

  /** for variable of type T */
  sealed abstract class NarrowCause[T]

  case class EqExc[T](value: T) extends NarrowCause[T]

  case class InSetExc[T](setValue: Set[T]) extends NarrowCause[T]

  case class MustBeConcrete[T]() extends NarrowCause[T]

  case class NarrowDatatype[T](index: Int, cause: NarrowCause[_]) extends NarrowCause[T]


  class EvalException(msg: String, exc: Throwable = null) extends Exception(msg, exc)

  case class Ctxt(varValues: HMap[Var, SymbolicValue] = HMap[Var, SymbolicValue]()) {
    def +[T](v: (Var[T], SymbolicValue[T])): Ctxt = copy(varValues = varValues + v)

    def apply[T](v: Var[T]): SymbolicValue[T] =
      varValues.getOrElse(v,
        throw new EvalException(s"Could not find $v in ${varValues.values}"))
  }


  def tryEval[T](expr: Expr[T])(implicit ctxt: Ctxt): Either[NarrowException[_], T] =
    try {
      Right(eval(expr))
    } catch {
      case n: NarrowException[t] =>
        Left(n)
    }

  def eval[T](expr: Expr[T])(implicit ctxt: Ctxt): T = {
    evalS(expr) match {
      case v: Concrete[t] => v.value
      case other =>
        throw NarrowException(other.variables.head, MustBeConcrete())
    }
  }

  //  var i = 0

  def evalS[T](expr: Expr[T])(implicit ctxt: Ctxt): SymbolicValue[T] = expr match {
    case v: Var[t] => ctxt(v)
    case f: Forall[T] =>
      val setV: Iterable[T] = f.typ.values
      val v = f.v
      val body = f.body

      def evalBody(value: SymbolicValue[T]): Boolean = {
        val newCtxt = ctxt + (v -> value)
        //        if (newCtxt.varValues.size == 3) {
        //          i += 1
        //          println(s"$i. exec body with ${newCtxt.varValues}")
        //        }
        eval(body)(newCtxt)
      }

      def loop(values: LazyList[SymbolicValue[T]]): Boolean = {
        for (value <- values) {
          try {
            val res = evalBody(value)
            if (!res)
              return false
          } catch {
            case NarrowException(va1, cause1) if va1 == v =>
              val va = va1.asInstanceOf[Var[T]]
              val cause = cause1.asInstanceOf[NarrowCause[T]]
              cause match {
                case EqExc(value) =>
                  // if value is checked for equality, check once with equal and once with not equal
                  return loop(LazyList(Concrete(value), NotEqVal(v, value)))
                case InSetExc(setValue) =>

                  val vals: LazyList[SymbolicValue[T]] = {
                    if (isSetComplete(setV, setValue)) {
                      // set contains all values, so check with every value
                      setV.to(LazyList).map(v => Concrete(v))
                    } else {
                      // if value is checked in a set, try with symbolic value not in set and all values in set
                      LazyList[SymbolicValue[T]](NotInSetValue(v, setValue)) ++ setValue.to(LazyList).map(v => Concrete(v))
                    }
                  }

                  return loop(vals)
                case MustBeConcrete() =>
                  // if the value must be concrete, try all possible values
                  // TODO if type is a datatype, don't generate symbolic DatatypeValue
                  return loop(setV.to(LazyList).map(v => Concrete(v)))
                case NarrowDatatype(index, cause) =>
                  // TODO refine datatype
                  return loop(setV.to(LazyList).map(v => Concrete(v)))
              }
          }
        }
        true
      }

      val res: Boolean =
        if (setV.isEmpty) {
          true
        } else {
          val initialValues: LazyList[SymbolicValue[T]] =
            if (setV.sizeCompare(3) <= 0) {
              // not worth it to use symbolic values, just check the whole set:
              setV.map(v => Concrete(v)).to(LazyList)
            } else {
              // first try with a symbolic value
              LazyList[SymbolicValue[T]](AnyValue(v))
            }
          loop(initialValues)
        }

      Concrete(res)
    case Neg(negatedExpr) =>
      Concrete(!eval(negatedExpr))
    case And(left, right) =>
      Concrete(eval(left) && eval(right))
    case Eq(left, right) =>


      def checkEq[Q](left: SymbolicValue[Q], right: SymbolicValue[Q]): Boolean = {
        (left, right) match {
          case _ if left == right => true
          case (SymbolicDatatypeValue(name1, args1), SymbolicDatatypeValue(name2, args2)) =>
            if (name1 == name2 && args1.length == args2.length) {
              args1.zip(args2).forall { case (a1, a2) =>
                checkEq(a1.asInstanceOf[SymbolicValue[Any]],
                  a2.asInstanceOf[SymbolicValue[Any]])
              }
            } else {
              false
            }
          case (Concrete(x), Concrete(y)) =>
            x == y
          case (Concrete(x), AnyValue(v)) =>
            throw NarrowException(v, EqExc(x))
          case (AnyValue(v), Concrete(x)) =>
            throw NarrowException(v, EqExc(x))
          case (NotEqVal(x, v1), Concrete(v2)) if v1 == v2 =>
            false
          case (Concrete(v2), NotEqVal(x, v1)) if v1 == v2 =>
            false
          case (x, y) =>
            val v =
              if (x.variables.nonEmpty)
                x.variables.head
              else
                y.variables.head
            throw NarrowException(v, MustBeConcrete())
        }
      }

      val leftV = evalS(left)
      val rightV = evalS(right)

      Concrete(checkEq(leftV, rightV))
    case IsElem(elem, set) =>
      val elemV = evalS(elem)
      val setV = eval(set)

      val res = {
        elemV match {
          case Concrete(x) =>
            setV.contains(x)
          case AnyValue(variable) =>
            throw NarrowException(variable, InSetExc(setV))
          case NotInSetValue(variable, s) if setV.subsetOf(s) =>
            // not in s, therefore not in setV
            false
          case other =>
            throw NarrowException(other.variables.head, MustBeConcrete())
        }
      }


      Concrete(res)
    case c: ConstructDt[t] =>
      SymDatatypeValue(c.name, c.construct, c.args.map(e => evalS(e)))
    case g: Get[k, v] =>
      val m = eval(g.map)
      val k = eval(g.key)
      Concrete(m.getOrElse(k, eval(g.default)))
    case p: Pair[x,y] =>
      Concrete((eval(p.a), eval(p.b)))
    case o: Opaque[a, r] =>
      Concrete(o.func(eval(o.arg)))
    case ConstExpr(v) => Concrete(v)
  }


  /** checks if s contains all possible values */
  private def isSetComplete[T](univ: Iterable[T], s: Set[T]) = {
    univ match {
      case univSet: Set[T] =>
        univSet.subsetOf(s)
      case _ =>
        univ.forall(s.contains)
    }
  }
}
