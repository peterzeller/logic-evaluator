package com.github.peterzeller.logiceval

import com.github.peterzeller.logiceval.utils.{LazyListUtils, PrettyPrintDoc}
import scala.reflect.runtime.universe._

import scala.math.Ordered.orderingToOrdered
import scala.math.Ordering.Implicits.seqOrdering

/**
 * Example logic
 */
object SimpleLogic {

  /**
   * Environment in which formulas are evaluated
   */
  abstract class Env {
    def customTypeValues[T](c: CustomType[T]): Iterable[T]
  }

  sealed abstract class Type[T] {
    def print: String = PrettyPrinting.printTyp(this).prettyStr(120)

    def values(env: Env): Iterable[T]

    def castU(x: Any): T = {
      x.asInstanceOf[T]
    }

    def cast(x: Any): T = {
      require(check(x), s"$x (${x.getClass}) is not a member of $this")
      x.asInstanceOf[T]
    }

    /** checks if x is a value of this type */
    def check(x: Any): Boolean

    //    def values: Iterable[T] = this match {
    //      case SetType(elemType) => ???
    //      case MapType(keyType, valueType) => ???
    //      case Datatype(name, cases) =>
    //        for {
    //          c <- cases.to(LazyList)
    //          argList = c.argTypes.map(_.values.to(LazyList))
    //          args <- LazyListUtils.allCombinations(argList)
    //        } yield {
    //          c.construct(args)
    //        }
    //      case CustomType(name, customValues) => customValues
    //      case BoolType() => Set(false, true)
    //    }
  }

  case class SetType[T](elemType: Type[T]) extends Type[Set[T]] {
    override def values(env: Env): Iterable[Set[T]] = ???

    /** checks if x is a value of this type */
    override def check(x: Any): Boolean =
      x match {
        case s: Set[_] =>
          s.forall(elemType.check)
        case _ => false
      }
  }

  case class MapType[K, V](keyType: Type[K], valueType: Type[V]) extends Type[Map[K, V]] {
    override def values(env: Env): Iterable[Map[K, V]] = ???

    override def check(x: Any): Boolean =
      x match {
        case m: Map[_, _] =>
          m.forall(e => keyType.check(e._1) && valueType.check(e._2))
        case _ => false
      }
  }

  case class Datatype[T](name: String, cases: List[DtCase[T]]) extends Type[T] {
    override def values(env: Env): Iterable[T] = {
      for {
        c <- cases.to(LazyList)
        argList = c.argTypes.map(_.values(env).to(LazyList))
        args <- LazyListUtils.allCombinations(argList)
      } yield {
        c.construct(args)
      }
    }

    /** checks if x is a value of this type */
    override def check(x: Any): Boolean =
      cases.exists(c => c.check(x) )
  }

  case class DtCase[T](name: String, argTypes: List[Type[_]])(val construct: List[Any] => T, checkC: T => Boolean, args: T => List[Any]) {

    def checkShallow(x: Any): Boolean =
      try {
        checkC(x.asInstanceOf[T])
      } catch {
        case _: Throwable => false
      }

    // checks whether x is of this case
    def check(x: Any): Boolean =
      checkShallow(x) && extractArgs(x).zip(argTypes).forall(e => e._2.check(e._1))

    def extractArgs(x: Any): List[Any] =
      args(x.asInstanceOf[T])

  }

  case class CustomType[T](name: String)(checkA: Any => Boolean) extends Type[T] {
    override def values(env: Env): Iterable[T] = env.customTypeValues(this)

    /** checks if x is a value of this type */
    override def check(x: Any): Boolean =
      checkA(x)
  }

  case class PairType[A, B](a: Type[A], b: Type[B]) extends Type[(A, B)] {
    override def values(env: Env): Iterable[(A, B)] =
      for {
        x <- a.values(env)
        y <- b.values(env)
      } yield (x, y)

    /** checks if x is a value of this type */
    override def check(x: Any): Boolean =
      x match {
        case (xa, xb) =>
          a.check(xa) && b.check(xb)
        case _ =>
          false
      }
  }

  case class BoolType() extends Type[Boolean] {
    override def values(env: Env): Iterable[Boolean] = bools

    /** checks if x is a value of this type */
    override def check(x: Any): Boolean =
      x.isInstanceOf[Boolean]
  }

  private val bools = Set(false, true)


  sealed abstract class Expr[T] {
    def doc: PrettyPrintDoc.Doc = PrettyPrinting.printExpr(this, 100)

    override def toString: String = doc.prettyStr(120)

    def freeVars: Set[Var[_]] = this match {
      case v: Var[_] => Set(v)
      case f: Forall[t] =>
        f.body.freeVars - f.v
      case n: Neg =>
        n.negatedExpr.freeVars
      case a: And =>
        a.left.freeVars ++ a.right.freeVars
      case e: Eq[t] =>
        e.left.freeVars ++ e.right.freeVars
      case e: IsElem[t] =>
        e.elem.freeVars ++ e.set.freeVars
      case c: ConstructDt[t] =>
        c.args.view.flatMap(_.freeVars).toSet
      case e: Get[k, v] =>
        e.map.freeVars ++ e.key.freeVars
      case p: Pair[_, _] =>
        p.a.freeVars ++ p.b.freeVars
      case o: Opaque[_, _] =>
        o.arg.freeVars
      case c: ConstExpr[_] =>
        Set()
    }
  }

  case class Var[T](name: String) extends Expr[T]

  case class Forall[T](v: Var[T], typ: Type[T], body: Expr[Boolean]) extends Expr[Boolean]

  case class Neg(negatedExpr: Expr[Boolean]) extends Expr[Boolean]

  case class And(left: Expr[Boolean], right: Expr[Boolean]) extends Expr[Boolean]

  case class Eq[T](left: Expr[T], right: Expr[T]) extends Expr[Boolean]

  case class IsElem[T](elem: Expr[T], set: Expr[Set[T]]) extends Expr[Boolean]

  case class ConstructDt[T](typ: Datatype[T], name: String, construct: List[Any] => T, args: List[Expr[_]]) extends Expr[T]

  def optionType[T](t: Type[T]): Datatype[Option[T]] =
    Datatype("Option", List(
      DtCase("None", List())(x => None, _.isEmpty, x => List()),
      DtCase("Some", List(t))(x => Some(t.cast(x.head)), _.isDefined, x => List(x.get))
    ))

  def SomeE[T](elem: Expr[T])(implicit t: Type[T]): Expr[Option[T]] =
    ConstructDt(optionType(t), "Some", x => Some(x.head.asInstanceOf[T]), List(elem))

  def NoneE[T](implicit t: Type[T]): Expr[Option[T]] =
    ConstructDt(optionType(t), "None", _ => None, List())


  case class Get[K, V](map: Expr[Map[K, V]], key: Expr[K], default: Expr[V]) extends Expr[V]

  case class Pair[A, B](a: Expr[A], b: Expr[B]) extends Expr[(A, B)]

  case class Opaque[A, R](argType: Type[A], resultType: Type[R], func: (Env, A) => R, arg: Expr[A]) extends Expr[R]

  case class ConstExpr[T](v: T)(implicit val typ: Type[T]) extends Expr[T]

  //  case class DatatypeValue(name: String, args: T)


}
