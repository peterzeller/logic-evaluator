package com.github.peterzeller.logiceval

import com.github.peterzeller.logiceval.utils.{LazyListUtils, PrettyPrintDoc}
import scala.reflect.runtime.universe._

import scala.math.Ordered.orderingToOrdered
import scala.math.Ordering.Implicits.seqOrdering

/**
 * Example logic
 */
object SimpleLogic {

  abstract class TypeEnv {
    def customTypeValues[T](c: CustomType[T]): Iterable[T]
  }

  sealed abstract class Type[T] {
    def print: String = PrettyPrinting.printTyp(this).prettyStr(120)

    def values(env: TypeEnv): Iterable[T]

    def cast(x: Any): T =
      x.asInstanceOf[T]

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
    override def values(env: TypeEnv): Iterable[Set[T]] = ???
  }

  case class MapType[K, V](keyType: Type[K], valueType: Type[V]) extends Type[Map[K, V]] {
    override def values(env: TypeEnv): Iterable[Map[K, V]] = ???
  }

  case class Datatype[T](name: String, cases: List[DtCase[T]]) extends Type[T] {
    override def values(env: TypeEnv): Iterable[T] = {
      for {
        c <- cases.to(LazyList)
        argList = c.argTypes.map(_.values(env).to(LazyList))
        args <- LazyListUtils.allCombinations(argList)
      } yield {
        c.construct(args)
      }
    }
  }

  case class DtCase[T](name: String, argTypes: List[Type[_]], construct: List[Any] => T)

  case class CustomType[T](name: String) extends Type[T] {
    override def values(env: TypeEnv): Iterable[T] = env.customTypeValues(this)
  }

  case class PairType[A, B](a: Type[A], b: Type[B]) extends Type[(A, B)] {
    override def values(env: TypeEnv): Iterable[(A, B)] =
      for {
        x <- a.values(env)
        y <- b.values(env)
      } yield (x, y)
  }

  case class BoolType() extends Type[Boolean] {
    override def values(env: TypeEnv): Iterable[Boolean] = bools
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
      DtCase("None", List(), x => Some(t.cast(x.head))),
      DtCase("Some", List(t), x => None)
    ))

  def SomeE[T](elem: Expr[T])(implicit t: Type[T]): Expr[Option[T]] =
    ConstructDt(optionType(t), "Some", x => Some(x.head.asInstanceOf[T]), List(elem))

  def NoneE[T](implicit t: Type[T]): Expr[Option[T]] =
    ConstructDt(optionType(t), "None", _ => None, List())


  case class Get[K, V](map: Expr[Map[K, V]], key: Expr[K], default: Expr[V]) extends Expr[V]

  case class Pair[A, B](a: Expr[A], b: Expr[B]) extends Expr[(A, B)]

  case class Opaque[A, R](argType: Type[A], resultType: Type[R], func: A => R, arg: Expr[A]) extends Expr[R]

  case class ConstExpr[T](v: T)(implicit val typ: Type[T]) extends Expr[T]

  //  case class DatatypeValue(name: String, args: T)


}
