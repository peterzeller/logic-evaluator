package test

import com.github.peterzeller.logiceval.SimpleLogic
import com.github.peterzeller.logiceval.SimpleLogic.{And, AnyValue, BoolType, BoolVal, ConstExpr, ConstructDt, CustomType, Datatype, DatatypeValue, DtCase, Eq, Expr, MapValue, Neg, SetValue, Type, Value, Var}
import org.scalacheck.{Arbitrary, Gen}
import org.scalacheck._
import Gen._
import Arbitrary.arbitrary
import org.scalacheck.util.Buildable
import test.LogicTypeClasses.valueGen

object LogicTypeClasses {

  def typeGen: Gen[Type] =
    oneOf(
      Gen.const(BoolType),
      Gen.const(CustomType("Int", Set(0, 1, 2, 3, 4).map(AnyValue))),
      genDatatype
    )

  def genDatatype: Gen[Datatype] =
    oneOf(
      // pair
      for (x <- typeGen; y <- typeGen) yield
        Datatype("Prod", List(DtCase("Pair", List(x, y)))),
      // option
      for (x <- typeGen) yield
        Datatype("Option", List(DtCase("None", List()), DtCase("Some", List(x)))),
      // either
      for (x <- typeGen; y <- typeGen) yield
        Datatype("Either", List(
          DtCase("Left", List(x)),
          DtCase("Right", List(y)))),
    )

  def pairGen[A, B](a: Gen[A], b: Gen[B]): Gen[(A, B)] =
    for {
      x <- a
      y <- b
    } yield (x, y)

  //  def genList[T](elemGens: List[Gen[T]]): Gen[List[T]] =
  //    elemGens match {
  //      case Nil =>
  //        List()
  //      case ::(head, next) =>
  //    }

  def valueGen(t: Type): Gen[Value] = t match {
    case SimpleLogic.SetType(elemType) =>
      for {
        elems <- Gen.containerOf[Set, Value](valueGen(elemType))
      } yield SetValue(elems)
    case SimpleLogic.MapType(keyType, valueType) =>
      for {
        elems <- Gen.mapOf[Value, Value](pairGen(valueGen(keyType), valueGen(valueType)))
      } yield MapValue(elems)
    case Datatype(name, cases) =>
      for {
        c <- Gen.oneOf(cases)
        args <- Gen.sequence[List[Value], Value](c.argTypes.map(valueGen))
      } yield
        DatatypeValue(c.name, args)

    case CustomType(name, customValues) =>
      Gen.oneOf(customValues)
    case SimpleLogic.BoolType =>
      Gen.oneOf(BoolVal(false), BoolVal(true))
  }

  def exprGen(t: Type, vars: Map[Var, Type]): Gen[Expr] = {
    t match {
      case SimpleLogic.BoolType =>
        oneOf(
          for (x <- exprGen(t, vars)) yield Neg(x),
          for (x <- exprGen(t, vars); y <- exprGen(t, vars)) yield And(x, y),
          for {
            t <- typeGen
            l <- exprGen(t, vars)
            r <- exprGen(t, vars)
          } yield Eq(l, r)
        )
      case SimpleLogic.Datatype(name, cases) =>
        for {
          c <- Gen.oneOf(cases)
          args <- Gen.sequence[List[Expr], Expr](c.argTypes.map(exprGen(_, vars)))
        } yield ConstructDt(c.name, args)
      case _ =>
        // generate a constant expression for the type
        for {
          elems <- valueGen(t)
        } yield ConstExpr(elems)
    }
  }


  implicit val exprArg: Arbitrary[Expr] = Arbitrary(exprGen(BoolType, Map()))


}
