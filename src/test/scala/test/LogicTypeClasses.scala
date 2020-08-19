package test

import com.github.peterzeller.logiceval.SimpleLogic
import com.github.peterzeller.logiceval.SimpleLogic.{And, AnyValue, BoolType, BoolVal, ConstExpr, ConstructDt, CustomType, Datatype, DatatypeValue, DtCase, Eq, Expr, Forall, Get, IsElem, MapType, MapValue, Neg, SetType, SetValue, Type, Value, Var}
import org.scalacheck.{Arbitrary, Gen}
import org.scalacheck._
import Gen._
import Arbitrary.arbitrary
import org.scalacheck.util.Buildable
import test.LogicTypeClasses.valueGen

import scala.collection.immutable

object LogicTypeClasses {

  private val intType = CustomType("Int", (0 to 5).map(AnyValue).toSet)
  private val unitType = CustomType("Unit", Set(0).map(AnyValue))


  def typeGen(size: Int): Gen[Type] = {
    oneOf(
      Gen.const(BoolType),
      Gen.const(intType),
      Gen.const(unitType),
      if (size <= 0) Gen.const(BoolType) else Gen.lzy(genDatatype(size))
    )
  }

  def typeSize(x: Type): Int = x match {
    case SetType(elemType) =>
      Math.pow(2, typeSize(elemType)).toInt
    case MapType(keyType, valueType) =>
      Math.pow(2, typeSize(keyType) + typeSize(valueType)).toInt
    case Datatype(name, cases) =>
      cases.map(c => c.argTypes.map(t => typeSize(t)).product).sum
    case CustomType(name, customValues) =>
      customValues.size
    case SimpleLogic.BoolType =>
      2
  }

  def genDatatype(size: Int): Gen[Datatype] = {
    oneOf(
      // pair
      for (x <- typeGen(size / 3); y <- typeGen(size / typeSize(x))) yield
        Datatype(s"Prod[${x.print}, ${y.print}]", List(DtCase("Pair", List(x, y)))),
      // option
      for (x <- typeGen(size / 2)) yield
        Datatype(s"Option[${x.print}]", List(DtCase("None", List()), DtCase("Some", List(x)))),
      // either
      for (x <- typeGen(size / 3); y <- typeGen(size / typeSize(x))) yield
        Datatype(s"Either[${x.print}, ${y.print}]", List(
          DtCase("Left", List(x)),
          DtCase("Right", List(y)))),
    )
  }

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

  def valueGen(t: Type, size: Int): Gen[Value] = {
    t match {
      case SimpleLogic.SetType(elemType) =>
        for {
          elems <- Gen.containerOfN[Set, Value](size, valueGen(elemType, size / 2))
        } yield SetValue(elems)
      case SimpleLogic.MapType(keyType, valueType) =>
        for {
          elems <- Gen.mapOfN[Value, Value](size,
            pairGen(valueGen(keyType, size / 2),
              valueGen(valueType, size/2)))
          default <- valueGen(valueType, size/2)
        } yield MapValue(elems, default)
      case Datatype(name, cases) =>
        for {
          c <- Gen.oneOf(cases)
          args <- Gen.sequence[List[Value], Value](c.argTypes.map(valueGen(_, size/2)))
        } yield
          DatatypeValue(c.name, args)
      case CustomType(name, customValues) =>
        Gen.oneOf(customValues)
      case SimpleLogic.BoolType =>
        Gen.oneOf(BoolVal(false), BoolVal(true))
    }
  }

  def nextVar(vars: Map[Var, Type]): Var = {
    var i = 1
    while (vars.contains(Var(s"x$i"))) {
      i += 1
    }
    Var(s"x$i")
  }

  def exprGen(t: Type, size: Int, vars: Map[Var, Type]): Gen[Expr] = {
    if (size <= 0) {
      // generate leaf if size is 0
      constExprGen(t, size)
    } else {
      val vars2: List[Var] = vars.filter(p => p._2 == t).keys.toList
      val varGens: List[(Int, Gen[Expr])] = vars2.map(v => (100, Gen.const(v)))
      val normalGens: List[(Int, Gen[Expr])] = {
        t match {
          case SimpleLogic.BoolType =>
            List(
              200 -> (for {
                x <- Gen.lzy(exprGen(BoolType, size - 1, vars))
              } yield Neg(x)),
              150 -> (for {
                x <- Gen.lzy(exprGen(BoolType, size / 2, vars))
                y <- Gen.lzy(exprGen(BoolType, size / 2, vars))
              } yield And(x, y)),
              50 -> (for {
                t <- oneOfL(typeGen(size / 3) :: vars.values.map(Gen.const).toList)
                l <- Gen.lzy(exprGen(t, size / 3, vars))
                r <- Gen.lzy(exprGen(t, size / 3, vars))
              } yield Eq(l, r)),
              200 -> (for {
                vt <- typeGen(size / 2)
                v = nextVar(vars)
                b <- Gen.lzy(exprGen(BoolType, size / 2, vars + (v -> vt)))
              } yield Forall(v, vt, b)),
              30 -> (for {
                et <- typeGen(size / 2)
                elem <- Gen.lzy(exprGen(et, size / 2, vars))
                set <- Gen.lzy(exprGen(SetType(et), size / 2, vars))
              } yield IsElem(elem, set))
            )
          case SimpleLogic.Datatype(name, cases) =>
            List(
              100 -> (for {
                c <- Gen.oneOf(cases)
                args <- Gen.lzy(Gen.sequence[List[Expr], Expr](c.argTypes.map(exprGen(_, size / c.argTypes.size - 1, vars))))
              } yield ConstructDt(c.name, args))
            )
          case _ =>
            // generate a constant expression for the type
            List()
        }
      }
      val mapLookupGen: Gen[Expr] =
        for {
          keyType <- typeGen(size / 2)
          map <- Gen.lzy(exprGen(MapType(keyType, t), size / 2, vars))
          key <- Gen.lzy(exprGen(keyType, size / 2, vars))
        } yield Get(map, key)

      val gens: List[(Int, Gen[Expr])] = varGens ++ normalGens ++ List(
        5 ->  constExprGen(t, size),
        1 -> mapLookupGen
      )


      Gen.frequency(gens: _*)
    }
  }

  def oneOfL[T](l: List[Gen[T]]): Gen[T] = l match {
    case List(x) => x
    case x :: y :: zs => Gen.oneOf(x, y, zs: _*)
  }

  private def constExprGen(t: Type, size: Int): Gen[Expr] = {
    for {
      elems <- valueGen(t, size)
    } yield ConstExpr(elems)
  }

  implicit val exprArg: Arbitrary[Expr] = Arbitrary(
    Gen.sized(size => exprGen(BoolType, size, Map())))


}
