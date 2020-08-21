package test

import java.lang.Math.{log, min}

import com.github.peterzeller.logiceval.SimpleLogic
import com.github.peterzeller.logiceval.SimpleLogic._
import com.github.peterzeller.logiceval.utils.HMap
import org.scalacheck.Gen._
import org.scalacheck.{Arbitrary, Gen}

object LogicTypeClasses {

  private val intType = CustomType[Int]("Int")(_.isInstanceOf[Int])
  private val unitType = CustomType[Unit]("Unit")(_.isInstanceOf[Unit])

  private val intDomain = (0 to 5).toSet
  private val unitDomain = Set(())

  val typeEnv: Env = new Env {
    override def customTypeValues[T](c: CustomType[T]): Iterable[T] = {
      if (c == intType) intDomain.asInstanceOf[Set[T]]
      else if (c == unitType) unitDomain.asInstanceOf[Set[T]]
      else ???
    }
  }

  def typeGen(size: Int): Gen[Type[Any]] = {
    oneOf(
      Gen.const(BoolType()),
      Gen.const(intType),
      Gen.const(unitType),
      if (size <= 0) Gen.const(BoolType()) else Gen.lzy(genDatatype(size))
    ).asInstanceOf[Gen[Type[Any]]]
  }

  /** estimate size of a type */
  def typeSize(x: Type[_]): Int = x match {
    case SetType(elemType) =>
      Math.pow(2, typeSize(elemType)).toInt
    case MapType(keyType, valueType) =>
      Math.pow(2, typeSize(keyType) + typeSize(valueType)).toInt
    case Datatype(name, cases) =>
      cases.map(c => c.argTypes.map(t => typeSize(t)).product).sum
    case c: CustomType[t] =>
      typeEnv.customTypeValues(c).size
    case SimpleLogic.BoolType() =>
      2
    case PairType(a, b) =>
      typeSize(a) * typeSize(b)
  }

  def constructPair(p: List[Any]): (Any, Any) =
    (p(0), p(1))

  def constructSome(p: List[Any]): Option[Any] =
    Some(p(0))

  def constructNone(p: List[Any]): Option[Any] =
    None

  def constructLeft(p: List[Any]): Either[Any, Any] =
    Left(p(0))

  def constructRight(p: List[Any]): Either[Any, Any] =
    Right(p(0))

  def genDatatype[T](size: Int): Gen[Datatype[T]] = {
    oneOf(
      // pair
      for (x <- typeGen(size / 3); y <- typeGen(size / typeSize(x))) yield
        Datatype(s"Prod[${x.print}, ${y.print}]", List(
          DtCase[(Any, Any)]("Pair", List(x, y))(constructPair, { case (a, b) => true case _ => false }, x => List(x._1, x._2)))),
      // option
      for (x <- typeGen(size / 2)) yield
        Datatype(s"Option[${x.print}]", List(
          DtCase[Option[_]]("None", List())(constructNone, _.isEmpty, _ => List()),
          DtCase[Option[_]]("Some", List(x))(constructSome, _.isDefined, x => List(x.get)))),
      // either
      for (x <- typeGen(size / 3); y <- typeGen(size / typeSize(x))) yield
        Datatype(s"Either[${x.print}, ${y.print}]", List(
          DtCase[Either[_, _]]("Left", List(x))(constructLeft, _.isLeft, x => List(x.swap.getOrElse(???))),
          DtCase[Either[_, _]]("Right", List(y))(constructRight, _.isRight, x => List(x.getOrElse(???))))),
    ).asInstanceOf[Gen[Datatype[T]]]
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

  def valueGen[T](t: Type[T], size: Int): Gen[T] = {
    t match {
      case st: SimpleLogic.SetType[t] =>
        for {
          elems <- Gen.containerOfN[Set, t](min(typeSize(t), log(size).toInt), valueGen(st.elemType, size / 2))
        } yield elems
      case mt: SimpleLogic.MapType[k, v] =>
        val keyType = mt.keyType
        val valueType = mt.valueType
        for {
          elems <- Gen.mapOfN[k, v](min(typeSize(keyType), log(size).toInt),
            pairGen(valueGen(keyType, size / 2),
              valueGen(valueType, size / 2)))
        } yield elems
      case Datatype(name, cases) =>
        for {
          c <- Gen.oneOf(cases)
          args <- Gen.sequence[List[Any], Any](c.argTypes.map(valueGen(_, size / 2)))
        } yield {
          c.construct(args)
        }
      case c: CustomType[t] =>
        Gen.oneOf(typeEnv.customTypeValues(c))
      case SimpleLogic.BoolType() =>
        Gen.oneOf(false, true)
      case PairType(a, b) =>
        for {
          x <- valueGen(a, size / 2)
          y <- valueGen(b, size / 2)
        } yield (x, y)
    }
  }

  def nextVar[T](vars: HMap[Var, Type]): Var[T] = {
    var i = 1
    while (vars.contains(Var(s"x$i"))) {
      i += 1
    }
    Var(s"x$i")
  }


  def exprGen[T](t: Type[T], size: Int, vars: HMap[Var, Type]): Gen[Expr[T]] = {
    if (size <= 0) {
      // generate leaf if size is 0
      constExprGen(t, size)
    } else {
      val vars2: List[Var[_]] = vars.filter(p => p._2 == t).keys.toList
      val varGens: List[(Int, Gen[Expr[_]])] = vars2.map(v => (100, Gen.const(v)))
      val normalGens: List[(Int, Gen[Expr[_]])] = {
        t match {
          case SimpleLogic.BoolType() =>
            val varTypesGen: List[Gen[Type[Any]]] = vars.values.map(Gen.const).toList.asInstanceOf[List[Gen[Type[Any]]]]
            List(
              200 -> (for {
                x <- Gen.lzy(exprGen(BoolType(), size - 1, vars))
              } yield Neg(x)),
              150 -> (for {
                x <- Gen.lzy(exprGen(BoolType(), size / 2, vars))
                y <- Gen.lzy(exprGen(BoolType(), size / 2, vars))
              } yield And(x, y)),
              50 -> (for {
                t: Type[Any] <- oneOfL(typeGen(size / 3) :: varTypesGen)
                l: Expr[Any] <- Gen.lzy(exprGen[Any](t, size / 3, vars))
                r: Expr[Any] <- Gen.lzy(exprGen[Any](t, size / 3, vars))
              } yield Eq[Any](l, r).asInstanceOf[Expr[T]]),
              200 -> (for {
                vt: Type[Any] <- typeGen(size / 2)
                v: Var[Any] = nextVar(vars)
                b <- Gen.lzy(exprGen(BoolType(), size / 2, vars + (v -> vt)))
              } yield Forall(v, vt, b)),
              30 -> (for {
                et <- typeGen(size / 2)
                elem <- Gen.lzy(exprGen(et, size / 2, vars))
                set <- Gen.lzy(exprGen(SetType(et), size / 2, vars))
              } yield IsElem(elem, set))
            )
          case dt@SimpleLogic.Datatype(name, cases) =>
            List(
              100 -> (for {
                c <- Gen.oneOf(cases)
                args <- Gen.lzy(Gen.sequence[List[Expr[_]], Expr[_]](c.argTypes.map(exprGen(_, size / c.argTypes.size - 1, vars))))
              } yield ConstructDt(dt, c, args))
            )
          case _ =>
            // generate a constant expression for the type
            List()
        }
      }
      val mapLookupGen: Gen[Expr[_]] =
        for {
          keyType <- typeGen(size / 2)
          map <- Gen.lzy(exprGen(MapType(keyType, t), size / 2, vars))
          key <- Gen.lzy(exprGen(keyType, size / 2, vars))
          default <- Gen.lzy(exprGen(t, size / 2, vars))
        } yield Get(map, key, default)

      val gens: List[(Int, Gen[Expr[_]])] = varGens ++ normalGens ++ List(
        5 -> constExprGen(t, size),
        1 -> mapLookupGen
      )


      Gen.frequency(gens: _*).asInstanceOf[Gen[Expr[T]]]
    }
  }

  def oneOfL[T](l: List[Gen[T]]): Gen[T] = l match {
    case List(x) => x
    case x :: y :: zs => Gen.oneOf(x, y, zs: _*)
  }

  private def constExprGen[T](t: Type[T], size: Int): Gen[Expr[T]] = {
    for {
      elems <- valueGen(t, size)
    } yield ConstExpr(elems)(t)
  }

  implicit val exprArg: Arbitrary[Expr[Boolean]] = Arbitrary(
    Gen.sized(size => exprGen(BoolType(), size, HMap[Var, Type]())))


}
