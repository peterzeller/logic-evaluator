package test

import java.lang.Math.{log, min}

import com.github.peterzeller.logiceval.{SimpleLogic, TypeCheck}
import com.github.peterzeller.logiceval.SimpleLogic._
import com.github.peterzeller.logiceval.utils.HMap
import smallcheck.Series
import smallcheck.Series.{frequency, oneOf, oneOfList, oneOfSeries}

object SmallCheckSeries {

  private val intType = CustomType[Int]("Int")(_.isInstanceOf[Int])
  private val unitType = CustomType[Unit]("Unit")(_.isInstanceOf[Unit])

  private val intDomain: Set[Int] = Set(0, 1, 2)
  private val unitDomain: Set[Unit] = Set(())

  val typeEnv: Env = new Env {
    override def customTypeValues[T](c: CustomType[T]): Iterable[T] = {
      if (c == intType) intDomain.asInstanceOf[Set[T]]
      else if (c == unitType) unitDomain.asInstanceOf[Set[T]]
      else ???
    }
  }

  def typeSeries: Series[Type[Any]] = {
    frequency(List(
      100 -> Series.const(BoolType().asInstanceOf[Type[Any]]),
      100 -> Series.const(intType.asInstanceOf[Type[Any]]),
      10 -> Series.const(unitType.asInstanceOf[Type[Any]]),
      1 -> Series.lzy(genDatatype)
    ))
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

  def genDatatype: Series[Type[Any]] = {
    oneOfSeries(
      // pair
      for (x <- typeSeries; y <- typeSeries) yield
        prodDt(x, y),
      // option
      for (x <- typeSeries) yield
        optionDt(x),
      // either
      for (x <- typeSeries; y <- typeSeries) yield
        eitherDt(x, y),
    ).asInstanceOf[Series[Type[Any]]]
  }

  private def eitherDt(x: Type[Any], y: Type[Any]) = {
    Datatype(s"Either[${x.print}, ${y.print}]", List(
      DtCase[Either[_, _]]("Left", List(x))(constructLeft, _.isLeft, x => List(x.swap.getOrElse(???))),
      DtCase[Either[_, _]]("Right", List(y))(constructRight, _.isRight, x => List(x.getOrElse(???)))))
  }

  private def optionDt(x: Type[Any]) = {
    Datatype(s"Option[${x.print}]", List(
      DtCase[Option[_]]("None", List())(constructNone, _.isEmpty, _ => List()),
      DtCase[Option[_]]("Some", List(x))(constructSome, _.isDefined, x => List(x.get))))
  }

  private def prodDt(x: Type[Any], y: Type[Any]) = {
    Datatype(s"Prod[${x.print}, ${y.print}]", List(
      DtCase[(Any, Any)]("Pair", List(x, y))(constructPair, { case (a, b) => true case _ => false }, x => List(x._1, x._2))))
  }

  def pairSeries[A, B](a: Series[A], b: Series[B]): Series[(A, B)] =
    for {
      x <- a
      y <- b
    } yield (x, y)

  //  def genList[T](elemSeriess: List[Series[T]]): Series[List[T]] =
  //    elemSeriess match {
  //      case Nil =>
  //        List()
  //      case ::(head, next) =>
  //    }

  def valueSeries[T](t: Type[T]): Series[T] =
    t match {
      case st: SimpleLogic.SetType[t] =>
        for {
          elems <- Series.seriesSet(valueSeries(st.elemType))
        } yield elems
      case mt: SimpleLogic.MapType[k, v] =>
        val keyType = mt.keyType
        val valueType = mt.valueType
        for {
          elems <- Series.seriesMap[k, v](
            valueSeries(keyType),
            valueSeries(valueType))
        } yield elems
      case Datatype(name, cases) =>
        for {
          c <- Series.constant(cases)
          args <- Series.sequence(c.argTypes.map((e: Type[_]) => valueSeries(e.asInstanceOf[Type[Any]])))
        } yield {
          c.construct(args)
        }
      case c: CustomType[t] =>
        Series.oneOfList(typeEnv.customTypeValues(c))
      case SimpleLogic.BoolType() =>
        Series.oneOf(false, true)
      case PairType(a, b) =>
        for {
          x <- valueSeries(a)
          y <- valueSeries(b)
        } yield (x, y)
    }

  def nextVar[T](vars: HMap[Var, Type]): Var[T] = {
    var i = 1
    while (vars.contains(Var(s"x$i"))) {
      i += 1
    }
    Var(s"x$i")
  }


  def dtExprWithVar(v: (Var[Any], Type[Any]), vars: HMap[Var, Type]): Series[Expr[Any]] = {
    Series.oneOfSeries(
      Series.const(v._1),
      // product
      for {
        t <- typeSeries
        e <- Series.lzy(exprSeries(t, vars))
        dt1 = prodDt(v._2, t)
        dt2 = prodDt(t, v._2)
        r <- Series.oneOf(
          ConstructDt(dt1, dt1.cases(0), List(v._1, e)),
          ConstructDt(dt2, dt2.cases(0), List(e, v._1))
        )
      } yield r.asInstanceOf[Expr[Any]],
      // either
      for {
        t <- typeSeries
        e <- Series.lzy(exprSeries(t, vars))
        dt1 = eitherDt(v._2, t)
        dt2 = eitherDt(t, v._2)
        r <- Series.oneOf(
          ConstructDt(dt1, dt1.cases(0), List(v._1)),
          ConstructDt(dt2, dt2.cases(1), List(v._1))
        )
      } yield r.asInstanceOf[Expr[Any]],
      // option
      Series.const{
        val dt = optionType(v._2)
        ConstructDt(dt, dt.cases(1), List(v._1)).asInstanceOf[Expr[Any]]
      }
    )

  }

  def exprSeries[T](t: Type[T], vars: HMap[Var, Type]): Series[Expr[T]] = {
    //    if (size <= 0) {
    //      // generate leaf if size is 0
    //      constExprSeries(t, size)
    //    } else {
    val vars2: List[Var[T]] = vars.filter(p => p._2 == t).keys.toList.asInstanceOf[List[Var[T]]]
    val varSeriess: List[(Int, Series[Expr[T]])] = vars2.map(v => (100, Series.const(v)))
    val normalSeriess: List[(Int, Series[Expr[T]])] = {
      t match {
        case SimpleLogic.BoolType() =>
          List(
            200 -> (for {
              x <- Series.lzy(exprSeries(BoolType(), vars))
            } yield Neg(x)),
            150 -> (for {
              x <- Series.lzy(exprSeries(BoolType(), vars))
              y <- Series.lzy(exprSeries(BoolType(), vars))
            } yield And(x, y)),
            100 -> (for {
              v <- Series.oneOfList(vars.map)
              l <- Series.lzy(dtExprWithVar(v.asInstanceOf[(Var[Any], Type[Any])], vars))
              lt = TypeCheck.calcType(l)(TypeCheck.Ctxt(namedVars = vars))
              r <- Series.lzy(exprSeries(lt, vars))
            } yield Eq(l, r).asInstanceOf[Expr[T]]),
            //              50 -> (for {
            //                t: Type[Any] <- Series.oneOfSeries(typeSeries)
            //                l: Expr[Any] <- Series.lzy(exprSeries[Any](t, vars))
            //                r: Expr[Any] <- Series.lzy(exprSeries[Any](t, vars))
            //              } yield Eq[Any](l, r).asInstanceOf[Expr[T]]),
            200 -> (for {
              vt: Type[Any] <- typeSeries
              v: Var[Any] = nextVar(vars)
              b <- Series.lzy(exprSeries(BoolType(), vars + (v -> vt)))
            } yield Forall(v, vt, b)),
            //              30 -> (for {
            //                et <- typeSeries
            //                elem <- Series.lzy(exprSeries(et, vars))
            //                set <- Series.lzy(exprSeries(SetType(et), vars))
            //              } yield IsElem(elem, set))
          )
        case dt@SimpleLogic.Datatype(name, cases) =>
          List(
            100 -> (for {
              c <- Series.oneOfList(cases)
              args <- Series.lzy(Series.sequence(c.argTypes.map(t => exprSeries[Any](t.asInstanceOf[Type[Any]], vars).sized(1 / (c.argTypes.size + 1)))))
            } yield ConstructDt(dt, c, args))
          )
        case _ =>
          // generate a constant expression for the type
          List()
      }
    }
    //      val mapLookupSeries: Series[Expr[T]] =
    //        for {
    //          keyType <- typeSeries
    //          map <- Series.lzy(exprSeries(MapType(keyType, t), vars))
    //          key <- Series.lzy(exprSeries(keyType, vars))
    //          default <- Series.lzy(exprSeries(t, vars))
    //        } yield Get(map, key, default)

    val gens: List[(Int, Series[Expr[T]])] = varSeriess ++ normalSeriess ++ List(
      5 -> constExprSeries(t.asInstanceOf[Type[T]]),
      //        1 -> mapLookupSeries
    )


    Series.frequency(gens).limited(_ ^ 2).asInstanceOf[Series[Expr[T]]]
    //    }
  }


  private def constExprSeries[T](t: Type[T]): Series[Expr[T]] = {
    for {
      elems <- valueSeries(t)
    } yield ConstExpr(elems)(t)
  }

  implicit val implicitExprSeries: Series[Expr[Boolean]] = {
    exprSeries(BoolType(), HMap[Var, Type]())
  }


}
