package test

import com.github.peterzeller.logiceval.SimpleLogic._
import com.github.peterzeller.logiceval.{NarrowingEvaluator, SimpleEvaluator, SimpleLogic, TypeCheck}
import org.scalacheck.Prop.forAll
import org.scalacheck.Test
import org.scalatest.funsuite.AnyFunSuite
import smallcheck.{Property, SmallCheck}
import test.LogicTypeClasses._
import test.SmallCheckSeries.implicitExprSeries


class NarrowingEvaluatorTest extends AnyFunSuite {
  //  "The Hello object" should "say hello" in {
  //    Hello.greeting shouldEqual "hello"
  //  }


  def measure[T](f: () => T): (Long, T) = {
    val t0 = System.nanoTime()
    val res = f()
    val dur = System.nanoTime() - t0
    (dur, res)
  }


  def testExpr(expr: Expr[_])(implicit typeEnv: Env): Unit = {
    println(s"$expr")
    val (t1, r1) = measure(() => SimpleEvaluator.startEval(expr, typeEnv))
    val (t2, r2) = measure(() => NarrowingEvaluator.startEval(expr, typeEnv))

    val ratio = t2.toDouble / t1.toDouble

    println(s"Times: $t1 -- $t2 // ratio = $ratio")
    println()
    assert(r1 == r2)
  }

  test("equals formula") {
    /*
    ¬(¬(∀x1: Int.
      ∀x2: Int.
        ¬(∀x3: Int.
          x2 = x3
            ∧ x1
              ∈ {1800, 203, 1515, 891, 885, 32, 200, 1622, 1635, 1688, 241, 1356, 494, 576, 1418, 1040, 311, 373, 1596, 1049, 446, 370, 412, 62, 1941, 1541, 967, 1247, 829, 902, 914, 1038, 1647, 746, 2000, 509, 1281, 236, 1373, 575, 1268, 175, 1151, 390, 1939, 677, 239, 513, 1052, 34, 1537, 61, 978, 1750, 443, 695, 687, 755, 420, 340, 1771, 155, 628, 1134, 1360})))
  */
    val x1 = Var[Int]("x1")
    val x2 = Var[Int]("x2")
    val x3 = Var[Int]("x3")
    val S = Set(1800, 203, 1515, 891, 885, 32, 200, 1622, 1635, 1688, 241, 1356, 494, 576, 1418, 1040, 311, 373, 1596, 1049, 446, 370, 412, 62, 1941, 1541, 967, 1247, 829, 902, 914, 1038, 1647, 746, 2000, 509, 1281, 236, 1373, 575, 1268, 175, 1151, 390, 1939, 677, 239, 513, 1052, 34, 1537, 61, 978, 1750, 443, 695, 687, 755, 420, 340, 1771, 155, 628, 1134, 1360)

    val intDom = Range.inclusive(0, 2000).toSet
    implicit val t_int: Type[Int] = CustomType("Int")(_.isInstanceOf[Int])
    implicit val t_int_set: Type[Set[Int]] = SetType(t_int)

    implicit val typeEnv: Env = new Env {
      override def customTypeValues[T](c: CustomType[T]): Iterable[T] = intDom.asInstanceOf[Set[T]]
    }

    testExpr(
      Neg(
        Neg(
          Forall(x1, t_int,
            Forall(x2, t_int,
              Neg(Forall(x3, t_int,
                And(
                  Eq(x2, x3),
                  IsElem(x1, ConstExpr(S))
                )
              ))
            )
          )
        )
      ))

  }

  test("simpleEq") {
    val x1 = Var[Int]("x1")


    val intDom: Seq[Int] = Range.inclusive(0, 100000)
    implicit val t_int: Type[Int] = CustomType("Int")(_.isInstanceOf[Int])
    implicit val t_int_set: Type[Set[Int]] = SetType(t_int)

    implicit val typeEnv: Env = new Env {
      override def customTypeValues[T](c: CustomType[T]): Iterable[T] = intDom.asInstanceOf[Iterable[T]]
    }

    testExpr(
      Forall(x1, t_int,
        Neg(Eq(x1, ConstExpr(99999))
        )
      ))

    testExpr(
      Forall(x1, t_int,
        Eq(x1, ConstExpr(99999))
      ))

  }

  test("simpleEq unit") {
    val x1 = Var[Unit]("x1")


    val intDom = Set(())
    implicit val t_unit: Type[Unit] = CustomType("Unit")(_.isInstanceOf[Unit])
    implicit val t_int_set: Type[Set[Unit]] = SetType(t_unit)

    implicit val typeEnv: Env = new Env {
      override def customTypeValues[T](c: CustomType[T]): Iterable[T] = intDom.asInstanceOf[Iterable[T]]
    }

    testExpr(
      Forall(x1, t_unit,
        Neg(Eq(x1, ConstExpr(()))
        )
      ))

    testExpr(
      Forall(x1, t_unit,
        Eq(x1, ConstExpr(()))
      ))

  }

  test("simpleEq empty") {
    val x1 = Var[Unit]("x1")
    val x2 = Var[Unit]("x1")
    val x3 = Var[Unit]("x1")

    val intDom = Set()
    implicit val t_unit: Type[Unit] = CustomType("Unit")(_.isInstanceOf[Unit])
    implicit val t_int_set: Type[Set[Unit]] = SetType(t_unit)

    implicit val typeEnv: Env = new Env {
      override def customTypeValues[T](c: CustomType[T]): Iterable[T] = intDom.asInstanceOf[Iterable[T]]
    }

    testExpr(
      Forall(x1, t_unit,
        Forall(x2, t_unit,
          Forall(x3, t_unit,
            Neg(Eq(x2, x1)
            )
          )
        )
      )
    )


  }

  test("datatype eq") {
    val x1 = Var[Int]("x1")


    val intDom = Range.inclusive(0, 100)
    implicit val t_int: Type[Int] = CustomType("Int")(_.isInstanceOf[Int])
    implicit val t_int_set: Type[Set[Int]] = SetType(t_int)

    implicit def t_option[T](implicit t: Type[T]): Datatype[Option[T]] = SimpleLogic.optionType(t)

    implicit val typeEnv: Env = new Env {
      override def customTypeValues[T](c: CustomType[T]): Iterable[T] = intDom.asInstanceOf[Iterable[T]]
    }

    val t_option_int = t_option(t_int)
    testExpr(
      Forall(x1, t_int,
        Neg(Eq(
          ConstructDt(t_option_int, t_option_int.cases(1), List(x1)),
          ConstExpr[Option[Int]](Some(42)))
        )
      ))

  }


  test("equals formula short") {
    /*
    ¬(¬(∀x1: Int. ∀x2: Int. ¬(∀x3: Int. x2 = x3 ∧ x1 ∈ {2, 3})))
  */
    val x1 = Var[Int]("x1")
    val x2 = Var[Int]("x2")
    val x3 = Var[Int]("x3")
    val S = Set(2, 3)


    val intDom = Range.inclusive(0, 5)
    implicit val t_int: Type[Int] = CustomType("Int")(_.isInstanceOf[Int])
    implicit val t_int_set: Type[Set[Int]] = SetType(t_int)

    implicit val typeEnv: Env = new Env {
      override def customTypeValues[T](c: CustomType[T]): Iterable[T] = intDom.asInstanceOf[Iterable[T]]
    }

    testExpr(
      Neg(
        Neg(
          Forall(x1, t_int,
            Forall(x2, t_int,
              Neg(Forall(x3, t_int,
                And(
                  Eq(x2, x3),
                  IsElem(x1, ConstExpr(S))
                )
              ))
            )
          )
        )
      ))

  }

  test("ScalaCheck: equal to simple evaluator") {
    println("Foo")
    var timeS = 0L
    var timeN = 0L
    var maxTime = 0L
    var i = 0L

    val prop = forAll { (expr: Expr[Boolean]) =>
      System.gc()

      TypeCheck.checkType(expr)(TypeCheck.Ctxt())

      i += 1
      println(s"$i. $expr")

      val (t1, r1) = measure(() => SimpleEvaluator.startEval(expr, typeEnv))
      val (t2, r2) = measure(() => NarrowingEvaluator.startEval(expr, typeEnv))


      timeS += t1
      timeN += t2


      val ratio = t2.toDouble / t1.toDouble
      if (t1 > maxTime) {
        maxTime = t1
      }

      println(s"ratio = $ratio")
      println(s"Times: $t1 -- $t2   // overall: $timeS  -- $timeN // ${timeN.toDouble / timeS}")
      println()


      r1 == r2
    }
    val params = Test.Parameters.default.withMinSuccessfulTests(5000)
      .withMaxSize(100000)
    val res: Test.Result = Test.check(params, prop)
    println(s"res = $res")
    res.status match {
      case Test.Passed =>
        println("passed")
      case Test.Proved(args) =>
        println("proved")
      case Test.Failed(args, labels) =>
        val expr: Expr[_] = args.head.arg.asInstanceOf[Expr[_]]
        fail(
          s"""
             |Failed for
             |$expr
             |
             |SimpleEval: ${SimpleEvaluator.startEval(expr, typeEnv)}
             |NarrowEval: ${NarrowingEvaluator.startEval(expr, typeEnv)}
             |""".stripMargin)
      case Test.Exhausted =>
        println("exhausted")
      case Test.PropException(args, e, labels) =>
        println("prop exception")
        e.printStackTrace(System.out)
    }
    assert(res.passed)
    //    prop.check()

  }


  test("SmallCheck: equal to simple evaluator") {

    SmallCheck.check(2000) { (expr: Expr[Boolean]) =>
      TypeCheck.checkType(expr)(TypeCheck.Ctxt())

      val r1 = SimpleEvaluator.startEval(expr, typeEnv)
      val r2 = NarrowingEvaluator.startEval(expr, typeEnv)
      r1 == r2
    }

  }


}
