package test

import com.github.peterzeller.logiceval.{NarrowingEvaluator, SimpleEvaluator}
import com.github.peterzeller.logiceval.SimpleLogic._
import org.scalacheck.{Prop, Properties, Test}
import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers
import org.scalacheck.Prop.forAll
import org.scalacheck.util.Pretty
import test.LogicTypeClasses._

import scala.collection.immutable.TreeSet


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

  test("equal to simple evaluator") {
    println("Foo")
    var timeS = 0L
    var timeN = 0L
    var maxTime = 0L
    var i = 0L

    val prop = forAll { (expr: Expr) =>
      System.gc()

      i += 1
      println(s"$i. $expr")

      val (t1, r1) = measure(() => SimpleEvaluator.startEval(expr))
      val (t2, r2) = measure(() => NarrowingEvaluator.startEval(expr))


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
    val params = Test.Parameters.default.withMinSuccessfulTests(1000)
      .withMaxSize(100000)
    val res: Test.Result = Test.check(params, prop)
    println(s"res = $res")
    res.status match {
      case Test.Passed =>
        println("passed")
      case Test.Proved(args) =>
        println("proved")
      case Test.Failed(args, labels) =>
        val expr: Expr = args.head.arg.asInstanceOf[Expr]
        fail(
          s"""
             |Failed for
             |$expr
             |
             |SimpleEval: ${SimpleEvaluator.startEval(expr)}
             |NarrowEval: ${NarrowingEvaluator.startEval(expr)}
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

  def testExpr(expr: Expr): Unit = {
    val (t1, r1) = measure(() => SimpleEvaluator.startEval(expr))
    val (t2, r2) = measure(() => NarrowingEvaluator.startEval(expr))

    val ratio = t2.toDouble / t1.toDouble
    println(s"$expr")
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
    val x1 = Var("x1")
    val x2 = Var("x2")
    val x3 = Var("x3")
    val t_int = CustomType("Int", (0 to 2000).map(AnyValue).toSet)
    val S = SetValue(TreeSet(1800, 203, 1515, 891, 885, 32, 200, 1622, 1635, 1688, 241, 1356, 494, 576, 1418, 1040, 311, 373, 1596, 1049, 446, 370, 412, 62, 1941, 1541, 967, 1247, 829, 902, 914, 1038, 1647, 746, 2000, 509, 1281, 236, 1373, 575, 1268, 175, 1151, 390, 1939, 677, 239, 513, 1052, 34, 1537, 61, 978, 1750, 443, 695, 687, 755, 420, 340, 1771, 155, 628, 1134, 1360).map(AnyValue))

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

  test("equals formula short") {
      /*
      ¬(¬(∀x1: Int. ∀x2: Int. ¬(∀x3: Int. x2 = x3 ∧ x1 ∈ {2, 3})))
    */
      val x1 = Var("x1")
      val x2 = Var("x2")
      val x3 = Var("x3")
      val t_int = CustomType("Int", (0 to 10).map(AnyValue).to(TreeSet))
      val S = SetValue(Set(2, 3).map(AnyValue))

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

}
