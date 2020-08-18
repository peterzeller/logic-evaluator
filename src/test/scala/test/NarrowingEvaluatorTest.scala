package test

import com.github.peterzeller.logiceval.{NarrowingEvaluator, SimpleEvaluator}
import com.github.peterzeller.logiceval.SimpleLogic.Expr
import org.scalacheck.{Prop, Properties}
import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers
import org.scalacheck.Properties
import org.scalacheck.Prop.forAll
import org.scalacheck.util.Pretty
import test.LogicTypeClasses._


class NarrowingEvaluatorTest extends AnyFunSuite {
  //  "The Hello object" should "say hello" in {
  //    Hello.greeting shouldEqual "hello"
  //  }



  test("equal to simple evaluator") {
    forAll { (expr: Expr) =>

      println(s"Testing $expr")

      val r1 = SimpleEvaluator.startEval(expr)
      val r2 = NarrowingEvaluator.startEval(expr)

      r1 == r2
    }
  }
}
