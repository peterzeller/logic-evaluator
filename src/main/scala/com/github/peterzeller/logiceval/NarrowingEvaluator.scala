package com.github.peterzeller.logiceval

import java.util

import com.github.peterzeller.logiceval.SimpleLogic._

import scala.annotation.tailrec

object NarrowingEvaluator {
  /** global flag for enabling type checks */
  var checked: Boolean = true

  sealed abstract class Sym

  case class SymAny() extends Sym

  case class SymNotEq(x: Any) extends Sym

  case class SymNotInSet(set: Set[Any]) extends Sym

  class BoundList[T](val l: util.ArrayList[T] = new util.ArrayList[T]()) extends AnyVal {
    def size: Int = l.size()


    private def arIndex(b: Bound[_]): Int = l.size() - 1 - b.index

    def apply(b: Bound[_]): T = l.get(arIndex(b))

    def push(t: T): Unit = l.add(t)

    def pop(): T = {
      val i = l.size() - 1
      val res = l.get(i)
      l.remove(i)
      res
    }

    def update(b: Bound[_], elem: T): T = {
      l.set(arIndex(b), elem)
    }

  }

  class NoMoreValuesException(b: Bound[_]) extends Exception


  def startEval[T](expr: Expr[T], env: Env): T = {


    val boundValues = new BoundList[Any]()
    val remainingValues = new BoundList[Iterator[Any]]()
    val allValues = new BoundList[Iterable[Any]]()


    /** obtain a concrete value for bound b */
    def getBound[Q](b: Bound[Q]): Q = {
      var res = boundValues(b)
      res match {
        case sym: Sym =>
          // make the bound value concrete
          val it =
            sym match {
              case SymAny() =>
                allValues(b).iterator
              case SymNotEq(x) =>
                allValues(b).iterator.filter(_ != x)
              case SymNotInSet(set) =>
                allValues(b).iterator.filter(!set.contains(_))
            }
          res = it.nextOption().getOrElse(throw new NoMoreValuesException(b))
          remainingValues(b) = remainingValues(b) ++ it
          boundValues(b) = res
        case _ =>
      }
      res.asInstanceOf[Q]
    }

    def eval[Q](expr: Expr[Q]): Q = expr match {
      case v: Var[Q] => throw new Exception(s"unexpected $v")
      case b: Bound[Q] =>
        getBound(b)
      case ForallD(v, t, body) =>
        boundValues.push(SymAny())
        remainingValues.push(Iterator.empty)
        allValues.push(t.values(env))
        val currentBound = Bound[Any](0)

        @tailrec
        def loop(): Boolean = {
//          val indent = "  " * boundValues.size
//          println(s"$indent eval $expr")
//          println(s"$indent with ${boundValues(currentBound)}")
          val r: Boolean = eval(body)
//          println(s"$indent end with ${boundValues(currentBound)}")
          if (!r) {
            false
          } else {
            remainingValues(currentBound).nextOption() match {
              case None =>
                // no more values to check
                true
              case Some(next) =>
                boundValues(currentBound) = next
                loop()
            }
          }


        }

        val res = loop()
        boundValues.pop()
        remainingValues.pop()
        allValues.pop()
        res
      case Neg(negatedExpr) =>
        !eval(negatedExpr)
      case And(left, right) =>
        eval(left) && eval(right)
      case Eq(left, right) =>
        // TODO symbolic handling

        def checkEqU(pair: (Expr[_], Expr[_]), checkedFirstRotation: Boolean = false): Boolean = {
          checkEq(pair.asInstanceOf[(Expr[Any], Expr[Any])], checkedFirstRotation)
        }

        def checkEq[S](pair: (Expr[S], Expr[S]), checkedFirstRotation: Boolean = false): Boolean = {
          pair match {
            case (b: Bound[S], other) =>

              val otherV = eval(other)
              checkEqV(b, otherV)

            case (ConstructDt(t1, n1, args1), ConstructDt(t2, n2, args2)) =>
              n1 == n2 &&
                args1.length == args2.length &&
                args1.zip(args2).forall(p => checkEqU(p))
            case (cd: ConstructDt[_], other) =>
              val otherV = eval(other)
              checkEqV(cd, otherV)
            case (left, right) =>
              if (checkedFirstRotation)
                eval(left) == eval(right)
              else
                checkEq((right, left), checkedFirstRotation = true)
          }

        }

        // check equality of expression and concrete value
        def checkEqV(e: Expr[_], otherV: Any): Boolean = {
          e match {
            case b: Bound[_] =>
              val v = boundValues(b)
              v match {
                case s: Sym =>
                  s match {
                    case SymAny() =>
                      // make equal
                      boundValues(b) = otherV
                      // remember to check notEq if there is at least one other element in all values
                      if (allValues(b).exists(_ != otherV))
                        remainingValues(b) ++= Iterator.single(SymNotEq(otherV))
                      true
                    case SymNotEq(x) if x == otherV => false
                    case _ =>
                      // make concrete
                      getBound(b) == otherV
                  }
                case _ =>
                  v == otherV
              }
            case ConstructDt(typ, name, args) =>
              if (name.checkShallow(otherV))
                args.zip(name.extractArgs(otherV)).forall(p => checkEqV(p._1, p._2))
              else
                false
            case _ =>
              eval(e) == otherV
          }
        }

        checkEq((left, right))
      case IsElem(elem, set) =>
        // TODO symbolic handling
        eval(set).contains(eval(elem))
      case c: ConstructDt[t] =>
        val argsE: List[Any] = c.args.map((e: Expr[_]) => eval(e))
        val res = c.name.construct(argsE)
        res
      case g: Get[k, v] =>
        val m = eval(g.map)
        val k = eval(g.key)
        m.getOrElse(k, eval(g.default))
      case Pair(a, b) =>
        (eval(a), eval(b))
      case g: Opaque[a, r] =>
        val res = g.func(env, eval(g.arg))
        res
      case c@ConstExpr(v) =>
        v
    }

    eval(expr)
  }


  class EvalException(msg: String, exc: Throwable = null) extends Exception(msg, exc)


}
