package com.github.peterzeller.logiceval

import com.github.peterzeller.logiceval.SimpleLogic._


object ReverseEvaluator {

  case class Ctxt(
    // possible values (nonempty set per variable)
    possibleValues: Map[Var, Set[Value]],
    currentValues: Map[Var, Value],
    backtrack: () => Value
  )

  sealed abstract class Result

  case class FinalAnswer(result: Value) extends Result

  object BackTrack extends Result

  type ContFunc = (Ctxt, Value) => Value

  sealed abstract class Continuation {
    def func: ContFunc
  }

  case class SimpleContinuation(
    func: ContFunc
  ) extends Continuation

  case class BoolContinuation(
    ifFalse: Ctxt => Value,
    ifTrue: Ctxt => Value
  ) extends Continuation {
    override def func: ContFunc = (ctxt, value) =>
      if (value.boolVal) ifTrue(ctxt) else ifFalse(ctxt)
  }

  def evaluateFormula(expr: Expr, ctxt: Ctxt, continuation: Continuation): Value = {
    expr match {
      case Opaque(f, args) =>
//        f(args.map(evaluateFormula(_, ctxt)))
        ???
      case ConstExpr(v) =>
        continuation.func(ctxt, v)
      case v: Var =>
        ctxt.currentValues.get(v) match {
          case Some(value) => value
          case None =>
            val possibleValues = ctxt.possibleValues.getOrElse(v,
              throw new Exception(s"Unknown variable $v"))
            val newPossibleValues = ctxt.possibleValues.removed(v)

            def step(values: Set[Value]): Value = {
              if (values.isEmpty) {
                ctxt.backtrack()
              } else {
                val first = possibleValues.head
                val rest = possibleValues.tail
                val newCtxt = ctxt.copy(
                  possibleValues = newPossibleValues,
                  currentValues = ctxt.currentValues + (v -> first),
                  backtrack = () => step(rest)
                )
                continuation.func(newCtxt, first)
              }
            }

            step(possibleValues)
        }
      case Forall(v, set, body) =>
        // TODO handle negation switch forall x. ! forall y.
        val setV = set.values
        val oldPossible = ctxt.possibleValues.get(v)
        val oldBound = ctxt.currentValues.get(v)
        val newCtxt = ctxt.copy(
          possibleValues = ctxt.possibleValues + (v -> setV.toSet)
        )
        evaluateFormula(body, newCtxt, BoolContinuation(
          ifFalse = { ctxt2 =>
            // forall is false overall:
            continuation.func(ctxt2, BoolVal(false))
          },
          ifTrue = { ctxt2 =>
            ???
          }
        ))
      case Neg(negatedExpr) => ???
      case And(left, right) => ???
      case Eq(left, right) => ???
      case IsElem(elem, set) => ???
      case ConstructDt(name, args) => ???
      case Domain(map) => ???
      case Get(map, key) => ???
    }


  }


}
