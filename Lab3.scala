package jsy.student

import jsy.lab3.Lab3Like
import jsy.util.JsyApplication

object Lab3 extends JsyApplication with Lab3Like {
  import jsy.lab3.ast._
  
  /*
   * CSCI 3155: Lab 3 
   * <Bryan Heiser>
   * 
   * Partner: <Joe Los>
   * Collaborators: <Any Collaborators>
   */

  /*
   * Fill in the appropriate portions above by replacing things delimited
   * by '<'... '>'.
   * 
   * Replace the '???' expression with your code in each function.
   *
   * Do not make other modifications to this template, such as
   * - adding "extends App" or "extends Application" to your Lab object,
   * - adding a "main" method, and
   * - leaving any failing asserts.
   * 
   * Your lab will not be graded if it does not compile.
   * 
   * This template compiles without error. Before you submit comment out any
   * code that does not compile or causes a failing assert. Simply put in a
   * '???' as needed to get something  that compiles without error. The '???'
   * is a Scala expression that throws the exception scala.NotImplementedError.
   */
  
  /*
   * The implementations of these helper functions for conversions can come
   * Lab 2. The definitions for the new value type for Function are given.
   */
  
  def toNumber(v: Expr): Double = {
    require(isValue(v))
    (v: @unchecked) match {
      case N(n) => n
      case B(false) => 0
      case B(true) => 1
      case Undefined => Double.NaN
      case S(s) => val number = s.toDouble; if (number.isNaN) Double.NaN else number
      case Function(_, _, _) => Double.NaN
    }
  }
  
  def toBoolean(v: Expr): Boolean = {
    require(isValue(v))
    (v: @unchecked) match {
      case B(b) => b
      case Function(_, _, _) => true
      case N(n) => if (n==0 || n.isNaN) false else true
      case S(s) => if (s=="") false else true
      case Undefined => false
    }
  }
  
  def toStr(v: Expr): String = {
    require(isValue(v))
    (v: @unchecked) match {
      case S(s) => s
        // Here in toStr(Function(_, _, _)), we will deviate from Node.js that returns the concrete syntax
        // of the function (from the input program).
      case Function(_, _, _) => "function"
      case B(b) => if (b) "true" else "false"
      case N(n) => n.toString
      case Undefined => "undefined"
    }
  }

  /*
   * Helper function that implements the semantics of inequality
   * operators Lt, Le, Gt, and Ge on values.
   *
   * We suggest a refactoring of code from Lab 2 to be able to
   * use this helper function in eval and step.
   */
  def inequalityVal(bop: Bop, v1: Expr, v2: Expr): Boolean = {
    require(isValue(v1))
    require(isValue(v2))
    require(bop == Lt || bop == Le || bop == Gt || bop == Ge)
    (v1, v2) match {
      case (S(s1), S(s2)) => bop match {
        case Lt => s1 < s2
        case Le => s1 <= s2
        case Gt => s1 > s2
        case Ge => s1 >= s2
      }
      case (_, _) => bop match {
        case Lt => toNumber(v1) < toNumber(v2)
        case Le => toNumber(v1) <= toNumber(v2)
        case Gt => toNumber(v1) > toNumber(v2)
        case Ge => toNumber(v1) >= toNumber(v2)
      }
    }
  }


  /* Big-Step Interpreter with Dynamic Scoping */
  
  /*
   * Start by copying your code from Lab 2 here.
   */
  def eval(env: Env, e: Expr): Expr = {
    e match {
      /* Base Cases */
      case N(_) | B(_) | S(_) | Undefined | Function(_, _, _) => e
      case Var(x) => lookup(env, x)
      
      /* Inductive Cases */
      case Print(e1) => println(pretty(eval(env, e1))); Undefined

        // ****** Your cases here
      case ConstDecl(x, e1, e2) =>
        val p: Expr = eval(env, e1)
        val env1: Env = extend(env, x, p)
        eval(env1, e2)

      case If(e1, e2, e3) => if (toBoolean(eval(env, e1))) eval(env, e2) else eval(env, e3)

      case Unary(uop, e1) => uop match {
        case Neg => eval(env, e1) match {
          case N(n) => N(-n)
          case B(b) => if (b) N(-1) else N(-0)
          case _ => N(Double.NaN)
        }
        case Not => eval(env, e1) match {
          case N(n) => if (n==0) B(true) else B(false)
          case B(b) => if (b) B(false) else B(true)
          case S(s) => B(false)
          case Undefined => B(true)
        }
      }

      case Binary(bop, e1, e2) => bop match {
        case Plus => (eval(env, e1), eval(env,e2)) match {
          case (S(s), v) => S(s + toStr(v))
          case (v, S(s)) => S(toStr(v) + s)
          case (v1,v2) => N(toNumber(v1) + toNumber(v2))
        }
        case Minus => (eval(env, e1), eval(env, e2)) match {
          case (S(s), _) => N(Double.NaN)
          case (_, S(s)) => N(Double.NaN)
          case (v1, v2) => N(toNumber(v1) - toNumber(v2))
        }
        case Times => (eval(env, e1), eval(env, e2)) match {
          case (S(s), _) => N(Double.NaN)
          case (_, S(s)) => N(Double.NaN)
          case (v1, v2) => N(toNumber(v1) * toNumber(v2))
        }
        case Div => (eval(env, e1), eval(env, e2)) match {
          case (S(s), _) => N(Double.NaN)
          case (_, S(s)) => N(Double.NaN)
          case (v1, v2) => N(toNumber(v1) / toNumber(v2))
        }
        case Eq => (eval(env, e1), eval(env, e2)) match {
          case (Function(_,_,_), _) => throw DynamicTypeError(e)
          case (_, Function(_,_,_)) => throw DynamicTypeError(e)
          case (v1, v2) => B(v1==v2)
        }
        case Ne => (eval(env, e1), eval(env, e2)) match {
          case (Function(_,_,_), _) => throw DynamicTypeError(e)
          case (_, Function(_,_,_)) => throw DynamicTypeError(e)
          case (v1, v2) => B(v1!=v2)
        }
        case And => (eval(env, e1), eval(env, e2)) match {
          case (N(n1), N(n2)) => if (n1!=0 && n2!=0) N(n2) else N(0)
          case (N(n), uk) => if (n!=0) uk else N(0)
          case (B(b), uk) => if (b) uk else B(false)
          case (_, B(b)) => if (b) B(true) else B(false)
          case (S(s1), S(s2)) => S(s2)
        }
        case Or => (eval(env, e1), eval(env, e2)) match {
          case (B(false), B(false)) => B(false)
          case (N(0), N(0)) => N(0)
          case (B(true), B(true)) | (_, B(true)) | (B(true), _) => B(true)
          case (uk, _) => uk
        }
        case Seq => eval(env, e1); eval(env, e2)

        case Lt | Le | Gt | Ge => B(inequalityVal(bop, eval(env, e1), eval(env,e2)))
      }

      case Call(e1, e2) => eval(env, e1) match {
        case Function(None, x, v1) => {
          val env1:Env = extend(env, x, eval(env, e2))
          eval(env1, v1)
        }
        case Function(Some(x1), x2, body) => {
          val v1:Expr = eval(env, e1)
          val v2: Expr = eval(env, e2)
          val env1: Env = extend(env, x1, v1)
          val env2: Env = extend(env1, x2, v2)
          eval(env2, body)
        }
      }

      //case _ => ??? // delete this line when done
    }
  }
    

  /* Small-Step Interpreter with Static Scoping */

  def iterate(e0: Expr)(next: (Expr, Int) => Option[Expr]): Expr = {
    def loop(e: Expr, n: Int): Expr = next(e, n) match {
      case None => e
      case Some(e1) => loop(e1, n+1)
    }
    loop(e0, 0)
  }
  
  def substitute(e: Expr, v: Expr, x: String): Expr = {
    require(isValue(v))
    e match {
      case N(_) | B(_) | Undefined | S(_) => e
      case Print(e1) => Print(substitute(e1, v, x))
      case Unary(uop, e1) => Unary(uop, substitute(e1, v, x))
      case Binary(bop, e1, e2) => Binary(bop, substitute(e1, v, x), substitute(e2, v, x))
      case If(e1, e2, e3) => If(substitute(e1, v, x), substitute(e2, v, x), substitute(e3, v, x))
      case Call(e1, e2) => Call(substitute(e1, v, x), substitute(e2, v, x))
      case Var(y) => if (y==x) v else e
      case Function(None, y, e1) => if (y==x) e else Function(None, y, substitute(e1, v, x))
      case Function(Some(y1), y2, e1) => if (y1==x || y2==x) e else Function(Some(y1), y2, substitute(e1, v, x))
      case ConstDecl(y, e1, e2) => if (y==x)  ConstDecl(y, substitute(e1, v, x), e2) else ConstDecl(y, substitute(e1, v, x), substitute(e2, v, x))
    }
  }
    
  def step(e: Expr): Expr = {
    e match {
      /* Base Cases: Do Rules */
      case Print(v1) if isValue(v1) => println(pretty(v1)); Undefined //DoPrint
      
        // ****** Your cases here
      case Unary(Neg, v) if isValue(v) => N(-toNumber(v)) //DoNeg
      case Unary(Not, v) if isValue(v) => B(!toBoolean(v)) //DoNot

      case Binary(Seq, v1, e2) if isValue(v1) => e2 //DoSeq

      case Binary(Plus, v1, v2) if isValue(v1) && isValue(v2) => (v1, v2) match {
        case (S(s), v) => S(s + toStr(v)) //DoPlusString1
        case (v, S(s)) => S(toStr(v) + s) //DoPlusString2
        case (a, b) => N(toNumber(a) + toNumber(b)) //DoPlusNumber
      }
        //DoArith
      case Binary(Minus, v1, v2) if isValue(v1) && isValue(v2) => N(toNumber(v1) - toNumber(v2))
      case Binary(Times, v1, v2) if isValue(v1) && isValue(v2) => N(toNumber(v1) * toNumber(v2))
      case Binary(Div, v1, v2) if isValue(v1) && isValue(v2) => N(toNumber(v1) / toNumber(v2))

      case Binary(And, v1, e2) if isValue(v1) => if (toBoolean(v1)) e2 else v1//DoAndTrue and False

      case Binary(Or, v1, e2) if isValue(v1) => if (toBoolean(v1)) v1 else e2//DoOrTrue and False

      case Binary(bop, v1, v2) if isValue(v1) && isValue(v2) => bop match {
        //DoInequalityNumber1 & 2 and DoInequalityString
        case Lt | Le | Gt | Ge => B(inequalityVal(bop, v1, v2))

        //DoEquality
        case Eq | Ne => (v1, v2) match {
          case (Function(_,_,_),_) => throw DynamicTypeError(e)
          case (_,Function(_,_,_)) => throw DynamicTypeError(e)
          case (_,_) => if (bop==Eq) B(v1 == v2) else B(v1 != v2)
        }
      }

      case If(v1, e2, e3) if isValue(v1) => if (toBoolean(v1)) e2 else e3 //DoIfTrue and False

      case Call(v1, v2) if isValue(v1) && isValue(v2) => v1 match {
        case Function(None, x, e1) => substitute(e1, v2, x) //DoCall
        case Function(Some(x1), x2, e1) => {
          val temp = substitute(e1, v1, x1)
          substitute(temp, v2, x2) //DoCallRec
        }
        case _ => throw DynamicTypeError(e)
      }

      case ConstDecl(x, v1, e2) if isValue(v1) => substitute(e2, v1, x) //DoConst

      /* Inductive Cases: Search Rules */
      case Print(e1) => Print(step(e1)) //SearchPrint
      
        // ****** Your cases here
      case Unary(uop, e1) => Unary(uop, step(e1)) //SearchUnary

        //SearchBinaryArith and SearchEquality
      case Binary(bop, v1, e2) if isValue(v1) => bop match {
        case Eq | Ne => v1 match {
          case Function(_,_,_) => throw DynamicTypeError(e)
          case _ => Binary(bop, v1, step(e2))
        }
        case _ => Binary(bop, v1, step(e2))
      }

      case Binary(bop, e1, e2) => Binary(bop, step(e1), e2) //SearchBinary

      case If(e1, e2, e3) => If(step(e1), e2, e3) //SearchIf

      case ConstDecl(x, e1, e2) => ConstDecl(x, step(e1), e2) //SearchConst

        //SearchCall1 & 2
      case Call(e1, e2) => e1 match {
        case Function(_,_,_) => Call(e1, step(e2))
        case _ => Call(step(e1), e2)
      }

      /* Cases that should never match. Your cases above should ensure this. */
      case Var(_) => throw new AssertionError("Gremlins: internal error, not closed expression.")
      case N(_) | B(_) | Undefined | S(_) | Function(_, _, _) => throw new AssertionError("Gremlins: internal error, step should not be called on values.");
    }
  }


  /* External Interfaces */
  
  //this.debug = true // uncomment this if you want to print debugging information
  this.keepGoing = true // comment this out if you want to stop at first exception when processing a file

}
