object Lab2 extends jsy.util.JsyApplication {
  import jsy.lab2.Parser
  import jsy.lab2.ast._
  
  /*
   * CSCI 3155: Lab 2
   * <Your Name>
   * 
   * Partner: <Your Partner's Name>
   * Collaborators: <Any Collaborators>
   */

  /*
   * Fill in the appropriate portions above by replacing things delimited
   * by '<'... '>'.
   * 
   * Replace 'YourIdentiKey' in the object name above with your IdentiKey.
   * 
   * Replace the 'throw new UnsupportedOperationException' expression with
   * your code in each function.
   * 
   * Do not make other modifications to this template, such as
   * - adding "extends App" or "extends Application" to your Lab object,
   * - adding a "main" method, and
   * - leaving any failing asserts.
   * 
   * Your lab will not be graded if it does not compile.
   * 
   * This template compiles without error. Before you submit comment out any
   * code that does not compile or causes a failing assert.  Simply put in a
   * 'throws new UnsupportedOperationException' as needed to get something
   * that compiles without error.
   */
  
  /* We represent a variable environment is as a map from a string of the
   * variable name to the value to which it is bound.
   * 
   * You may use the following provided helper functions to manipulate
   * environments, which are just thin wrappers around the Map type
   * in the Scala standard library.  You can use the Scala standard
   * library directly, but these are the only interfaces that you
   * need.
   */
  
  type Env = Map[String, Expr]
  val emp: Env = Map()
  def get(env: Env, x: String): Expr = env(x)
  def extend(env: Env, x: String, v: Expr): Env = {
    require(isValue(v))
    env + (x -> v)
  }
  
  /* Some useful Scala methods for working with Scala values include:
   * - Double.NaN
   * - s.toDouble (for s: String)
   * - n.isNaN (for n: Double)
   * - n.isWhole (for n: Double)
   * - s (for n: Double)
   * - s format n (for s: String [a format string like for printf], n: Double)
   */

  def toNumber(v: Expr): Double = {
    require(isValue(v))
    (v: @unchecked) match {
      case N(n) => n
      case _ => throw new UnsupportedOperationException
    }
  }
  
  def toBoolean(v: Expr): Boolean = {
    require(isValue(v))
    (v: @unchecked) match {
      case B(b) => b
      case _ => throw new UnsupportedOperationException
    }
  }
  
  def toStr(v: Expr): String = {
    require(isValue(v))
    (v: @unchecked) match {
      case S(s) => s
      case Undefined => "undefined"
      case _ => throw new UnsupportedOperationException
    }
  }
  
  def eval(env: Env, e: Expr): Expr = {
    /* Some helper functions for convenience. */
    def eToVal(e: Expr): Expr = eval(env, e)
    
    def eToNum(e:Expr):Double = e match {
      case B(b) => if (b) 1 else 0
      case N(n) => n
      case S(s) => throw new UnsupportedOperationException
      case _ => throw new UnsupportedOperationException
    }
    
    def eToBool(e:Expr):Boolean = e match {
      case B(b) => b
      case N(n) => if (n == 0) false else true
      case S(s) => if (s == "") false else true
      case _ => throw new UnsupportedOperationException
    }

    e match {
      /* Base Cases */
      
      /* Inductive Cases */
      case Print(e1) => println(pretty(eToVal(e1))); Undefined
      case Binary(bop,e1,e2) => {
        val arg1 = eToVal(e1)
        val arg2 = eToVal(e2)
        bop match {
          //Logical operators
          case And => B(eToBool(arg1) && eToBool(arg2))
          case Or => B(eToBool(arg1) || eToBool(arg2))
          case Eq => B(eToNum(arg1) == eToNum(arg2))
          case Ne => B(eToNum(arg1) != eToNum(arg2))
          case Lt => B(eToNum(arg1) < eToNum(arg2))
          case Le => B(eToNum(arg1) <= eToNum(arg2))
          case Gt => B(eToNum(arg1) > eToNum(arg2))
          case Ge => B(eToNum(arg1) >= eToNum(arg2))
          
          //Arithmetic operators
          case Plus => N(eToNum(arg1) + eToNum(arg2))
          case Minus => N(eToNum(arg1) - eToNum(arg2))
          case Times => N(eToNum(arg1) * eToNum(arg2))
          case Div => {
            val da1 = eToNum(arg1)
            val da2 = eToNum(arg2)
            if (da2 != 0) N(da1/da2)
            else {
              if (da1 > 0) N(Double.PositiveInfinity)
              else if (da1 < 0) N(Double.NegativeInfinity)
              else N(Double.NaN)
            }
          } case _ => throw new UnsupportedOperationException
        }
      } case Unary(uop,e1) => {
        uop match {
          case Neg => N(-eToNum(e1))
          case Not => B(!eToBool(e1))
        }
      }
      case N(_) | B(_) | S(_) | Undefined => e
      case _ => throw new UnsupportedOperationException
    }
  }
    
  // Interface to run your interpreter starting from an empty environment.
  def eval(e: Expr): Expr = eval(emp, e)

  // Interface to run your interpreter from a string.  This is convenient
  // for unit testing.
  def eval(s: String): Expr = eval(Parser.parse(s))

 /* Interface to run your interpreter from the command-line.  You can ignore what's below. */ 
 def processFile(file: java.io.File) {
    if (debug) { println("Parsing ...") }
    
    val expr = Parser.parseFile(file)
    
    if (debug) {
      println("\nExpression AST:\n  " + expr)
      println("------------------------------------------------------------")
    }
    
    if (debug) { println("Evaluating ...") }
    
    val v = eval(expr)
    
    println(pretty(v))
  }

}