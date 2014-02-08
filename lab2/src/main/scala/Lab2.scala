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
			case B(b) => if (b) 1 else 0
			case S(s) => try {
				s.toDouble
			} catch {
				case _ => Double.NaN
			} case Undefined => Double.NaN
			case _ => throw new UnsupportedOperationException
		}
	}

	def toBoolean(v: Expr): Boolean = {
		require(isValue(v))
		(v: @unchecked) match {
			case B(b) => b
			case N(n) => n != 0 && !n.isNaN()
			case S(s) => s != ""
			case _ => false
		}
	}

	def toStr(v: Expr): String = {
		require(isValue(v))
		(v: @unchecked) match {
			case S(s) => s
			case B(b) => b.toString
			case N(n) => if (n % 1 == 0) n.toInt.toString else n.toString
			case Undefined => "undefined"
			case _ => throw new UnsupportedOperationException
		}
	}

	def eval(env: Env, e: Expr): Expr = {
		/* Some helper functions for convenience. */
		def eToVal(e: Expr): Expr = eval(env, e)

			e match {
				/* Inductive Cases */
				case Print(e1) => println(pretty(eToVal(e1))); Undefined
				case If(e1,e2,e3) => if (toBoolean(eToVal(e1))) eToVal(e2) else eToVal(e3)
				case Binary(bop,e1,e2) => {
					val retE1 = eToVal(e1)
					val retE2 = eToVal(e2)
					bop match {
						//Logical Operators
						case Or => if (toBoolean(retE1)) retE1 else retE2
						case And => if (!toBoolean(retE1)) retE1 else retE2
						case Eq => B((retE1 == retE2))
						case Ne => B(retE1 != retE2)
						case Lt => (retE1,retE2) match {
							case (S(_),S(_)) => B(toStr(retE1) < toStr(retE2))
							case (_,_) => B(toNumber(retE1) < toNumber(retE2))
						} case Le => (retE1,retE2) match {
							case (S(_),S(_)) => B(toStr(retE1) <= toStr(retE2))
							case (_,_) => B(toNumber(retE1) <= toNumber(retE2))
						} case Gt => (retE1,retE2) match {
							case (S(_),S(_)) => B(toStr(retE1) > toStr(retE2))
							case (_,_) => B(toNumber(retE1) > toNumber(retE2))
						} case Ge => (retE1,retE2) match {
							case (S(_),S(_)) => B(toStr(retE1) >= toStr(retE2))
							case (_,_) => B(toNumber(retE1) >= toNumber(retE2))
						}

						//Arithmetic Operators
						case Plus => {
							(retE1,retE2) match {
								case (S(_),_) | (_,S(_)) => S(toStr(retE1) + toStr(retE2))
								case (_,_) => N(toNumber(retE1) + toNumber(retE2))
							}
						} case Minus => N(toNumber(retE1) - toNumber(retE2))
						case Times => N(toNumber(retE1) * toNumber(retE2))
						case Div => {
							val arg1 = toNumber(retE1)
							val arg2 = toNumber(retE2)
							if (arg2 != 0) N(arg1 / arg2)
							else {
								if (arg1 > 0) N(Double.PositiveInfinity)
								else if (arg1 < 0) N(Double.NegativeInfinity)
								else N(Double.NaN)
							}
						} 

						case Seq => {
							eToVal(e1)
							eToVal(e2)
						}
					}
				} case Unary(uop,e1) => {
					uop match {
						case Neg => N(-toNumber(eToVal(e1))) //Evaluates e1 and then converts it into a number
						case Not => B(!toBoolean(eToVal(e1))) //Evaluates e1 and then converts it into a boolean
					}
				} case ConstDecl(str,e1,e2) => eval(env + (str->eToVal(e1)),e2) //Adds interpreted value of e1 to map with key str
				case Var(str) => env(str); //Checks map for Expr with name str
				case N(_) | B(_) | S(_) | Undefined => e //Base classes
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