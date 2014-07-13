import scala.language.implicitConversions    
import scala.language.reflectiveCalls
import scala.annotation.tailrec   

// Custom Stack definition

sealed trait EvalSpec[L, R, V]

case class Constant[L, R, V](v: V) extends EvalSpec[L, R, V] {
	override def toString = v.toString
}

case class Recurse[L, R, V](lst: L, rexpFunc: V => V, rexpNew: R, f: V => EvalSpec[L, R, V]) extends EvalSpec[L, R, V]

private sealed trait EvalStack[L, R, V]

private case class ConstantFrame[L, R, V](constant: Constant[L, R, V], tail: Option[ContinueFrame[L, R, V]]) extends EvalStack[L, R, V]

private case class RecurseFrame[L, R, V](recurse: Recurse[L, R, V], tail: Option[ContinueFrame[L, R, V]]) extends EvalStack[L, R, V]

private case class ContinueFrame[L, R, V](f: V => EvalSpec[L, R, V], tail: Option[ContinueFrame[L, R, V]]) extends EvalStack[L, R, V]

def evaluate[L, R, V](f: (L, R)  => EvalSpec[L, R, V])(l: L)(r: R) = {
	@scala.annotation.tailrec
	def process(stack: EvalStack[L, R, V]): V = {
		stack match {
			case ConstantFrame(Constant(c), None) => c
			case ConstantFrame(Constant(c), Some(ContinueFrame(g, tail))) => process(makeStack(g(c), tail))
			case RecurseFrame(Recurse(rlst, rfunc, rnew, rinj), tail) => process(makeStack(f(rlst, rnew), 
				Some(ContinueFrame(rinj, tail))))
		}
	}

	process(makeStack(f(l, r), None))
}

private def makeStack[L, R, V](top: EvalSpec[L, R, V], tail: Option[ContinueFrame[L, R, V]]): EvalStack[L, R, V] = 
	top match {
		case constant@Constant(_) => ConstantFrame(constant, tail)
		case recurse@Recurse(_, _, _, _) => RecurseFrame(recurse, tail)
	}

implicit def toConst[L, R, V](v: V): Constant[L, R, V] = Constant[L, R, V](v)


def parseSimpStack:(List[Char], Rexp) => EvalSpec[List[Char], Rexp, Val] = evaluate[List[Char], Rexp, Val] { 
	case (Nil, r) => if (nullable(r)) Constant(mkEps(r)) else throw new IllegalArgumentException 
	case (head::tail, r) => {
		val (rsimp, func) = simplify(der(r, head));
		Recurse(tail, func, rsimp, injHelper(r, head, _: Val, func))
	}
} (_) (_)

def injHelper(r: Rexp, c: Char, vOld: Val, vReverse: Val => Val): EvalSpec[List[Char], Rexp, Val] = {
	Constant(inj(r, c, vReverse(vOld)))
}
// Rexp definition
    
abstract class Rexp 
case object NULL extends Rexp
case object EMPTY extends Rexp
case object DUMMY extends Rexp
case class CHAR(c: Char) extends Rexp
case class ALT(r1: Rexp, r2: Rexp) extends Rexp 
case class SEQ(r1: Rexp, r2: Rexp) extends Rexp 
case class STAR(r: Rexp) extends Rexp 
case class RECD(x: String, r: Rexp) extends Rexp
case class RANGE(left_border: Char, right_border: Char) extends Rexp

// Rexp length calculation

def calculateRexpElements(r: Rexp): Int = r match {
	case CHAR(_) => 1
	case NULL => 1
	case EMPTY => 1
	case SEQ(x, y) => 1 + calculateRexpElements(x) + calculateRexpElements(y)
	case ALT(x, y) => 1 + calculateRexpElements(x) + calculateRexpElements(y)
	case STAR(x) => 1 + calculateRexpElements(x)
	case RECD(_, x) => 1 + calculateRexpElements(x)
	case RANGE(_, _) => 1
}

// Val definition

abstract class Val
case object Void extends Val
case class Chr(c: Char) extends Val
case class Seqv(v1: Val, v2: Val) extends Val
case class Left(v: Val) extends Val
case class Right(v: Val) extends Val
case class Stars(l: List[Val]) extends Val
case class Rec(x: String, v: Val) extends Val

def charlist2Rexp(s: List[Char]): Rexp = s match {
	case Nil => EMPTY
	case c::Nil => CHAR(c)
	case c::tail => SEQ(CHAR(c), charlist2Rexp(tail))
}

implicit def string2Rexp(s: String): Rexp = charlist2Rexp(s.toList)

implicit def rexpOps(r: Rexp) = new {
	def | (s: Rexp) = ALT(r, s)
	def % = STAR(r)
	def ~ (s: Rexp) = SEQ(r, s)
}

implicit def stringOps(s: String) = new {
	def | (r: Rexp) = ALT(s, r)
	def | (r: String) = ALT(s, r)
	def % = STAR(s)
	def ~ (r: Rexp) = SEQ(s, r)
	def ~ (r: String) = SEQ(s, r)
	def $ (r: Rexp) = RECD(s, r)	
}

def nullable(r: Rexp): Boolean = r match {
	case NULL => false
	case EMPTY => true
	case CHAR(_) => false
	case ALT(v1, v2) => nullable(v1) || nullable(v2)
	case SEQ(v1, v2) => nullable(v1) && nullable(v2)
	case STAR(_) => true
	case RECD(_, v) => nullable(v)
	case RANGE(_, _) => false
}

def der(r: Rexp, c: Char): Rexp = r match {
	case NULL => NULL
	case EMPTY => NULL
	case CHAR(v) => if (v == c) EMPTY else NULL
	case ALT(v1, v2) => ALT(der(v1, c), der(v2, c))
	case SEQ(v1, v2) => 
		if (nullable(v1)) ALT(SEQ(der(v1, c), v2), der(v2, c)) 
		else SEQ(der(v1, c), v2)
	case STAR(v) => SEQ(der(v, c), STAR(v))
	case RECD(_, v) => der(v, c)
	case RANGE(lb, rb) => if (lb <= c && rb >= c) EMPTY else NULL
}

def ders(r: Rexp, s: List[Char]): Rexp = s match {
	case Nil => r
	case head::tail => ders(der(r, head), tail)
}

def flat(v: Val): String = v match {
	case Void => ""
	case Chr(c) => c.toString
	case Left(v) => flat(v)
	case Right(v) => flat(v)
	case Seqv(v1, v2) => flat(v1) + flat(v2)
	case Stars(lst) => lst.map(flat).mkString 
	case Rec(_, v) => flat(v)
}

def env(v: Val): List[(String, String)] = v match {
	case Void => Nil
	case Chr(c) => Nil
	case Left(v) => env(v)
	case Right(v) => env(v)
	case Seqv(v1, v2) => env(v1) ::: env(v2)
	case Stars(lst) => lst.flatMap(env)
	case Rec(s, v) => (s, flat(v)) :: env(v)
}

def mkEps(r: Rexp): Val = r match {
	case EMPTY => Void
	case ALT(v1, v2) => 
		if (nullable(v1)) Left(mkEps(v1))
		else Right(mkEps(v2))
	case SEQ(v1, v2) => Seqv(mkEps(v1), mkEps(v2))
	case STAR(r) => Stars(Nil)
	case RECD(s, v) => Rec(s, mkEps(v))
	case RANGE(_, _) => throw new IllegalArgumentException("mkEps range error") 
}

def inj(r: Rexp, c: Char, v: Val): Val = (r, v) match {
	case (STAR(r), Seqv(v1, Stars(vs))) => Stars(inj(r, c, v1)::vs)
	case (SEQ(r1, r2), Seqv(v1, v2)) => Seqv(inj(r1, c, v1), v2)
	case (SEQ(r1, r2), Left(Seqv(v1, v2))) => { 
		println("val in injection seq is " + v);
		Seqv(inj(r1, c, v1), v2)
	}
	case (SEQ(r1, r2), Right(v2)) => Seqv(mkEps(r1), inj(r2, c, v2))
	case (ALT(r1, r2), Left(v1)) => {
		println("val in injection alt is " + v);
		Left(inj(r1, c, v1))
	}
	case (ALT(r1, r2), Right(v2)) => Right(inj(r2, c, v2))
	case (CHAR(d), Void) => Chr(d)
	case (RECD(s, r1), _) => Rec(s, inj(r1, c, v))
	case (RANGE(lb, rb), Void) => if (c >= lb && c <= rb) Chr(c) else throw new IllegalArgumentException("Range error in injection")
}

def matcher(r: Rexp, s: String): Boolean = nullable(ders(r, s.toList))

def parse(r: Rexp, s: List[Char]): Val = s match {
	case Nil => if (nullable(r)) mkEps(r) else throw new IllegalArgumentException
	case head::tail => inj(r, head, parse(der(r, head), tail))
} 


// altFinder without RECD
def altFinder(r: Rexp, seq: Rexp, step: Int): (Rexp, Int, Boolean) = seq match {
	case ALT(left, right) => {
		if (r == left) (right, step, false)
		else {
			val (r1, step1, flag) = altFinder(r, right, step + 1);
			(if (r1 == DUMMY) left else ALT(left, r1), step1, flag)
		}
	}
	case reg => if (r == reg) (DUMMY, step, true)
				else  (reg, -1, false)
}


// altFinder with Rec
def altFinderRec(r: Rexp, seq: Rexp, step: Int): (Rexp, Int, Boolean) = { 
	seq match {
	case ALT(left, right) => (r, left) match {
		case (RECD(_, r1), RECD(_, r2)) => {
			if (r1 == r2) (right, step, false)
			else { 
				right match {
					case RECD(str, r3) => {
						val (rn, step1, flag) = altFinderRec(r, r3, step)
						(if (rn == DUMMY) left else ALT(left, RECD(str, rn)), step1, flag)
					}
					case r3 => {
						val (rn, step1, flag) = altFinderRec(r, r3, step + 1)
						(if (rn == DUMMY) left else ALT(left, rn), step1, flag)	
					}
				}
			}
		}
		case (RECD(_, r1), r2) => {
			if (r1 == r2) (right, step, false)
			else {
				right match {
					case RECD(str, r3) => {
						val (rn, step1, flag) = altFinderRec(r, r3, step)
						(if (rn == DUMMY) left else ALT(left, RECD(str, rn)), step1, flag)
					}
					case r3 => {
						val (rn, step1, flag) = altFinderRec(r, r3, step + 1)
						(if (rn == DUMMY) left else ALT(left, rn), step1, flag)	
					}
				}
			}
		}
		case (r1, RECD(_, r2)) => {
			if (r1 == r2) (right, step, false)
			else {
				right match {
					case RECD(str, r3) => {
						val (rn, step1, flag) = altFinderRec(r, r3, step)
						(if (rn == DUMMY) left else ALT(left, RECD(str, rn)), step1, flag)
					}
					case r3 => {
						val (rn, step1, flag) = altFinderRec(r, r3, step + 1)
						(if (rn == DUMMY) left else ALT(left, rn), step1, flag)	
					}
				} 
			}
		}
		case (r1, r2) => {
			if (r1 == r2) (right, step, false)
			else {
				right match {
					case RECD(str, r3) => {
						val (rn, step1, flag) = altFinderRec(r, r3, step)
						(if (rn == DUMMY) left else ALT(left, RECD(str, rn)), step1, flag)
					}
					case r3 => {
						val (rn, step1, flag) = altFinderRec(r, r3, step + 1)
						(if (rn == DUMMY) left else ALT(left, rn), step1, flag)	
					}
				}
			}
		}
	}
	case RECD(str, r1) if step == 1 => {
		val (rn, step1, flag) = altFinderRec(r, r1, step)
		(if (rn == DUMMY) r else ALT(r, RECD(str, rn)), step1, flag)
	}
	case reg => (r, reg) match {
		case (RECD(_, r1), r2) => {
			if (r1 == r2) (DUMMY, step, true)
				else  (reg, -1, false)
		}
		case (r1, r2) => {
			if (r1 == r2) (DUMMY, step, true)
				else  (reg, -1, false)
		}
	}
}
}


// complex simplification with associativity changes and reduction of alt-sequences
def simplify(r: Rexp): (Rexp, Val => Val) = r match {
	case ALT(ALT(x, y), z) => {
		val (r1, f1) = simplify(ALT(x, ALT(y, z)))
		(r1, associativityFunction(_: Val, f1))
	} 
	case ALT(x, y) => {
		y match {
			case ALT(_, _) => {
				val (reg, steps, flag) = altFinderRec(x, y, 1);
				if (steps == -1) {
					val (x1, f1) = simplify(x)
					val (y1, f2) = simplify(y)
					(x1, y1) match {
						case (NULL, z) => (z, (v: Val) => Right(f2(v)))
						case (z, NULL) => (z, (v: Val) => Left(f1(v)))
						case (z1, z2) => if (z1 == z2) (z1, (v: Val) => Left(f1(v))) 
							else (ALT(z1, z2), alternativeValPartial(_: Val, f1, f2))
					}
				} else { 
					val (r1, f1) = simplify(ALT(x, reg))
					if (!flag) {
						(r1, middleFunction(_: Val, steps, f1))
					} else {
						(r1, endFunction(_: Val, steps, f1))	
					}
				}
			}
			case _ => {
				val (x1, f1) = simplify(x)
				val (y1, f2) = simplify(y)
				(x1, y1) match {
					case (NULL, z) => (z, (v: Val) => Right(f2(v)))
					case (z, NULL) => (z, (v: Val) => Left(f1(v)))
					case (z1, z2) => if (z1 == z2) (z1, (v: Val) => Left(f1(v))) 
						else (ALT(z1, z2), alternativeValPartial(_: Val, f1, f2))
				}
			}
		}
	}
	case SEQ(x, y) => {
		val (x1, f1) = simplify(x)
		val (y1, f2) = simplify(y)
		(x1, y1) match {
			case (NULL, _) => (NULL, (v: Val) => v)
			case (_, NULL) => (NULL, (v: Val) => v)
			case (EMPTY, z) => (z, seqvEmptyLeftPartial(_: Val, f1, f2))
			case (z, EMPTY) => (z, seqvEmptyRightPartial(_: Val, f1, f2))
			case (z1, z2) => (SEQ(z1, z2), seqvPartial(_: Val, f1, f2))
		}
	}
	case RECD(s, x) => {
		val (x1, f1) = simplify(x)
		(RECD(s, x1), recFunction(_: Val, f1))
	}
	case reg => (reg, (v: Val) => v)
}

def simplifyWithoutAssociativity(r: Rexp): (Rexp, Val => Val) = r match {
	case ALT(x, y) => {
		val (x1, f1) = simplifyWithoutAssociativity(x)
		val (y1, f2) = simplifyWithoutAssociativity(y)
		(x1, y1) match {
			case (NULL, _) => (y1, (v: Val) => Right(f2(v)))
			case (_, NULL) => (x1, (v: Val) => Left(f1(v)))
			case _ => if (x1 == y1) (x1, (v: Val) => Left(f1(v))) 
				else (ALT(x1, y1), alternativeValPartial(_: Val, f1, f2))
		}
	}
	case SEQ(x, y) => {
		val (x1, f1) = simplifyWithoutAssociativity(x)
		val (y1, f2) = simplifyWithoutAssociativity(y)
		(x1, y1) match {
			case (NULL, _) => (NULL, (v: Val) => v)
			case (_, NULL) => (NULL, (v: Val) => v)
			case (EMPTY, _) => (y1, seqvEmptyLeftPartial(_: Val, f1, f2))
			case (_, EMPTY) => (x1, seqvEmptyRightPartial(_: Val, f1, f2))
			case _ => (SEQ(x1, y1), seqvPartial(_: Val, f1, f2))
		}
	} 
	case RECD(s, x) => {
		val (x1, f1) = simplifyWithoutAssociativity(x)
		(RECD(s, x1), recFunction(_: Val, f1))
	}
	case reg => (reg, (v: Val) => v)
}

def recFunction(v: Val, f: Val => Val): Val = v match {
	case Rec(s, v) => Rec(s, f(v))
}

def seqvEmptyLeftPartial(v: Val, f1: Val => Val, f2: Val => Val): Val = Seqv(f1(Void), f2(v))

def seqvEmptyRightPartial(v: Val, f1: Val => Val, f2: Val => Val): Val = Seqv(f1(v), f2(Void))

def alternativeValPartial(v: Val, f1: Val => Val, f2: Val => Val): Val = v match {
	case Left(x) => Left(f1(x))
	case Right(x) => Right(f2(x))
	case _ => throw new IllegalArgumentException
}

def seqvPartial(v: Val, f1: Val => Val, f2: Val => Val): Val = v match {
	case Seqv(v1, v2) => Seqv(f1(v1), f2(v2))
	case _ => throw new IllegalArgumentException
}

def associativityFunction(v: Val, f: Val => Val) : Val = f(v) match {
	case Left(v1) => Left(Left(v1))
	case Right(Left(v2)) => Left(Right(v2))
	case Right(Right(v3)) => Right(v3)
}

def middleFunction(v: Val, steps: Int, f: Val => Val): Val = adder(f(v), steps, (v1: Val) => Right(v1))

def endFunction(v: Val, steps: Int, f: Val => Val): Val = adder(f(v), steps - 1, (v1: Val) => Left(v1))

def adder(v: Val, steps: Int, f: Val => Val): Val = {
	if (steps == 0) f(v)
	else v match {
		case Right(x) => Right(adder(x, steps - 1, f))
		case v1 => v1
	}
}

def parseSimp(r: Rexp, s: List[Char]): Val = {
	// println(calculateRexpElements(r));
	s match {
		case Nil => if (nullable(r)) mkEps(r) else throw new IllegalArgumentException
		case head::tail => {
			val dr = der(r, head)
			val (rd, funct) = simplify(dr)
			inj(r, head, funct(parseSimp(rd, tail)))
		}
	}
}

def parseSimpNoAssociativity(r: Rexp, s: List[Char]): Val = {
	// println(calculateRexpElements(r));
	s match {
		case Nil => if (nullable(r)) mkEps(r) else throw new IllegalArgumentException
		case head::tail => {
			val (rd, funct) = simplifyWithoutAssociativity(der(r, head))
			val iv = inj(r, head, funct(parseSimpNoAssociativity(rd, tail)))
			println("---------------")
			iv
		}
	}
}

def PLUS(r: Rexp) = r ~ r.%
val SYM: Rexp = RANGE('a', 'z') //"a" | "b" | "c" | "d" | "e" | "f" | "g" | "h" | "i" | "j" | "k" | "l" | "m" | "n" | "o" | "p" | "q" | "r" | "s" | "t" | "u" | "v" | "w" | "x" | "y" | "z"
val DIGIT = "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9"
val ID = SYM ~ (SYM | DIGIT).% 
val NUM = PLUS(DIGIT)
val KEYWORD : Rexp = "skip" | "while" | "do" | "if" | "then" | "else" | "read" | "write" | "true" | "false"
val SEMI: Rexp = ";"
val OP: Rexp = ":=" | "==" | "-" | "+" | "*" | "!=" | "<" | ">" | "<=" | ">=" | "%" | "/"
val WHITESPACE = PLUS(" " | "\n" | "\t")
val RPAREN: Rexp = ")"
val LPAREN: Rexp = "("
val BEGIN: Rexp = "{"
val END: Rexp = "}"


val WHILE_REGS = (("k" $ KEYWORD) | 
                  ("i" $ ID) | 
                  ("o" $ OP) | 
                  ("n" $ NUM) | 
                  ("s" $ SEMI) | 
                  ("p" $ (LPAREN | RPAREN)) | 
                  ("b" $ (BEGIN | END)) | 
                  ("w" $ WHITESPACE)).%
// Some Tests

val pfib = """read n"""
val pfib2 = """read n; write n; int a := 5;"""

def calculator(r: Rexp, s: List[Char]): Unit = s match {
	case Nil => println(calculateRexpElements(r))
	case head::tail => {
		println(calculateRexpElements(r))
		calculator(der(r, head), tail)
	}
}

println(parse(WHILE_REGS, "r".toList))
println(parseSimpNoAssociativity(WHILE_REGS, "r".toList))

// calculator(WHILE_REGS, pfib2.toList)

// println(parseSimp(WHILE_REGS, pfib2.toList))
// println("________________________________")
// println(g(pfib.toList, WHILE_REGS))
// println(parseSimp(WHILE_REGS, pfib2.toList) == parseSimpNoAssociativity(WHILE_REGS, pfib2.toList))
// println(env(parseSimp(WHILE_REGS, pfib2.toList)))
//------------------------------------

// val regularka: Rexp = ("a" | "b" | "c" | "d" | "e").%
// val stroka = "aebdc"

// println(parseSimpNoAssociativity(regularka, stroka.toList))


//------------------------------------

//------------------------------------

// val checker: Rexp = (("a1" $ "a") | ("b" $ "re") | ("w" $ " ")).%
// println(checker)
// parseSimp(checker, "a re".toList)


//------------------------------------

def time[T](code: => T) = {
  val start = System.nanoTime()
  val result = code
  val end = System.nanoTime()
  println((end - start)/1.0e9)
  result
}

// val prog2 = """
// i := 2;
// max := 100;
// while i < max do {
//   isprime := 1;
//   j := 2;
//   while (j * j) <= i + 1  do {
//     if i % j == 0 then isprime := 0  else skip;
//     j := j + 1
//   };
//   if isprime == 1 then write i else skip;
//   i := i + 1
// }"""

// for (i <- 500 to 500 by 1) {
//   print(i.toString + ":  ")
//   parseSimpStack((prog2 * i).toList, WHILE_REGS)
// }


// for (i <- 1 to 50 by 1) {
//   time(parseSimp(WHILE_REGS, (prog2 * i).toList))
// }

