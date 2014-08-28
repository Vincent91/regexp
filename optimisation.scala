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
		val (rsimp, func) = simplifyWithoutAssociativity(der(r, head));
		Recurse(tail, func, rsimp, injHelper(r, head, _: Val, func))
	}
} (_) (_)

def injHelper(r: Rexp, c: Char, vOld: Val, vReverse: Val => Val): EvalSpec[List[Char], Rexp, Val] = {
	Constant(inj(r, c, vReverse(vOld), 0, 0))
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
case class RANGE(lb: Char, rb: Char) extends Rexp

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
case class Left(v: Val, c: Int) extends Val
case class Right(v: Val, c: Int) extends Val
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
	case RANGE(lb, rb) => if (lb <= c && c <= rb) EMPTY else NULL
}

def ders(r: Rexp, s: List[Char]): Rexp = s match {
	case Nil => r
	case head::tail => ders(der(r, head), tail)
}

def flat(v: Val): String = v match {
	case Void => ""
	case Chr(c) => c.toString
	case Left(v, _) => flat(v)
	case Right(v, _) => flat(v)
	case Seqv(v1, v2) => flat(v1) + flat(v2)
	case Stars(lst) => lst.map(flat).mkString 
	case Rec(_, v) => flat(v)
}

def env(v: Val): List[(String, String)] = v match {
	case Void => Nil
	case Chr(c) => Nil
	case Left(v, _) => env(v)
	case Right(v, _) => env(v)
	case Seqv(v1, v2) => env(v1) ::: env(v2)
	case Stars(lst) => lst.flatMap(env)
	case Rec(s, v) => (s, flat(v)) :: env(v)
}

def valSize(v: Val): Int = v match {
	case Void => 1
	case Chr(c) => 1
	case Left(v, n) => 1 + valSize(v)
	case Right(v, n) => 1 + valSize(v)
	case Seqv(v1, v2) => 1 + valSize(v1) + valSize(v2)
	case Stars(lst) => 1 + lst.map(valSize).sum
	case Rec(s, v) => 1 + valSize(v)
}

def valSizeExpanded(v: Val): Int = v match {
	case Void => 1
	case Chr(c) => 1
	case Left(v, n) => n + valSizeExpanded(v)
	case Right(v, n) => n + valSizeExpanded(v)
	case Seqv(v1, v2) => 1 + valSizeExpanded(v1) + valSizeExpanded(v2)
	case Stars(lst) => 1 + lst.map(valSizeExpanded).sum
	case Rec(s, v) => 1 + valSizeExpanded(v)
}

def mkEps(r: Rexp, left1: Int = 0, right1: Int = 0): Val = r match {
	case EMPTY => {
		if (left1 != 0) 
			Left(Void, left1)
		else if (right1 != 0)
			Right(Void, right1)
		else 
			Void
	}
	case ALT(v1, v2) => {
		if (nullable(v1)) {
			if (right1 != 0)
				Right(mkEps(v1, 1, 0), right1)
			else
				mkEps(v1, left1 + 1, 0)
		} else { 
			if (left1 != 0)
				Left(mkEps(v2, 0, 1), left1)
			else 
				mkEps(v2, 0, right1 + 1)
		}
	}
	case SEQ(v1, v2) => {
		if (left1 != 0)
			Left(Seqv(mkEps(v1), mkEps(v2)), left1)
		else if (right1 != 0)
			Right(Seqv(mkEps(v1), mkEps(v2)), right1)
		else
			Seqv(mkEps(v1), mkEps(v2))
	}
	case STAR(r) => {
		if (left1 != 0)
			Left(Stars(Nil), left1)
		else if (right1 != 0)
			Right(Stars(Nil), right1)
		else 
			Stars(Nil)
	}
	case RECD(s, v) => { 
		if (left1 != 0) 
			Left(Rec(s, mkEps(v)), left1)
		else if (right1 != 0)
			Right(Rec(s, mkEps(v)), right1)
		else 
			Rec(s, mkEps(v))
	}
	case RANGE(_, _) => throw new IllegalArgumentException("Range must not be reached in mkEps")
}

//mind-blowing - why the hell does not it work this way?
def inj(r: Rexp, c: Char, v: Val, left_counter: Int = 0, right_counter: Int = 0): Val ={ 
	// println(v);
		(r, v) match {
		case (STAR(r), Seqv(v1, Stars(vs))) => {
			// println("star " + left_counter + " " + right_counter);
			Stars(inj(r, c, v1, 0, 0)::vs)
		}
		case (SEQ(r1, r2), Seqv(v1, v2)) => {
			// println("seq seq " + left_counter + " " + right_counter);
			Seqv(inj(r1, c, v1, 0, 0), v2)
		}
		case (SEQ(r1, r2), Left(Seqv(v1, v2), counter1)) if (counter1 - 1 == left_counter) => {
			// Seqv(inj(r1, c, v1), v2)
			// println("val in injection seq is " + v);
			// println("left and right " + left_counter + " " + right_counter);
			// println("seq left " + left_counter + " " + right_counter);
			if (left_counter == 0)
				Seqv(inj(r1, c, v1, 0, 0), v2)
			else 
				Left(Seqv(inj(r1, c, v1, 0, 0), v2), left_counter)
		}
		case (SEQ(r1, r2), Right(v2, counter)) => {
			// Seqv(mkEps(r1), inj(r2, c, if (counter == 1) v2 else Right(v2, counter - 1)))
			// println("seq right " + left_counter + " " + right_counter);
			if (right_counter == 0) {
				Seqv(mkEps(r1), inj(r2, c, if (counter == 1) v2 else Right(v2, counter - 1), 0, 0))
			} else {
				Right(Seqv(mkEps(r1), inj(r2, c, if (counter - right_counter == 1) v2 else Right(v2, counter - 1 - right_counter), 0, 0)) , right_counter)
			}
		}
		case (ALT(r1, r2), Right(v2, counter)) => {
			// val vl = inj(r2, c, if (counter == 1) v2 else Right(v2, counter - 1))
			// vl match {
			// 	case Right(vr, counter1) => Right(vr, counter1 + 1)
			// 	case vr => Right(vr, 1)
			// }
			// println("alt right " + left_counter + " " + right_counter);
			if (right_counter == counter - 1)
				Right(inj(r2, c, v2, 0, 0), counter)
			else
				inj(r2, c, v, 0, right_counter + 1)
		}
		case (ALT(r1, r2), Left(v1, counter)) => {
			// val vl = inj(r1, c, if (counter == 1) v1 else Left(v1, counter - 1))
			// vl match {
			// 	case Left(vr, counter1) => Left(vr, counter1 + 1)
			// 	case vr => Left(vr, 1)
			// }
			// println("val in injection alt is " + v);
			// println("left and right " + left_counter + " " + right_counter + " counter " + counter);
			// println("alt left " + left_counter + " " + right_counter);
			if (counter - left_counter == 1)
				Left(inj(r1, c, v1, 0, 0), counter)
			else 
				inj(r1, c, v, left_counter + 1, 0)
		}
		case (CHAR(d), Void) => {
			// println("char void" + left_counter + " " + right_counter);
			Chr(d)
		}
		case (RECD(s, r1), Left(v1, counter)) => {
			// println("rect left " + left_counter + " " + right_counter);
			Left(Rec(s, inj(r1, c, Left(v1, counter - left_counter), 0, 0)), left_counter)
		}
		case (RECD(s, r1), Right(v2, counter)) => {
			// println("rect right " + left_counter + " " + right_counter);
			Left(Rec(s, inj(r1, c, Right(v2, counter - right_counter), 0, 0)), right_counter)
		}
		case (RECD(s, r1), _) => {
			// println("recd anything " + left_counter + " " + right_counter);
			Rec(s, inj(r1, c, v, 0, 0))
		}
		case (RANGE(lb, rb), Void) => if (lb <= c && c <= rb) Chr(c) else throw new IllegalArgumentException("Range error in injection")
	}
}

def valChecker(v: Val): Boolean = v match {
	case Void => true
	case Chr(c) => true
	case Left(Left(_, _), _) => false
	case Left(v, n) => if (n < 1) false else valChecker(v)
	case Right(Right(_, _), _) => false
	case Right(v, n) => if (n < 1) false else valChecker(v)
	case Seqv(v1, v2) => valChecker(v1) && valChecker(v2)
	case Stars(lst) => lst.map(valChecker).forall(x => x == true)
	case Rec(s, v) => valChecker(v)
}


def matcher(r: Rexp, s: String): Boolean = nullable(ders(r, s.toList))

def parse(r: Rexp, s: List[Char]): Val = s match {
	case Nil => if (nullable(r)) mkEps(r) else throw new IllegalArgumentException
	case head::tail => inj(r, head, parse(der(r, head), tail), 0, 0)
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
						case (NULL, _) => (y1, addRight(_: Val, f2))
						case (_, NULL) => (x1, addLeft(_: Val, f1))
						case (z1, z2) => if (z1 == z2) (z1, addLeft(_: Val, f1))  
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
					case (NULL, _) => (y1, addRight(_: Val, f2))
					case (_, NULL) => (x1, addLeft(_: Val, f1))
					case (z1, z2) => if (z1 == z2) (z1, addLeft(_: Val, f1))  
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

def addRight(v: Val, f: Val => Val): Val = f(v) match {
	case Right(v1, counter) => Right(v1, counter + 1)
	case v1 => Right(v1, 1)
}

def addLeft(v: Val, f: Val => Val): Val = f(v) match {
	case Left(v1, counter) => Left(v1, counter + 1)
	case v1 => Left(v1, 1)
}

def simplifyWithoutAssociativity(r: Rexp): (Rexp, Val => Val) = r match {
	case ALT(x, y) => {
		val (x1, f1) = simplifyWithoutAssociativity(x)
		val (y1, f2) = simplifyWithoutAssociativity(y)
		(x1, y1) match {
			case (NULL, _) => (y1, addRight(_: Val, f2))
			case (_, NULL) => (x1, addLeft(_: Val, f1))
			case _ => if (x1 == y1) (x1, addLeft(_: Val, f1)) 
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
	case Left(x, counter) => {
		if (counter == 1) {
			f1(x) match {
				case Left(v1, counter1) => Left(v1, counter1 + 1)
				case v1 => Left(v1, 1)
			}
		} else {
			f1(Left(x, counter - 1)) match {
				case Left(v1, counter1) => Left(v1, counter1 + 1)
				case v1 => Left(v1, 1)
			}
		}		
	}
	case Right(x, counter) => {
		if (counter == 1) {
			f2(x) match {
				case Right(v1, counter1) => Right(v1, counter1 + 1)
				case v1 => Right(v1, 1)
			}
		} else {
			f1(Right(x, counter - 1)) match {
				case Right(v1, counter1) => Right(v1, counter1 + 1)
				case v1 => Right(v1, 1)
			}
		}		
	}
	case _ => throw new IllegalArgumentException
}

def seqvPartial(v: Val, f1: Val => Val, f2: Val => Val): Val = v match {
	case Seqv(v1, v2) => Seqv(f1(v1), f2(v2))
	case _ => throw new IllegalArgumentException
}

def associativityFunction(v: Val, f: Val => Val) : Val = f(v) match {
	case Left(v1, counter) => Left(v1, counter + 1)
	case Right(Left(v2, counter), 1) => {
		if (counter > 1)
			Left(Right(Left(v2, counter - 1), 1), 1)
		else
			v2 match {
				case Right(v3, counter1) => Left(Right(v3, counter1 + 1) , 1)
				case _ => Left(Right(v2, 1), 1)
			}
	}
	case Right(v3, counter) if counter > 1 => Right(v3, counter - 1)
}

def middleFunction(v: Val, steps: Int, f: Val => Val): Val = f(v) match {
	case Right(v1, counter) if counter >= steps => Right(v1, counter + 1)
	case v1 => v1
}

def endFunction(v: Val, steps: Int, f: Val => Val): Val = f(v) match {
	case Right(v1, counter) if counter >= steps - 1 => {
		if (counter == steps - 1) {
			v1 match {
				case Left(v2, counter1) => Right(Left(v2, counter1 + 1), counter)
				case _ => Right(Left(v1, 1), counter)
			}
		} else {
			Right(Left(Right(v1, counter - (steps - 1)), 1), steps - 1)
		}
	}
	case v1 => v1	
}

// def adder(v: Val, steps: Int, f: Val => Val): Val = {
// 	if (steps == 0) f(v)
// 	else v match {
// 		case Right(x) => Right(adder(x, steps - 1, f))
// 		case v1 => v1
// 	}
// }

def parseSimp(r: Rexp, s: List[Char]): Val = {
	// println(calculateRexpElements(r));
	s match {
		case Nil => if (nullable(r)) mkEps(r) else throw new IllegalArgumentException
		case head::tail => {
			val dr = der(r, head)
			val (rd, funct) = simplify(dr)
			inj(r, head, funct(parseSimp(rd, tail)), 0, 0)
		}
	}
}

def parseSimpNoAssociativity(r: Rexp, s: List[Char]): Val = {
	// println(calculateRexpElements(r));
	// println("rexp " + r)
	s match {
		case Nil => {
			// println("current regex " + r);
			if (nullable(r)) { 
				val vl = mkEps(r)
				// if (!valChecker(vl))
					// println("Achtung!")
				// println("val " + vl)
				vl 
			} else 
				throw new IllegalArgumentException
		} 
		case head::tail => {
			val (rd, funct) = simplifyWithoutAssociativity(der(r, head))
			val vl = funct(parseSimpNoAssociativity(rd, tail))
			// if (!valChecker(vl))
				// println("Cazzo!")
			// println("val " + vl)
			val vl2 = inj(r, head, vl, 0, 0)
			// println("---------------")
			vl2
		}
	}
}

def PLUS(r: Rexp) = r ~ r.%
def QUESTION(r: Rexp) = (EMPTY | r)
val SYM1 = "a" | "b" | "c" | "d" | "e" | "f" | "g" | "h" | "i" | "j" | "k" | "l" | "m" | "n" | "o" | "p" | "q" | "r" | "s" | "t" | "u" | "v" | "w" | "x" | "y" | "z"
val SYM2 = RANGE('a', 'z') //
val DIGIT1 = "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9"
val DIGIT2 = RANGE('0', '9') //
val ID1 = SYM1 ~ (SYM1 | DIGIT1).% 
val ID2 = SYM2 ~ (SYM2 | DIGIT2).%
val NUM1 = PLUS(DIGIT1)
val NUM2 = PLUS(DIGIT2)
val KEYWORD : Rexp = "skip" | "while" | "do" | "if" | "then" | "else" | "read" | "write" | "true" | "false"
val SEMI: Rexp = ";"
val OP: Rexp = ":=" | "==" | "-" | "+" | "*" | "!=" | "<" | ">" | "<=" | ">=" | "%" | "/"
val WHITESPACE = PLUS(" " | "\n" | "\t")
val RPAREN: Rexp = ")"
val LPAREN: Rexp = "("
val BEGIN: Rexp = "{"
val END: Rexp = "}"
val DOT: Rexp = (SYM1 | DIGIT1)


val WHILE_REGS = (("k" $ KEYWORD) |
				  ("i" $ ID1) | 
                  ("o" $ OP) | 
                  ("n" $ NUM1) | 
                  ("s" $ SEMI) | 
                  ("p" $ (LPAREN | RPAREN)) | 
                  ("b" $ (BEGIN | END)) | 
                  ("w" $ WHITESPACE)).%

val WHILE_REGS1 = (KEYWORD | ID1 | OP | NUM1 | SEMI | LPAREN | RPAREN | BEGIN | END | WHITESPACE).%
val WHILE_REGS2 = (KEYWORD | ID2 | OP | NUM2 | SEMI | LPAREN | RPAREN | BEGIN | END | WHITESPACE).%
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

val regularka: Rexp = (("r" | "e" | "a" | "d").% | KEYWORD).%
val stroka = "read"


// println(parseSimpNoAssociativity(WHILE_REGS, pfib.toList))

// val result1 = parseSimpNoAssociativity(WHILE_REGS1, pfib2.toList)
// val result2 = parseSimpNoAssociativity(WHILE_REGS2, pfib2.toList)

// println(valSize(result1) + " " + valSizeExpanded(result1))
// println(valSize(result2) + " " + valSizeExpanded(result2))

// val rega: Rexp = ("k" $ KEYWORD | ("w" $ WHITESPACE) | ("i" $ ID)).%

// val result = parseSimpNoAssociativity(WHILE_REGS2, pfib.toList)

// println(result)
// println(valSize(result))
// println(valSizeExpanded(result))

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
  // println((end - start)/1.0e9)
  (end - start)/1.0e9 
}

val prog2 = """
i := 2;
max := 100;
while i < max do {
  isprime := 1;
  j := 2;
  while (j * j) <= i + 1  do {
    if i % j == 0 then isprime := 0  else skip;
    j := j + 1
  };
  if isprime == 1 then write i else skip;
  i := i + 1
}"""

// for (i <- 1 to 50 by 1) {
// 	var timeHolder: Double = 0;
// 	// for (j <- 1 to 100 by 1) {			
//   		// timeHolder += time(parseSimpStack((prog2 * i).toList, WHILE_REGS));
//   	// }
//   	// println("%4.4f".format(timeHolder / 100));
//   	println(valSizeExpanded(parseSimpNoAssociativity(WHILE_REGS, (prog2 * i).toList)));
// }


var r = 0.0

val ptrn: Rexp = ("a" | "b" | "ab").%

val sequenceOfA = "a" * 100000

// for (i <- 1 to 400 by 1) {
//   r += time(parseSimpStack(sequenceOfA.toList, ptrn))
// }

// println("%4.4f".format(r / 400))

// println(time(parseSimpStack(("a" * 4000000).toList, ptrn)))

val test2Rexp = "}"; val test2 = "}"	//(0,1)

println("test 2: " + parseSimpNoAssociativity(test2Rexp, test2.toList))

val test3Rexp = "]"; val test3 = "]"	//(0,1)

println("test 3: " + parseSimpNoAssociativity(test3Rexp, test3.toList))

val test8Rexp = (DOT ~ DOT).% ~ (DOT ~ DOT ~ DOT).%; val test8 = "abcd"	//(0,4)(2,4)(?,?)

println("test 8: " + parseSimpNoAssociativity(test8Rexp, test8.toList))

val test9Rexp =  ("ab" | "a") ~ ("bc" | "c"); val test9	= "abc"	//(0,3)(0,2)(2,3)

println("test 9: " + parseSimpNoAssociativity(test9Rexp, test9.toList))

val test10Rexp = (("ab") ~ "c") | "abc"; val test10 = "abc"	//(0,3)(0,2)

println("test 10: " + parseSimpNoAssociativity(test10Rexp, test10.toList))

val test12Rexp = ("a".%) ~ (QUESTION("b")) ~ (PLUS("b")) ~ "bbb"; val test12 = "aaabbbbbbb"	//(0,10)(0,3)(3,4)(4,7)

println("test 12: " + parseSimpNoAssociativity(test12Rexp, test12.toList))

val test15Rexp = (("a" | "a") | "a"); val test15 = "a"	//(0,1)(0,1)(0,1)

println("test 15: " + parseSimpNoAssociativity(test15Rexp, test15.toList))

val test16Rexp = ("a".%) ~ ("a" | "aa"); val test16 = "aaaa"	//(0,4)(0,3)(3,4)

println("test 16: " + parseSimpNoAssociativity(test16Rexp, test16.toList))

val test17Rexp = "a".% ~ (("a" ~ DOT) | "aa"); val test17 =	"aaaa"	//(0,4)(2,4)

println("test 17: " + parseSimpNoAssociativity(test17Rexp, test17.toList))

val test18Rexp = "a" ~ ("b") | "c" ~ ("d") | "a" ~ ("e") ~ "f"; val test18 = "aef"	//(0,3)(?,?)(?,?)(1,2)

println("test 18: " + parseSimpNoAssociativity(test18Rexp, test18.toList))

val test19Rexp = QUESTION("a" | "b") ~ DOT.%; val test19 = "b"	//(0,1)(0,1)

println("test 19: " + parseSimpNoAssociativity(test19Rexp, test19.toList))

val test20Rexp = ("a" | "b") ~ "c" | "a" ~ ("b" | "c"); val test20 = "ac"	//(0,2)(0,1)(?,?)

println("test 20: " + parseSimpNoAssociativity(test20Rexp, test20.toList))

val test21Rexp = ("a" | "b") ~ "c" | "a" ~ ("b" | "c"); val test21 = "ab"	//(0,2)(?,?)(1,2)

println("test 21: " + parseSimpNoAssociativity(test21Rexp, test21.toList))

val test22Rexp = ("a" | "b").% ~ "c" | ("a" | "ab").% ~ "c"; val test22 = "abc"	//(0,3)(1,2)(?,?)

println("test 22: " + parseSimpNoAssociativity(test22Rexp, test22.toList))

val test24Rexp = (DOT ~ "a" | DOT ~ "b") ~ DOT.% | DOT.% ~ (DOT ~ "a" | DOT ~ "b"); val test24 = "xa"	//(0,2)(0,2)(?,?)

println("test 24: " + parseSimpNoAssociativity(test24Rexp, test24.toList))

val test25Rexp = QUESTION("a") ~ ("ab" | "ba") ~ "ab"; val test25 = "abab"	//(0,4)(0,2)

println("test 25: " + parseSimpNoAssociativity(test25Rexp, test25.toList))

val test26Rexp = QUESTION("a") ~ ("a" ~ QUESTION("c") ~ "b" | "ba") ~ "ab"; val test26 = "abab"	//(0,4)(0,2)

println("test 26: " + parseSimpNoAssociativity(test26Rexp, test26.toList))

val test30Rexp = ("aa" | "aaa").% | ("a" | "aaaaa"); val test30 = "aa"	//(0,2)(0,2)(?,?)

println("test 30: " + parseSimpNoAssociativity(test30Rexp, test30.toList))

val test31Rexp = ("a" ~ DOT | DOT ~ "a" ~ DOT).% | ("a" | DOT ~ "a" ~ DOT ~ DOT ~ DOT); val test31 = "aa"	//(0,2)(0,2)(?,?)

println("test 31: " + parseSimpNoAssociativity(test31Rexp, test31.toList))

val test34Rexp = ("aB" | "cD").%; val test34 = "aBcD"	//(0,4)(2,4)

println("test 34: " + parseSimpNoAssociativity(test34Rexp, test34.toList))

val test39Rexp = ("a") ~ ("b") ~ ("c"); val test39 = "abc"	//(0,3)(0,1)(1,2)(2,3)

println("test 39: " + parseSimpNoAssociativity(test39Rexp, test39.toList))

val test43Rexp = (((((((((((((((((((((((((((((("x")))))))))))))))))))))))))))))); val test43 = "x"	// (0,1)(0,1)(0,1)(0,1)(0,1)(0,1)(0,1)(0,1)(0,1)(0,1)(0,1)(0,1)(0,1)(0,1)(0,1)(0,1)(0,1)(0,1)(0,1)(0,1)(0,1)(0,1)(0,1)(0,1)(0,1)(0,1)(0,1)(0,1)(0,1)(0,1)(0,1)

println("test 43: " + parseSimpNoAssociativity(test43Rexp, test43.toList))

val test44Rexp = (((((((((((((((((((((((((((((("x")))))))))))))))))))))))))))))).%; val test44 = "xx"	//(0,2)(1,2)(1,2)(1,2)(1,2)(1,2)(1,2)(1,2)(1,2)(1,2)(1,2)(1,2)(1,2)(1,2)(1,2)(1,2)(1,2)(1,2)(1,2)(1,2)(1,2)(1,2)(1,2)(1,2)(1,2)(1,2)(1,2)(1,2)(1,2)(1,2)(1,2)

println("test 44: " + parseSimpNoAssociativity(test44Rexp, test44.toList))

val test45Rexp = QUESTION("a") ~ ("ab" | "ba").%; val test45 = "ababababababababababababababababababababababababababababababababababababababababa"	//(0,81)(79,81)

println("test 45: " + parseSimpNoAssociativity(test45Rexp, test45.toList))

val test50Rexp = "a".% ~ "a".% ~ "a".% ~ "a".% ~ "a".% ~ "b"; val test50 = "aaaaaaaaab"	//(0,10)

println("test 50: " + parseSimpNoAssociativity(test50Rexp, test50.toList))

val test51Rexp = "a" ~ PLUS("b") ~ "bc"; val test51 = "abbc"		//(0,4)

println("test 51: " + parseSimpNoAssociativity(test51Rexp, test51.toList))

val test52Rexp = "a" ~ PLUS("b") ~ "bc"; val test52 = "abbbbc"		//(0,6)

println("test 52: " + parseSimpNoAssociativity(test52Rexp, test52.toList))

val test53Rexp = "a" ~ QUESTION("b") ~ "bc"; val test53 = "abbc"		//(0,4)

println("test 53: " + parseSimpNoAssociativity(test53Rexp, test53.toList))

val test54Rexp = "a" ~ QUESTION("b") ~ "bc"; val test54 = "abc"		//(0,3)

println("test 54: " + parseSimpNoAssociativity(test54Rexp, test54.toList))

val test55Rexp = "a" ~ QUESTION("b") ~ "c"; val test55 = "abc"		//(0,3)

println("test 55: " + parseSimpNoAssociativity(test55Rexp, test55.toList))

val test58Rexp = "a(b";	val test58 = "a(b"		//(0,3)

println("test 58: " + parseSimpNoAssociativity(test58Rexp, test58.toList))

val test59Rexp = "a" ~ "(".% ~ "b"; val test59 = "ab"		//(0,2)

println("test 59: " + parseSimpNoAssociativity(test59Rexp, test59.toList))

val test60Rexp = "a" ~ "(".% ~ "b"; val test60 = "a((b"		//(0,4)

println("test 60: " + parseSimpNoAssociativity(test60Rexp, test60.toList))

val test62Rexp = ("a") ~ "b" ~ ("c"); val test62 = "abc"		//(0,3)(0,1)(2,3)

println("test 62: " + parseSimpNoAssociativity(test62Rexp, test62.toList))

val test64Rexp = "a".%; val test64 = "aaa"		//(0,3)

println("test 64: " + parseSimpNoAssociativity(test64Rexp, test64.toList))

val test68Rexp = (PLUS("a") | "b").%; val test68 = "ab"		//(0,2)(1,2)

println("test 68: " + parseSimpNoAssociativity(test68Rexp, test68.toList))

val test69Rexp = PLUS(PLUS("a") | "b"); val test69 = "ab"		//(0,2)(1,2)

println("test 69: " + parseSimpNoAssociativity(test69Rexp, test69.toList))

val test72Rexp = (RANGE('a', 'c')).% ~ "d"; val test72 = "abbbcd"	//	(0,6)(4,5)

println("test 72: " + parseSimpNoAssociativity(test72Rexp, test72.toList))

val test73Rexp = (RANGE('a', 'c')).% ~ "bcd"; val test73 = "abcd"	//	(0,4)(0,1)

println("test 73: " + parseSimpNoAssociativity(test73Rexp, test73.toList))

val test74Rexp = "a" | "b" | "c" | "d" | "e"; val test74 = "e"		//(0,1)

println("test 74: " + parseSimpNoAssociativity(test74Rexp, test74.toList))

val test75Rexp = ("a" | "b" | "c" | "d" | "e") ~ "f"; val test75 = "ef"	//	(0,2)(0,1)

println("test 75: " + parseSimpNoAssociativity(test75Rexp, test75.toList))

val test79Rexp = ("ab" | ("a" ~ "b".%)) ~ "bc"; val test79 = "abc"		//(0,3)(0,1)

println("test 79: " + parseSimpNoAssociativity(test79Rexp, test79.toList))

val test80Rexp = "a" ~ (RANGE('b', 'c').%) ~ "c".%; val test80 = "abc"		//(0,3)(1,3)

println("test 80: " + parseSimpNoAssociativity(test80Rexp, test80.toList))

val test81Rexp = "a" ~ (RANGE('b', 'c').%) ~ ("c".% ~ "d"); val test81 = "abcd"	//	(0,4)(1,3)(3,4)

println("test 81: " + parseSimpNoAssociativity(test81Rexp, test81.toList))

val test82Rexp = "a" ~ (PLUS(RANGE('b', 'c'))) ~ ("c".% ~ "d"); val test82 = "abcd"	//	(0,4)(1,3)(3,4)

println("test 82: " + parseSimpNoAssociativity(test82Rexp, test82.toList))

val test83Rexp = "a" ~ (RANGE('b', 'c').%) ~ (PLUS("c") ~ "d"); val test83 = "abcd"	//	(0,4)(1,2)(2,4)

println("test 83: " + parseSimpNoAssociativity(test83Rexp, test83.toList))

val test84Rexp = "a" ~ RANGE('b', 'd').% ~ "dcdcde"; val test84 = "adcdcde"	//	(0,7)

println("test 84: " + parseSimpNoAssociativity(test84Rexp, test84.toList))

val test85Rexp = ("ab" | "a") ~ "b".% ~ "c"; val test85	= "abc"		//(0,3)(0,2)

println("test 85: " + parseSimpNoAssociativity(test85Rexp, test85.toList))

val test86Rexp = (("a") ~ ("b") ~ "c") ~ ("d"); val test86 = "abcd"	//	(0,4)(0,3)(0,1)(1,2)(3,4)

println("test 86: " + parseSimpNoAssociativity(test86Rexp, test86.toList))

val test88Rexp = ("b" ~ PLUS("c") ~ "d" | "e" ~ "f".% ~ "g" ~ DOT | QUESTION("h") ~ "i" ~ ("j" | "k")); val test88 = "effgz"	
//	(0,5)(0,5)(?,?)

println("test 88: " + parseSimpNoAssociativity(test88Rexp, test88.toList))

val test89Rexp = ("b" ~ PLUS("c") ~ "d" | "e" ~ "f".% ~ "g" ~ DOT | QUESTION("h") ~ "i" ~ ("j" | "k")); val test89 = "ij"		
//(0,2)(0,2)(1,2)

println("test 89: " + parseSimpNoAssociativity(test89Rexp, test89.toList))

val test92Rexp = (DOT.%) ~ "c" ~ (DOT.%); val test92 = "abcde"		//(0,5)(0,2)(3,5)

println("test 92: " + parseSimpNoAssociativity(test92Rexp, test92.toList))

val test93Rexp = "a" ~ ("bc") ~ "d"; val test93 = "abcd"		//(0,4)(1,3) 

println("test 93: " + parseSimpNoAssociativity(test93Rexp, test93.toList))
