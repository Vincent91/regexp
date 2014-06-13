import scala.language.implicitConversions    
    
abstract class Rexp 
case object NULL extends Rexp
case object EMPTY extends Rexp
case class CHAR(c: Char) extends Rexp
case class ALT(r1: Rexp, r2: Rexp) extends Rexp 
case class SEQ(r1: Rexp, r2: Rexp) extends Rexp 
case class STAR(r: Rexp) extends Rexp 

abstract class Val
case object Void extends Val
case class Chr(c: Char) extends Val
case class Seqv(v1: Val, v2: Val) extends Val
case class Left(v: Val) extends Val
case class Right(v: Val) extends Val
case class Stars(l: List[Val]) extends Val

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
}

def nullable(r: Rexp): Boolean = r match {
	case NULL => false
	case EMPTY => true
	case CHAR(_) => false
	case ALT(v1, v2) => nullable(v1) || nullable(v2)
	case SEQ(v1, v2) => nullable(v1) && nullable(v2)
	case STAR(_) => true
}

def der(r: Rexp, c: Char): Rexp = r match {
	case NULL => NULL
	case EMPTY => NULL
	case CHAR(v) => if (v == c) EMPTY else NULL
	case ALT(v1, v2) => ALT(der(v1, c), der(v2, c))
	case SEQ(v1, v2) => 
		if (nullable(v1)) ALT(SEQ(der(v1, c), v2), der(v2, c)) 
		else SEQ(der(v1, c), v2)
	case STAR(r) => SEQ(der(r, c), STAR(r))
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
}

def mkEps(r: Rexp): Val = r match {
	case EMPTY => Void
	case ALT(v1, v2) => 
		if (nullable(v1)) Left(mkEps(v1))
		else Right(mkEps(v2))
	case SEQ(v1, v2) => Seqv(mkEps(v1), mkEps(v2))
	case STAR(r) => Stars(Nil)
}

def inj(r: Rexp, c: Char, v: Val): Val = (r, v) match {
	case (STAR(r), Seqv(v1, Stars(vs))) => Stars(inj(r, c, v1)::vs)
	case (SEQ(r1, r2), Seqv(v1, v2)) => Seqv(inj(r1, c, v1), v2)
	case (SEQ(r1, r2), Left(Seqv(v1, v2))) => Seqv(inj(r1, c, v1), v2)
	case (SEQ(r1, r2), Right(v2)) => Seqv(mkEps(r1), inj(r2, c, v2))
	case (ALT(r1, r2), Left(v1)) => Left(inj(r1, c, v1))
	case (ALT(r1, r2), Right(v2)) => Right(inj(r2, c, v2))
	case (CHAR(d), Void) => Chr(d)
}

def matcher(r: Rexp, s: String): Boolean = nullable(ders(r, s.toList))

def parse(r: Rexp, s: List[Char]): Val = s match {
	case Nil => if (nullable(r)) mkEps(r) else throw new IllegalArgumentException
	case head::tail => inj(r, head, parse(der(r, head), tail))
} 

def compare(r: Rexp, s: Rexp): Boolean = if (r == s) true else false

def simplify(r: Rexp): (Rexp, Val => Val) = r match {
	case ALT(ALT(x, y), z) => {
		val (r1, f1) = simplify(ALT(x, ALT(y, z)))
		(r1, associativityFunction(_: Val, f1))
	}
	case CHAR(x) => (CHAR(x), (v: Val) => v)
	case NULL => (NULL, (v: Val) => v)
	case EMPTY => (EMPTY, (v: Val) => v)
	case SEQ(x, y) => {
		val (x1, f1) = simplify(x)
		val (y1, f2) = simplify(y)
		(x1, y1) match {
			case (EMPTY, z) => (z, seqvEmptyLeftPartial(_: Val, f1, f2))
			case (z, EMPTY) => (z, seqvEmptyRightPartial(_: Val, f1, f2))
			case (z1, z2) => (SEQ(z1, z2), seqvPartial(_: Val, f1, f2))
		}
	} 
	case ALT(x, y) => {
		val (x1, f1) = simplify(x)
		val (y1, f2) = simplify(y)
		(x1, y1) match {
			case (z, NULL) => (z, (v: Val) => Left(f1(v)))
			case (NULL, z) => (z, (v: Val) => Right(f2(v)))
			case (EMPTY, EMPTY) => (EMPTY, (v: Val) => Left(f1(v)))
			case (z1, z2) => (ALT(z1, z2), alternativeValPartial(_: Val, f1, f2))
		}
	}
	case r => (r, (v: Val) => v)
}

def calculateRexpElements(r: Rexp): Int = r match {
	case CHAR(_) => 1
	case NULL => 1
	case EMPTY => 1
	case SEQ(x, y) => 1 + calculateRexpElements(x) + calculateRexpElements(y)
	case ALT(x, y) => 1 + calculateRexpElements(x) + calculateRexpElements(y)
	case STAR(x) => 1 + calculateRexpElements(x)
}


def simplifyWithoutAssociativity(r: Rexp): (Rexp, Val => Val) = r match {
	case CHAR(x) => (CHAR(x), (v: Val) => v)
	case NULL => (NULL, (v: Val) => v)
	case EMPTY => (EMPTY, (v: Val) => v)
	case SEQ(x, y) => {
		val (x1, f1) = simplifyWithoutAssociativity(x)
		val (y1, f2) = simplifyWithoutAssociativity(y)
		(x1, y1) match {
			case (EMPTY, z) => (z, seqvEmptyLeftPartial(_: Val, f1, f2))
			case (z, EMPTY) => (z, seqvEmptyRightPartial(_: Val, f1, f2))
			case (z1, z2) => (SEQ(z1, z2), seqvPartial(_: Val, f1, f2))
		}
	} 
	case ALT(x, y) => {
		val (x1, f1) = simplifyWithoutAssociativity(x)
		val (y1, f2) = simplifyWithoutAssociativity(y)
		(x1, y1) match {
			case (z, NULL) => (z, (v: Val) => Left(f1(v)))
			case (NULL, z) => (z, (v: Val) => Right(f2(v)))
			case (EMPTY, EMPTY) => (EMPTY, (v: Val) => Left(f1(v)))
			case (z1, z2) if z1 == z2 => (z1, (v: Val) => Left(f1(v)))
			case (z1, z2) => (ALT(z1, z2), alternativeValPartial(_: Val, f1, f2))
		}
	}
	case r => (r, (v: Val) => v)
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

def parseSimp(r: Rexp, s: List[Char]): Val = s match {
	case Nil => {
		println(calculateRexpElements(r))
		if (nullable(r)) mkEps(r) else throw new IllegalArgumentException
	}
	case head::tail => {
		println(calculateRexpElements(r))
		val (rd, funct) = simplify(r)
		funct(inj(rd, head, parseSimp(der(rd, head), tail)))
	}
}

def parseSimpNoAssociativity(r: Rexp, s: List[Char]): Val = 
	s match {
	case Nil => {
		println(calculateRexpElements(r))
		if (nullable(r)) mkEps(r) else throw new IllegalArgumentException
	}
	case head::tail => {
		println(calculateRexpElements(r))
		val (rd, funct) = simplifyWithoutAssociativity(r)
		funct(inj(rd, head, parseSimpNoAssociativity(der(rd, head), tail)))
	}
}

def associativityFunction(v: Val, f: Val => Val) : Val = f(v) match {
	case Left(v1) => Left(Left(v1))
	case Right(Left(v2)) => Left(Right(v2))
	case Right(Right(v3)) => Right(v3)
}

def PLUS(r: Rexp) = r ~ r.%
val SYM = "a" | "b" | "c" | "d" | "e" | "f" | "g" | "h" | "i" | "j" | "k" | "l" | "m" | "n" | "o" | "p" | "q" | "r" | "s" | "t" | "u" | "v" | "w" | "x" | "y" | "z"
val DIGIT = "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9"
val ID = SYM ~ (SYM | DIGIT).% 
val NUM = PLUS(DIGIT)
val KEYWORD : Rexp = "skip" | "while" | "do" | "if" | "then" | "else" | "read" | "write" | "true" | "false"
val SEMI: Rexp = ";"
val OP: Rexp = ":=" | "==" | "-" | "+" | "*" | "!=" | "<" | ">" | "%" | "/"
val WHITESPACE = PLUS(" " | "\n" | "\t")
val RPAREN: Rexp = ")"
val LPAREN: Rexp = "("
val BEGIN: Rexp = "{"
val END: Rexp = "}"

val WHILE_REGS = (KEYWORD | ID | OP | NUM | SEMI | LPAREN | RPAREN | BEGIN | END | WHITESPACE).%

// Some Tests

val pfib = """read n"""

def calculator(r: Rexp, s: List[Char]): Unit = s match {
	case Nil => println(calculateRexpElements(r))
	case head::tail => {
		println(calculateRexpElements(r))
		calculator(der(r, head), tail)
	}
}

//calculator(WHILE_REGS, pfib.toList)

println(parseSimpNoAssociativity(WHILE_REGS, pfib.toList))
// println("________________________________")
// println(parseSimpNoAssociativity(WHILE_REGS, pfib.toList))


//------------------------------------

// val regularka = (("aa" | "ab" | "c" | "a") ~ ("ee" | "ed" | "e" | "c")).%
// val stroka = "ae"

// println(calculateRexpElements(regularka))
// println(calculateRexpElements(der(regularka, 'a')))
// println("-------------")
// println(calculateRexpElements(der(der(regularka, 'a'), 'e')))
// println()
// println(parseSimpNoAssociativity(regularka, stroka.toList))
// println("-------------")
// println(parseSimp(regularka, stroka.toList))

//------------------------------------
