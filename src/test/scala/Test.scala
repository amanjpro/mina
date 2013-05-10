import ch.usi.inf.l3.mina._

object Test{
  def b(v: Int) = v + 2
  def k() = {
    val c = CT(~1)
    c match {
      case -2 => CT(3 + 3)
      case 3 => CT(~2 + 88)
    }
  }
  def main(str: Array[String]) {
    val c = CT(b(1))
    val fail = CT(new Test)
    val j = c
    val ll = CT(j + k())
    println(ll)
  }
}

class Test {
  def dd() = "kk"
  def r() = {
    val d = dd()
    val a = 1
    val b = a
    a
  }
}