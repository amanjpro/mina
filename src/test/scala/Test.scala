import ch.usi.inf.l3.mina._

object Test{
  def b(v: Int) = v + 2
  def k = {
    val c = CT(~1)
  }
  def main(str: Array[String]) {
    val c = CT(b(1))
    val k = c
    println(c)
  }
}

class Test {
  def k() = "kk"
  def r() = {
    val d = k()
    val a = 1
    val b = a
    a
  }
}