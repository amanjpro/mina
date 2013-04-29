import ch.usi.inf.l3.mina._

object Test{
  def b() = CT(1)
  def k = {
    val c = 1
  }
  def main(str: Array[String]) {
    val c = CT(b())
    val k = c
    println(c)
  }
}

class Test {
  val k = 3
  def r() = {
    val a = 1
    val b = a
    a
  }
}