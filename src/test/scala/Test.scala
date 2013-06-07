//package test

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
    val d = b(2)
    val obj = CT(new Test)
    val j = 9
    val ll = j + obj.dd(CT("test"), 0)
    println(ll)
  }
}

class Test {
  def dd() = "ddd"
  def dd(b: String, n: Int) = "kk" + b + n
  def r() = {
    val d = dd()
    val a = 1
    val b = a
    a
  }
}

