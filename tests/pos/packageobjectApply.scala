package object foo {
  def apply(x: Int) = x
}

object Test {
  def main(args: Array[String]): Unit = {
    println(foo(42))
  }
}