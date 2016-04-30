import dotty.linker.rewrites

@rewrites
object rules{
  def twoDropsOnes(x: List[Int]) = 
    x.drop(1).drop(1)
  def twoDropsOnes$opt(x: List[Int]) = 
    x.drop(2)
  def twoDropRights(x: List[Int], a: Int, b: Int) = 
    x.dropRight(a).dropRight(b)
  def twoDropRights$opt(x: List[Int], a: Int, b: Int) = 
    x.dropRight(a + b)
  def twoFilters(x: List[Int], a: Int => Boolean, b: Int => Boolean) = 
    x.filter(a).filter(b)
  def twoFilters$opt(x: List[Int], a: Int => Boolean, b: Int => Boolean) = 
    x.filter(x => a(x) && b(x))
}

object Test{
  def main(args: Array[String]): Unit = {
     List(1,2,3).drop(1).drop(1)
     List(1,2,3).dropRight(1).dropRight(1)
     List(1,2,3).filter(_ > 2).filter(_ > 1)
  }
}
