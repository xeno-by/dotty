import dotty.linker._

@rewrites
object rules/* extends NeedsMeta */ {
  def twoDropsOnes(x: List[Int]) =
    Rewrite(x.drop(1).drop(1), x.drop(2))
  def twoDropRights(x: List[Int], a: Int, b: Int) = 
    Rewrite(x.dropRight(a).dropRight(b), x.dropRight(a + b))

  /************************************/
  def twoFilters(x: List[Int], a: Int => Boolean, b: Int => Boolean)(implicit apure: IsPure[a.type]) =
    Rewrite(from   = x.filter(a).filter(b),
            to     = x.filter(x => a(x) && b(x)))


  def prettyPrint(x: Any)(implicit source: Source[x.type]) = 
    Rewrite(Test.myPrettyPrint(x), println(source + " = " + x))

  /*
  def twoFilters(x: List[Int], a: Int => Boolean, b: Int => Boolean) =
    Rewrite(filter = meta.isPure(a), // restriction: the expressions that are used here are very limited
            from   = x.filter(a).filter(b),
            to     = x.filter(x => a(x) && b(x)))



  def twoFilters(x: List[Int], a: Int => Boolean, b: Int => Boolean)(implicit meta: Semantics) =
    if (meta.isPure(a))
      Rewrite(x.filter(a).filter(b), x.filter(x => a(x) && b(x)))

  def twoFilters(x: List[Int], a: Int => Boolean, b: Int => Boolean) =
    RewriteMeta(meta{ /* full blown meta */ })
  */
}

object Test{
  def myPrettyPrint(a: Any) = ???
  def main(args: Array[String]): Unit = {
     List(1,2,3).drop(1).drop(1)
     List(1,2,3).dropRight(1).dropRight(1)
     List(1,2,3).filter(_ > 2).filter(_ > 1)
     myPrettyPrint(args.length)
  }
}
