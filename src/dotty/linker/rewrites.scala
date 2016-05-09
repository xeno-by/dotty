package dotty.linker

import scala.annotation.Annotation

/** An annotation used to mark classes containing rewriting rules. */
class rewrites extends Annotation {}

sealed class Rewrite[T] private(from: T, to: T)
object Rewrite {
  def apply[T](from: T, to: T): Rewrite[T] = new Rewrite(from, to)
}

sealed class Warning[T] private (pattern: T, msgfun: /*List[String] => */String)
object Warning {
  // def apply[T](pattern: T, msgfun: List[String] => String): Warning[T] = new Warning[T](pattern, msgfun) // will work only on second compilation
  def apply[T](pattern: T, msg: String)                   : Warning[T] = new Warning[T](pattern, msg)
}

object Error {
  // def apply[T](pattern: T, msgfun: List[String] => String): Warning[T] = new Warning[T](pattern, msgfun) // will work only on second compilation
  def apply[T](pattern: T, msg: String)                   : Warning[T] = Warning.apply[T](pattern, msg)
}

final class IsLiteral[T] private ()
final class Source[T] private()
final class IsPure[T] private ()


abstract class MetaRewrite[T, Context, Tree] private(body: Context => Tree) {}
object MetaRewrite {
  def apply[T](body: Any => Any) = ???
}
