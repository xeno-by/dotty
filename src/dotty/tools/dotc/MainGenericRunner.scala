package dotty.tools
package dotc

import java.net.URL
import config.CompilerCommand
import core.Contexts.{Context, ContextBase}
import config.{ScalaSettings => DottySettings}
import scala.reflect.internal.util.ScalaClassLoader
import scala.tools.nsc.{GenericRunnerSettings => ScalaRunnerSettings}

object MainGenericRunner {
  private def loadClasspath(dsettings: DottySettings)(implicit ctx: Context): Seq[URL] = {
    val ssettings = new ScalaRunnerSettings(msg => sys.error(s"fatal error: $msg"))
    ssettings.classpath.value = dsettings.classpath.value
    ssettings.classpathURLs
  }

  def main(args: Array[String]): Unit = {
    def fail(message: String) = { Console.err.println(message); sys.exit(1) }
    val initCtx = (new ContextBase).initialCtx
    val summary = CompilerCommand.distill(args)(initCtx)
    implicit val ctx: Context = initCtx.fresh.setSettings(summary.sstate)
    val rest = CompilerCommand.checkUsage(summary)
    rest match {
      case objectName :: arguments =>
        val classpath = loadClasspath(ctx.settings)
        val classLoader = ScalaClassLoader.fromURLs(classpath)
        classLoader.run(objectName, arguments)
      case Nil =>
        fail("nothing to run")
    }
  }
}
