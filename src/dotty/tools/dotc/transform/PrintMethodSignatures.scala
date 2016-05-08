package dotty.tools.dotc.transform

import dotty.tools.dotc.ast.tpd
import dotty.tools.dotc.core.Constants.Constant
import dotty.tools.dotc.core.Contexts.Context
import dotty.tools.dotc.core.DenotTransformers._
import dotty.tools.dotc.core.Flags
import dotty.tools.dotc.core.SymDenotations._
import dotty.tools.dotc.core.Types._
import dotty.tools.dotc.transform.TreeTransforms.{TransformerInfo, _}

/** */
class PrintMethodSignatures extends MiniPhaseTransform { thisTransform =>
  override def phaseName = "printMethodSignatures"
  import tpd._
  override def transformDefDef(tree: tpd.DefDef)(implicit ctx: Context, info: TransformerInfo): tpd.Tree = if (tree.rhs.isEmpty || (tree.symbol is Flags.Label)) tree else {
    val symbStr = tree.symbol.fullName + "#" + tree.symbol.initial.info.show + "##" + tree.symbol.signature
    val print = ref(ctx.definitions.Predef_println).appliedTo(Literal(Constant(symbStr)))
    val rhs = Block(List(print), tree.rhs)
    cpy.DefDef(tree)(rhs = rhs)
  }
}
