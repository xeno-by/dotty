package dotty.tools.dotc
package transform.linker

import core._
import Contexts.Context
import Flags._
import Symbols._
import SymDenotations._
import Types._
import Decorators._
import DenotTransformers._
import StdNames._
import NameOps._
import ast.Trees._
import dotty.tools.dotc.ast.tpd
import util.Positions._
import Names._
import dotty.tools.dotc.transform.TreeTransforms.{MiniPhaseTransform, TransformerInfo, TreeTransform}

import collection.mutable
import scala.collection.immutable.::


/** This phase applies rewritings provided by libraries. */
class Rewrites extends MiniPhaseTransform { thisTransform =>
  import ast.tpd._

  override def phaseName: String = "rewrites"
  val namePattern = "$opt"

  def isOptVersion(n: Name) = n.endsWith(namePattern)
  def dropOpt(n: Name)(implicit ctx: Context) = if (isOptVersion(n)) n.dropRight(namePattern.length) else n

  private var annot: Symbol = null
  private var pairs: List[(DefDef, DefDef)] = null

  def collectPatters(tree: tpd.Tree)(implicit ctx: Context) = {
    val collector = new TreeAccumulator[List[(DefDef, DefDef)]] {
      def apply(x: List[(tpd.DefDef, tpd.DefDef)], tree: tpd.Tree)(implicit ctx: Context): List[(tpd.DefDef, tpd.DefDef)] = {
        tree match {
          case t: tpd.TypeDef if t.isClassDef && t.symbol.hasAnnotation(annot) =>
            val stats = t.rhs.asInstanceOf[Template].body
            val defsByName = stats.filter(x => x.isInstanceOf[DefDef]).asInstanceOf[List[DefDef]].map(x => (x.symbol.name, x)).toMap
            val pairs = defsByName.groupBy(x => dropOpt(x._1)).filter(x => x._2.size > 1)
            val (errors, realPairs) = pairs.partition(x => x._2.size > 2)

            errors.foreach(x => ctx.error("overloads are not supported", x._2.head._2.pos))
            val prepend = realPairs.map(x=>
              (x._2.values.find(x => !isOptVersion(x.symbol.name)).get,
                x._2.values.find(x => isOptVersion(x.symbol.name)).get)
            ).toList


            foldOver(prepend ::: x, t)
          case _ => foldOver(x, tree)
        }
      }
    }
    collector.apply(Nil, tree)
  }

  override def prepareForUnit(tree: tpd.Tree)(implicit ctx: Context): TreeTransform = {
    annot = ctx.requiredClass("dotty.linker.rewrites")
    pairs = collectPatters(tree)
    ctx.warning(s"found rewriting rules: ${pairs.map(x=> x._1.symbol.showFullName).mkString(", ")}")
    pairs.foreach(checkSupported)
    this
  }

  private def checkSupported(pair :(tpd.DefDef, tpd.DefDef))(implicit ctx: Context): Unit = {
    val pattern = pair._1
    val rewrite = pair._2
    def unsupported(reason: String) = ctx.error("Unsupported pattern: " + reason, pattern.pos)
    if (pattern.symbol.signature != rewrite.symbol.signature)
      unsupported("signatures do not match")
    if (pattern.vparamss.flatten.map(_.name) != rewrite.vparamss.flatten.map(_.name))
      unsupported("arguments should have same names")
    new TreeTraverser {
      def traverse(tree: tpd.Tree)(implicit ctx: Context): Unit =
        tree match {
          case t: Apply => traverseChildren(tree)
          case Block(Nil, exp) => traverse(exp)
          case t @ Block(List(fn: DefDef), c: Closure) =>
            unsupported(s"No closures in patterns yet. Sorry. Use function-arguments instead.")
          //traverseChildren(fn.rhs)
          case t: Literal => ()
          case _: Select | _: Ident => traverseChildren(tree)
          case _ => unsupported(s"${tree.getClass.getSimpleName} tree is currently unsupported")
        }
    }.traverse(pattern.rhs)
  }


  override def transformUnit(tree: tpd.Tree)(implicit ctx: Context, info: TransformerInfo): tpd.Tree = {
    annot = null
    pairs = null
    tree
  }


  override def transformDefDef(tree: tpd.DefDef)(implicit ctx: Context, info: TransformerInfo): tpd.Tree = {
    if (tree.symbol.ownersIterator.findSymbol(x => x.hasAnnotation(annot)).exists) tree
    else {
      val mapping = new TreeMap() {
        override def transform(tree: tpd.Tree)(implicit ctx: Context):tpd.Tree = tree match {
          case tree: DefTree =>
            super.transform(tree)(ctx.withOwner(tree.symbol))
          case tree =>
            val scanner = pairs.iterator.map(x => (x, isSimilar(tree, x._1))).find(x => x._2.nonEmpty)
            if (scanner.nonEmpty) {
              val ((patern, rewrite), Some(binding)) = scanner.get
              ctx.warning(s"Applying rule ${dropOpt(rewrite.symbol.name)}, substitution: ${binding.map(x => s"${x._1} -> ${x._2._1.show}").mkString(", ")}")
              val subByName = binding.map(x => (x._1.name, x._2)).toMap[Name, (Tree, Symbol)]
              val substitution = new TreeMap() {
                override def transform(tree: tpd.Tree)(implicit ctx: Context): tpd.Tree = tree match {
                  case tree: DefTree =>
                    super.transform(tree)(ctx.withOwner(tree.symbol))
                  case _ =>
                    if (tree.symbol.maybeOwner == rewrite.symbol && tree.symbol.is(Flags.Param)) {
                      val (oldTree, oldOwner) = subByName(tree.symbol.name)
                      oldTree.changeOwner(oldOwner, ctx.owner)
                    }
                    else super.transform(tree)
                }
              }
              super.transform(substitution.transform(rewrite.rhs)).changeOwner(rewrite.symbol, ctx.owner)
            } else super.transform(tree)
        }
      }

      mapping.transform(tree)
    }
  }

  override def transformTypeDef(tree: tpd.TypeDef)(implicit ctx: Context, info: TransformerInfo): tpd.Tree = {
    if (tree.symbol.hasAnnotation(annot) && !(tree.symbol.isStatic && tree.symbol.is(Flags.Module)))
      ctx.error("Rewrite rulles can only be defined in top level module classes", tree.pos)

    tree
  }


  private def isSimilar(tree: Tree, pattern: DefDef)(implicit ctx: Context): Option[Map[Symbol, (Tree, Symbol)]] = {
    var currentMapping = new mutable.HashMap[Symbol, (Tree, Symbol)]()
    def seb/*skipEmptyBlocks*/(x: Tree) = x match {
      case Block(Nil, t) => t
      case _ => x
    }
    def abort = currentMapping = null
    try {
      def bind(sym: Symbol, tree: Tree, oldOwner: Symbol) = {
        if (currentMapping.contains(sym)) abort
        else currentMapping.put(sym, (tree, oldOwner))
      }
      def loop(subtree: Tree, subpat: Tree)(implicit ctx: Context): Unit = seb(subtree) match {
        case Apply(sel, args) => seb(subpat) match {
          case Apply(selpat, selargs) if selargs.hasSameLengthAs(args) =>
            loop(sel, selpat)
            args.zip(selargs).foreach(x => loop(x._1, x._2))
          case subpat: Ident if (subpat.symbol.owner == pattern.symbol && subpat.symbol.is(Flags.Param)) => // new binding
            bind(subpat.symbol, subtree, ctx.owner)
          case _ =>
            abort
        }
        case Block(List(fn: DefDef), c: Closure) => seb(subpat) match {
          case subpat: Ident if (subpat.symbol.owner == pattern.symbol && subpat.symbol.is(Flags.Param)) => // new binding
            bind(subpat.symbol, subtree, ctx.owner)
          case _ => abort
        }
        case subtree: Ident => seb(subpat) match {
          case subpat: Ident if (subpat.symbol.owner == pattern.symbol && subpat.symbol.is(Flags.Param)) => // new binding
            bind(subpat.symbol, subtree, ctx.owner)
          case subpat: RefTree if (subpat.symbol eq subtree.symbol) => //same ref
          case _ => abort
        }
        case subtree: Select => seb(subpat) match {
          case subpat: Ident if (subpat.symbol.owner == pattern.symbol && subpat.symbol.is(Flags.Param)) => // new binding
            bind(subpat.symbol, subtree, ctx.owner)
          case subpat: Select if (subpat.symbol eq subtree.symbol) => //same ref
            loop(subtree.qualifier, subpat.qualifier)
          case _ => abort
        }
        case subtree: Literal => seb(subpat) match {
          case subpat: Ident if (subpat.symbol.owner == pattern.symbol && subpat.symbol.is(Flags.Param)) => // new binding
            bind(subpat.symbol, subtree, ctx.owner)
          case subpat: Literal if (subpat.const.value == subtree.const.value) =>   //todo: is it fine to ignore tag?
          case _ => abort
        }
        case _ => abort
      }
      loop(tree, pattern.rhs)
    } catch {
      case e: NullPointerException =>
    }
    if ((currentMapping eq null) || currentMapping.size != pattern.vparamss.flatten.size) None
    else Some(currentMapping.toMap)
  }
}
