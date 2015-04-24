package dotty.tools.dotc
package transform

import core._
import Symbols._, Types._, Contexts._, Names._, StdNames._, Constants._, SymUtils._
import scala.collection.{ mutable, immutable }
import Flags._
import TreeTransforms._
import DenotTransformers._
import ast.Trees._
import ast.untpd
import Decorators._
import ValueClasses.isDerivedValueClass
import scala.collection.mutable.ListBuffer
import scala.language.postfixOps

/** Synthetic method implementations for case classes, case objects,
 *  and value classes.
 *  Selectively added to case classes/objects, unless a non-default
 *  implementation already exists:
 *    def equals(other: Any): Boolean
 *    def hashCode(): Int
 *    def canEqual(other: Any): Boolean
 *    def toString(): String
 *  Special handling:
 *    protected def readResolve(): AnyRef
 *
 *  Selectively added to value classes, unless a non-default
 *  implementation already exists:
 *
 *    def equals(other: Any): Boolean
 *    def hashCode(): Int
 */
class SyntheticMethods(thisTransformer: DenotTransformer) {
  import ast.tpd._

  private var myValueSymbols: List[Symbol] = Nil
  private var myCaseSymbols: List[Symbol] = Nil

  private def initSymbols(implicit ctx: Context) =
    if (myValueSymbols.isEmpty) {
      myValueSymbols = List(defn.Any_hashCode, defn.Any_equals)
      myCaseSymbols = myValueSymbols ++ List(defn.Any_toString, defn.Product_canEqual, defn.Product_productArity)
    }

  def valueSymbols(implicit ctx: Context) = { initSymbols; myValueSymbols }
  def caseSymbols(implicit ctx: Context) = { initSymbols; myCaseSymbols }

  /** The synthetic methods of the case or value class `clazz`.
   */
  def syntheticMethods(clazz: ClassSymbol)(implicit ctx: Context): List[Tree] = {
    val clazzType = clazz.typeRef
    lazy val accessors =
      if (isDerivedValueClass(clazz))
        clazz.termParamAccessors
      else
        clazz.caseAccessors

    val symbolsToSynthesize: List[Symbol] =
      if (clazz.is(Case)) caseSymbols
      else if (isDerivedValueClass(clazz)) valueSymbols
      else Nil

    def syntheticDefIfMissing(sym: Symbol): List[Tree] = {
      val existing = sym.matchingMember(clazz.thisType)
      if (existing == sym || existing.is(Deferred)) syntheticDef(sym) :: Nil
      else Nil
    }

    def syntheticDef(sym: Symbol): Tree = {
      val synthetic = sym.copy(
        owner = clazz,
        flags = sym.flags &~ Deferred | Synthetic | Override,
        coord = clazz.coord).enteredAfter(thisTransformer).asTerm

      def forwardToRuntime(vrefss: List[List[Tree]]): Tree =
        ref(defn.runtimeMethod("_" + sym.name.toString)).appliedToArgs(This(clazz) :: vrefss.head)

      def syntheticRHS(implicit ctx: Context): List[List[Tree]] => Tree = synthetic.name match {
        case nme.hashCode_ if isDerivedValueClass(clazz) => vrefss => valueHashCodeBody
        case nme.hashCode_ => vrefss => caseHashCodeBody
        case nme.toString_ => forwardToRuntime
        case nme.equals_ => vrefss => equalsBody(vrefss.head.head)
        case nme.canEqual_ => vrefss => canEqualBody(vrefss.head.head)
        case nme.productArity => vrefss => Literal(Constant(accessors.length))
      }
      ctx.log(s"adding $synthetic to $clazz at ${ctx.phase}")
      DefDef(synthetic, syntheticRHS(ctx.withOwner(synthetic)))
    }

    /** The class
     *
     *      case class C(x: T, y: U)
     *
     *  gets the equals method:
     *
     *      def equals(that: Any): Boolean =
     *        (this eq that) || {
     *          that match {
     *            case x$0 @ (_: C) => this.x == this$0.x && this.y == x$0.y
     *            case _ => false
     *         }
     *
     *  If C is a value class the initial `eq` test is omitted.
     */
    def equalsBody(that: Tree)(implicit ctx: Context): Tree = {
      val thatAsClazz = ctx.newSymbol(ctx.owner, nme.x_0, Synthetic, clazzType, coord = ctx.owner.pos) // x$0
      def wildcardAscription(tp: Type) =
        Typed(untpd.Ident(nme.WILDCARD).withType(tp), TypeTree(tp))
      val pattern = Bind(thatAsClazz, wildcardAscription(clazzType)) // x$0 @ (_: C)
      val comparisons = accessors map (accessor =>
        This(clazz).select(accessor).select(defn.Any_==).appliedTo(ref(thatAsClazz).select(accessor)))
      val rhs = // this.x == this$0.x && this.y == x$0.y
        if (comparisons.isEmpty) Literal(Constant(true)) else comparisons.reduceLeft(_ and _)
      val matchingCase = CaseDef(pattern, EmptyTree, rhs) // case x$0 @ (_: C) => this.x == this$0.x && this.y == x$0.y
      val defaultCase = CaseDef(wildcardAscription(defn.AnyType), EmptyTree, Literal(Constant(false))) // case _ => false
      val matchExpr = Match(that, List(matchingCase, defaultCase))
      if (isDerivedValueClass(clazz)) matchExpr
      else {
        val eqCompare = This(clazz).select(defn.Object_eq).appliedTo(that.asInstance(defn.ObjectType))
        eqCompare or matchExpr
      }
    }

    /** The class
     *
     *  class C(x: T) extends AnyVal
     *
     *  gets the hashCode method:
     *
     *    def hashCode: Int = x.hashCode()
     */
    def valueHashCodeBody(implicit ctx: Context): Tree = {
      assert(accessors.length == 1)
      ref(accessors.head).select(nme.hashCode_).ensureApplied
    }

    /** The class
     *
     *    case class C(x: T, y: T)
     *
     *  gets the hashCode method:
     *
     *    def hashCode: Int = {
     *      <synthetic> var acc: Int = 0xcafebabe;
     *      acc = Statics.mix(acc, x);
     *      acc = Statics.mix(acc, Statics.this.anyHash(y));
     *      Statics.finalizeHash(acc, 2)
     *    }
     */
    def caseHashCodeBody(implicit ctx: Context): Tree = {
      val acc = ctx.newSymbol(ctx.owner, "acc".toTermName, Mutable | Synthetic, defn.IntType, coord = ctx.owner.pos)
      val accDef = ValDef(acc, Literal(Constant(0xcafebabe)))
      val mixes = for (accessor <- accessors.toList) yield
        Assign(ref(acc), ref(defn.staticsMethod("mix")).appliedTo(ref(acc), hashImpl(accessor)))
      val finish = ref(defn.staticsMethod("finalizeHash")).appliedTo(ref(acc), Literal(Constant(accessors.size)))
      Block(accDef :: mixes, finish)
    }

    /** The hashCode implementation for given symbol `sym`. */
    def hashImpl(sym: Symbol)(implicit ctx: Context): Tree = {
      val d = defn
      import d._
      sym.info.finalResultType.typeSymbol match {
        case UnitClass | NullClass              => Literal(Constant(0))
        case BooleanClass                       => If(ref(sym), Literal(Constant(1231)), Literal(Constant(1237)))
        case IntClass                           => ref(sym)
        case ShortClass | ByteClass | CharClass => ref(sym).select(nme.toInt)
        case LongClass                          => ref(staticsMethod("longHash")).appliedTo(ref(sym))
        case DoubleClass                        => ref(staticsMethod("doubleHash")).appliedTo(ref(sym))
        case FloatClass                         => ref(staticsMethod("floatHash")).appliedTo(ref(sym))
        case _                                  => ref(staticsMethod("anyHash")).appliedTo(ref(sym))
      }
    }

    /** The class
     *
     *    case class C(...)
     *
     *  gets the canEqual method
     *
     *    def canEqual(that: Any) = that.isInstanceOf[C]
     */
    def canEqualBody(that: Tree): Tree = that.isInstance(clazzType)

    symbolsToSynthesize flatMap syntheticDefIfMissing
  }

  def addSyntheticMethods(impl: Template)(implicit ctx: Context) =
    if (ctx.owner.is(Case) || isDerivedValueClass(ctx.owner))
      cpy.Template(impl)(body = impl.body ++ syntheticMethods(ctx.owner.asClass))
    else
      impl
}
