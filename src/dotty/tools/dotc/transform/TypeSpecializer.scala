package dotty.tools.dotc.transform

import java.util

import dotty.tools.dotc.ast.{tpd, TreeTypeMap}
import dotty.tools.dotc.ast.Trees._
import dotty.tools.dotc.core.Contexts.Context
import dotty.tools.dotc.core.DenotTransformers.InfoTransformer
import dotty.tools.dotc.core.Names.TermName
import dotty.tools.dotc.core.Symbols.Symbol
import dotty.tools.dotc.core.{NameOps, Symbols, Flags}
import dotty.tools.dotc.core.Types._
import dotty.tools.dotc.transform.TreeTransforms.{TransformerInfo, MiniPhaseTransform}
import scala.collection.mutable
import dotty.tools.dotc.core.StdNames.nme
import dotty.tools._
import TypeUtils._

import scala.collection.mutable.ListBuffer

class TypeSpecializer extends MiniPhaseTransform  with InfoTransformer {

  import tpd._
  override def phaseName = "specialize"

  private def primitiveTypes(implicit ctx: Context) =
    defn.ScalaValueTypes

  private def defn(implicit ctx:Context) = ctx.definitions

  type Specialization = Array[Type]

  /**
   *  Methods requested for specialization
   *  Generic Symbol   =>  List[  (position in list of args, specialized type requested)  ]
   */
  private val specializationRequests: mutable.HashMap[Symbols.Symbol, List[Specialization]] = mutable.HashMap.empty

  /**
   *  A map that links symbols to their specialized variants.
   *  Each symbol maps to another map, from the list of specialization types to the specialized symbol.
   *  Generic symbol  =>
   *     Map{ List of [ Tuple(position in list of args, specialized Type) ] for each variant  =>  Specialized Symbol }
   */
  private val newSymbolMap: mutable.HashMap[Symbol, mutable.HashMap[Specialization, Symbols.Symbol]] = mutable.HashMap.empty

  /**
   *  A list of symbols gone through the specialisation pipeline
   *  Is used to make calls to transformInfo idempotent
   */
  private val processed: util.IdentityHashMap[Symbol, Symbol] = new util.IdentityHashMap()


  def isSpecializable(sym: Symbol, numOfTypes: Int)(implicit ctx: Context): Boolean =
    numOfTypes > 0 &&
      sym.name != nme.asInstanceOf_ &&
      !newSymbolMap.contains(sym) &&
      !(sym is Flags.JavaDefined) &&
      !sym.isPrimaryConstructor

  /** Get list of types to specialize for */
  def getSpecTypes(method: Symbol, poly: PolyType)(implicit ctx: Context): List[Specialization] = {

    val requested = specializationRequests.getOrElse(method, List.empty)
    if (requested.nonEmpty) {
      requested
    }
    else {
      if (ctx.settings.Yspecialize.value > 0) {
        val filteredPrims: Specialization = primitiveTypes.filter(tpe => poly.paramBounds.forall(_.contains(tpe))).toArray   // TODO: looks fishy + move to pre-spec
        List.range(0, Math.min(poly.paramNames.length, ctx.settings.Yspecialize.value)).map(i => filteredPrims)
      }
      else Nil
    }
  }

  /** was decl requested to be specialized */
  def requestedSpecialization(decl: Symbol)(implicit ctx: Context): Boolean =
    ctx.settings.Yspecialize.value != 0 || specializationRequests.contains(decl)

  def registerSpecializationRequest(methodOrClass: Symbols.Symbol)(arguments: Specialization)
                                   (implicit ctx: Context) = {
    assert(methodOrClass.isClass || methodOrClass.is(Flags.Method))
    if (ctx.phaseId > this.treeTransformPhase.id)
      assert(ctx.phaseId <= this.treeTransformPhase.id)
    val prev = specializationRequests.getOrElse(methodOrClass, List.empty)
    specializationRequests.put(methodOrClass, arguments :: prev)
  }

  /* Provided a class that owns a method to be specialized, adds specializations to the body of the class, without forcing new symbols
  *  provided a method to be specialized, specializes it and enters it into its owner
  * */
  override def transformInfo(tp: Type, sym: Symbol)(implicit ctx: Context): Type = {

    def enterNewSyms(newDecls: List[Symbol], classInfo: ClassInfo) = {
      val decls = classInfo.decls.cloneScope
      newDecls.foreach(decls.enter)
      classInfo.derivedClassInfo(decls = decls)
    }

    def specializeMethods(sym: Symbol) = {
      processed.put(sym, sym)
      sym.info match {
        case classInfo: ClassInfo =>
          val newDecls = classInfo.decls
            .filter(_.symbol.isCompleted) // We do not want to force symbols. Unforced symbol are not used in the source
            .filterNot(_.isConstructor)
            .filter(requestedSpecialization)
            .flatMap(decl => {
            decl.info.widen match {
              case poly: PolyType if isSpecializable(decl.symbol, poly.paramNames.length) =>
                generateMethodSpecializations(getSpecTypes(decl, poly))(poly, decl)
              case _ => Nil
            }
          })

          if (newDecls.nonEmpty) enterNewSyms(newDecls.toList, classInfo)
          else tp
        case poly: PolyType if isSpecializable(sym, poly.paramNames.length) =>
          if (sym.owner.info.isInstanceOf[ClassInfo]) {
            transformInfo(sym.owner.info, sym.owner)  //why does it ever need to recurse into owner?
            tp
          }
          else if (requestedSpecialization(sym) &&
            isSpecializable(sym, poly.paramNames.length)) {
            generateMethodSpecializations(getSpecTypes(sym, poly))(poly, sym)
            tp
          }
          else tp
        case _ => tp
      }
    }

    def generateMethodSpecializations(specTypes: List[Specialization])
                                     (poly: PolyType, decl: Symbol)
                                     (implicit ctx: Context): List[Symbol] = {
     specTypes.map(x => generateSpecializedSymbol(x, poly, decl))
    }

    def generateSpecializedSymbol(instantiations: Specialization, poly: PolyType, decl: Symbol)
                                 (implicit ctx: Context): Symbol = {
      val newSym = ctx.newSymbol(
        decl.owner,
        NameOps.NameDecorator(decl.name)
          .specializedFor(Nil, Nil, instantiations.toList, poly.paramNames)
          .asInstanceOf[TermName],
        decl.flags | Flags.Synthetic,
        poly.duplicate(poly.paramNames, poly.paramBounds.zip(instantiations).map(x => TypeBounds(x._1.lo & x._2, x._1.hi & x._2)), poly.resType)
      )

      val map: mutable.HashMap[Specialization, Symbols.Symbol] = newSymbolMap.getOrElse(decl, mutable.HashMap.empty)
      map.put(instantiations, newSym)
      newSymbolMap.put(decl, map)

      newSym
    }

    if (!processed.containsKey(sym) &&
      (sym ne defn.ScalaPredefModule.moduleClass) &&
      !(sym is Flags.JavaDefined) &&
      !(sym is Flags.Scala2x) &&
      !(sym is Flags.Package) &&
      !sym.isAnonymousClass/*why? becasue nobody can call from outside? they can still be called from inside the class*/) {
      specializeMethods(sym)
    } else tp
  }

  override def transformDefDef(tree: DefDef)(implicit ctx: Context, info: TransformerInfo): Tree = {

    tree.tpe.widen match {

      case poly: PolyType
        if !(tree.symbol.isPrimaryConstructor
          || (tree.symbol is Flags.Label)
          ) =>
        val origTParams = tree.tparams.map(_.symbol)
        val origVParams = tree.vparamss.flatten.map(_.symbol)

        def specialize(decl : Symbol): List[Tree] = {
          if (newSymbolMap.contains(decl)) {
            val specInfo = newSymbolMap(decl)
            val newSyms = specInfo.values.toList


            newSyms.map { newSym =>
              val newSymType = newSym.info.widenDealias
              println(s"specializing ${tree.symbol} for ${newSymType.show}")
              polyDefDef(newSym.asTerm, { tparams => vparams => {

                val treemap: (Tree => Tree) = _ match {
                  case Return(t, from) if from.symbol == tree.symbol => Return(t, ref(newSym))
                  case t: TypeApply =>
                    transformTypeApply(t)
                  case t: Apply =>
                    transformApply(t)
                  case t => t
                }

                val abstractPolyType = tree.symbol.info.widenDealias.asInstanceOf[PolyType]
                val vparamTpes = vparams.flatten.map(_.tpe)
                val typemap = new TypeMap {
                  override def apply(tp: Type): Type = {
                    val t = mapOver(tp)
                      .substDealias(origTParams, tparams)
                      .substParams(abstractPolyType, tparams)
                      .subst(origVParams, vparamTpes)
                    t
                  }
                }

                val typesReplaced = new TreeTypeMap(
                  treeMap = treemap,
                  typeMap = typemap,
                  oldOwners = tree.symbol :: Nil,
                  newOwners = newSym :: Nil
                ).transform(tree.rhs)

                typesReplaced
              }})
            }
          } else Nil
        }
        val specializedTrees = specialize(tree.symbol)
        Thicket(tree :: specializedTrees)
      case _ => tree
    }
  }

  def rewireTree(tree: Tree)(implicit ctx: Context): Tree = {
    assert(tree.isInstanceOf[TypeApply])
    val TypeApply(fun, args) = tree
    if (newSymbolMap.contains(fun.symbol)){
      val availableSpecializations = newSymbolMap(fun.symbol)
      val betterDefs = availableSpecializations.filter {
        case (instantiations, symbol) => {
          instantiations.zip(args).forall {
            case (specTpe, arg) =>
              arg.tpe <:< specTpe
          }}}.toList

      if (betterDefs.length > 1) {
        ctx.debuglog(s"Several specialized variants fit for ${fun.symbol.name} of ${fun.symbol.owner}." +
          s" Defaulting to no specialization.")
        tree
      }

      else if (betterDefs.nonEmpty) {
        val newFunSym = betterDefs.head._2
        ctx.debuglog(s"method ${fun.symbol.name} of ${fun.symbol.owner} rewired to specialized variant")
        val prefix = fun match {
          case Select(pre, name) =>
            pre
          case t @ Ident(_) if t.tpe.isInstanceOf[TermRef] =>
            val tp = t.tpe.asInstanceOf[TermRef]
            if (tp.prefix ne NoPrefix)
              ref(tp.prefix.termSymbol)
            else EmptyTree
          case _ => EmptyTree
        }
        if (prefix ne EmptyTree) prefix.select(newFunSym).appliedToTypeTrees(args)
        else ref(newFunSym).appliedToTypeTrees(args)
      } else tree
    } else tree
  }

  override def transformTypeApply(tree: tpd.TypeApply)(implicit ctx: Context, info: TransformerInfo): Tree = {
    val TypeApply(fun, _) = tree
    if (fun.tpe.widenDealias.isParameterless) rewireTree(tree)
    else tree
  }

  override def transformApply(tree: Apply)(implicit ctx: Context, info: TransformerInfo): Tree = {
    val Apply(fun, args) = tree
    fun match {
      case fun: TypeApply =>
        val typeArgs = fun.args
        val newFun = rewireTree(fun)
        if (fun ne newFun)
          Apply(newFun, args)
        else tree
      case fun : Apply =>
        Apply(transformApply(fun), args)
      case _ => tree
    }
  }
}
