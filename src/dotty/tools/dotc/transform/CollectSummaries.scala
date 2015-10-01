package dotty.tools.dotc
package transform

import TreeTransforms._
import core.DenotTransformers._
import core.Symbols._
import core.Contexts._
import core.Types._
import core.Flags._
import core.Decorators._
import core.SymDenotations._
import core.StdNames.nme
import core.Names._
import core.NameOps._
import ast.Trees._
import SymUtils._
import dotty.tools.backend.jvm.CollectEntryPoints
import dotty.tools.dotc.FromTasty.TASTYCompilationUnit
import dotty.tools.dotc.ast.tpd
import dotty.tools.dotc.core.Constants.Constant
import dotty.tools.dotc.core.tasty.DottyUnpickler.TreeSectionUnpickler
import dotty.tools.dotc.core.tasty.TastyName.Table
import dotty.tools.dotc.core.tasty.TastyUnpickler.SectionUnpickler
import dotty.tools.dotc.core.{ClassfileLoader, TypeErasure, Flags}
import dotty.tools.dotc.core.Phases.Phase
import dotty.tools.dotc.core.tasty._
import dotty.tools.dotc.transform.Summaries.{ErazedType, CallInfo, MethodSummary}
import dotty.tools.dotc.typer.Mode
import collection.{ mutable, immutable }
import collection.mutable.{ LinkedHashMap, LinkedHashSet, TreeSet }

class CollectSummaries extends MiniPhase { thisTransform =>
  import tpd._
  import Summaries._

  /** the following two members override abstract members in Transform */
  val phaseName: String = "summaries"

  val treeTransform: TreeTransform = new Collect

  private var methodSums = List[MethodSummary]()
  private var noSummaryAvailable = Set[Symbol]()

   /*
  def getSummary(d: Symbol)(implicit ctx: Context): Option[MethodSummary] = {
    if (noSummaryAvailable(d)) None
    else methodSums.find(_.methodDef == d).orElse {
      val nw = retrieveSummary(d)
      methodSums = nw ::: methodSums
      nw.headOption
    }
  }

  private def retrieveSummary(claz: Symbol)(implicit ctx: Context): List[MethodSummary] = {
    val topDenot = claz.topLevelClass.denot.asSymDenotation
    topDenot match {
      case clsd: ClassDenotation =>
        clsd.initInfo match {
          case info: ClassfileLoader =>
            info.load(clsd) match {
              case Some(unpickler: DottyUnpickler) =>
                class STreeUnpickler(reader: TastyReader, tastyName: TastyName.Table) extends TreeUnpickler(reader, tastyName) {

                  roots = Set.empty

                  def getStartReader: Option[TreeReader] = {
                    val st = new TreeReader(reader)
                    st.skipToplevel()(ctx.addMode(Mode.AllowDependentFunctions))

                    while (true) {
                      while (reader.nextByte != TastyFormat.VALDEF && !reader.isAtEnd) st.skipTree()
                      if (reader.isAtEnd) return None // no section here
                      val tag = reader.readByte()
                      val end = reader.readEnd()
                      val name = st.readName()
                      if (name.toString == sectionName + unpickler.unpickler.uuid) return Some(st.forkAt(end))
                      st.skipTree() // skip type
                      st.skipTree() // skip rhs
                    }

                    None
                  }

               }
                class STreeSectionUnpickler extends TreeSectionUnpickler {
                  override def unpickle(reader: TastyReader, tastyName: Table): STreeUnpickler = {
                      new STreeUnpickler(reader, tastyName)
                  }
                }

                val tastySection = unpickler.unpickler.unpickle(new STreeSectionUnpickler).get
                val treeReader = tastySection.asInstanceOf[STreeUnpickler].getStartReader.get

                val unp = new SectionUnpickler[List[MethodSummary]](sectionName) {
                  def unpickle(reader: TastyReader, tastyName: Table): List[MethodSummary] = {
                    def readSymbolRef = {
                      val s = treeReader.readType()
                      s.termSymbol.orElse(s.typeSymbol).orElse(s.classSymbol)
                    }

                    def readType = treeReader.readType()

                    def readMS: MethodSummary = {
                      val sym = readSymbolRef
                      val methodsSz = reader.readInt()

                      val methodsCalled = new mutable.HashMap[Type, List[CallInfo]]()

                      for(_ <- 0 until methodsSz) {
                        val reciever = readType
                        val listSz = reader.readInt()

                        def readCallInfo: CallInfo = {
                          val t = readType
                          val targsSz = reader.readByte()
                          val targs = for(_ <- 0 until targsSz) yield readType
                          val argsSz = reader.readByte()
                          val argsPassed = for(_ <- 0 until argsSz) yield readSymbolRef
                          new CallInfo(t, targs.toList, argsPassed.toList)
                        }

                        val calls = for(_ <- 0 until listSz) yield readCallInfo
                        methodsCalled(reciever) = calls.toList
                      }

                      val accessedModulesSz = reader.readInt()

                      val accesedModules = for(_ <- 0 until accessedModulesSz) yield readSymbolRef

                      val argumentReturned = reader.readByte()

                      val bitsExtected =
                        sym.info.widenDealias.asInstanceOf[MethodType].paramTypess.foldLeft(0)(_+_.size) + 2 // this and thisAccessed
                      val bytesExpected = bitsExtected / 8 + (if(bitsExtected % 8 > 0) 1 else 0)
                      val bytes = reader.readBytes(bytesExpected)
                      val (thisAccessed :: argumentStoredToHeap) = bytes.toList.flatMap{ bt =>
                        List((bt & 1)  != 0, (bt & 2)  != 0, (bt & 4)  != 0, (bt & 8)   != 0,
                             (bt & 16) != 0, (bt & 32) != 0, (bt & 64) != 0, (bt & 128) != 0)
                      }

                      new MethodSummary(sym, thisAccessed, methodsCalled, accesedModules.toList, argumentReturned.toByte, argumentStoredToHeap.take(bitsExtected - 1))
                    }

                    val version = reader.readInt()

                    val methodsSz = reader.readInt()

                    val methods = for(_ <- 0 until methodsSz) yield readMS

                    methods.toList
                  }
                }
                unpickler.unpickler.unpickle(unp).getOrElse(Nil)
              case _ => Nil
            }
        }
    }
  }  */

  def methodSummaries = methodSums

  class Collect extends TreeTransform {
    def phase = thisTransform

    var methodSumarries = List[MethodSummary]()
    var methodSummaryStack = mutable.Stack[MethodSummary]()
    var curMethodSummary: MethodSummary = null

    override def prepareForUnit(tree: tpd.Tree)(implicit ctx: Context): TreeTransform = {
      if (ctx.compilationUnit.isInstanceOf[TASTYCompilationUnit])
        NoTransform // will retrieve them lazily
      else this
    }


    override def prepareForDefDef(tree: tpd.DefDef)(implicit ctx: Context): TreeTransform = {
      val sym = tree.symbol
      if(!(sym is Flags.Label)) {
        methodSummaryStack.push(curMethodSummary)
        val args = tree.vparamss.flatten.map(_.symbol) // outer param for constructors
        curMethodSummary = new MethodSummary(sym,
          false,
          mutable.Map.empty,
          Nil,
          -1,
          (0 to args.length).map(_ => true).toList
        )
      }
      this
    }


    override def prepareForValDef(tree: tpd.ValDef)(implicit ctx: Context): TreeTransform = {
      val sym = tree.symbol
      if (sym.exists && ((sym.is(Flags.Lazy) &&  (sym.owner.is(Package) || sym.owner.isClass)) ||  //lazy vals and modules
        sym.owner.name.startsWith(nme.LOCALDUMMY_PREFIX) || // blocks inside constructor
        sym.owner.isClass)) { // fields
        // owner is a template
        methodSummaryStack.push(curMethodSummary)
        curMethodSummary = new MethodSummary(sym,
          false,
          mutable.Map.empty,
          Nil,
          -1,
          List(true)
        )
      }
      this
    }



    override def prepareForTemplate(tree: tpd.Template)(implicit ctx: Context): TreeTransform = {
      val sym = tree.symbol
      if(!(sym is Flags.Label)) {
        methodSummaryStack.push(curMethodSummary)
        curMethodSummary = new MethodSummary(sym,
          false,
          mutable.Map.empty,
          Nil,
          -1,
          List(true)
        )
      }
      this
    }


    override def transformTemplate(tree: tpd.Template)(implicit ctx: Context, info: TransformerInfo): tpd.Tree = {
      val sym = tree.symbol
      if(!(sym is Flags.Label)) {
        assert(curMethodSummary.methodDef eq tree.symbol)
        methodSumarries = curMethodSummary :: methodSumarries
        curMethodSummary = methodSummaryStack.pop()
      }
      tree
    }

    override def transformDefDef(tree: tpd.DefDef)(implicit ctx: Context, info: TransformerInfo): tpd.Tree = {
      if (tree.name.toString.contains("Iterable"))
        println("hoo")
      if(!(tree.symbol is Flags.Label)) {
        assert(curMethodSummary.methodDef eq tree.symbol)
        methodSumarries = curMethodSummary :: methodSumarries
        curMethodSummary = methodSummaryStack.pop()
      }
      tree
    }

    override def transformValDef(tree: tpd.ValDef)(implicit ctx: Context, info: TransformerInfo): tpd.Tree = {
      val sym = tree.symbol
      if(sym.exists && ((sym.is(Flags.Lazy) &&  (sym.owner.is(Package) || sym.owner.isClass)) ||  //lazy vals and modules
        sym.owner.name.startsWith(nme.LOCALDUMMY_PREFIX) || // blocks inside constructor
        sym.owner.isClass)) { // fields
        assert(curMethodSummary.methodDef eq tree.symbol)

        methodSumarries = curMethodSummary :: methodSumarries
        curMethodSummary = methodSummaryStack.pop()
      }
      tree
    }

    override def transformTypeDef(tree: tpd.TypeDef)(implicit ctx: Context, info: TransformerInfo): tpd.Tree = {
      val sym = tree.symbol
      if(sym.isClass) {
        val isEntryPoint = CollectEntryPoints.isJavaEntryPoint(sym)
        /*summaries = ClassSummary(sym.asClass,
          methodSumarries
        ) :: summaries
        methodSumarries = Nil*/
      }
      tree
    }

    def registerModule(sym: Symbol)(implicit ctx: Context): Unit = {
      if((curMethodSummary ne null) && (sym is Flags.ModuleVal)) {
        curMethodSummary.accessedModules = sym :: curMethodSummary.accessedModules
        registerModule(sym.owner)
      }
      val res = sym.info.finalResultType.termSymbol
      if ((curMethodSummary ne null) && (res is Flags.ModuleVal)) {
        curMethodSummary.accessedModules = res :: curMethodSummary.accessedModules
        registerModule(res.owner)
      }

    }

    def registerCall(tree: Tree)(implicit ctx: Context): Unit = {

      def symbolOf(t: Tree) = {
        val s = t.symbol.orElse(t.tpe.classSymbol).orElse(TypeErasure.erasure(t.tpe).classSymbol)
        assert(s.exists)
        s
      }

      def receiverArgumentsAndSymbol(t: Tree, accArgs: List[List[Tree]] = Nil, accT: List[Tree] = Nil):
      (Tree, Tree, List[List[Tree]], List[Tree], Type) = t match {
        case Block(stats, expr) => receiverArgumentsAndSymbol(expr, accArgs, accT)
        case TypeApply(fun, targs) if fun.symbol eq t.symbol => receiverArgumentsAndSymbol(fun, accArgs, targs)
        case Apply(fn, args) if fn.symbol == t.symbol => receiverArgumentsAndSymbol(fn, args :: accArgs, accT)
        case Select(qual, _) =>
          (qual, t, accArgs, accT, t.tpe)
        case x: This => (x, x, accArgs, accT, x.tpe)
        case x => (x, x, accArgs, accT, x.tpe)
      }
      val widenedTp = tree.tpe.widen
      if ((widenedTp.isInstanceOf[MethodicType]) && (!tree.symbol.exists || tree.symbol.info.isInstanceOf[MethodicType])) return;
      val (reciever, call, arguments, typeArguments, method) = receiverArgumentsAndSymbol(tree)

      val storedReciever = reciever.tpe

      assert(storedReciever.exists)

      val args: List[Type] = arguments.flatten.map(x =>  x match {
        case Select(New(tp),_) => new PreciseType(tp.tpe)
        case Apply(Select(New(tp), _), args) => new PreciseType(tp.tpe)
        case Apply(TypeApply(Select(New(tp), _), targs), args) => new PreciseType(tp.tpe)
        case _ =>
          x.tpe match {
            case _ if x.isInstanceOf[NamedArg] => ref(symbolOf(x.asInstanceOf[NamedArg].arg)).tpe
            case _ => x.tpe
      }})

      curMethodSummary.methodsCalled(storedReciever) = CallInfo(method, typeArguments.map(_.tpe), args) :: curMethodSummary.methodsCalled.getOrElse(storedReciever, Nil)
    }

    override def transformIdent(tree: tpd.Ident)(implicit ctx: Context, info: TransformerInfo): tpd.Tree = {
      if (!tree.symbol.is(Flags.Package)) {
        registerModule(tree.symbol)
      }
      val select = tree.tpe match {
        case TermRef(prefix: TermRef, name) =>
          Some(tpd.ref(prefix).select(tree.symbol))
        case TermRef(prefix: ThisType, name) =>
          Some(tpd.This(prefix.cls).select(tree.symbol))
        case TermRef(NoPrefix, name) =>
          if (tree.symbol is Flags.Method) Some(This(tree.symbol.topLevelClass.asClass).select(tree.symbol)) // workaround #342 todo: remove after fixed
          else None
        case _ => None
      }

      select.map(transformSelect)

      tree
    }

    override def transformSelect(tree: tpd.Select)(implicit ctx: Context, info: TransformerInfo): tpd.Tree = {
      if (!tree.symbol.is(Flags.Package)) {
        registerModule(tree.symbol)
        registerCall(tree)
      }
      // handle nullary methods
      tree
    }

    override def transformThis(tree: tpd.This)(implicit ctx: Context, info: TransformerInfo): tpd.Tree = {
      curMethodSummary.thisAccessed = true
      tree
    }

    override def transformApply(tree: tpd.Apply)(implicit ctx: Context, info: TransformerInfo): tpd.Tree = {
      registerCall(tree)
      tree
    }

    override def transformTypeApply(tree: tpd.TypeApply)(implicit ctx: Context, info: TransformerInfo): tpd.Tree = {
      registerCall(tree)
      tree
    }

    override def transformUnit(tree: tpd.Tree)(implicit ctx: Context, info: TransformerInfo): tpd.Tree = {

      //println("hoho")
      methodSums = methodSumarries

      /*

      for { cls <- ctx.compilationUnit.picklers.keySet} {
        def serializeCS(methods: List[MethodSummary], pickler: TastyPickler): Unit = {
          val buf = new TastyBuffer(5000)
          val treePickl = pickler.treePkl
          val anchorTree = tpd.SyntheticValDef((sectionName + pickler.uuid.toString).toTermName, Literal(Constant(sectionName)))

          treePickl.preRegister(anchorTree)
          treePickl.pickle(anchorTree :: Nil)

          pickler.newSection(sectionName, buf)
          val start = treePickl.buf.currentAddr
          buf.writeInt(version)//1

          def writeSymbolRef(sym: Symbol) = {
            treePickl.pickleType(ref(sym).tpe)
          }
          def writeTypeRef(tp: Type) = {
            treePickl.pickleType(tp)
          }


          def serializeMS(ms: MethodSummary) = {
            writeSymbolRef(ms.methodDef) //26

            buf.writeInt(ms.methodsCalled.size) //29
            for ((reciever, methods) <- ms.methodsCalled) {
              writeTypeRef(reciever) //36
              buf.writeInt(methods.size)

              def writeCallInfo(c: CallInfo): Unit = {
                writeTypeRef(c.call)
                buf.writeByte(c.targs.size)
                c.targs foreach writeTypeRef

                buf.writeByte(c.argumentsPassed.size)
                c.argumentsPassed foreach writeSymbolRef
              }
              methods foreach writeCallInfo
            }

            buf.writeInt(ms.accessedModules.length)
            ms.accessedModules foreach writeSymbolRef

            buf.writeByte(ms.argumentReturned)
            (ms.thisAccessed :: ms.argumentStoredToHeap).grouped(8).map(_.foldRight(0) { (bl: Boolean, acc: Int) =>
              (if (bl) 1 else 0) + 2 * acc
            }) foreach (buf.writeByte)
          }

          buf.writeInt(methods.length) // 19

          methods foreach serializeMS

          val sz = treePickl.buf.currentAddr.index - start.index

          ctx.debuglog("new section for " + cls + " size:"
            + sz + "/" + buf.currentAddr + "increased by " + (sz + buf.length) * 1.0 / start.index)
          // note: this is huge overestimate. This section contains a lot of refferences to already existing symbols and types
          // and will be compressed during bytecode generation by TreePickler.compactify
        }

          val s = methodSumarries.filter(_.methodDef.topLevelClass == cls)

          // println(s)

          serializeCS(s, ctx.compilationUnit.picklers(cls))
      } */



      tree
    }
  }
}

object Summaries {
  val version: Int = 1
  val sectionName = "$ummaries"

   class PreciseType(u: Type) extends UncachedProxyType {
     def underlying(implicit ctx: Context): Type = u
   }

   class ErazedType extends UncachedProxyType {
     /** The type to which this proxy forwards operations. */
     def underlying(implicit ctx: Context): Type = ctx.definitions.AnyType
   }


  case class CallInfo(call: Type, // this is type of method, that includes full type of reciever, eg: TermRef(reciever, Method)
                       targs: List[Type],
                       argumentsPassed: List[Type]
                       )

  case class MethodSummary(methodDef: Symbol,
                           var thisAccessed: Boolean,
                           methodsCalled: mutable.Map[Type, List[CallInfo]],
                           var accessedModules: List[Symbol],
                           argumentReturned: Byte, // -1 if not known
                           var argumentStoredToHeap: List[Boolean] // not currently collected
                          )

  def simplifiedClassOf(t: Type)(implicit ctx: Context) = {
    val s = t.widenDealias.finalResultType.classSymbol.orElse(TypeErasure.erasure(t.widenDealias.finalResultType).classSymbol)
    assert(s.exists)
    s
  }
}

class BuildCallGraph extends Phase {
  import tpd._
  def phaseName: String = "callGraph"
  def isEntryPoint(s: Symbol)(implicit ctx: Context): Boolean = {
    (s.name eq nme.main) /* for speed */  && s.is(Method) && CollectEntryPoints.isJavaMainMethod(s)
  }

  class Worklist[A] {
    val reachableItems = mutable.Set[A]()
    var newItems = immutable.Set[A]()

    def +=(elem: A) = {
      // No new elements are accepted if they've already been reachable before
      if (!reachableItems(elem)) {
        newItems += elem
        reachableItems += elem
      }
    }

    /**
     * Add new items to the worklist. It also adds the items to the reachable set.
     */
    def ++=(xs: TraversableOnce[A]): this.type = { xs.seq foreach +=; this }

    /**
     * Clear the new items
     */
    def clear = {
      newItems = immutable.Set[A]()
    }

    /**
     * Do we have new items to process?
     */
    def nonEmpty = {
      newItems.nonEmpty
    }

    /**
     * How many new items do we have?
     */
    def size = {
      newItems.size
    }
  }

  final val AnalyseOrig = 1
  final val AnalyseTypes = 2
  final val AnalyseArgs = 3


  def buildCallGraph(mode: Int, specLimit: Int)(implicit ctx: Context) = {
    val collectedSummaries = ctx.summariesPhase.asInstanceOf[CollectSummaries].methodSummaries.map(x => (x.methodDef, x)).toMap
    val reachableMethods = new Worklist[CallInfo]()
    val reachableTypes = new Worklist[Type]()
    val outerMethod = mutable.Set[Symbol]()
    // val callSites = new Worklist[CallInfo]()

    def pushEntryPoint(s: Symbol) = {
      val tpe = ref(s).tpe
      val targs = tpe.widen match {
        case t: PolyType => t.paramNames.size
        case _ => 0
      }
      val call = new CallInfo(tpe, (0 until targs).map(x => new ErazedType()).toList, ctx.definitions.ArrayType(ctx.definitions.StringType) :: Nil)
      reachableMethods += call
      reachableTypes += ref(s.owner).tpe
    }

    collectedSummaries.values.foreach(x => if(isEntryPoint(x.methodDef)) pushEntryPoint(x.methodDef))
    println(s"\t Found ${reachableMethods.size} entry points")


    def registerParentModules(tp: Type): Unit = {
      var tp1 = tp
      while ((tp1 ne NoType) && (tp1 ne NoPrefix)) {
        if (tp1.widen ne tp1) registerParentModules(tp1.widen)
        if (tp1.dealias ne tp1) registerParentModules(tp1.dealias)
        if (tp1.termSymbol.is(Flags.Module)) {
          reachableTypes += ref(tp1.termSymbol).tpe
        }
        if (tp1.typeSymbol.is(Flags.Module)) {
          reachableTypes += ref(tp1.typeSymbol).tpe
        }
        tp1 = tp1.normalizedPrefix
      }
    }

    def instantiateCallSite(caller: CallInfo, rec: Type, callee: CallInfo, types: Traversable[Type]): Traversable[CallInfo] = {

      val receiver = callee.call.normalizedPrefix
      registerParentModules(receiver)

      val callSymbol = callee.call.termSymbol

      // if typearg of callee is a typeparam of caller, propagate typearg from caller to callee
      lazy val targs = callee.targs map {
        case t: TypeVar if mode >= AnalyseTypes && t.stripTypeVar.typeSymbol.owner == caller.call.termSymbol =>
          val abstractSym = callee.targs.head.stripTypeVar.typeSymbol
          val id = caller.call.termSymbol.info.asInstanceOf[PolyType].paramNames.indexOf(abstractSym.name)
          caller.targs(id).stripTypeVar
        case t => t
      }
      // if arg of callee is a param of caller, propagate arg fro caller to callee
      val args = callee.argumentsPassed.map {
        case x if x.isRepeatedParam =>
          val t = x.translateParameterized(defn.RepeatedParamClass, ctx.requiredClass("scala.collection.mutable.WrappedArray"))
          reachableTypes += t
          t
        case x if mode < AnalyseArgs =>
          ref(Summaries.simplifiedClassOf(x)).tpe
        case x: TermRef if x.symbol.is(Param) && x.symbol.owner == caller.call.termSymbol =>
          val id = caller.call.termSymbol.info.paramNamess.flatten.indexWhere(_ == x.symbol.name)
          caller.argumentsPassed(id)
        case x => x
      }
      def filterTypes(tp1: Type, tp2: Type): Boolean = {
        if (mode >= AnalyseTypes) tp1 <:< tp2
        else {
          val tp1w = tp1.widenDealias
          val tp2w = tp2.widenDealias
          tp1w.derivesFrom(tp2w.classSymbol)
        }
      }
      def dispatchCalls(recieverType: Type): Traversable[CallInfo] = {
        for (tp <- types
             if filterTypes(tp, recieverType);
             alt <-  tp.member(callSymbol.name).altsWith(p => p.matches(callSymbol.asSeenFrom(tp)))
             if alt.exists
        )
          yield CallInfo(tp.select(alt.symbol), targs, args)
      }

      receiver match {
        case t if callSymbol.isPrimaryConstructor =>
          reachableTypes += receiver
          CallInfo(callee.call, targs, args) :: Nil

          // super call in a class (know target precisely)
        case st: SuperType =>
          val thisTpe = st.thistpe
          val superTpe = st.supertpe
          val targetClass = st.supertpe.baseClasses.find(clz =>
            clz.info.decl(callSymbol.name).altsWith(p => p.signature == callSymbol.signature).nonEmpty
          )
          val targetMethod = targetClass.get.info.member(callSymbol.name).altsWith(p => p.signature == callSymbol.signature).head

          CallInfo(thisTpe.select(targetMethod.symbol), targs, args) :: Nil

          // super call in a trait
        case t if callSymbol.is(Flags.SuperAccessor) =>
          val prev = t.classSymbol
          types.flatMap {
            x =>
              val s = x.baseClasses.dropWhile(_ != prev)
              if (s.nonEmpty) {
                val parent = s.find(x => x.info.decl(callSymbol.name).altsWith(x => x.signature == callSymbol.signature).nonEmpty)
                parent match {
                  case Some(p) if p.exists =>
                    val method = p.info.decl(callSymbol.name).altsWith(x => x.signature == callSymbol.signature)
                    CallInfo(t.select(method.head.symbol), targs, args) :: Nil
                  case _ => Nil
                }
              } else Nil
          }

        case thisType: ThisType =>
          dispatchCalls(thisType.tref)
        case t =>
          dispatchCalls(t.widenDealias)
      }
    }

    def processCallSites(callSites: immutable.Set[CallInfo], instantiatedTypes: immutable.Set[Type]) = {

      for (method <- callSites) {
        // Find new call sites



        reachableMethods ++= {
          val summary = collectedSummaries.get(method.call.termSymbol)

          if (summary.isDefined) {

            reachableTypes ++= summary.get.accessedModules.map(x => ref(x).tpe)

            summary.get.methodsCalled.flatMap { x =>
              val reciever = x._1
              x._2.flatMap(callSite => instantiateCallSite(method, reciever, callSite, instantiatedTypes))
            }
          } else {
            outerMethod += method.call.termSymbol
            Nil
          }
        }

      }

    }


    while(reachableMethods.nonEmpty || reachableTypes.nonEmpty) {
      reachableTypes.clear

      val iteration = reachableMethods.newItems.toSet
      reachableMethods.clear
      processCallSites(iteration.toSet, reachableTypes.reachableItems.toSet)

      if (reachableTypes.nonEmpty) {
        println(s"\t Found ${reachableTypes.size} new instantiated types")

        processCallSites(reachableMethods.reachableItems.toSet, reachableTypes.newItems.toSet)
      }
      if (!(reachableMethods.nonEmpty || reachableTypes.nonEmpty))
        processCallSites(reachableMethods.reachableItems.toSet, reachableTypes.reachableItems.toSet)
      println(s"\t Found ${reachableMethods.size} new call sites: ${reachableMethods.newItems.toString().take(60)}")

    }

    val reachableClasses = reachableMethods.reachableItems.map(_.call.termSymbol.owner.info.widen.classSymbol)
    val reachableDefs = reachableMethods.reachableItems.map(_.call.termSymbol)


    val reachableSpecs: mutable.Set[(Symbol, List[Type])] = reachableMethods.reachableItems.flatMap { x =>
       val clas = x.call.termSymbol.owner.info.widen.classSymbol
       val meth = x.call.termSymbol
      if (mode >= AnalyseTypes) (meth, x.call.termSymbol.owner.info.baseArgInfos(clas)) :: Nil
      else {
        val clazSpecializationsCount =
           if (clas.primaryConstructor.info.widenDealias.isInstanceOf[PolyType]) specLimit
           else 1
        val methodSpecializationsCount =
           if (meth.info.widenDealias.isInstanceOf[PolyType]) specLimit
           else 1
        println(s"specializing $clas $meth for $clazSpecializationsCount * $methodSpecializationsCount")
        (0 until clazSpecializationsCount*methodSpecializationsCount).map(x => (meth, ConstantType(Constant(x)):: Nil)).toList

      }
    }



    println(s"\t Found: ${reachableClasses.size} reachable classes, ${reachableDefs.size} reachable methods, ${reachableSpecs.size} specializations")
    println(s"\t Found ${outerMethod.size} not defined calls: ${outerMethod.map(_.showFullName)}")
  }

  var runOnce = true
  def run(implicit ctx: Context): Unit = {
    if (runOnce) {
      val specLimit = 15
      println(s"\n\t\t\tOriginal analisys")
      buildCallGraph(AnalyseOrig, specLimit)

      println(s"\n\t\t\tType flow analisys")
      buildCallGraph(AnalyseTypes, specLimit)

      println(s"\n\t\t\tType & Arg flow analisys")
      buildCallGraph(AnalyseArgs, specLimit)

    }
    runOnce = false
  }
}
