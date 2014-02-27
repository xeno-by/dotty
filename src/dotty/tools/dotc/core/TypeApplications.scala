package dotty.tools.dotc
package core

import Types._
import Contexts._
import Symbols._
import Decorators._
import util.Stats._
import util.common._
import Names._
import StdNames._
import NameOps._
import Flags._
import util.Positions.Position
import collection.mutable

/** A decorator that provides methods for modeling type application */
class TypeApplications(val self: Type) extends AnyVal {

  /** The type parameters of this type are:
   *  For a ClassInfo type, the type parameters of its class.
   *  For a typeref referring to a class, the type parameters of the class.
   *  For a typeref referring to an alias type, the type parameters of the aliased type.
   *  For a typeref referring to an abstract type with a HigherKindedXYZ bound, the
   *  type parameters of the HigherKinded class.
   *  For a refinement type, the type parameters of its parent, unless there's a
   *  refinement with the same name. Inherited by all other type proxies.
   *  For an intersection type A & B, the type parameters of its left operand, A.
   *  Empty list for all other types.
   */
  final def typeParams(implicit ctx: Context): List[TypeSymbol] = /*>|>*/ track("typeParams") /*<|<*/ {
    self match {
      case tp: ClassInfo =>
        tp.cls.typeParams
      case tp: TypeRef =>
        println(s"tparams of $tp")
        val tsym = tp.typeSymbol
        if (tsym.isClass) tsym.typeParams
        else if (tsym.info.isAlias) tp.underlying.typeParams
        else Nil
      case tp: RefinedType =>
        tp.parent.typeParams filterNot (_.name == tp.refinedName)
      case tp: TypeProxy =>
        tp.underlying.typeParams
      case tp: AndType => // ??? needed
        tp.tp1.typeParams
      case _ =>
        Nil
    }
  }

  /** The type parameters of the underlying class.
   *  This is like `typeParams`, except for 2 differences.
   *  First, it does not adjust type parameters in refined types. I.e. type arguments
   *  do not remove corresponding type parameters.
   *  Second, it will return Nil for BoundTypes because we might get a NullPointer exception
   *  on PolyParam#underlying otherwise (demonstrated by showClass test).
   */
  final def safeUnderlyingTypeParams(implicit ctx: Context): List[TypeSymbol] = {
    def ifCompleted(sym: Symbol): Symbol = if (sym.isCompleted) sym else NoSymbol
    self match {
      case tp: ClassInfo =>
        tp.cls.typeParams
      case tp: TypeRef =>
        val tsym = tp.typeSymbol
        if (tsym.isClass) tsym.typeParams
        else if (tsym.isAliasType) tp.underlying.safeUnderlyingTypeParams
        else Nil
      case tp: BoundType =>
        Nil
      case tp: TypeProxy =>
        tp.underlying.safeUnderlyingTypeParams
      case tp: AndType => // ??? needed
        tp.tp1.safeUnderlyingTypeParams
      case _ =>
        Nil
    }
  }

  def uninstantiatedTypeParams(implicit ctx: Context): List[TypeSymbol] =
    typeParams filter (tparam => self.member(tparam.name).symbol == tparam)

  /** Encode the type resulting from applying this type to given arguments */
  final def appliedTo(args: List[Type])(implicit ctx: Context): Type = /*>|>*/ track("appliedTo") /*<|<*/ {

    def classArgs(tp: Type, tparams: List[TypeSymbol], args: List[Type]): Type = args match {
      case arg :: args1 =>
        if (tparams.isEmpty) {
          println(s"applied type mismatch: $self $args, typeParams = $typeParams, tsym = ${self.typeSymbol.debugString}") // !!! DEBUG
          println(s"precomplete decls = ${self.typeSymbol.decls.toList.map(_.denot).mkString("\n  ")}")
        }
        val tparam = tparams.head
        val tp1 = RefinedType(tp, tparam.name, arg.toBounds(tparam))
        classArgs(tp1, tparams.tail, args1)
      case nil => tp
    }

    if (args.isEmpty) self
    else self match {
      case tp: TypeRef =>
        val tsym = tp.symbol
        if (tsym.isAliasType)
          tp.underlying.appliedTo(args)
        else if (tsym.isClass)
          classArgs(tp, tsym.typeParams, args)
        else {
          def bound = tp.info.bounds.hi
          ((tp: Type) /: args.zipWithIndex) { (p, argIdx) =>
            val (arg, idx) = argIdx
            val refinedName = tpnme.higherKindedParamName(idx)
            val refinedVariance =
              if (self.typeSymbol.isCompleting) {
                ctx.warning("encountered F-bounded higher-kinded type parameters; assuming they are invariant")
                0
              }
              else bound.member(refinedName).info.bounds.variance
            RefinedType(p, refinedName, TypeAlias(arg, refinedVariance))
          }
        }
      case tp: TypeProxy =>
        tp.underlying.appliedTo(args)
      case AndType(l, r) =>
        l.appliedTo(args) & r
      case ErrorType =>
        self
    }
  }

  final def appliedTo(arg: Type)(implicit ctx: Context): Type = appliedTo(arg :: Nil)
  final def appliedTo(arg1: Type, arg2: Type)(implicit ctx: Context): Type = appliedTo(arg1 :: arg2 :: Nil)

  /** Turn this type, which is used as an argument for
   *  type parameter `tparam`, into a TypeBounds RHS
   */
  final def toBounds(tparam: Symbol)(implicit ctx: Context): TypeBounds = self match {
    case self: TypeBounds => // this can happen for wildcard args
      self
    case _ =>
      val v = tparam.variance
      if (v > 0 && !(tparam is Local) && !(tparam is ExpandedTypeParam)) TypeBounds.upper(self)
      else if (v < 0 && !(tparam is Local) && !(tparam is ExpandedTypeParam)) TypeBounds.lower(self)
      else TypeAlias(self, v)
  }

  /** The type arguments of the base type instance wrt `base` of this type */
  final def baseTypeArgs(base: Symbol)(implicit ctx: Context): List[Type] =
    if (self derivesFrom base)
      base.typeParams map (param => self.member(param.name).info.argType(param))
    else
      Nil

  /** The first type argument of the base type instance wrt `base` of this type */
  final def firstBaseTypeArg(base: Symbol)(implicit ctx: Context): Type = base.typeParams match {
    case param :: _ if self derivesFrom base =>
      self.member(param.name).info.argType(param)
    case _ =>
      NoType
  }

  /** Translate a type of the form From[T] to To[T], keep other types as they are.
   *  `from` and `to` must be static classes, both with one type parameter, and the same variance.
   */
  def translateParameterized(from: ClassSymbol, to: ClassSymbol)(implicit ctx: Context): Type =
    if (self derivesFrom from)
      RefinedType(to.typeRef, to.typeParams.head.name, self.member(from.typeParams.head.name).info)
    else self

  /** If this is an encoding of a (partially) applied type, return its arguments,
   *  otherwise return Nil
   */
  final def typeArgs(implicit ctx: Context): List[Type] = {
    var tparams: List[TypeSymbol] = null
    def recur(tp: Type, refineCount: Int): mutable.ListBuffer[Type] = tp.stripTypeVar match {
      case tp @ RefinedType(tycon, name) =>
        val buf = recur(tycon, refineCount + 1)
        if (buf == null) null
        else {
          if (tparams == null) tparams = tycon.typeParams
          if (buf.size < tparams.length) {
            val tparam = tparams(buf.size)
            if (name == tparam.name) buf += tp.refinedInfo.argType(tparam)
            else null
          } else null
        }
      case _ =>
        if (refineCount == 0) null
        else new mutable.ListBuffer[Type]
    }
    val buf = recur(self, 0)
    if (buf == null) Nil else buf.toList
  }

  /** The core type without any type arguments.
   *  @param `typeArgs` must be the type arguments of this type.
   */
  final def withoutArgs(typeArgs: List[Type]): Type = typeArgs match {
    case _ :: typeArgs1 =>
      val RefinedType(tycon, _) = self
      tycon.withoutArgs(typeArgs1)
    case nil =>
      self
  }

  /** If this is the image of a type argument to type parameter `tparam`,
   *  recover the type argument, otherwise NoType.
   */
  final def argType(tparam: Symbol)(implicit ctx: Context): Type = self match {
    case TypeBounds(lo, hi) =>
      if (lo eq hi) hi
      else {
        val v = tparam.variance
        if (v > 0 && (lo isRef defn.NothingClass)) hi
        else if (v < 0 && (hi isRef defn.AnyClass)) lo
        else self // it's wildcard type; return its bounds
      }
    case _ =>
      NoType
  }

  /** The element type of a sequence or array */
  def elemType(implicit ctx: Context): Type =
    firstBaseTypeArg(defn.SeqClass) orElse firstBaseTypeArg(defn.ArrayClass)

  /** If this type is of the normalized form Array[...[Array[T]...]
   *  return the number of Array wrappers and T.
   *  Otherwise return 0 and the type itself
   */
  final def splitArray(implicit ctx: Context): (Int, Type) = {
    def recur(n: Int, tp: Type): (Int, Type) = tp.stripTypeVar match {
      case RefinedType(tycon, _) if tycon isRef defn.ArrayClass =>
        tp.typeArgs match {
          case arg :: Nil => recur(n + 1, arg)
          case _ => (n, tp)
        }
      case _ =>
        (n, tp)
    }
    recur(0, self)
  }

  /** Given a type alias
   *
   *      type T[boundSyms] = p.C[targs]
   *
   *  produce its equivalent right hand side RHS that makes no reference to the bound
   *  symbols on the left hand side. I.e. the type alias can be replaced by
   *
   *      type T = RHS
   *
   *  It is required that `C` is a class and that every bound symbol in `boundSyms` appears
   *  as an argument in `targs`. If these requirements are not met an error is
   *  signalled by calling the parameter `error`.
   *
   *  The rewriting replaces bound symbols by references to the
   *  parameters of class C. Example:
   *
   *  Say we have:
   *
   *     class Triple[type T1, type T2, type T3]
   *     type A[X] = Triple[(X, X), X, String]
   *
   *  Then this is rewritable, as `X` appears as second type argument to `Triple`.
   *  Occurrences of `X` are rewritten to `this.T2` and the whole definition becomes:
   *
   *     type A = Triple { type T1 = (this.T2, this.T2); type T3 = String }
   *
   *  If the RHS is an intersection type A & B, we Lambda abstract on A instead and
   *  then recombine with & B.
   */
  def LambdaAbstract(boundSyms: List[Symbol])(error: (String, Position) => Unit)(implicit ctx: Context): Type = self match {
    case AndType(l, r) =>
      AndType(l.LambdaAbstract(boundSyms)(error), r)
    case _ =>
      val cls = self.typeSymbol
      if (!cls.isClass)
        error("right-hand side of parameterized alias type must refer to a class", cls.pos)

      val correspondingParamName: Map[Symbol, TypeName] = {
        for {
          (tparam, targ: TypeRef) <- cls.typeParams zip typeArgs
          if boundSyms contains targ.symbol
        } yield targ.symbol -> tparam.name
      }.toMap

      val correspondingNames = correspondingParamName.values.toSet

      def replacements(rt: RefinedType): List[Type] =
        for (sym <- boundSyms) yield {
          correspondingParamName get sym match {
            case Some(name) =>
              TypeRef(RefinedThis(rt), name)
            case None =>
              error(s"parameter $sym of type alias does not appear as type argument of the aliased $cls", sym.pos)
              defn.AnyType
          }
        }

      def rewrite(tp: Type): Type = tp match {
        case tp @ RefinedType(parent, name: TypeName) =>
          if (correspondingNames contains name) rewrite(parent)
          else RefinedType(
            rewrite(parent),
            name,
            rt => tp.refinedInfo.subst(boundSyms, replacements(rt)))
        case tp =>
          tp
      }

      rewrite(self)
  }

  /** Given the typebounds L..H of higher-kinded abstract type
   *
   *    type T[v_i X_i >: bL_i <: bH_i] >: L <: H
   *
   *  produce its equivalent bounds L'..R that make no reference to the bound
   *  symbols X_i on the left hand side. The idea is to rewrite the declaration to
   *
   *      type T >: L <: HConstr' { type v_i _$hk$i >: bL_i <: bH_i } { HRefinements }
   *
   *  where
   *
   *  - `bL_i` is the lower bound of bound symbol #i under substitution `substBoundSyms`
   *  - `bH_i` is the upper bound of bound symbol #i under substitution `substBoundSyms`
   *  - `substBoundSyms` is the substitution that maps every bound symbol X_i to the
   *    reference `<this>._$hk$i`, where `<this>` is the RefinedThis referring to the
   *    refined type `HConstr' { type v_i _$hk$i >: bL_i <: bH_i }`.
   *    Note: This leads to F_bounded refinements if the higher-kinded type parameter
   *    is also F-bounded. We might need to eliminate F-boundedness by having two staged refinements,
   *    one which intropduces the $hk_i$, the other which introduces its bounds.
   *  - `HConstr` is the type constructor part of H without any refinements that refer to X_i.
   *    It is required that HConstr does not refer to any higher-kinded parameter X_i.
   *  - `HRefinements` are top-level refinements of H where the first (innermost) refinement
   *    does refer to a higher-kinded parameter X_i.
   *
   *  Example:
   *
   *      type T[+X <: F[X]] <: Traversable[X, T]
   *
   *  is rewritten to:
   *
   *      type T <: Traversable { type +_$hk0 <: F[<this>.$_hk$0] } { type Elem = hk$0 } { type Repr = T }
   *
   *  where <this> refers to Traversable { type +_$hk0 <: F[<this>.$_hk$0] }.
   */
  def higherKindedBounds(boundSyms: List[Symbol])(implicit ctx: Context): TypeBounds = {
    val TypeBounds(lo, hi) = self
    val hkParamNames = boundSyms.indices.toList map tpnme.higherKindedParamName
    def substBoundSyms(tp: Type)(rt: RefinedType): Type =
      tp.subst(boundSyms, hkParamNames map (TypeRef(RefinedThis(rt), _)))
    def isBoundRef(tp: Type) = tp match {
      case tp: TypeRef => boundSyms contains tp.symbol
      case _ => false
    }
    def fail(kind: String, bound: Type): Nothing =
      throw new TypeError(s"cannot make sense of F_bounded higher-kinded $kind bound ${bound}")
    if (lo existsPart isBoundRef) fail("lower", lo)
    val hkBound = (hi /: (boundSyms zip hkParamNames)) {(p, sn) =>
      val (boundSym, hkName) = sn
      RefinedType(p, hkName, boundSym.info)
    }
    println(s"hkbound = $hkBound")
    val result = TypeBounds(lo, substBoundSyms(hkBound)(hkBound.asInstanceOf[RefinedType]))
    println(s"hkbounds = ${substBoundSyms(hkBound)(hkBound.asInstanceOf[RefinedType])}")
    println(s"hkbounds of ${self} are ${result}")
    result
  }
}