package com.wavesplatform.lang.v1.compiler

import cats.data._
import cats.syntax.all._
import com.wavesplatform.lang.ExprCompiler
import com.wavesplatform.lang.ScriptVersion.Versions.V1
import com.wavesplatform.lang.directives.Directive
import com.wavesplatform.lang.v1.FunctionHeader
import com.wavesplatform.lang.v1.FunctionHeader.FunctionHeaderType
import com.wavesplatform.lang.v1.compiler.Terms._
import com.wavesplatform.lang.v1.evaluator.ctx.PredefFunction.FunctionTypeSignature
import com.wavesplatform.lang.v1.parser.BinaryOperation._
import com.wavesplatform.lang.v1.parser.Expressions.PART
import com.wavesplatform.lang.v1.parser.{Expressions, Parser}
import monix.eval.Coeval

import scala.util.Try

class CompilerV1(ctx: CompilerContext) extends ExprCompiler {
  override type V = V1.type
  override val version: V = V1

  override def compile(input: String, directives: List[Directive]): Either[String, version.ExprT] = {
    Parser(input) match {
      case fastparse.core.Parsed.Success(xs, _) =>
        if (xs.size > 1) Left("Too many expressions")
        else if (xs.isEmpty) Left("No expression")
        else
          CompilerV1(ctx, xs.head) match {
            case Left(err)   => Left(err.toString)
            case Right(expr) => Right(expr)
          }
      case f @ fastparse.core.Parsed.Failure(_, _, _) => Left(f.toString)
    }
  }
}

object CompilerV1 {

  type TypeResolutionError      = String
  type CompilationResult[T]     = Either[TypeResolutionError, T]
  private type SetTypeResult[T] = EitherT[Coeval, String, T]

  type ResolvedArgsResult = EitherT[Coeval, String, List[EXPR]]

  private def setType(ctx: CompilerContext, t: SetTypeResult[Expressions.EXPR]): SetTypeResult[EXPR] = t.flatMap {
    case x: Expressions.CONST_LONG       => EitherT.pure(CONST_LONG(x.value))
    case Expressions.CONST_BYTEVECTOR(p) => handlePart(p)(CONST_BYTEVECTOR)
    case Expressions.CONST_STRING(p)     => handlePart(p)(CONST_STRING)
    case Expressions.TRUE                => EitherT.pure(TRUE)
    case Expressions.FALSE               => EitherT.pure(FALSE)
    case Expressions.BINARY_OP(a, op, b) =>
      op match {
        case AND_OP => setType(ctx, EitherT.pure(Expressions.IF(a, b, Expressions.FALSE)))
        case OR_OP  => setType(ctx, EitherT.pure(Expressions.IF(a, Expressions.TRUE, b)))
        case _      => setType(ctx, EitherT.pure(Expressions.FUNCTION_CALL(opsToFunctions(op), List(a, b))))
      }

    case getter: Expressions.GETTER =>
      for {
        field <- EitherT.fromEither[Coeval](getter.field.toEither)
        r <- setType(ctx, EitherT.pure(getter.ref))
          .subflatMap { ref =>
            ref.tpe match {
              case typeRef: TYPEREF =>
                val refTpe = ctx.predefTypes.get(typeRef.name).map(Right(_)).getOrElse(Left(s"Undefined type: ${typeRef.name}"))
                val fieldTpe = refTpe.flatMap { ct =>
                  val fieldTpe = ct.fields.collectFirst {
                    case (fieldName, tpe) if fieldName == field => tpe
                  }

                  fieldTpe.map(Right(_)).getOrElse(Left(s"Undefined field ${typeRef.name}.$field"))
                }

                fieldTpe.right.map(tpe => GETTER(ref = ref, field = field, tpe = tpe))
              case x => Left(s"Can't access to '$field' of a primitive type $x")
            }
          }
      } yield r

    case Expressions.FUNCTION_CALL(name, args) =>
      for {
        name <- EitherT.fromEither[Coeval](name.toEither)
        r <- ctx.functionTypeSignaturesByName(name) match {
          case Nil                   => EitherT.fromEither[Coeval](Left(s"Function '$name' not found"))
          case singleOverload :: Nil => resolvedFuncArguments(ctx, args).subflatMap(matchFuncOverload(name, args, _, singleOverload))
          case many =>
            resolvedFuncArguments(ctx, args).subflatMap { resolvedArgs =>
              val matchedSignatures = many
                .zip(many.map(matchFuncOverload(name, args, resolvedArgs, _)))
                .collect {
                  case (sig, result) if result.isRight => (sig, result)
                }

              matchedSignatures match {
                case Nil                       => Left(s"Can't find a function '$name'(${resolvedArgs.map(_.tpe.typeInfo).mkString(", ")})")
                case (_, oneFuncResult) :: Nil => oneFuncResult
                case manyPairs =>
                  val candidates = manyPairs.map { case (sig, _) => s"'$name'(${sig.args.mkString(", ")})" }
                  Left(s"Can't choose an overloaded function. Candidates: ${candidates.mkString("; ")}")
              }
            }
        }
      } yield r

    case block: Expressions.BLOCK =>
      for {
        letName <- EitherT.fromEither[Coeval](block.let.name.toEither)
        r <- (ctx.varDefs.get(letName), ctx.functionDefs.get(letName)) match {
          case (Some(_), _) => EitherT.leftT[Coeval, EXPR](s"Value '$letName' already defined in the scope")
          case (_, Some(_)) =>
            EitherT.leftT[Coeval, EXPR](s"Value '$letName' can't be defined because function with such name is predefined")
          case (None, None) =>
            setType(ctx, EitherT.pure(block.let.value)).flatMap { exprTpe =>
              val updatedCtx = ctx.copy(varDefs = ctx.varDefs + (letName -> exprTpe.tpe))
              setType(updatedCtx, EitherT.pure(block.body))
                .map { inExpr =>
                  BLOCK(
                    let = LET(letName, exprTpe),
                    body = inExpr,
                    tpe = inExpr.tpe
                  )
                }
            }
        }
      } yield r

    case ifExpr: Expressions.IF =>
      (setType(ctx, EitherT.pure(ifExpr.cond)), setType(ctx, EitherT.pure(ifExpr.ifTrue)), setType(ctx, EitherT.pure(ifExpr.ifFalse))).tupled
        .subflatMap[String, EXPR] {
          case (resolvedCond: EXPR, resolvedIfTrue, resolvedIfFalse) =>
            if (resolvedCond.tpe != BOOLEAN)
              Left(s"IF clause is expected to be BOOLEAN, acutal: ${resolvedCond.tpe}")
            else {
              val ifTrueTpe  = resolvedIfTrue.tpe
              val ifFalseTpe = resolvedIfFalse.tpe
              TypeInferrer.findCommonType(ifTrueTpe, ifFalseTpe) match {
                case Some(tpe) =>
                  Right(
                    IF(
                      cond = resolvedCond,
                      ifTrue = resolvedIfTrue,
                      ifFalse = resolvedIfFalse,
                      tpe = tpe
                    ))
                case None => Left(s"Can't find common type for $ifTrueTpe and $ifFalseTpe")
              }
            }
        }

    case ref: Expressions.REF =>
      EitherT.fromEither {
        ref.key.toEither.flatMap { key =>
          ctx.varDefs
            .get(key)
            .map { tpe =>
              REF(key = key, tpe = tpe)
            }
            .toRight(s"A definition of '${ref.key}' is not found")
        }
      }

    case Expressions.INVALID(message, _) =>
      EitherT.leftT[Coeval, EXPR](message)
  }

  private def resolvedFuncArguments(ctx: CompilerContext, args: List[Expressions.EXPR]): ResolvedArgsResult = {
    import cats.instances.list._
    val r: List[SetTypeResult[EXPR]] = args.map(arg => setType(ctx, EitherT.pure(arg)))(collection.breakOut)
    r.sequence[SetTypeResult, EXPR]
  }

  private def matchFuncOverload(funcName: String,
                                funcArgs: List[Expressions.EXPR],
                                resolvedArgs: List[EXPR],
                                f: FunctionTypeSignature): Either[String, EXPR] = {
    val argTypes   = f.args
    val resultType = f.result
    if (funcArgs.lengthCompare(argTypes.size) != 0)
      Left(s"Function '$funcName' requires ${argTypes.size} arguments, but ${funcArgs.size} are provided")
    else {
      val typedExpressionArgumentsAndTypedPlaceholders: List[(EXPR, TYPEPLACEHOLDER)] = resolvedArgs.zip(argTypes)

      val typePairs = typedExpressionArgumentsAndTypedPlaceholders.map { case (typedExpr, tph) => (typedExpr.tpe, tph) }
      for {
        resolvedTypeParams <- TypeInferrer(typePairs)
        resolvedResultType <- TypeInferrer.inferResultType(resultType, resolvedTypeParams)
      } yield
        FUNCTION_CALL(
          FunctionHeader(funcName, f.args.map(FunctionHeaderType.fromTypePlaceholder)),
          typedExpressionArgumentsAndTypedPlaceholders.map(_._1),
          resolvedResultType
        )
    }
  }

  private def handlePart[T](part: PART[T])(f: T => EXPR): SetTypeResult[EXPR] = part match {
    case PART.VALID(x)            => EitherT.pure(f(x))
    case PART.INVALID(x, message) => EitherT.leftT[Coeval, EXPR](s"$message: $x")
  }

  def apply(c: CompilerContext, expr: Expressions.EXPR): CompilationResult[EXPR] = {
    def result = setType(c, EitherT.pure(expr)).value().left.map { e =>
      s"Typecheck failed: $e"
    }
    Try(result) match {
      case scala.util.Failure(ex)  => Left(ex.toString)
      case scala.util.Success(res) => res
    }
  }
}
