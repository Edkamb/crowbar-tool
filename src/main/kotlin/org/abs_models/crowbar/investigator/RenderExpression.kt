package org.abs_models.crowbar.investigator

import org.abs_models.crowbar.data.Const
import org.abs_models.crowbar.data.DataTypeExpr
import org.abs_models.crowbar.data.Expr
import org.abs_models.crowbar.data.Field
import org.abs_models.crowbar.data.ProgVar
import org.abs_models.frontend.ast.AddAddExp
import org.abs_models.frontend.ast.AndBoolExp
import org.abs_models.frontend.ast.Call
import org.abs_models.frontend.ast.CaseExp
import org.abs_models.frontend.ast.ConstructorPattern
import org.abs_models.frontend.ast.DataConstructorExp
import org.abs_models.frontend.ast.DivMultExp
import org.abs_models.frontend.ast.EqExp
import org.abs_models.frontend.ast.Exp
import org.abs_models.frontend.ast.FieldUse
import org.abs_models.frontend.ast.FloatLiteral
import org.abs_models.frontend.ast.FnApp
import org.abs_models.frontend.ast.GTEQExp
import org.abs_models.frontend.ast.GTExp
import org.abs_models.frontend.ast.GetExp
import org.abs_models.frontend.ast.IfExp
import org.abs_models.frontend.ast.IntLiteral
import org.abs_models.frontend.ast.LTEQExp
import org.abs_models.frontend.ast.LTExp
import org.abs_models.frontend.ast.LiteralPattern
import org.abs_models.frontend.ast.MinusExp
import org.abs_models.frontend.ast.MultMultExp
import org.abs_models.frontend.ast.NegExp
import org.abs_models.frontend.ast.NewExp
import org.abs_models.frontend.ast.NotEqExp
import org.abs_models.frontend.ast.NullExp
import org.abs_models.frontend.ast.OrBoolExp
import org.abs_models.frontend.ast.Pattern
import org.abs_models.frontend.ast.PatternVar
import org.abs_models.frontend.ast.PatternVarUse
import org.abs_models.frontend.ast.StringLiteral
import org.abs_models.frontend.ast.SubAddExp
import org.abs_models.frontend.ast.ThisExp
import org.abs_models.frontend.ast.UnderscorePattern
import org.abs_models.frontend.ast.VarUse

fun renderExpression(expression: Expr, varSubMap: Map<String, String> = mapOf()): String {
    return if (expression.absExp == null)
        renderSimpleCrowbarExpression(expression, varSubMap) // Fallback rendering, required for pattern expressions
    else
        renderAbsExpression(expression.absExp!!, varSubMap)
}

fun renderAbsExpression(e: Exp, m: Map<String, String>): String {
    return when (e) {
        is ThisExp         -> "this"
        is NullExp         -> "null"
        is IntLiteral      -> e.content
        is FloatLiteral    -> e.content
        is StringLiteral   -> "\"${e.content}\""
        is FieldUse        -> "this.${e.name}"
        is VarUse          -> if (m.containsKey(e.name)) m[e.name]!! else e.name
        is GTEQExp         -> "(${renderAbsExpression(e.left, m)} >= ${renderAbsExpression(e.right, m)})"
        is LTEQExp         -> "(${renderAbsExpression(e.left, m)} <= ${renderAbsExpression(e.right, m)})"
        is GTExp           -> "(${renderAbsExpression(e.left, m)} > ${renderAbsExpression(e.right, m)})"
        is LTExp           -> "(${renderAbsExpression(e.left, m)} < ${renderAbsExpression(e.right, m)})"
        is EqExp           -> "(${renderAbsExpression(e.left, m)} == ${renderAbsExpression(e.right, m)})"
        is NotEqExp        -> "(${renderAbsExpression(e.left, m)} != ${renderAbsExpression(e.right, m)})"
        is AddAddExp       -> "(${renderAbsExpression(e.left, m)} + ${renderAbsExpression(e.right, m)})"
        is SubAddExp       -> "(${renderAbsExpression(e.left, m)} - ${renderAbsExpression(e.right, m)})"
        is MultMultExp     -> "(${renderAbsExpression(e.left, m)} * ${renderAbsExpression(e.right, m)})"
        is DivMultExp      -> "(${renderAbsExpression(e.left, m)} / ${renderAbsExpression(e.right, m)})"
        is MinusExp        -> "-${renderAbsExpression(e.operand, m)}"
        is AndBoolExp      -> "(${renderAbsExpression(e.left, m)} && ${renderAbsExpression(e.right, m)})"
        is OrBoolExp       -> "(${renderAbsExpression(e.left, m)} || ${renderAbsExpression(e.right, m)})"
        is GetExp          -> "(${renderAbsExpression(e.pureExp, m)}).get"
        is NegExp          -> "!${renderAbsExpression(e.operand, m)}"
        is NewExp          -> "new ${e.className}(${e.paramList.joinToString(", ") { renderAbsExpression(it, m) }})"
        is Call            -> "${e.methodSig.name}(${e.params.joinToString(", ") { renderAbsExpression(it, m) }})"
        is IfExp           -> "(if ${renderAbsExpression(e.condExp, m)} then ${renderAbsExpression(e.thenExp, m)} else ${renderAbsExpression(e.elseExp, m)})"
        is FnApp           -> "${e.name}(${e.params.joinToString(", ") { renderAbsExpression(it, m) }})"
        is CaseExp         -> {
            val branches = e.branchList.joinToString("\n") {
                "${renderPattern(it.left, m)} => ${renderAbsExpression(it.right, m)}"
            }
            "case ${renderAbsExpression(e.expr, m)} {\n${indent(branches, 1)}\n}"
        }
        is DataConstructorExp -> {
            if (e.params.toList().isEmpty())
                e.dataConstructor!!.name
            else
                "${e.dataConstructor!!.name}(${e.params.joinToString(", ") { renderAbsExpression(it, m) }})"
        }
        else               -> throw Exception("Cannot render ABS Expression: $e")
    }
}

fun renderPattern(p: Pattern, m: Map<String, String>): String {
    return when (p) {
        is LiteralPattern     -> renderAbsExpression(p.literal, m)
        is PatternVar         -> p.`var`.name
        is PatternVarUse      -> if (m.containsKey(p.name)) m[p.name]!! else p.name
        is UnderscorePattern  -> "_"
        is ConstructorPattern ->
            if (p.params.toList().isEmpty())
                p.constructor
            else
                "${p.constructor}(${p.params.joinToString(", ") { renderPattern(it, m) }})"
        else -> throw Exception("Cannot render unknown ABS pattern: $p")
    }
}

fun renderSimpleCrowbarExpression(e: Expr, m: Map<String, String>): String {
    return when (e) {
        is Const           -> e.name
        is ProgVar         -> if (m.containsKey(e.name)) m[e.name]!! else e.name
        is Field           -> "this." + e.name.substring(0, e.name.length - 2)
        is DataTypeExpr    -> if (e.e.isEmpty()) e.name else "${e.name}({${
            e.e.joinToString(", ") {
                renderExpression(
                    it,
                    m
                )
            }
        })"
        else               -> throw Exception("Cannot render complex crowbar Expression: ${e.prettyPrint()}")
    }
}
