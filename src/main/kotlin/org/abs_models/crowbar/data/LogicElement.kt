package org.abs_models.crowbar.data


interface LogicElement: Anything {
    fun toSMT(isInForm : Boolean) : String //isInForm is set when a predicate is expected, this is required for the interpretation of Bool Terms as Int Terms
}
interface Formula: LogicElement
interface Term : LogicElement
//interface LogicVariable : Term //for FO

val binaries = listOf(">=","<=","<",">","=","!=","+","-","*","/","&&","||")

data class FormulaAbstractVar(val name : String) : Formula, AbstractVar {
    override fun prettyPrint(): String {
        return name
    }
    override fun toSMT(isInForm : Boolean) : String = name
}

data class Function(val name : String, val params : List<Term> = emptyList()) : Term {
    override fun prettyPrint(): String {
        return prettyPrintFunction(params, name)
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = params.fold(super.iterate(f),{ acc, nx -> acc + nx.iterate(f)})

    override fun toSMT(isInForm : Boolean) : String {
        val back = getSMT(name, isInForm)
        if(params.isEmpty()) {
            if(name.startsWith("-")) return "(- ${name.substring(1)})" //CVC4 requires -1 to be passed as (- 1)
            return name
        }
        val list = params.fold("",{acc,nx -> acc+ " ${nx.toSMT(isInForm)}"})
        return "($back $list)"
    }
}
data class UpdateOnTerm(val update : UpdateElement, val target : Term) : Term {
    override fun prettyPrint(): String {
        return "{"+update.prettyPrint()+"}"+target.prettyPrint()
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + update.iterate(f) + target.iterate(f)
    override fun toSMT(isInForm : Boolean) : String = throw Exception("Updates are not translatable to Z3")
}
data class Impl(val left : Formula, val right : Formula) : Formula {
    override fun prettyPrint(): String {
        return "(${left.prettyPrint()}) -> (${right.prettyPrint()})"
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + left.iterate(f) + right.iterate(f)
    override fun toSMT(isInForm : Boolean) : String = if(isInForm) "(=> ${left.toSMT(isInForm)} ${right.toSMT(isInForm)})" else Or(Not(left),right).toSMT(isInForm)
}
data class And(val left : Formula, val right : Formula) : Formula {
    override fun prettyPrint(): String {
        if(left == True) return right.prettyPrint()
        if(right == True) return left.prettyPrint()
        return "(${left.prettyPrint()}) /\\ (${right.prettyPrint()})"
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + left.iterate(f) + right.iterate(f)
    override fun toSMT(isInForm : Boolean) : String = if(isInForm) "(and ${left.toSMT(isInForm)} ${right.toSMT(isInForm)})" else "(iAnd ${left.toSMT(isInForm)} ${right.toSMT(isInForm)})"
}
data class Or(val left : Formula, val right : Formula) : Formula {
    override fun prettyPrint(): String {
        if(left == False) return right.prettyPrint()
        if(right == False) return left.prettyPrint()
        return "(${left.prettyPrint()}) \\/ (${right.prettyPrint()})"
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + left.iterate(f) + right.iterate(f)
    override fun toSMT(isInForm : Boolean) : String = if(isInForm) "(or ${left.toSMT(isInForm)} ${right.toSMT(isInForm)})" else "(iOr ${left.toSMT(isInForm)} ${right.toSMT(isInForm)})"
}
data class Not(val left : Formula) : Formula {
    override fun prettyPrint(): String {
        return "!"+left.prettyPrint()
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + left.iterate(f)
    override fun toSMT(isInForm : Boolean) : String = if(isInForm) "(not ${left.toSMT(isInForm)})" else "(iNot ${left.toSMT(isInForm)})"
}
data class Predicate(val name : String, val params : List<Term> = emptyList()) : Formula {
    override fun prettyPrint(): String {
        return prettyPrintFunction(params, name)
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = params.fold(super.iterate(f),{ acc, nx -> acc + nx.iterate(f)})
    override fun toSMT(isInForm : Boolean) : String {
        if(params.isEmpty()) return name
        val back = getSMT(name, isInForm)
        val list = params.fold("",{acc,nx -> acc+ " ${nx.toSMT(false)}"})
        return "($back $list)"
    }
}
data class UpdateOnFormula(val update : UpdateElement, val target : Formula) : Formula {
    override fun prettyPrint(): String {
        return "{"+update.prettyPrint()+"}"+target.prettyPrint()
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + update.iterate(f) + target.iterate(f)
    override fun toSMT(isInForm : Boolean) : String = throw Exception("Updates are not translatable to Z3")
}
object True : Formula {
    override fun prettyPrint(): String {
        return "true"
    }
    override fun toSMT(isInForm : Boolean) : String = if(isInForm) "true" else "1"
}
object False : Formula {
    override fun prettyPrint(): String {
        return "false"
    }
    override fun toSMT(isInForm : Boolean) : String = if(isInForm) "false" else "0"
}




object Heap : ProgVar("heap","Heap")
object OldHeap : ProgVar("oldheap","Heap")

fun store(field: Field, value : Term) : Function = Function("store", listOf(Heap, field, value))
fun select(field : Field) : Function = Function("select", listOf(Heap, field))
fun anon(heap : Term) : Function = Function("anon", listOf(heap))
fun poll(term : Term) : Function = Function("poll", listOf(term))
fun readFut(term : Expr) : Expr = SExpr("valueOf", listOf(term))
fun exprToTerm(input : Expr, old : Boolean=false) : Term {
    return when(input){
        is ProgVar -> input
        is Field -> {
            if(old)
                return Function("old", listOf(select(input)))
            return select(input)
        }
        is PollExpr -> poll(exprToTerm(input.e1))
        is Const -> Function(input.name)
        is SExpr -> {
            if(input.op == "old")
                if(input.e.size == 1)
                    Function(input.op, input.e.map { ex -> exprToTerm(ex, true) })
                else
                    throw Exception("Special keyword old must have one argument, actual arguments size:" + input.e.size)
            Function(input.op, input.e.map { ex -> exprToTerm(ex, old) })
        }
        else -> throw Exception("Expression cannot be converted to term: "+input.prettyPrint())
    }
}

//todo: the comparisons with 1 should be removed once the Bool data type is split from Int
fun exprToForm(input : Expr, old : Boolean=false) : Formula {
    if(input is SExpr && input.op == "&&" && input.e.size ==2 ) return And(exprToForm(input.e[0], old), exprToForm(input.e[1], old))
    if(input is SExpr && input.op == "||" && input.e.size ==2 ) return Or(exprToForm(input.e[0], old), exprToForm(input.e[1], old))
    if(input is SExpr && input.op == "->" && input.e.size ==2 ) return Impl(exprToForm(input.e[0], old), exprToForm(input.e[1], old))
    if(input is SExpr && input.op == "!" && input.e.size ==1 ) return Not(exprToForm(input.e[0]))
    if(input is SExpr && input.op == "!=") return Not(exprToForm(SExpr("=",input.e), old))

    if(input is SExpr){
        if(input.op == "old"){
            if(input.e.size == 1) {
                return exprToForm(input.e[0], true)
            }else
                throw Exception("Special keyword old must have one argument, actual arguments size:" + input.e.size)
        }
        return Predicate(input.op, input.e.map { ex -> exprToTerm(ex, old) })
    }
    if(input is Field || input is ProgVar || input is Const)
        return exprToForm(SExpr("=",listOf(input, Const("1"))), old)
    throw Exception("Expression cannot be converted to formula: $input")
}

fun deupdatify(input: LogicElement) : LogicElement {
    return when(input){
        is UpdateOnTerm -> deupdatify(apply(input.update, input.target))
        is UpdateOnFormula -> deupdatify(apply(input.update, input.target))
        is Function -> Function(input.name, input.params.map { p -> deupdatify(p) as Term })
        is Predicate -> Predicate(input.name, input.params.map { p -> deupdatify(p) as Term })
        is Impl -> Impl(deupdatify(input.left) as Formula, deupdatify(input.right) as Formula)
        is And -> And(deupdatify(input.left) as Formula, deupdatify(input.right) as Formula)
        is Or -> Or(deupdatify(input.left) as Formula, deupdatify(input.right) as Formula)
        is Not -> Not(deupdatify(input.left) as Formula)
        else                -> input
    }
}

fun apply(update: UpdateElement, input: LogicElement) : LogicElement {
    return when(update) {
        is EmptyUpdate -> input
        is ElementaryUpdate -> subst(input, update.lhs, update.rhs)
        is ChainUpdate -> apply(update.left, apply(update.right, input))
        else                -> input
    }
}


fun subst(input: LogicElement, map: Map<LogicElement,LogicElement>) : LogicElement {
    if(map.containsKey(input)) return map.getValue(input)
    when(input){
        is EmptyUpdate -> return EmptyUpdate
        is ElementaryUpdate -> return ElementaryUpdate(input.lhs, subst(input.rhs, map) as Term)
        is ChainUpdate -> {
            if(map.keys.any { it is ProgVar && input.left.assigns(it)}) return ChainUpdate(subst(input.left, map) as UpdateElement, input.right)
            return ChainUpdate(subst(input.left, map) as UpdateElement, subst(input.right, map) as UpdateElement)
        }
        is Function -> return Function(input.name, input.params.map { p -> subst(p, map) as Term })
        is Predicate -> return Predicate(input.name, input.params.map { p -> subst(p, map) as Term })
        is Impl -> return Impl(subst(input.left, map) as Formula, subst(input.right, map) as Formula)
        is And -> return And(subst(input.left, map) as Formula, subst(input.right, map) as Formula)
        is Or -> return Or(subst(input.left, map) as Formula, subst(input.right, map) as Formula)
        is Not -> return Not(subst(input.left,map) as Formula)
        is UpdateOnTerm -> {
            if(map.keys.any { it is ProgVar && input.update.assigns(it)}) return UpdateOnTerm(subst(input.update, map) as UpdateElement, input.target)
            return UpdateOnTerm(subst(input.update, map) as UpdateElement, subst(input.target, map) as Term)
        }
        is UpdateOnFormula -> {
            if(map.keys.any { it is ProgVar && input.update.assigns(it)}) return UpdateOnFormula(subst(input.update, map) as UpdateElement, input.target)
            return UpdateOnFormula(subst(input.update, map) as UpdateElement, subst(input.target, map) as Formula)
        }
        else                -> return input
    }
}
fun subst(input: LogicElement, elem : ProgVar, term : Term) : LogicElement = subst(input, mapOf(Pair(elem,term)))


fun valueOfFunc(t : Term) = Function("valueOf", listOf(t))

fun getSMT(name: String, isInForm: Boolean): String{
    if(!isInForm) {
        if (name == "||") return "iOr"
        if (name == "&&") return "iAnd"
        if (name == "!")  return "iNot"
        if (name == "<")  return "iLt"
        if (name == "<=") return "iLeq"
        if (name == ">")  return "iGt"
        if (name == ">=") return "iGeq"
        if (name == "=")  return "iEq"
        if (name == "!=") return "iNeq"
    } else {
        if (name == "||") return "or"
        if (name == "&&") return "and"
        if (name == "!")  return "not"
    }
    return name
}

fun prettyPrintFunction(params: List<Term>, name: String):String{
    if(params.isEmpty()) return name
    if(binaries.contains(name) && params.size == 2) return params[0].prettyPrint() + name + params[1].prettyPrint()
    return name+"("+params.map { p -> p.prettyPrint() }.fold("", { acc, nx -> "$acc,$nx" }).removePrefix(",") + ")"
}
/*
fun subst(input: LogicElement, elem : ProgVar, term : Term) : LogicElement {
    when(input){
        elem                -> return term
        is EmptyUpdate -> return EmptyUpdate
        is ElementaryUpdate -> return ElementaryUpdate(input.lhs, subst(input.rhs, elem, term) as Term)
        is ChainUpdate -> {
            if(input.left.assigns(elem)) return ChainUpdate(subst(input.left, elem, term) as UpdateElement, input.right)
            return ChainUpdate(subst(input.left, elem, term) as UpdateElement, subst(input.right, elem, term) as UpdateElement)
        }
        is Function -> return Function(input.name, input.params.map { p -> subst(p, elem, term) as Term })
        is Predicate -> return Predicate(input.name, input.params.map { p -> subst(p, elem, term) as Term })
        is Impl -> return Impl(subst(input.left, elem, term) as Formula, subst(input.right, elem, term) as Formula)
        is And -> return And(subst(input.left, elem, term) as Formula, subst(input.right, elem, term) as Formula)
        is Or -> return Or(subst(input.left, elem, term) as Formula, subst(input.right, elem, term) as Formula)
        is Not -> return Not(subst(input.left, elem, term) as Formula)
        is UpdateOnTerm -> {
            if(input.update.assigns(elem)) return UpdateOnTerm(subst(input.update, elem, term) as UpdateElement, input.target)
            return UpdateOnTerm(subst(input.update, elem, term) as UpdateElement, subst(input.target, elem, term) as Term)
        }
        is UpdateOnFormula -> {
            if(input.update.assigns(elem)) return UpdateOnFormula(subst(input.update, elem, term) as UpdateElement, input.target)
            return UpdateOnFormula(subst(input.update, elem, term) as UpdateElement, subst(input.target, elem, term) as Formula)
        }
        else                -> return input
    }
}
 */