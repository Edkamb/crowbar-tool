package org.abs_models.crowbar.types

import org.abs_models.crowbar.data.*
import org.abs_models.crowbar.data.AssignStmt
import org.abs_models.crowbar.data.AwaitStmt
import org.abs_models.crowbar.data.Function
import org.abs_models.crowbar.data.IfStmt
import org.abs_models.crowbar.data.ReturnStmt
import org.abs_models.crowbar.data.SkipStmt
import org.abs_models.crowbar.data.Stmt
import org.abs_models.crowbar.data.WhileStmt
import org.abs_models.crowbar.interfaces.translateABSExpToSymExpr
import org.abs_models.crowbar.interfaces.translateABSStmtToSymStmt
import org.abs_models.crowbar.main.*
import org.abs_models.crowbar.rule.FreshGenerator
import org.abs_models.crowbar.rule.MatchCondition
import org.abs_models.crowbar.rule.Rule
import org.abs_models.crowbar.tree.*
import org.abs_models.frontend.ast.*
import org.abs_models.frontend.typechecker.DataTypeType
import org.abs_models.frontend.typechecker.Type
import org.abs_models.frontend.typechecker.UnknownType
import kotlin.system.exitProcess


val intFunction = setOf("+","-","*","/")
val booleanFunction = setOf(">=","<=","<",">","=","!=",">=","<=","<",">","&&","||", "true", "false")

//Declaration
interface PostInvType : DeductType{
    companion object : PostInvType
    override fun extractMethodNode(classDecl: ClassDecl, name : String, repos: Repository) : SymbolicNode {
        val mDecl = classDecl.methods.firstOrNull { it.methodSig.name == name }
        if (mDecl == null) {
            System.err.println("method not found: ${classDecl.qualifiedName}.${name}")
            exitProcess(-1)
        }

        output("Crowbar  : loading specification....")
        val symb: SymbolicState?
        val objInv: Formula?
        val metpost: Formula?
        val metpre: Formula?
        val roles: Formula?
        val body: Stmt?
        var overlapsSet : String? = null
        var succeedsSet : String? = null
        val hasPre = hasHeapPre(mDecl)
        try {
            objInv = extractSpec(classDecl, "ObjInv", UnknownType.INSTANCE)
            metpost = extractSpec(mDecl, "Ensures", mDecl.type)
            metpre = extractInheritedSpec(mDecl.methodSig, "Requires")
            body = getNormalizedStatement(mDecl.block)
            roles = extractRoleSpec(classDecl)
            if(hasPre) {
                overlapsSet = extractContextSet(mDecl, "Overlaps")
                succeedsSet = extractContextSet(mDecl, "Succeeds")
            }
        } catch (e: Exception) {
            e.printStackTrace()
            System.err.println("error during translation, aborting")
            exitProcess(-1)
        }
        output("Crowbar-v: method post-condition: ${metpost.prettyPrint()}", Verbosity.V)
        output("Crowbar-v: object invariant: ${objInv.prettyPrint()}",Verbosity.V)
        val updateOldHeap = ChainUpdate(ElementaryUpdate(LastHeap,Heap), ElementaryUpdate(OldHeap, Heap))
        symb = SymbolicState(And(And(objInv,metpre),roles), updateOldHeap, Modality(body, PostInvariantPair(metpost, objInv)))
        if(hasPre && (overlapsSet == null || succeedsSet == null)){
            output("Crowbar: Method ${mDecl.methodSig.name} has a heap precondition but does not fully specify its context.")
            val full = classDecl.allMethodSigs.joinToString(",") { it.name }
            if(overlapsSet == null) overlapsSet = full
            if(succeedsSet == null) succeedsSet = full
        }
        return SymbolicNode(symb, if (hasPre) listOf(SymbolicNode(symb, emptyList()),
                                                     StaticNode("Overlaps ${classDecl.moduleName()}.${classDecl.name}.${mDecl.methodSig.name} {$overlapsSet}"),
                                                     StaticNode("Succeeds ${classDecl.moduleName()}.${classDecl.name}.${mDecl.methodSig.name} {$succeedsSet}"))
                                  else emptyList())
    }

    fun hasHeapPre(mDecl: MethodImpl) : Boolean{
        for (annotation in mDecl.nodeAnnotations) {
            if (!annotation.type.toString().endsWith(".Spec") || annotation.value !is DataConstructorExp) continue
            val annotated = annotation.value as DataConstructorExp
            if (annotated.constructor == "Requires") return true
        }
        return false
    }

    fun extractContextSet(mDecl: MethodImpl, expectedSpec: String): String? {

        for (annotation in mDecl.nodeAnnotations) {
            if (!annotation.type.toString().endsWith(".Spec")) continue
            if (annotation.value !is DataConstructorExp) {
                throw Exception("Could not extract any specification from $mDecl because of the expected value")
            }
            val annotated = annotation.value as DataConstructorExp
            if (annotated.constructor != expectedSpec) continue
            val content = annotated.getParam(0) as Exp
            if(content !is FnApp ||
               content.name != "list" ||
               content.getParam(0) !is ListLiteral ||
               (content.getParam(0) as ListLiteral).pureExpList.any { it !is StringLiteral })
                throw Exception("Could not extract context set $expectedSpec from ${mDecl.methodSig.name}: set must be declared using list[\"str\",...]")
            return (content.getParam(0) as ListLiteral).pureExpList.joinToString(",") { (it as StringLiteral).content }
        }
        return null
    }

    override fun extractInitialNode(classDecl: ClassDecl) : SymbolicNode {

        var body = getNormalizedStatement(classDecl.initBlock)
        for (fieldDecl in classDecl.fields){
            if(fieldDecl.hasInitExp()){
                val nextBody = AssignStmt(Field(fieldDecl.name+"_f", fieldDecl.type),
                        translateABSExpToSymExpr(fieldDecl.initExp, UnknownType.INSTANCE))
                body = SeqStmt(nextBody,body)
            }
        }

        output("Crowbar  : loading specification....")
        val objInv: Formula?
        val objPre: Formula?
        try {
            objInv = extractSpec(classDecl, "ObjInv", UnknownType.INSTANCE)
            objPre = extractSpec(classDecl, "Requires",UnknownType.INSTANCE)
        } catch (e: Exception) {
            e.printStackTrace()
            System.err.println("error during translation, aborting")
            exitProcess(-1)
        }
        if (verbosity >= Verbosity.V) {
            output("Crowbar-v: object precondition: ${objPre.prettyPrint()}")
            output("Crowbar-v: object invariant: ${objInv.prettyPrint()}")
        }
        val symb = SymbolicState(objPre, EmptyUpdate, Modality(body, PostInvariantPair(True, objInv)))
        return SymbolicNode(symb, emptyList())
    }

    override fun exctractMainNode(model: Model) : SymbolicNode {

        if(!model.hasMainBlock()){
            System.err.println("model has no main block!")
            exitProcess(-1)
        }

        val v = appendStmt(translateABSStmtToSymStmt(model.mainBlock), SkipStmt)
        return SymbolicNode(SymbolicState(True, EmptyUpdate, Modality(v, PostInvariantPair(True, True))), emptyList())
    }

    override fun exctractFunctionNode(fDecl: FunctionDecl): SymbolicNode {
        val symb: SymbolicState?
        val funpost: Formula?
        val funpre: Formula?
        var body: Stmt? = null
        try {
            funpre = extractSpec(fDecl, "Requires", fDecl.type)
            funpost = extractSpec(fDecl, "Ensures", fDecl.type)
            val fDef = fDecl.functionDef
            if(fDef is BuiltinFunctionDef){
                throw Exception("error during translation, cannot handle builtin yet")
            }else if(fDef is ExpFunctionDef){
                body = ReturnStmt(translateABSExpToSymExpr(fDef.rhs, fDecl.type))
            }
        }catch (e: Exception) {
            e.printStackTrace()
            System.err.println("error during translation, aborting")
            throw e
        }
        if(body != null) {
            symb = SymbolicState(funpre, EmptyUpdate, Modality(body, PostInvariantPair(funpost, True)))
            return SymbolicNode(symb, emptyList())
        }else{
            throw Exception("error during translation of function contract")
        }
    }
}

data class PostInvAbstractVar(val name : String) : PostInvType, AbstractVar{
    override fun prettyPrint(): String {
        return name
    }
}

data class PostInvariantPair(val post : Formula, val objInvariant : Formula) : PostInvType {
    override fun prettyPrint(): String {
        return post.prettyPrint()+", "+objInvariant.prettyPrint()
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + post.iterate (f) + objInvariant.iterate (f)
}

abstract class PITAssign(protected val repos: Repository,
                         conclusion : Modality) : Rule(conclusion){

    protected fun assignFor(loc : Location, rhs : Term) : ElementaryUpdate{
        return if(loc is Field)   ElementaryUpdate(Heap, store(loc, rhs)) else ElementaryUpdate(loc as ProgVar, rhs)
    }

    protected fun symbolicNext(loc : Location,
                     rhs : Term,
                     remainder : Stmt,
                     target : DeductType,
                     iForm : Formula,
                     iUp : UpdateElement,
                     infoObj: NodeInfo) : SymbolicNode{
        return SymbolicNode(SymbolicState(
            iForm,
            ChainUpdate(iUp, assignFor(loc,rhs)),
            Modality(remainder, target)
        ), info = infoObj)
    }
}

//Type system
class PITLocAssign(repos: Repository) : PITAssign(repos,Modality(
    SeqStmt(AssignStmt(LocationAbstractVar("LHS"), ExprAbstractVar("EXPR")), StmtAbstractVar("CONT")),
    PostInvAbstractVar("TYPE"))) {

    override fun transform(cond: MatchCondition, input : SymbolicState): List<SymbolicTree> {
        val lhs = cond.map[LocationAbstractVar("LHS")] as Location
        val rhsExpr = cond.map[ExprAbstractVar("EXPR")] as Expr
        val rhs = exprToTerm(rhsExpr)
        val remainder = cond.map[StmtAbstractVar("CONT")] as Stmt
        val target = cond.map[PostInvAbstractVar("TYPE")] as DeductType
        val info = InfoLocAssign(lhs, rhsExpr)
        return listOf(symbolicNext(lhs, rhs, remainder, target, input.condition, input.update, info))
    }
}

class PITSyncAssign(repos: Repository) : PITAssign(repos, Modality(
    SeqStmt(SyncStmt(LocationAbstractVar("LHS"), ExprAbstractVar("EXPR")),
        StmtAbstractVar("CONT")),
    PostInvAbstractVar("TYPE"))) {

    override fun transform(cond: MatchCondition, input : SymbolicState): List<SymbolicTree> {
        val lhs = cond.map[LocationAbstractVar("LHS")] as Location
        val rhsExpr = cond.map[ExprAbstractVar("EXPR")] as Expr
        val rhs = exprToTerm(rhsExpr)
        val remainder = cond.map[StmtAbstractVar("CONT")] as Stmt
        val target = cond.map[PostInvAbstractVar("TYPE")] as DeductType

        // Generate SMT representation of the future expression to get its model value later
        val futureSMTExpr = apply(input.update, rhs) as Term
        val info = InfoGetAssign(lhs, rhsExpr, futureSMTExpr)

        return listOf(symbolicNext(lhs, rhs, remainder, target, input.condition, input.update, info))
    }

}

class PITAllocAssign(repos: Repository) : PITAssign(repos, Modality(
    SeqStmt(AllocateStmt(LocationAbstractVar("LHS"), ExprAbstractVar("EXPR")),
        StmtAbstractVar("CONT")),
    PostInvAbstractVar("TYPE"))) {

    override fun transform(cond: MatchCondition, input : SymbolicState): List<SymbolicTree> {
        val lhs = cond.map[LocationAbstractVar("LHS")] as Location
        val rhsExpr = cond.map[ExprAbstractVar("EXPR")] as Expr
        val rhs = exprToTerm(rhsExpr) as Function
        val remainder = cond.map[StmtAbstractVar("CONT")] as Stmt
        val target = cond.map[PostInvAbstractVar("TYPE")] as DeductType

        val classNameExpr = rhs.params[0] as Function
        val nextRhs = Function(rhs.name,rhs.params.subList(1,rhs.params.size))

        //construct precondition check of the class creation
        val precond = repos.classReqs.getValue(classNameExpr.name).first
        val targetDecl = repos.classReqs[classNameExpr.name]!!.second
        val substMap = mutableMapOf<LogicElement,LogicElement>()
        for(i in 0 until targetDecl.numParam){
            val pName = select(Field(targetDecl.getParam(i).name+"_f", targetDecl.getParam(i).type))
            val pValue = nextRhs.params[i]
            substMap[pName] = pValue
        }
        val precondSubst = subst(precond, substMap) as Formula

        val pre = LogicNode(
            input.condition,
            UpdateOnFormula(input.update, precondSubst),
            info = InfoClassPrecondition(precondSubst)
        )

        // Generate SMT representation of the NEW expression to get its model value later
        val constructorSMTExpr = apply(input.update, nextRhs).toSMT()

        val next = symbolicNext(lhs,
                                            nextRhs,
                                            remainder,
                                            target,
                                            And(input.condition, UpdateOnFormula(input.update, Not(Predicate("=", listOf(nextRhs, Function("0")))))),
                                            ChainUpdate(input.update, assignFor(lhs, nextRhs)),
                                            InfoObjAlloc(lhs, rhsExpr, constructorSMTExpr))

        return listOf(pre, next)
    }
}


class PITCallAssign(repos: Repository) : PITAssign(repos, Modality(
    SeqStmt(CallStmt(LocationAbstractVar("LHS"), ExprAbstractVar("CALLEE"), CallExprAbstractVar("CALL")),
        StmtAbstractVar("CONT")),
    PostInvAbstractVar("TYPE"))) {

    override fun transform(cond: MatchCondition, input : SymbolicState): List<SymbolicTree> {
        val lhs = cond.map[LocationAbstractVar("LHS")] as Location
        val calleeExpr = cond.map[ExprAbstractVar("CALLEE")] as Expr
        val callee = exprToTerm(calleeExpr)
        val call = cond.map[CallExprAbstractVar("CALL")] as CallExpr
        val remainder = cond.map[StmtAbstractVar("CONT")] as Stmt
        val target = cond.map[PostInvAbstractVar("TYPE")] as DeductType

        val notNullCondition = Not(Predicate("=", listOf(callee,Function("0", emptyList()))))

        val absExp = calleeExpr.absExp
        val isNonNull = absExp?.nonNull() ?: false
        val nonenull = LogicNode(
            input.condition,
            UpdateOnFormula(input.update, notNullCondition),
            info = InfoNullCheck(notNullCondition)
        )

        //construct precondition check of the call
        val precond = repos.methodReqs.getValue(call.met).first
        val targetDecl = repos.methodReqs.getValue(call.met).second
        val substMap = mutableMapOf<LogicElement,LogicElement>()
        for(i in 0 until targetDecl.numParam){
            val pName = ProgVar(
                targetDecl.getParam(i).name,
                targetDecl.getParam(i).type
            )
            val pValue = exprToTerm(call.e[i])
            substMap[pName] = pValue
        }
        val precondSubst = subst(precond, substMap) as Formula
        val pre = LogicNode(
            input.condition,
            UpdateOnFormula(input.update, precondSubst),
            info = InfoMethodPrecondition(precondSubst)
        )

        val freshFut = FreshGenerator.getFreshFuture(targetDecl.type)
        val read = repos.methodEnss[call.met]
        val postCond = read?.first ?: True

        val targetPostDecl = read!!.second
        val substPostMap = mutableMapOf<LogicElement,LogicElement>()
        for(i in 0 until targetDecl.numParam){
            val pName = ProgVar(
                targetPostDecl.getParam(i).name,
                targetPostDecl.getParam(i).type
            )
            val pValue = exprToTerm(call.e[i])
            substPostMap[pName] = pValue
        }

        val updateNew = ElementaryUpdate(ReturnVar(targetDecl.type.qualifiedName, targetDecl.type),valueOfFunc(freshFut))

        val next = symbolicNext(lhs,
                                            freshFut,
                                            remainder,
                                            target,
                                            And(input.condition, UpdateOnFormula(input.update,UpdateOnFormula(updateNew,subst(postCond, substPostMap) as Formula))),
                                            input.update,
                                            InfoCallAssign(lhs, calleeExpr, call, freshFut.name))
        if (isNonNull) return listOf(pre, next)
        return listOf(nonenull,pre,next)
    }
}


class PITSyncCallAssign(repos: Repository) : PITAssign(repos, Modality(
        SeqStmt(SyncCallStmt(LocationAbstractVar("LHS"), ExprAbstractVar("CALLEE"), SyncCallExprAbstractVar("CALL")),
                StmtAbstractVar("CONT")),
        PostInvAbstractVar("TYPE"))) {

    override fun transform(cond: MatchCondition, input: SymbolicState): List<SymbolicTree> {
        val lhs = cond.map[LocationAbstractVar("LHS")] as Location
        val call = cond.map[SyncCallExprAbstractVar("CALL")] as SyncCallExpr
        val calleeExpr = cond.map[ExprAbstractVar("CALLEE")] as Expr
        val remainder = cond.map[StmtAbstractVar("CONT")] as Stmt
        val target = cond.map[PostInvAbstractVar("TYPE")] as DeductType


        val precond = repos.syncMethodReqs.getValue(call.met).first //Todo: objInv
        val targetPreDecl = repos.syncMethodReqs.getValue(call.met).second

        val freshVar = FreshGenerator.getFreshProgVar(targetPreDecl.type)//ASK<<

        val updateNew = ElementaryUpdate(ReturnVar(targetPreDecl.type.qualifiedName, targetPreDecl.type), freshVar)

        val substPreMap = mapSubstPar(call, targetPreDecl)
        val precondSubst = subst(precond, substPreMap) as Formula

        //preconditions
        val first = LogicNode(
                input.condition,
                UpdateOnFormula(input.update, precondSubst),
                info = InfoMethodPrecondition(precondSubst)
        )

        val postCond = repos.syncMethodEnss[call.met]?.first ?: True //Todo: objInv
        val targetPostDecl = repos.syncMethodEnss[call.met]!!.second
        val substPostMap = mapSubstPar(call, targetPostDecl)

        val anon = ElementaryUpdate(Heap, anon(Heap))

        //XXX handle  last here as well
        val someHeap = FreshGenerator.getFreshProgVar(Heap.concrType)
        val heapUpdate = ChainUpdate(ElementaryUpdate(OldHeap,Heap), ElementaryUpdate(LastHeap,someHeap))

        val updateLeftNext = ChainUpdate(input.update, ChainUpdate(heapUpdate, ChainUpdate(anon, updateNew)))
        val updateRightNext = ChainUpdate(input.update, anon)
        val updateOnFormula =  UpdateOnFormula(updateLeftNext, subst(postCond, substPostMap) as Formula)

        // Generate SMT representation of the anonymized heap for future heap reconstruction
        val anonHeapExpr = apply(updateRightNext, Heap) as Term
        // Generate SMT expression of method return value for model evaluation
        val returnValExpr = apply(updateRightNext, freshVar) as Term

        val next = symbolicNext(lhs,
                freshVar,
                remainder,
                target,
                And(input.condition, updateOnFormula),
                updateRightNext,
                InfoSyncCallAssign(lhs, calleeExpr, call, anonHeapExpr, returnValExpr))

        return listOf(first,next)
    }
}

fun mapSubstPar(callExpr: SyncCallExpr, targetDecl: MethodSig): MutableMap<LogicElement, LogicElement> {

    val substMap = mutableMapOf<LogicElement, LogicElement>()

    for (i in 0 until targetDecl.numParam) {
        val pName = ProgVar(
            targetDecl.getParam(i).name,
            targetDecl.getParam(i).type
        )
        val pValue = exprToTerm(callExpr.e[i])
        substMap[pName] = pValue

    }
    return substMap
}

object PITSkip : Rule(Modality(
        SkipStmt,
        PostInvariantPair(FormulaAbstractVar("POST"), FormulaAbstractVar("OBJ")))) {

    override fun transform(cond: MatchCondition, input : SymbolicState): List<SymbolicTree> {
        val target = cond.map[FormulaAbstractVar("POST")] as Formula
        val res = LogicNode(
                    input.condition,
                    UpdateOnFormula(input.update, target),
                    info = InfoSkipEnd(target)
        )
        return listOf(res)
    }
}

object PITSkipSkip : Rule(Modality(
        SeqStmt(SkipStmt, StmtAbstractVar("CONT")),
        PostInvAbstractVar("TYPE"))) {

    override fun transform(cond: MatchCondition, input : SymbolicState): List<SymbolicTree> {
        val cont = cond.map[StmtAbstractVar("CONT")] as Stmt
        val pitype = cond.map[PostInvAbstractVar("TYPE")] as DeductType
        val res = SymbolicNode(SymbolicState(input.condition, input.update, Modality(cont, pitype)), info = InfoSkip())
        return listOf(res)
    }
}

object PITScopeSkip : Rule(Modality(
        SeqStmt(ScopeMarker, StmtAbstractVar("CONT")),
        PostInvAbstractVar("TYPE"))) {

    override fun transform(cond: MatchCondition, input : SymbolicState): List<SymbolicTree> {
        val cont = cond.map[StmtAbstractVar("CONT")] as Stmt
        val pitype = cond.map[PostInvAbstractVar("TYPE")] as DeductType
        val res = SymbolicNode(SymbolicState(input.condition, input.update, Modality(cont, pitype)), info = InfoScopeClose())
        return listOf(res)
    }
 }

object PITReturn : Rule(Modality(
        ReturnStmt(ExprAbstractVar("RET")),
        PostInvariantPair(FormulaAbstractVar("POST"), FormulaAbstractVar("OBJ")))) {

    override fun transform(cond: MatchCondition, input : SymbolicState): List<SymbolicTree> {
        val target = cond.map[FormulaAbstractVar("OBJ")] as Formula
        val targetPost = cond.map[FormulaAbstractVar("POST")] as Formula
        val retExpr = cond.map[ExprAbstractVar("RET")] as Expr
        val ret = exprToTerm(retExpr)
        val typeReturn = getReturnType(ret)
        val res = LogicNode(
            input.condition,
            And(
                    UpdateOnFormula(ChainUpdate(input.update, ElementaryUpdate(ReturnVar(typeReturn.qualifiedName,typeReturn), ret)), targetPost),
                    UpdateOnFormula(input.update, target)
            ),
            info = InfoReturn(retExpr, targetPost, target, input.update)
        )
        return listOf(res)
    }
}

object PITIf : Rule(Modality(
        SeqStmt(IfStmt(ExprAbstractVar("LHS"), StmtAbstractVar("THEN"), StmtAbstractVar("ELSE")),
                StmtAbstractVar("CONT")),
        PostInvAbstractVar("TYPE"))) {

    override fun transform(cond: MatchCondition, input : SymbolicState): List<SymbolicTree> {

        val contBody = SeqStmt(ScopeMarker, cond.map[StmtAbstractVar("CONT")] as Stmt) // Add a ScopeMarker statement to detect scope closure
        val guardExpr = cond.map[ExprAbstractVar("LHS")] as Expr

        //then
        val guardYes = exprToForm(guardExpr)
        val bodyYes = SeqStmt(cond.map[StmtAbstractVar("THEN")] as Stmt, contBody)
        val updateYes = input.update
        val typeYes = cond.map[PostInvAbstractVar("TYPE")] as DeductType
        val resThen = SymbolicState(And(input.condition, UpdateOnFormula(updateYes, guardYes)), updateYes, Modality(bodyYes, typeYes))

        //else
        val guardNo = Not(exprToForm(guardExpr))
        val bodyNo = SeqStmt(cond.map[StmtAbstractVar("ELSE")] as Stmt, contBody)
        val updateNo = input.update
        val typeNo = cond.map[PostInvAbstractVar("TYPE")] as DeductType
        val resElse = SymbolicState(And(input.condition, UpdateOnFormula(updateNo, guardNo)), updateNo, Modality(bodyNo, typeNo))
        return listOf(SymbolicNode(resThen, info = InfoIfThen(guardExpr)), SymbolicNode(resElse, info = InfoIfElse(guardExpr)))
    }
}

object PITAwait : Rule(Modality(
        SeqStmt(AwaitStmt(ExprAbstractVar("GUARD"),PPAbstractVar("PP")), StmtAbstractVar("CONT")),
        PostInvariantPair(FormulaAbstractVar("POST"), FormulaAbstractVar("OBJ")))) {

    override fun transform(cond: MatchCondition, input : SymbolicState): List<SymbolicTree> {
        val guardExpr = cond.map[ExprAbstractVar("GUARD")] as Expr
        val guard = exprToForm(guardExpr)
        val cont = cond.map[StmtAbstractVar("CONT")] as Stmt
        val target = cond.map[FormulaAbstractVar("OBJ")] as Formula
        val targetPost = cond.map[FormulaAbstractVar("POST")] as Formula

        val updateLastHeap = ElementaryUpdate(LastHeap, Heap)

        // Generate SMT representation of the anonymized heap for future heap reconstruction
        val anonHeapExpr = apply(ChainUpdate(input.update, ElementaryUpdate(Heap,anon(Heap))), Heap) as Term

        val lNode = LogicNode(input.condition, UpdateOnFormula(input.update, target), info = InfoInvariant(target))

        val sStat = SymbolicState(
                And(
                        input.condition,
                        UpdateOnFormula(
                                ChainUpdate(input.update,ChainUpdate(ElementaryUpdate(Heap,anon(Heap)),updateLastHeap)),
                                And(target,guard)
                        )
                ),
                ChainUpdate(input.update, ChainUpdate(ElementaryUpdate(Heap,anon(Heap)),updateLastHeap)),
                Modality(cont, PostInvariantPair(targetPost,target)))

        return listOf(lNode,SymbolicNode(sStat, info = InfoAwaitUse(guardExpr, anonHeapExpr)))
    }
}

//todo: warning: this is the throwaway variant of loop invariants
object PITWhile : Rule(Modality(
        SeqStmt(WhileStmt(ExprAbstractVar("GUARD"),
                          StmtAbstractVar("BODY"),
                          PPAbstractVar("PP"),
                          FormulaAbstractVar("INV")),
                StmtAbstractVar("CONT")),
        PostInvariantPair(FormulaAbstractVar("POST"),
                          FormulaAbstractVar("OBJ")))) {

    override fun transform(cond: MatchCondition, input : SymbolicState): List<SymbolicTree> {
        val guardExpr = cond.map[ExprAbstractVar("GUARD")] as Expr
        val guard = exprToForm(guardExpr)
        val body = cond.map[StmtAbstractVar("BODY")] as Stmt
        val cont = cond.map[StmtAbstractVar("CONT")] as Stmt
        val targetInv = cond.map[FormulaAbstractVar("INV")] as Formula
        val target = cond.map[FormulaAbstractVar("OBJ")] as Formula
        val targetPost = cond.map[FormulaAbstractVar("POST")] as Formula

        //Initial Case
        val initial = LogicNode(input.condition, UpdateOnFormula(input.update, targetInv), info = InfoLoopInitial(guardExpr, targetInv))

        //Preserves Case
        val preservesInfo = InfoLoopPreserves(guardExpr, targetInv)
        val preserves = SymbolicState(And(targetInv,guard),
                                      EmptyUpdate,
                                      Modality(appendStmt(body,SeqStmt(ScopeMarker, SkipStmt)), PostInvariantPair(targetInv,target)))

        //Use Case
        val useInfo = InfoLoopUse(guardExpr, targetInv)
        val use = SymbolicState(And(targetInv,Not(guard)),
                                  EmptyUpdate,
                                  Modality(cont, PostInvariantPair(targetPost,target)))
        return listOf(
            initial,
            SymbolicNode(preserves, info = preservesInfo),
            SymbolicNode(use, info = useInfo)
        )

    }
}


object PITBranch : Rule(Modality(
    SeqStmt(BranchStmt(ExprAbstractVar("LHS"),
        BranchAbstractListVar("BRANCHES")),StmtAbstractVar("CONT")),
    PostInvAbstractVar("TYPE"))) {

    override fun transform(cond: MatchCondition, input : SymbolicState): List<SymbolicTree> {
        val matchExpr = cond.map[ExprAbstractVar("LHS")] as Expr
        val match = exprToTerm(matchExpr)
        val type = cond.map[PostInvAbstractVar("TYPE")] as DeductType
        val cont = cond.map[StmtAbstractVar("CONT")] as Stmt
        val branches = cond.map[BranchAbstractListVar("BRANCHES")] as BranchList
        val update = input.update
        var ress = listOf<SymbolicNode>()
        var no : Formula = True
        for(br in branches.content){
            val preCond = Predicate("=",listOf(match, exprToTerm(br.matchTerm)))
            // Add two scope close markers for counterexample generation (one for branch, one for switch)
            val contBody = SeqStmt(br.branch, SeqStmt(ScopeMarker, SeqStmt(ScopeMarker, cont)))
            val ss = SymbolicState(And(no,And(input.condition, UpdateOnFormula(update, preCond))), update, Modality(contBody, type))
            ress = ress + SymbolicNode(ss, info = InfoBranch(matchExpr, br.matchTerm, no))
            no = And(no, Not(preCond))
        }
        return ress
    }
}

fun getReturnType(term: Term) : Type {
    if(term is ProgVar){
        return term.concrType
    }
    else if(term is DataTypeConst){
        return term.concrType!!
    }
    else if (term is Function) {booleanFunction
        if ( term.name in intFunction || term.name.toIntOrNull() != null)
            return ADTRepos.model!!.intType
        if (term.name == "valueOf")
            return ((term.params[0] as ProgVar).concrType as DataTypeType).getTypeArg(0)
        if (term.name in booleanFunction)
            return ADTRepos.model!!.boolType
        return when (term.name) {
            "Unit" -> ADTRepos.model!!.unitType
            "ite" -> getReturnType(term.params[1])
            "select" -> (term.params[1] as Field).concrType
            else -> {
                val fName = term.name.replace("-",".")
                if(FunctionRepos.isKnown(fName))
                    return FunctionRepos.get(fName).type
                else
                    throw Exception("Function $fName not defined")
            }
        }
    }
    else
        throw java.lang.Exception("Term $term not allowed as return ")
}
