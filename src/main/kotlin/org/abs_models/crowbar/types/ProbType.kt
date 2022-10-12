package org.abs_models.crowbar.types

import org.abs_models.crowbar.data.*
import org.abs_models.crowbar.interfaces.translateStatement
import org.abs_models.crowbar.main.*
import org.abs_models.crowbar.rule.FreshGenerator
import org.abs_models.crowbar.rule.MatchCondition
import org.abs_models.crowbar.rule.Rule
import org.abs_models.crowbar.tree.*
import org.abs_models.frontend.ast.ClassDecl
import org.abs_models.frontend.ast.FunctionDecl
import org.abs_models.frontend.ast.MainBlock
import org.abs_models.frontend.ast.Model
import java.util.*
import kotlin.system.exitProcess


interface PDLType : DeductType {
    companion object : PDLType

    override fun extractMethodNode(classDecl: ClassDecl, name: String, repos: Repository): SymbolicNode {
        throw Exception("PDL only applies to the main block")
    }

    override fun extractInitialNode(classDecl: ClassDecl): SymbolicNode {
        throw Exception("PDL only applies to the main block")
    }

    override fun exctractMainNode(model: Model): SymbolicNode {
        if(!model.hasMainBlock()){
            if(reporting) throw Exception("model has no main block!")
            System.err.println("model has no main block!")
            exitProcess(-1)
        }

        val v = appendStmt(translateStatement(model.mainBlock, Collections.emptyMap()), SkipStmt)
        val spec = extractPDLSpec(model.mainBlock)
        return SymbolicNode(SymbolicState(True, EmptyUpdate, Modality(v, spec), listOf()), Collections.emptyList())
    }

    fun extractPDLSpec(mainBlock: MainBlock) : PDLSpec{
        val postCond = extractSpec(mainBlock, "Ensures",mainBlock.type)
        println("Post Cond: "+ postCond.toString());
        val prob = extractTermSpec(mainBlock, "Prob");
        println("Probability: "+ prob);

        return PDLSpec(postCond, prob.toString(), setOf())

        //TODO("IMPLEMENT ME")
    }

    override fun exctractFunctionNode(fDecl: FunctionDecl): SymbolicNode {
        throw Exception("PDL only applies to the main block")
    }

}

data class PDLEquation(val head : String, val split : String, val tail1 : String, val tail2 : String){
    override fun toString(): String =
        "$head = $split*$tail1 + (1-$split)*$tail2 "

}

data class PDLAbstractVar(val name : String) : PDLType, AbstractVar{
    override fun prettyPrint(): String {
        return name
    }
}


data class PDLSpec(val post : Formula, val prob : String, val equations : Set<PDLEquation>) : PDLType {
    override fun prettyPrint(): String {
        return post.prettyPrint()+" with "+prob+ " "+equations.joinToString(", ")
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f)
}

object PDLScopeSkip : Rule(Modality(
    SeqStmt(ScopeMarker, StmtAbstractVar("CONT")),
    PDLAbstractVar("TYPE"))) {

    override fun transform(cond: MatchCondition, input : SymbolicState): List<SymbolicTree> {
        val cont = cond.map[StmtAbstractVar("CONT")] as Stmt
        val pitype = cond.map[PDLAbstractVar("TYPE")] as DeductType
        val res = SymbolicNode(SymbolicState(input.condition, input.update, Modality(cont, pitype), input.exceptionScopes), info = InfoScopeClose())
        return listOf(res)
    }
}

object PDLSkip : Rule(Modality(
        SkipStmt,
        PDLAbstractVar("Spec"))) {

    override fun transform(cond: MatchCondition, input : SymbolicState): List<SymbolicTree> {

        val spec = cond.map[PDLAbstractVar("Spec")] as PDLSpec

        val res = LogicNode(
            input.condition,
                UpdateOnFormula(input.update, spec.post)
            ,
            info = NoInfo()
        )

        val stNode: StaticNode?
        if(res.evaluate()){
            println(spec.prob + "==1")
            val eqT = PDLEquation("1","1", spec.prob, "0")
            stNode = StaticNode("",spec.equations.plus(eqT))
//            println("Static Node: " + stNode.toString())
        } else{
            println(spec.prob + "==0")
            val eqF = PDLEquation("0","1", spec.prob, "0")
            stNode = StaticNode("",spec.equations.plus(eqF))
//            println("Static Node: " + stNode.toString())
        }
//        val zeros  = divByZeroNodes(listOf(retExpr), SkipStmt, input, repos)
        return listOf(res,stNode)
    }
    }
    object PDLSkipComposition : Rule(Modality(
        SeqStmt(SkipStmt, StmtAbstractVar("COUNT"))
        , PDLAbstractVar("Spec"))) {

        override fun transform(cond: MatchCondition, input: SymbolicState): List<SymbolicTree> {
            val count = cond.map[StmtAbstractVar("COUNT")] as Stmt
            val spec = cond.map[PDLAbstractVar("Spec")] as PDLSpec
//            println("count: "+count)
//            println("spec: " + spec)
            val sStat = SymbolicState(
                input.condition,
                input.update,
                Modality(count, spec),
                input.exceptionScopes
            )
//            println("Skip Composition: ")
//            println(sStat.modality)
            return listOf<SymbolicTree>(SymbolicNode(sStat, info = NoInfo()))//Ask Eduard: Is NoInfo ok here?
        }
    }
    abstract class PDLAssign(val repos: Repository,
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
                               infoObj: NodeInfo,
                               scopes: List<ConcreteExceptionScope>) : SymbolicNode{
        return SymbolicNode(SymbolicState(
            iForm,
            ChainUpdate(iUp, assignFor(loc,rhs)),
            Modality(remainder, target),
            scopes
        ), info = infoObj)
    }
    }

    class PDLLocAssign(repos: Repository) : PDLAssign(repos,Modality(
        SeqStmt(AssignStmt(LocationAbstractVar("LHS"), ExprAbstractVar("EXPR")), StmtAbstractVar("CONT")),
        PDLAbstractVar("TYPE"))) {

        override fun transform(cond: MatchCondition, input : SymbolicState): List<SymbolicTree> {
//            println("PDLAssign matched")
            val lhs = cond.map[LocationAbstractVar("LHS")] as Location
            val rhsExpr = cond.map[ExprAbstractVar("EXPR")] as Expr
            val rhs = exprToTerm(rhsExpr)
            val remainder = cond.map[StmtAbstractVar("CONT")] as Stmt
            val target = cond.map[PDLAbstractVar("TYPE")] as DeductType
            // for the CEG
            val info = InfoLocAssign(lhs, rhsExpr)

            //ABS pure expression may still throw implicit exceptions, which are handled by ZeroNodes
            val zeros  = divByZeroNodes(listOf(rhsExpr), remainder, input, repos)

            //consume statement and add ZeroNodes
//            println("PDLLocAssign is applied.")
            return listOf(symbolicNext(lhs, rhs, remainder, target, input.condition, input.update, info, input.exceptionScopes)) + zeros
        }
    }

    class PDLIf(val repos: Repository) : Rule(Modality(
        SeqStmt(IfStmt(ExprAbstractVar("LHS"), StmtAbstractVar("THEN"), StmtAbstractVar("ELSE")),
            StmtAbstractVar("CONT")),
        PDLAbstractVar("TYPE"))) {

        override fun transform(cond: MatchCondition, input : SymbolicState): List<SymbolicTree> {

            val contBody = SeqStmt(ScopeMarker, cond.map[StmtAbstractVar("CONT")] as Stmt) // Add a ScopeMarker statement to detect scope closure
            val guardExpr = cond.map[ExprAbstractVar("LHS")] as Expr

            //then
            val guardYes = exprToForm(guardExpr)
            val bodyYes = SeqStmt(cond.map[StmtAbstractVar("THEN")] as Stmt, contBody)
            val updateYes = input.update
            val typeYes = cond.map[PDLAbstractVar("TYPE")] as DeductType
            val resThen = SymbolicState(And(input.condition, UpdateOnFormula(updateYes, guardYes)), updateYes, Modality(bodyYes, typeYes), input.exceptionScopes)
//           println("PDLIf is applied: ")
//            println("PDLIf Then branch: "+ resThen.toString())
            //else
            val guardNo = Not(exprToForm(guardExpr))
            val bodyNo = SeqStmt(cond.map[StmtAbstractVar("ELSE")] as Stmt, contBody)
            val updateNo = input.update
            val typeNo = cond.map[PDLAbstractVar("TYPE")] as DeductType
            val resElse = SymbolicState(And(input.condition, UpdateOnFormula(updateNo, guardNo)), updateNo, Modality(bodyNo, typeNo), input.exceptionScopes)
//            println("PDLIf Else branch: "+ resElse.toString())

            val zeros  = divByZeroNodes(listOf(guardExpr), contBody, input, repos)
            return listOf<SymbolicTree>(SymbolicNode(resThen, info = InfoIfThen(guardExpr)), SymbolicNode(resElse, info = InfoIfElse(guardExpr))) + zeros
        }
    }


    class PDLDemonIf(val repos: Repository) : Rule(Modality(
        SeqStmt(DemonicIfStmt(StmtAbstractVar("THEN"), StmtAbstractVar("ELSE")),
            StmtAbstractVar("CONT")),
        PDLAbstractVar("TYPE"))) {

        override fun transform(cond: MatchCondition, input : SymbolicState): List<SymbolicTree> {

            val contBody = SeqStmt(ScopeMarker, cond.map[StmtAbstractVar("CONT")] as Stmt) // Add a ScopeMarker statement to detect scope closure
            //val guardExpr = cond.map[ExprAbstractVar("LHS")] as Expr

            //then
           // val guardYes = exprToForm(guardExpr)
            val bodyYes = SeqStmt(cond.map[StmtAbstractVar("THEN")] as Stmt, contBody)
            val updateYes = input.update
            val typeYes = cond.map[PDLAbstractVar("TYPE")] as DeductType
            val resThen = SymbolicState(input.condition, updateYes, Modality(bodyYes, typeYes), input.exceptionScopes)
//            println("PDLDemonIf is applied: ")
//            println("Demonic Then branch: "+ resThen.toString())
            //else
            //val guardNo = Not(exprToForm(guardExpr))
            val bodyNo = SeqStmt(cond.map[StmtAbstractVar("ELSE")] as Stmt, contBody)
            val updateNo = input.update
            val typeNo = cond.map[PDLAbstractVar("TYPE")] as DeductType
            val resElse = SymbolicState(input.condition, updateNo, Modality(bodyNo, typeNo), input.exceptionScopes)
//            println("Demonic Else branch: "+ resElse.toString())

            val zeros  = divByZeroNodes(listOf(), contBody, input, repos)
            return listOf<SymbolicTree>(SymbolicNode(resThen), SymbolicNode(resElse)) + zeros
        }
    }

class PDLProbIf(val repos: Repository) : Rule(Modality(
    SeqStmt(ProbIfStmt(ExprAbstractVar("LHS"), StmtAbstractVar("THEN"), StmtAbstractVar("ELSE")),
        StmtAbstractVar("CONT")),
    PDLAbstractVar("Spec"))) {

    override fun transform(cond: MatchCondition, input : SymbolicState): List<SymbolicTree> {

        val contBody = SeqStmt(ScopeMarker, cond.map[StmtAbstractVar("CONT")] as Stmt) // Add a ScopeMarker statement to detect scope closure
        val expectedValue = cond.map[ExprAbstractVar("LHS")] as Expr
        val spec = cond.map[PDLAbstractVar("Spec")] as PDLSpec

        val p1 = FreshGenerator.getFreshPP().toString()
        val p2 = FreshGenerator.getFreshPP().toString()
        val p = spec.prob

        //then
        val bodyYes = appendStmt(cond.map[StmtAbstractVar("THEN")] as Stmt, contBody)
        val updateYes = input.update
        val resThen = SymbolicState(input.condition, updateYes, Modality(bodyYes, PDLSpec(spec.post, p1, spec.equations.plus(PDLEquation(p, expectedValue.toString(), p1, p2)))), input.exceptionScopes)//Ask Eduard: Should we also add 0 <= p1 <=1?
//        println("PDLProbIf is applied: ")
        println("Probablistic Then branch: "+spec.equations)
        //else
        val bodyNo = appendStmt(cond.map[StmtAbstractVar("ELSE")] as Stmt, contBody)
        val updateNo = input.update
        val resElse = SymbolicState(input.condition, updateNo, Modality(bodyNo, PDLSpec(spec.post, p2, spec.equations.plus(PDLEquation(p, expectedValue.toString(), p1, p2)))), input.exceptionScopes)
        println("Probablistic Else branch: "+ spec.equations)


        return listOf<SymbolicTree>(SymbolicNode(resThen, info = NoInfo()), SymbolicNode(resElse, info = NoInfo()))
    }
}


