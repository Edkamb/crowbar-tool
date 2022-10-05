package org.abs_models.crowbar.types

import org.abs_models.crowbar.data.*
import org.abs_models.crowbar.interfaces.translateStatement
import org.abs_models.crowbar.main.Repository
import org.abs_models.crowbar.main.reporting
import org.abs_models.crowbar.rule.MatchCondition
import org.abs_models.crowbar.rule.Rule
import org.abs_models.crowbar.tree.SymbolicNode
import org.abs_models.crowbar.tree.SymbolicTree
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
        TODO("IMPLEMENT ME")
    }

    override fun exctractFunctionNode(fDecl: FunctionDecl): SymbolicNode {
        throw Exception("PDL only applies to the main block")
    }

}

data class PDLEquation(val head : String, val split : String, val tail1 : String, val tail2 : String){
    override fun toString(): String =
        "$head = $split*$tail1 + (1-$split)$tail2 "

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

object PDLSkip : Rule(Modality(
    SkipStmt,
    PDLAbstractVar("Spec"))) {

    override fun transform(cond: MatchCondition, input : SymbolicState): List<SymbolicTree> {
        val spec = cond.map[PDLAbstractVar("Spec")] as PDLSpec
        TODO("IMPLEMENT ME")
    }
}