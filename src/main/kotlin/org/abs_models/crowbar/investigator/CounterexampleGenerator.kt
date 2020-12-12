package org.abs_models.crowbar.investigator

import java.io.File
import org.abs_models.crowbar.data.Field
import org.abs_models.crowbar.data.Formula
import org.abs_models.crowbar.data.Heap
import org.abs_models.crowbar.data.Location
import org.abs_models.crowbar.data.OldHeap
import org.abs_models.crowbar.data.ProgVar
import org.abs_models.crowbar.data.Term
import org.abs_models.crowbar.data.deupdatify
import org.abs_models.crowbar.data.filterHeapTypes
import org.abs_models.crowbar.data.specialHeapKeywords
import org.abs_models.crowbar.interfaces.generateSMT
import org.abs_models.crowbar.interfaces.plainSMTCommand
import org.abs_models.crowbar.main.ADTRepos
import org.abs_models.crowbar.main.Verbosity
import org.abs_models.crowbar.main.output
import org.abs_models.crowbar.main.tmpPath
import org.abs_models.crowbar.tree.InfoNode
import org.abs_models.crowbar.tree.InfoObjAlloc
import org.abs_models.crowbar.tree.LeafInfo
import org.abs_models.crowbar.tree.LogicNode
import org.abs_models.crowbar.tree.NoInfo
import org.abs_models.crowbar.tree.NodeInfo
import org.abs_models.crowbar.tree.SymbolicNode
import org.abs_models.crowbar.tree.SymbolicTree

object CounterexampleGenerator {

    var fileIndex = 1

    fun investigateAll(node: SymbolicNode, snippetID: String) {
        val uncloseable = node.collectLeaves().filter { it is LogicNode && !it.evaluate() }.map { it as LogicNode }

        // Splits in the symex tree _before_ the last full anonymization point can cause duplicate unclosed leafs
        // we consider nodes with identical pre and postconditions to be redundant
        val deduped = uncloseable.distinctBy {
            deupdatify(it.ante).prettyPrint() + deupdatify(it.succ).prettyPrint()
        }

        deduped.forEach {
            val counterexample = investigateSingle(node, it, snippetID)
            writeTestcase(counterexample, fileIndex)
            fileIndex++
        }
    }

    fun investigateFirst(node: SymbolicNode, snippetID: String) {
        val uncloseable = node.collectLeaves().first { it is LogicNode && !it.evaluate() } as LogicNode
        investigateSingle(node, uncloseable, snippetID)
    }

    private fun investigateSingle(node: SymbolicNode, uncloseable: LogicNode, snippetID: String): String {
        if (uncloseable.info !is LeafInfo)
            throw Exception("Unclosed branch does not have proof obligation information")

        val obligations = (uncloseable.info as LeafInfo).obligations

        output("Investigator: found unclosed branch", Verbosity.V)

        output("Investigator: collecting branch nodes....", Verbosity.V)
        val branchNodes = collectBranchNodes(node, uncloseable)
        val infoNodes = branchNodes.map { (it as InfoNode).info }

        // Remove expressions that contain definitions missing from the SMT model
        // This will cause the solver to error out, and any expression depending on a definition
        // not present in the SMT model is irrelevant to the correctness of the method anyway
        // Collect types of fields and variables from leaf node
        val pre = deupdatify(uncloseable.ante)
        val post = deupdatify(uncloseable.succ)
        val availableDefs = ((pre.iterate { it is Term } + post.iterate { it is Term }) as Set<Term>).map { collectUsedDefinitions(it) }.flatten().toSet()

        output("Investigator: collecting anonymized heap expressions....", Verbosity.V)
        val heapExpressionTerms = infoNodes.map { it.heapExpressions }.flatten()
        val heapExpressions = (heapExpressionTerms.filter { collectUsedDefinitions(it).minus(availableDefs).isEmpty() } + Heap + OldHeap)

        output("Investigator: collecting other smt expressions....", Verbosity.V)
        val miscExpressionTerms = infoNodes.map { it.smtExpressions }.flatten()
        val miscExpressions = miscExpressionTerms.filter { collectUsedDefinitions(it).minus(availableDefs).isEmpty() }.map { it.toSMT(false) }

        output("Investigator: collecting object allocation expressions....", Verbosity.V)
        val newExpressions = infoNodes.filter { it is InfoObjAlloc }.map { (it as InfoObjAlloc).newSMTExpr }

        output("Investigator: parsing model....", Verbosity.V)
        val model = getModel(uncloseable, heapExpressions, newExpressions, miscExpressions)

        output("Investigator: rendering counterexample....", Verbosity.V)

        return buildTestcase(infoNodes.asReversed(), model, obligations, snippetID)
    }

    private fun collectBranchNodes(root: SymbolicNode, leaf: SymbolicTree): List<SymbolicTree> {
        val parents = parentMapping(root)
        val nodes = mutableListOf<SymbolicTree>()
        var n: SymbolicTree? = leaf

        while (n != null) {
            nodes.add(n)

            if (n is InfoNode && n.info.isAnon)
                break

            n = parents[n]
        }

        return nodes
    }

    private fun parentMapping(root: SymbolicNode): Map<SymbolicTree, SymbolicTree?> {
        // Create child-parent mapping for symbolic tree
        val parents = mutableMapOf<SymbolicTree, SymbolicTree?>()
        val worklist = mutableListOf<SymbolicTree>(root)

        while (worklist.isNotEmpty()) {
            val elem = worklist.removeAt(0)

            if (elem is SymbolicNode) {
                elem.children.forEach {
                    parents[it] = elem
                }
                worklist.addAll(elem.children)
            }
        }

        return parents
    }

    private fun getModel(
        leaf: LogicNode,
        heapExpressions: List<Term>,
        newExpressions: List<String>,
        miscExpressions: List<String>
    ): Model {

        // "heap", "old", "last", etc do not reference program vars
        val usedTypes = ADTRepos.getAllTypePrefixes()
        val reservedVarNameStems = listOf("heap") + specialHeapKeywords.values.map { it.name }
        val reservedVarNames = usedTypes.map { tpe -> reservedVarNameStems.map { stem -> "${stem}_${tpe.replace(".","_")}" } }.flatten() + listOf("Unit")

        // Collect types of fields and variables from leaf node
        val fieldTypes = ((leaf.ante.iterate { it is Field } + leaf.succ.iterate { it is Field }) as Set<Field>).associate { Pair(it.name, it.dType) }
        val varTypes = ((leaf.ante.iterate { it is ProgVar } + leaf.succ.iterate { it is ProgVar }) as Set<ProgVar>).filter { !reservedVarNames.contains(it.name) }.associate { Pair(it.name, it.dType) }

        // Collect conjunctively joined sub-obligation parts
        val subObligationMap = collectSubObligations(deupdatify(leaf.succ) as Formula).associate { Pair(it.toSMT(true), it) }
        val subObligations = subObligationMap.keys.toList()

        // Build model command
        var baseModel = "(get-model)\n"

        if (heapExpressions.size > 0) {
            // We have to multiplex heap expressions here to get expressions for all types used in the SMT input
            // The result is a map of generic heap expressions to maps of types to corresponding types heap expressions
            usedTypes.forEach { dtype ->
                val typedHeapExpressions = heapExpressions.map { exp -> filterHeapTypes(exp, dtype) }
                baseModel += "; Heap expressions for sub-heap of type ${dtype}\n"
                baseModel += "(get-value (${typedHeapExpressions.joinToString(" ")}))\n"
            }
        }
        if (newExpressions.size > 0) {
            baseModel += "; Object creation expressions\n"
            baseModel += "(get-value (${newExpressions.joinToString(" ")}))\n"
        }
        if (miscExpressions.size > 0) {
            baseModel += "; Future & return expression evaluation, misc expressions\n"
            baseModel += "(get-value (${miscExpressions.joinToString(" ")}))\n"
        }
        if (subObligationMap.keys.size > 0) {
            baseModel += "; Proof sub-obligations\n"
            baseModel += "(get-value (${subObligations.joinToString(" ")}))\n"
        }

        // Get evaluations of all collected expressions (heap states after anon, new objects, future values, etc)
        val smtRep = generateSMT(leaf.ante, leaf.succ, modelCmd = baseModel)
        val solverResponse = plainSMTCommand(smtRep)!!

        // Can't parse model if solver timed out
        if (solverResponse.substring(0, 7) == "unknown") {
            output("Investigator: solver did not return definite sat/unsat result")
            return EmptyModel
        }

        ModelParser.loadSMT(solverResponse)

        val parsed = ModelParser.parseModel()
        val constants = parsed.filter { it is ModelConstant }.map{ it as ModelConstant }
        val vars = constants.filter { !(it.name matches Regex("(.*_f|fut_.*|NEW\\d.*|f_(\\d)+|DTypes\\-.*)") || reservedVarNames.contains(it.name)) }
        val fields = constants.filter { it.name matches Regex(".*_f") }
        val futLookup = constants.filter { it.name.startsWith("fut_") }.associate { Pair((it.value as MvInteger).value, it.name) }

        val initialAssignments = mutableListOf<Pair<Location, ModelValue>>()

        vars.forEach {
            val variable = ProgVar(it.name, varTypes[it.name]!!)
            initialAssignments.add(Pair(variable, it.value))
        }

        // Get heap-states at heap anonymization points
        val heapAssignments = getHeapMap(heapExpressions, fields, fieldTypes)

        val heapState = heapAssignments["heap"]!!
        initialAssignments.addAll(heapState)

        // Get mapping of object ids to names
        val objLookup = getObjectMap(newExpressions)

        // Get evaluations of misc expressions (return value expressions, values of futures, method return values)
        val smtExprs = getExpressionMap(miscExpressions)

        // Get evaluations of sub-obligations and create usable mapping by formula
        val subObligationValues = getExpressionMap(subObligations).mapKeys { subObligationMap[it.key]!! }.mapValues { (it.value as MvDataType).value == "true" }

        return Model(initialAssignments, heapAssignments, futLookup, objLookup, smtExprs, subObligationValues)
    }

    private fun getHeapMap(heapExpressions: List<Term>, fields: List<ModelConstant>, fieldTypes: Map<String, String>): Map<String, List<Pair<Field, ModelValue>>> {
        if (heapExpressions.size == 0)
            return mapOf()

        // This got a bit tricky with the introduction of multiple sub-heaps
        // We first parse the typed versions of all heap expressions for all used types
        val usedTypes = ADTRepos.getAllTypePrefixes()
        val parsedHeaps = usedTypes.map { Pair(it, ModelParser.parseArrayValues()) }.toMap()

        // And then find the correct value for every field in every heap state
        val heapMap = heapExpressions.mapIndexed { index, exp ->
            val heapContents = fields.map { field ->
                val fieldType = fieldTypes[field.name]!!
                // By looking up the value in the sub-heap of the right type
                // (ADTRepos.libPrefix maps ABS types to SMT types)
                val subheapID = ADTRepos.libPrefix(fieldType)
                val value = parsedHeaps[subheapID]!![index].getValue((field.value as MvInteger).value)
                Pair(Field(field.name, fieldType), value)
            }

            Pair(exp.toSMT(false), heapContents)
        }.toMap()

        return heapMap
    }

    private fun getExpressionMap(expressions: List<String>): Map<String, ModelValue> {
        if (expressions.size == 0)
            return mapOf()

        val parsed = ModelParser.parseScalarValues()
        val expMap = expressions.zip(parsed).associate { it }

        return expMap
    }

    private fun getObjectMap(newExpressions: List<String>): Map<Int, String> {
        if (newExpressions.size == 0)
            return mapOf()

        val parsed = ModelParser.parseScalarValues().map { (it as MvInteger).value }
        val objMap = parsed.zip(newExpressions).associate { it }

        return objMap
    }

    private fun buildTestcase(
        infoNodes: List<NodeInfo>,
        model: Model,
        obligations: List<Pair<String, Formula>>,
        snippetID: String
    ): String {
        val interfaceDef = "interface Ce { Unit ce(); }"
        val dataTypeDef = renderDataTypeDefs()

        val classFrameHeader = "module Counterexample;\n$interfaceDef\n$dataTypeDef\n\nclass CeFrame implements Ce {\n"
        val classFrameFooter = "\n}\n\n"

        val methodFrameHeader = "Unit ce() {\n"
        val methodFrameFooter = "\n}"

        val mainBlockInner = "Ce x = new CeFrame();\nx.ce();"
        val mainBlock = "{\n${indent(mainBlockInner, 1)}\n}\n"

        NodeInfoRenderer.reset(model)
        val initBlock = NodeInfoRenderer.initAssignments()
        val statements = mutableListOf<String>()
        val filteredNodes = infoNodes.filter { it !is NoInfo }

        for (it in filteredNodes) {
            statements.add(it.accept(NodeInfoRenderer))
        }

        // For some nodes, we want to render the initial assignments _after_ the node for more intuitive counterexamples
        // (so far, only the InfoLoopUse makes use of this)
        if (filteredNodes[0].initAfter)
            statements.add(1, initBlock)
        else
            statements.add(0, initBlock)

        val stmtHeader = "// Snippet from: $snippetID\n"
        val stmtString = statements.joinToString("\n")
        val explainer = "\n// Proof failed here. Trying to show:\n"
        val oblString = obligations.map { "// ${it.first}: ${NodeInfoRenderer.renderFormula(it.second)}" }.joinToString("\n")

        var subOblString = "\n// Failed to show the following sub-obligations:\n"
        subOblString += model.subObligations.filter { !it.value }.map { "// ${NodeInfoRenderer.renderFormula(it.key)}" }.joinToString("\n")

        val requiredScopeCloses = NodeInfoRenderer.closeScopes() // Close scopes left open due to abrupt proof end
        val fieldDefs = NodeInfoRenderer.fieldDefs().joinToString("\n")
        val methodContent = stmtHeader + stmtString + explainer + oblString + subOblString + requiredScopeCloses
        val methodFrame = methodFrameHeader + indent(methodContent, 1) + methodFrameFooter

        val classFrame = classFrameHeader + indent(fieldDefs, 1) + "\n\n" + indent(methodFrame, 1) + classFrameFooter + mainBlock

        return classFrame
    }

    private fun renderDataTypeDefs(): String {
        val usedDataTypes = ADTRepos.getAllTypePrefixes().map { ADTRepos.getSMTDType(it) }
        val defs = usedDataTypes.filter { it.dtype.startsWith("DTypes.") }.map {
            val values = it.values.map { it.removePrefix("DTypes.") }
            "data ${it.dtype.removePrefix("DTypes.")} = ${values.joinToString(" | ")};"
        }
        return defs.joinToString("\n")
    }

    private fun writeTestcase(content: String, index: Int) {
        val filename = "${tmpPath}crowbar-ce-$index.abs"
        val file = File(filename)
        file.createNewFile()
        file.writeText(content)
        output("Investigator: wrote counterexample to $filename")
    }
}

class Model(
    val initState: List<Pair<Location, ModelValue>>,
    val heapMap: Map<String, List<Pair<Field, ModelValue>>>,
    val futLookup: Map<Int, String>,
    val objLookup: Map<Int, String>,
    val smtExprs: Map<String, ModelValue>,
    val subObligations: Map<Formula, Boolean>
) {
    // The SMT solver may reference futures that were not defined in the program
    // we'll mark these with a questionmark and give the underlying integer id from the solver
    fun futNameById(id: Int) = if (futLookup.containsKey(id)) futLookup[id]!! else "fut_?($id)"
}

val EmptyModel = Model(listOf(), mapOf(), mapOf(), mapOf(), mapOf(), mapOf())
