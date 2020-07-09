package org.abs_models.crowbar.interfaces

import org.abs_models.crowbar.data.*
import org.abs_models.crowbar.data.Function
import org.abs_models.crowbar.main.*
import java.io.File
import java.util.concurrent.TimeUnit

//(set-option :timeout ${timeoutS*1000})
val smtHeader = """
    (set-logic ALL)
    (define-sort Field () Int)
    (define-sort MHeap () (Array Field Int))
    (declare-const heap MHeap)
    (declare-const oldheap MHeap)
    (declare-fun   anon (MHeap) MHeap)
    (declare-fun   valueOf (Int) Int)
    (define-fun iOr((x Int) (y Int)) Int
        (ite (or (= x 1) (= y 1)) 1 0))
    (define-fun iAnd((x Int) (y Int)) Int
        (ite (and (= x 1) (= y 1)) 1 0))
    (define-fun iNot((x Int)) Int
        (ite (= x 1) 0 1))
    (define-fun iLt((x Int) (y Int)) Int
        (ite (< x y) 1 0))
    (define-fun iLeq((x Int) (y Int)) Int
        (ite (<= x y) 1 0))
    (define-fun iGt((x Int) (y Int)) Int
        (ite (> x y) 1 0))
    (define-fun iGeq((x Int) (y Int)) Int
        (ite (>= x y) 1 0))
    (define-fun iEq((x Int) (y Int)) Int
        (ite (= x y) 1 0))
    (define-fun iNeq((x Int) (y Int)) Int
        (ite (= x y) 0 1)) 
    (define-fun iite((x Int) (y Int) (z Int)) Int (ite (= x 1) y z))
    (declare-const Unit Int)
    (assert (= Unit 0))
    """.trimIndent()

@Suppress("UNCHECKED_CAST")
fun generateSMT(ante : Formula, succ: Formula) : String {
    val pre = deupdatify(ante)
    val post = deupdatify(Not(succ))

    val fields =  (pre.iterate { it is Field } + post.iterate { it is Field }) as Set<Field>
    val vars =  ((pre.iterate { it is ProgVar } + post.iterate { it is ProgVar  }) as Set<ProgVar>).filter { it.name != "heap" && it.name != "oldheap"}
    val heaps =  ((pre.iterate { it is Function } + post.iterate{ it is Function }) as Set<Function>).map { it.name }.filter { it.startsWith("NEW") }
    val futs =  ((pre.iterate { it is Function } + post.iterate { it is Function }) as Set<Function>).filter { it.name.startsWith("fut_") }
    val funcs =  ((pre.iterate { it is Function } + post.iterate { it is Function }) as Set<Function>).filter { it.name.startsWith("f_") }
    var header = smtHeader
    header += FunctionRepos
    header = fields.fold(header, { acc, nx-> acc +"\n(declare-const ${nx.name} Field)"})
    header = vars.fold(header, {acc, nx-> acc+"\n(declare-const ${nx.name} Int)"}) //hack: dtype goes here
    header = heaps.fold(header, {acc, nx-> "$acc\n(declare-fun $nx (${"Int ".repeat(nx.split("_")[1].toInt())}) Int)" })
    header = futs.fold(header, { acc, nx-> acc +"\n(declare-const ${nx.name} Int)"})
    header = funcs.fold(header, { acc, nx-> acc +"\n(declare-const ${nx.name} Int)"})
    fields.forEach { f1 -> fields.minus(f1).forEach{ f2 -> header += "\n (assert (not (= ${f1.name} ${f2.name})))" } }

    return """
    $header 
    (assert ${pre.toSMT(true)} ) 
    (assert ${post.toSMT(true)}) 
    (check-sat)
    (exit)
    """.trimIndent()
}

/* https://stackoverflow.com/questions/35421699 */
fun String.runCommand(
        workingDir: File = File("."),
        timeoutAmount: Long = 60,
        timeoutUnit: TimeUnit = TimeUnit.SECONDS
): String? = try {
    ProcessBuilder(split("\\s".toRegex()))
            .directory(workingDir)
            .redirectOutput(ProcessBuilder.Redirect.PIPE)
            .redirectError(ProcessBuilder.Redirect.PIPE)
            .start().apply { waitFor(timeoutAmount, timeoutUnit) }
            .inputStream.bufferedReader().readText()
} catch (e: java.io.IOException) {
    e.printStackTrace()
    null
}

fun evaluateSMT(smtRep : String) : Boolean {
    val path = "${tmpPath}out.smt2"
    File(path).writeText(smtRep)
    val res = "$smtPath $path".runCommand()
    return res != null && res.trim() == "unsat"
}

fun evaluateSMT(ante: Formula, succ: Formula) : Boolean {
    val smtRep = generateSMT(ante, succ)
    if(verbosity >= Verbosity.VV) println("crowbar-v: \n$smtRep")
    return evaluateSMT(smtRep)
}