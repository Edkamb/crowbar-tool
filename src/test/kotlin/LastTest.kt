import io.kotlintest.shouldBe
import io.kotlintest.specs.StringSpec
import org.abs_models.crowbar.main.*
import org.abs_models.crowbar.types.PostInvType
import java.nio.file.Paths

class LastTest : StringSpec({
    val postInv = PostInvType::class
    val cvc: String = System.getenv("CVC") ?: "cvc"
    val z3: String = System.getenv("Z3") ?: "z3"
    for (smt in listOf(z3, cvc)) {
        println("testing with: $smt as backend")
        smtPath = smt
        val fails = listOf("noLastFail")
        val successes = listOf("simpleSuccess", "oldSuccess", "oldWithUpdateSuccess")

        "$smt last"{
            val (model, repos) = load(listOf(Paths.get("src/test/resources/last.abs")))
            val classDecl = model.extractClassDecl("Last", "LastC", repos)
            for(fail in fails) {
                val failNode = classDecl.extractMethodNode(postInv, fail, repos)
                executeNode(failNode, repos, postInv) shouldBe false
            }

            for(success in successes) {
                val successNode = classDecl.extractMethodNode(postInv, success, repos)
                executeNode(successNode, repos, postInv) shouldBe true
            }
        }
    }

})
