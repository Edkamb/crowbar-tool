import io.kotlintest.shouldBe
import io.kotlintest.specs.StringSpec
import org.abs_models.crowbar.main.*
import org.abs_models.crowbar.types.PostInvType
import java.nio.file.Paths

class OldTest : StringSpec({
    val postInv = PostInvType::class
    val cvc: String = System.getenv("CVC") ?: "cvc"
    val z3: String = System.getenv("Z3") ?: "z3"
    for (smt in listOf(z3, cvc)) {
        println("testing with: $smt as backend")
        smtPath = smt

        "$smt trivialOld"{
            val (model, repos) = load(listOf(Paths.get("src/test/resources/old.abs")))
            val classDecl = model.extractClassDecl("Old", "OldC", repos)

            val trivialSuccess = classDecl.extractMethodNode(postInv,"trivialSuccess", repos)
            executeNode(trivialSuccess, repos, postInv) shouldBe true

            val incrSuccess = classDecl.extractMethodNode(postInv,"incrSuccess", repos)
            executeNode(incrSuccess, repos, postInv) shouldBe true

            val trivialFail = classDecl.extractMethodNode(postInv,"trivialFail", repos)
            executeNode(trivialFail, repos, postInv) shouldBe false
        }

        "$smt simpleOld"{
            val (model, repos) = load(listOf(Paths.get("src/test/resources/old.abs")))
            val classDecl = model.extractClassDecl("Old", "OldC", repos)

            val simpleSuccess = classDecl.extractMethodNode(postInv,"simpleSuccess", repos)
            executeNode(simpleSuccess, repos, postInv) shouldBe true

            val simpleFail = classDecl.extractMethodNode(postInv,"simpleFail", repos)
            executeNode(simpleFail, repos, postInv) shouldBe false

        }

        "$smt inheritedOld"{
            val (model, repos) = load(listOf(Paths.get("src/test/resources/old.abs")))
            val classDecl = model.extractClassDecl("Old", "OldC", repos)

            val inheritedSimpleSuccess = classDecl.extractMethodNode(postInv,"inheritedSimpleSuccess", repos)
            executeNode(inheritedSimpleSuccess, repos, postInv) shouldBe true

            val inheritedSimpleFail = classDecl.extractMethodNode(postInv,"inheritedSimpleFail", repos)
            executeNode(inheritedSimpleFail, repos, postInv) shouldBe false
        }

        "$smt booleanOld"{
            val (model, repos) = load(listOf(Paths.get("src/test/resources/old.abs")))
            val classDecl = model.extractClassDecl("Old", "OldC", repos)

            val booleanValSuccess = classDecl.extractMethodNode(postInv,"booleanValSuccess", repos)
            executeNode(booleanValSuccess, repos, postInv) shouldBe true

            val booleanValFail = classDecl.extractMethodNode(postInv,"booleanValFail", repos)
            executeNode(booleanValFail, repos, postInv) shouldBe false
        }

        "$smt predicateOld"{
            val (model, repos) = load(listOf(Paths.get("src/test/resources/old.abs")))
            val classDecl = model.extractClassDecl("Old", "OldC", repos)

            val predicateSimpleSuccess = classDecl.extractMethodNode(postInv,"predicateSimpleSuccess", repos)
            executeNode(predicateSimpleSuccess, repos, postInv) shouldBe true

            val predicateSimpleFail = classDecl.extractMethodNode(postInv,"predicateSimpleFail", repos)
            executeNode(predicateSimpleFail, repos, postInv) shouldBe false


            val predicateImplSuccess = classDecl.extractMethodNode(postInv,"predicateImplSuccess", repos)
            executeNode(predicateImplSuccess, repos, postInv) shouldBe true

            val predicateImplFail = classDecl.extractMethodNode(postInv,"predicateImplFail", repos)
            executeNode(predicateImplFail, repos, postInv) shouldBe false

            val predicateComplexSuccess = classDecl.extractMethodNode(postInv,"predicateComplexSuccess", repos)
            executeNode(predicateComplexSuccess, repos, postInv) shouldBe true
        }

        "$smt ifOld"{
            val (model, repos) = load(listOf(Paths.get("src/test/resources/old.abs")))
            val classDecl = model.extractClassDecl("Old", "OldC", repos)

            val oldIfSuccess = classDecl.extractMethodNode(postInv,"oldIfSuccess", repos)
            executeNode(oldIfSuccess, repos, postInv) shouldBe true

        }

        "$smt awaitOld"{
            val (model, repos) = load(listOf(Paths.get("src/test/resources/old.abs")))
            val classDecl = model.extractClassDecl("Old", "OldC", repos)

            val awaitSuccess = classDecl.extractMethodNode(postInv,"awaitSuccess", repos)
            executeNode(awaitSuccess, repos, postInv) shouldBe true

        }

        "$smt whileOld"{
            val (model, repos) = load(listOf(Paths.get("src/test/resources/old.abs")))
            val classDecl = model.extractClassDecl("Old", "OldC", repos)

            val predicateWhileSuccess = classDecl.extractMethodNode(postInv,"predicateWhileSuccess", repos)
            executeNode(predicateWhileSuccess, repos, postInv) shouldBe true

        }


    }
})