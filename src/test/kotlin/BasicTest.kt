
import io.kotlintest.shouldBe
import io.kotlintest.specs.StringSpec
import org.abs_models.crowbar.data.*
import org.abs_models.crowbar.data.Function
import org.abs_models.crowbar.rule.MatchCondition
import org.abs_models.crowbar.rule.containsAbstractVar
import org.abs_models.crowbar.rule.match
import org.abs_models.crowbar.tree.SymbolicNode
import org.abs_models.crowbar.types.PostInvariantPair
import org.abs_models.crowbar.types.nextPITStrategy

class BasicTest : StringSpec() {

    private val conc = AddExpr(ProgVar("v"), AddExpr(Const("1"), ProgVar("v")))
    private val pattern = AddExpr(ExprAbstractVar("A"), AddExpr(Const("1"), ExprAbstractVar("A")))
    private val pattern2 = AddExpr(ExprAbstractVar("A"), AddExpr(ExprAbstractVar("A"), Const("1")))
    private val pattern3 = AddExpr(ExprAbstractVar("A"), Const("1"))

    init {

        /*"matchAndApply" {
            val cond = MatchCondition()
            match(conc, pattern, cond)
            assert(!cond.failure)
            val res = org.abs_models.crowbar.data.apply(pattern3,cond) as Anything
            res shouldBe AddExpr(ProgVar("v"), Const("1"))
            assert(!containsAbstractVar(res))
        }*/
        "Z3Test"{
            val prog = SeqStmt(
                    IfStmt(SExpr(">=", listOf(ProgVar("v"), Const("0"))),
                            AssignStmt(Field("f"), ProgVar("v")),
                            AssignStmt(Field("f"), SExpr("-", listOf(ProgVar("v"))))
                    ),
                    ReturnStmt(Field("f"))
            )

            val input3 = SymbolicState(
                    True,
                    EmptyUpdate,
                    Modality(prog, PostInvariantPair(Predicate(">=", listOf(select(Field("f")), Function("0"))),
                            True))
            )

            val strategy = nextPITStrategy()
            val node = SymbolicNode(input3, emptyList())
            strategy.execute(node)
            println(node.debugString(0))
            println(node.finishedExecution())
            for(l in node.collectLeaves()){
                println(l.evaluate())
            }
        }
        "deupdatify" {/* { v := 0 }{ v := v+1 } ((v == { v := v+1 }(v+w)) /\ { v := v+1 }!(v == w))
                          ->
                         (0+1 == (0+1+1+w)) /\ !(0+1+1 == w) */
            val s = UpdateOnFormula(ChainUpdate(ElementaryUpdate(ProgVar("v"), Function("0")), ElementaryUpdate(ProgVar("v"), Function("+", listOf(ProgVar("v"), Function("1"))))),
                    And(Predicate("=", listOf(
                            ProgVar("v"),
                            UpdateOnTerm(ElementaryUpdate(ProgVar("v"), Function("+", listOf(ProgVar("v"), Function("1")))),
                                    Function("+", listOf(ProgVar("v"), ProgVar("w"))))
                    )), UpdateOnFormula(ElementaryUpdate(ProgVar("v"), Function("+", listOf(ProgVar("v"), Function("1")))),
                            Not(Predicate("=", listOf(ProgVar("v"), ProgVar("w")))))))

            deupdatify(s).prettyPrint() shouldBe "(0+1=0+1+1+w) /\\ (!0+1+1=w)"
        }
        "apply" {
            apply(ElementaryUpdate(ProgVar("v"), Function("0")),
                    Predicate("=", listOf(Function("+", listOf(ProgVar("v"), ProgVar("v"))), Function("0")))) shouldBe
                    Predicate("=", listOf(Function("+", listOf(Function("0"), Function("0"))), Function("0")))
        }
        "subst" {
            subst(ProgVar("v"), ProgVar("v"), Function("0")) shouldBe Function("0")
            subst(ProgVar("w"), ProgVar("v"), Function("0")) shouldBe ProgVar("w")
            subst(Predicate("=",
                    listOf(Function("+", listOf(ProgVar("v"), ProgVar("v"))),
                            Function("0"))), ProgVar("v"), Function("0")) shouldBe
                    Predicate("=",
                            listOf(Function("+", listOf(Function("0"), Function("0"))),
                                    Function("0")))

            subst(Predicate("=",
                    listOf(Function("+", listOf(UpdateOnTerm(ElementaryUpdate(ProgVar("v"), Function("1")), ProgVar("v")),
                            UpdateOnTerm(ElementaryUpdate(ProgVar("w"), Function("1")), ProgVar("v")))),
                            Function("0"))), ProgVar("v"), Function("0")) shouldBe
                    Predicate("=",
                            listOf(Function("+", listOf(UpdateOnTerm(ElementaryUpdate(ProgVar("v"), Function("1")), ProgVar("v")),
                                    UpdateOnTerm(ElementaryUpdate(ProgVar("w"), Function("1")), Function("0")))),
                                    Function("0")))

            subst(ElementaryUpdate(ProgVar("v"), Function("+", listOf(ProgVar("v"), Function("1")))),
                    ProgVar("v"),
                    Function("0")) shouldBe
                    ElementaryUpdate(ProgVar("v"), Function("+", listOf(Function("0"), Function("1"))))

        }
        "matchAndFail1" {
            val cond = MatchCondition()
            match(conc, pattern2, cond)
            assert(cond.failure)
            cond.failReason shouldBe "AbstractVar A failed unification with two terms: v and 1"
        }
        "matchAndFail2"{
            val cond = MatchCondition()
            match(pattern, conc, cond)
            assert(cond.failure)
            cond.failReason shouldBe "Concrete statement contains abstract variables: ${pattern.prettyPrint()}"
        }
        "matchAndFail3"{
            val cond = MatchCondition()
            match(Const("v"), StmtAbstractVar("A"), cond)
            assert(cond.failure)
            cond.failReason shouldBe "AbstractVar A failed unification because of a type error: v"
        }
        "containsAbstractVar"{
            assert(!containsAbstractVar(conc))
            assert(containsAbstractVar(pattern))
            assert(containsAbstractVar(pattern2))
            assert(containsAbstractVar(pattern3))
        }
    }

}