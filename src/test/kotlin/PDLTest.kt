import io.kotlintest.shouldBe
import io.kotlintest.shouldThrow
import org.abs_models.crowbar.main.*
import java.nio.file.Paths

class PDLTest : CrowbarTest() {
	init {
		"typeerror"{
			shouldThrow<Exception> {
				load(listOf(Paths.get("src/test/resources/exception.abs")))
			}
		}
		for (smt in listOf(z3, cvc)){
			if (!backendAvailable(smt)) continue
			println("testing with $smt as backend")

			"$smt float"{
				smtPath = smt
				val (model, repos) = load(listOf(Paths.get("src/test/resources/float.abs")))
				val classDecl = model.extractClassDecl("M", "C")

				var res = classDecl.extractMethodNode(pdl, "success", repos)
				executeNode(res, repos, pdl) shouldBe true
				res = classDecl.extractMethodNode(pdl, "fail", repos)
				executeNode(res, repos, pdl) shouldBe false
				res = classDecl.extractMethodNode(pdl, "ticket271", repos)
				executeNode(res, repos, pdl) shouldBe true
				res = classDecl.extractMethodNode(pdl, "ticket272", repos)
				executeNode(res, repos, pdl) shouldBe true
			}

			"$smt string"{
				smtPath = smt
				val (model, repos) = load(listOf(Paths.get("src/test/resources/string.abs")))
				val classDecl = model.extractClassDecl("Strings", "C")
				var res = classDecl.extractMethodNode(pdl, "success", repos)
				executeNode(res, repos, pdl) shouldBe true
				res = classDecl.extractMethodNode(pdl, "successFieldFloat", repos)
				executeNode(res, repos, pdl) shouldBe true
				res = classDecl.extractMethodNode(pdl, "fail", repos)
				executeNode(res, repos, pdl) shouldBe false
			}

			"$smt random"{
				smtPath = smt
				val (model, repos) = load(listOf(Paths.get("src/test/resources/random.abs")))
				val classDecl = model.extractClassDecl("Random", "C")

				var res = classDecl.extractMethodNode(pdl, "success", repos)
				executeNode(res, repos, pdl) shouldBe true
				res = classDecl.extractMethodNode(pdl, "fail", repos)
				executeNode(res, repos, pdl) shouldBe false
				res = classDecl.extractMethodNode(pdl, "failEq", repos)
				executeNode(res, repos, pdl) shouldBe false
			}

			"$smt account"{
				smtPath = smt
				val (model, repos) = load(listOf(Paths.get("examples/account.abs")))
				val classDecl = model.extractClassDecl("Account", "AccountImpl")

				var res = classDecl.extractMethodNode(pdl, "withdraw", repos)
				executeNode(res, repos, pdl) shouldBe true
				res = classDecl.extractMethodNode(pdl, "deposit", repos)
				executeNode(res, repos, pdl) shouldBe true
				res = model.exctractMainNode(pdl)
				executeNode(res, repos, pdl) shouldBe true

			}

			"$smt resolves"{
				smtPath = smt
				val (model, repos) = load(listOf(Paths.get("src/test/resources/resolves.abs")))
				val classDecl = model.extractClassDecl("Resolve", "C")

				var res = classDecl.extractMethodNode(pdl, "success1", repos)
				executeNode(res, repos, pdl) shouldBe true
				res = classDecl.extractMethodNode(pdl, "fail1", repos)
				executeNode(res, repos, pdl) shouldBe false
				res = classDecl.extractMethodNode(pdl, "fail2", repos)
				executeNode(res, repos, pdl) shouldBe false
				res = classDecl.extractMethodNode(pdl, "fail3", repos)
				executeNode(res, repos, pdl) shouldBe false
			}
			"$smt success"{
				smtPath = smt
				val (model, repos) = load(listOf(Paths.get("src/test/resources/success.abs")))
				val classDecl = model.extractClassDecl("Success", "C")
				classDecl.executeAll(repos, pdl) shouldBe true
			}
			"$smt types"{
				smtPath = smt
				val (model, repos) = load(listOf(Paths.get("src/test/resources/types.abs")))
				val classDecl = model.extractClassDecl("Types", "C")

				val iNode = classDecl.extractInitialNode(pdl)
				executeNode(iNode, repos, pdl) shouldBe true

				val sNode = classDecl.extractMethodNode(pdl, "m", repos)
				executeNode(sNode, repos, pdl) shouldBe true

				val fNode = classDecl.extractMethodNode(pdl, "m2", repos)
				executeNode(fNode, repos, pdl) shouldBe false
			}

			"$smt ints"{
				smtPath = smt
				val (model, repos) = load(listOf(Paths.get("src/test/resources/ints.abs")))
				val classDecl = model.extractClassDecl("Ints", "C")
				classDecl.executeAll(repos, pdl) shouldBe true

				val mNode = model.exctractMainNode(pdl)
				executeNode(mNode, repos, pdl) shouldBe true
			}

			"$smt guards"{
				smtPath = smt
				val (model, repos) = load(listOf(Paths.get("src/test/resources/guards.abs")))
				val classDecl = model.extractClassDecl("Guard", "C")

				val m1Node = classDecl.extractMethodNode(pdl, "msucc", repos)
				executeNode(m1Node, repos, pdl) shouldBe true

				val m2Node = classDecl.extractMethodNode(pdl, "mfail", repos)
				executeNode(m2Node, repos, pdl) shouldBe false
			}

			"$smt fails"{
				smtPath = smt
				val (model, repos) = load(listOf(Paths.get("src/test/resources/fail.abs")))
				val classDecl = model.extractClassDecl("Fail", "C")

				val iNode = classDecl.extractInitialNode(pdl)
				executeNode(iNode, repos, pdl) shouldBe false

				for (m in classDecl.methods) {
					val node = classDecl.extractMethodNode(pdl, m.methodSig.name, repos)
					executeNode(node, repos, pdl) shouldBe false
				}
				val classDecl2 = model.extractClassDecl("Fail", "D")
				val node2 = classDecl2.extractMethodNode(pdl, "failure", repos)
				executeNode(node2, repos, pdl) shouldBe false
			}

			"$smt create"{
				smtPath = smt
				val (model, repos) = load(listOf(Paths.get("src/test/resources/create.abs")))
				val classDecl = model.extractClassDecl("Create", "C")

				val iNode = classDecl.extractInitialNode(pdl)
				executeNode(iNode, repos, pdl) shouldBe true

				val sNode = classDecl.extractMethodNode(pdl, "success", repos)
				executeNode(sNode, repos, pdl) shouldBe true

				val fNode = classDecl.extractMethodNode(pdl, "fail", repos)
				executeNode(fNode, repos, pdl) shouldBe false

				val mNode = model.exctractMainNode(pdl)
				executeNode(mNode, repos, pdl) shouldBe true
			}

			"$smt reference"{
				smtPath = smt
				val (model, repos) = load(listOf(Paths.get("src/test/resources/reference.abs")))
				val classDecl = model.extractClassDecl("Reference", "C")

				val iNode = classDecl.extractInitialNode(pdl)
				executeNode(iNode, repos, pdl) shouldBe true

				val m1Node = classDecl.extractMethodNode(pdl, "m1", repos)
				executeNode(m1Node, repos, pdl) shouldBe false

				val m2Node = classDecl.extractMethodNode(pdl, "m2", repos)
				executeNode(m2Node, repos, pdl) shouldBe false //see comment in file

				val m3Node = classDecl.extractMethodNode(pdl, "m3", repos)
				executeNode(m3Node, repos, pdl) shouldBe true

				val m4Node = classDecl.extractMethodNode(pdl, "m4", repos)
				executeNode(m4Node, repos, pdl) shouldBe true

				val mNode = model.exctractMainNode(pdl)
				executeNode(mNode, repos, pdl) shouldBe false
			}

			"$smt multi"{
				smtPath = smt
				val (model, repos) = load(
					listOf(
						Paths.get("src/test/resources/multi1.abs"),
						Paths.get("src/test/resources/multi2.abs")
					)
				)
				val classDecl = model.extractClassDecl("Multi1", "C")
				classDecl.executeAll(repos, pdl) shouldBe true

				val mNode = model.exctractMainNode(pdl)
				executeNode(mNode, repos, pdl) shouldBe true
			}

			"$smt callsuccess"{
				smtPath = smt
				val (model, repos) = load(listOf(Paths.get("src/test/resources/callsimplesuccess.abs")))
				val classDeclC = model.extractClassDecl("CallS", "C")
				classDeclC.executeAll(repos, pdl) shouldBe true
				val classDeclD = model.extractClassDecl("CallS", "D")
				classDeclD.executeAll(repos, pdl) shouldBe true
				val classDeclE = model.extractClassDecl("CallS", "E")
				classDeclE.executeAll(repos, pdl) shouldBe true
				val mNode = model.exctractMainNode(pdl)
				executeNode(mNode, repos, pdl) shouldBe true
			}

			"$smt callfail"{
				smtPath = smt
				val (model, repos) = load(listOf(Paths.get("src/test/resources/callsimplefail.abs")))
				val classDeclC = model.extractClassDecl("CallF", "C")
				val m0Node = classDeclC.extractMethodNode(pdl, "m", repos)
				executeNode(m0Node, repos, pdl) shouldBe false
				val classDeclD = model.extractClassDecl("CallF", "D")
				val m1Node = classDeclD.extractMethodNode(pdl, "m", repos)
				executeNode(m1Node, repos, pdl) shouldBe false
				val classDeclE = model.extractClassDecl("CallF", "E")
				val m2Node = classDeclE.extractMethodNode(pdl, "m", repos)
				executeNode(m2Node, repos, pdl) shouldBe false
				val mNode = model.exctractMainNode(pdl)
				executeNode(mNode, repos, pdl) shouldBe false
			}

			"$smt failinher"{
				smtPath = smt
				val (model, repos) = load(listOf(Paths.get("src/test/resources/callfailinherited.abs")))
				val classDeclC = model.extractClassDecl("Call", "C")
				val m0Node = classDeclC.extractMethodNode(pdl, "fail", repos)
				executeNode(m0Node, repos, pdl) shouldBe false
			}

			"$smt selfcall"{
				smtPath = smt
				val (model, repos) = load(listOf(Paths.get("src/test/resources/selfcall.abs")))
				val classDecl = model.extractClassDecl("Self", "C")
				val m0Node = classDecl.extractMethodNode(pdl, "n", repos)
				executeNode(m0Node, repos, pdl) shouldBe true
				val m1Node = classDecl.extractMethodNode(pdl, "m", repos)
				executeNode(m1Node, repos, pdl) shouldBe true
				val m2Node = classDecl.extractMethodNode(pdl, "m2", repos)
				executeNode(m2Node, repos, pdl) shouldBe false
				val mNode = model.exctractMainNode(pdl)
				executeNode(mNode, repos, pdl) shouldBe true
			}

			"$smt valueof"{
				smtPath = smt
				val (model, repos) = load(listOf(Paths.get("src/test/resources/valueof.abs")))
				val classDecl = model.extractClassDecl("Values", "C")

				val iNode = classDecl.extractInitialNode(pdl)
				executeNode(iNode, repos, pdl) shouldBe true

				var sNode = classDecl.extractMethodNode(pdl, "success", repos)
				executeNode(sNode, repos, pdl) shouldBe true

				sNode = classDecl.extractMethodNode(pdl, "readToField", repos)
				executeNode(sNode, repos, pdl) shouldBe true

				sNode = classDecl.extractMethodNode(pdl, "internal", repos)
				executeNode(sNode, repos, pdl) shouldBe true

				sNode = classDecl.extractMethodNode(pdl, "fail", repos)
				executeNode(sNode, repos, pdl) shouldBe false

				sNode = classDecl.extractMethodNode(pdl, "valueOfBoolFutSuccess", repos)
				executeNode(sNode, repos, pdl) shouldBe true
			}

			"$smt ensures-this"{
				smtPath = smt
				val (model, repos) = load(listOf(Paths.get("src/test/resources/ensures.abs")))
				val classDecl = model.extractClassDecl("ThisCalls", "C")

				val iNode = classDecl.extractInitialNode(pdl)
				executeNode(iNode, repos, pdl) shouldBe true

				var sNode = classDecl.extractMethodNode(pdl, "one", repos)
				executeNode(sNode, repos, pdl) shouldBe true

				sNode = classDecl.extractMethodNode(pdl, "pos", repos)
				executeNode(sNode, repos, pdl) shouldBe true

				sNode = classDecl.extractMethodNode(pdl, "callOneOnThis", repos)
				executeNode(sNode, repos, pdl) shouldBe true

				sNode = classDecl.extractMethodNode(pdl, "callOneIndirectlyOnThis", repos)
				executeNode(sNode, repos, pdl) shouldBe true

				sNode = classDecl.extractMethodNode(pdl, "callOneOnOther", repos)
				executeNode(sNode, repos, pdl) shouldBe true

				sNode = classDecl.extractMethodNode(pdl, "failOneOnThis", repos)
				executeNode(sNode, repos, pdl) shouldBe false
			}

			"$smt paramensures"{
				smtPath = smt
				val (model, repos) = load(listOf(Paths.get("src/test/resources/params.abs")))
				var classDecl = model.extractClassDecl("ParamCalls", "C")

				var sNode = classDecl.extractMethodNode(pdl, "firstArg", repos)
				executeNode(sNode, repos, pdl) shouldBe true

				sNode = classDecl.extractMethodNode(pdl, "fail", repos)
				executeNode(sNode, repos, pdl) shouldBe false


				classDecl = model.extractClassDecl("ParamCalls", "D")

				sNode = classDecl.extractMethodNode(pdl, "succ", repos)
				executeNode(sNode, repos, pdl) shouldBe true

				sNode = classDecl.extractMethodNode(pdl, "succZero", repos)
				executeNode(sNode, repos, pdl) shouldBe true
			}

			"$smt fieldvarclash"{
				smtPath = smt
				val (model, repos) = load(listOf(Paths.get("src/test/resources/fieldvarclash.abs")))
				val classDecl = model.extractClassDecl("FieldVarClash", "C")
				classDecl.executeAll(repos, pdl) shouldBe true

				val mNode = model.exctractMainNode(pdl)
				executeNode(mNode, repos, pdl) shouldBe true
			}

			"$smt recidentity"{
				smtPath = smt
				val (model, repos) = load(listOf(Paths.get("src/test/resources/identity.abs")))
				val classDecl = model.extractClassDecl("Iden", "C")

				var sNode = classDecl.extractMethodNode(pdl, "id", repos)
				executeNode(sNode, repos, pdl) shouldBe true

				sNode = classDecl.extractMethodNode(pdl, "nid", repos)
				executeNode(sNode, repos, pdl) shouldBe false

				sNode = classDecl.extractMethodNode(pdl, "nnid", repos)
				executeNode(sNode, repos, pdl) shouldBe false
			}

			"$smt examples"{
				smtPath = smt
				var (model, repos) = load(listOf(Paths.get("examples/c2abs.abs")))
				var classDecl = model.extractClassDecl("TestModule", "C_main")
				classDecl.executeAll(repos, pdl) shouldBe true

				classDecl = model.extractClassDecl("TestModule", "Global")
				classDecl.executeAll(repos, pdl) shouldBe true

				classDecl = model.extractClassDecl("TestModule", "C_set_x")
				classDecl.executeAll(repos, pdl) shouldBe true

				var mNode = model.exctractMainNode(pdl)
				executeNode(mNode, repos, pdl) shouldBe true

				var any = load(listOf(Paths.get("examples/gcd.abs")))
				model = any.first
				repos = any.second
				classDecl = model.extractClassDecl("CallS", "GcdC")
				classDecl.executeAll(repos, pdl) shouldBe true

				classDecl = model.extractClassDecl("CallS", "LogC")
				classDecl.executeAll(repos, pdl) shouldBe true

				mNode = model.exctractMainNode(pdl)
				executeNode(mNode, repos, pdl) shouldBe true

				any = load(listOf(Paths.get("examples/gcdfield.abs")))
				model = any.first
				repos = any.second
				classDecl = model.extractClassDecl("CallSField", "GcdC")
				classDecl.executeAll(repos, pdl) shouldBe true

				mNode = model.exctractMainNode(pdl)
				executeNode(mNode, repos, pdl) shouldBe true

				any = load(listOf(Paths.get("examples/one_to_fib_n.abs")))
				model = any.first
				repos = any.second

				classDecl = model.extractClassDecl("TestModule", "Global")
				classDecl.executeAll(repos, pdl) shouldBe true

				classDecl = model.extractClassDecl("TestModule", "C_set_x")
				classDecl.executeAll(repos, pdl) shouldBe true

				classDecl = model.extractClassDecl("TestModule", "C_two_unspec")
				classDecl.executeAll(repos, pdl) shouldBe true

				classDecl = model.extractClassDecl("TestModule", "C_add_zero")
				classDecl.executeAll(repos, pdl) shouldBe true

				classDecl = model.extractClassDecl("TestModule", "C_one_to_fib_n")
				classDecl.executeAll(repos, pdl) shouldBe true

				mNode = model.exctractMainNode(pdl)
				executeNode(mNode, repos, pdl) shouldBe true
			}

			"$smt functional"{
				smtPath = smt
				val (model, repos) = load(listOf(Paths.get("src/test/resources/func.abs")))
				val classDecl = model.extractClassDecl("Func", "C")

				var sNode = classDecl.extractMethodNode(pdl, "m", repos)
				executeNode(sNode, repos, pdl) shouldBe true

				sNode = classDecl.extractMethodNode(pdl, "n", repos)
				executeNode(sNode, repos, pdl) shouldBe false
			}

			"$smt synccall"{
				smtPath = smt
				val (model, repos) = load(listOf(Paths.get("src/test/resources/synccall.abs")))
				val classDecl = model.extractClassDecl("SyncCall", "SyncCallC")

				//empty contract for sync call
				val emptyContractSyncCallSuccessNode =
					classDecl.extractMethodNode(pdl, "emptyContractSuccess", repos)
				executeNode(emptyContractSyncCallSuccessNode, repos, pdl) shouldBe true
				//simple fail for sync call
				val simpleSyncCallFail = classDecl.extractMethodNode(pdl, "simpleSyncCallFail", repos)
				executeNode(simpleSyncCallFail, repos, pdl) shouldBe false
				//simple success for sync call
				val simpleSyncCallSuccess = classDecl.extractMethodNode(pdl, "simpleSyncCallSuccess", repos)
				executeNode(simpleSyncCallSuccess, repos, pdl) shouldBe true

				//simple success for sync call with inherited contracts
				val syncCallInheritedSuccess = classDecl.extractMethodNode(pdl, "syncCallInheritedSuccess", repos)
				executeNode(syncCallInheritedSuccess, repos, pdl) shouldBe true

				//simple success for sync call with complex inherited contracts
				val syncCallComplexInheritedSuccess =
					classDecl.extractMethodNode(pdl, "syncCallComplexInheritedSuccess", repos)
				executeNode(syncCallComplexInheritedSuccess, repos, pdl) shouldBe true

				//simple success for sync call with complex inherited contracts
				val updateFieldSuccess = classDecl.extractMethodNode(pdl, "updateFieldSuccess", repos)
				executeNode(updateFieldSuccess, repos, pdl) shouldBe true
			}

			"$smt unexposedcontract"{
				smtPath = smt
				val (model, repos) = load(listOf(Paths.get("src/test/resources/unexposedcontract.abs")))
				val classDecl = model.extractClassDecl("UnexposedContract", "UnexposedContractC")

				val unexposedContractFail = classDecl.extractMethodNode(pdl, "unexposedContractFail", repos)
				executeNode(unexposedContractFail, repos, pdl) shouldBe false

				val unexposedContractSuccess = classDecl.extractMethodNode(pdl, "unexposedContractSuccess", repos)
				executeNode(unexposedContractSuccess, repos, pdl) shouldBe true
			}

			"$smt syncField"{
				smtPath = smt
				val (model, repos) = load(listOf(Paths.get("src/test/resources/syncField.abs")))
				val classDecl = model.extractClassDecl("TargetField", "C")

				val unexposedContractFail = classDecl.extractMethodNode(pdl, "m", repos)
				executeNode(unexposedContractFail, repos, pdl) shouldBe true
			}

			"$smt suspend"{
				smtPath = smt
				val (model, repos) = load(listOf(Paths.get("src/test/resources/suspend.abs")))
				val classDecl = model.extractClassDecl("Susp", "C")

				var res = classDecl.extractMethodNode(pdl, "m1", repos)
				executeNode(res, repos, pdl) shouldBe true
				res = classDecl.extractMethodNode(pdl, "m2", repos)
				executeNode(res, repos, pdl) shouldBe false
			}

			/*"$smt nullable"{
			smtPath = smt
			val (model, repos) = load(listOf(Paths.get("src/test/resources/nullable.abs")))
			val classDecl = model.extractClassDecl("Nullable", "K")

			val res = classDecl.extractMethodNode(pdl,"m", repos)
			executeNode(res, repos, pdl) shouldBe true
		}*/ //TODO: disabled until Daniel's version is merged

			"$smt assert"{
				smtPath = smt
				val (model, repos) = load(listOf(Paths.get("src/test/resources/assert.abs")))
				val classDecl = model.extractClassDecl("Assert", "C")

				var res = classDecl.extractMethodNode(pdl, "fail1", repos)
				executeNode(res, repos, pdl) shouldBe false
				res = classDecl.extractMethodNode(pdl, "fail2", repos)
				executeNode(res, repos, pdl) shouldBe false
				res = classDecl.extractMethodNode(pdl, "fail3", repos)
				executeNode(res, repos, pdl) shouldBe false
				res = classDecl.extractMethodNode(pdl, "success1", repos)
				executeNode(res, repos, pdl) shouldBe true
				res = classDecl.extractMethodNode(pdl, "success2", repos)
				executeNode(res, repos, pdl) shouldBe true
				res = classDecl.extractMethodNode(pdl, "success3", repos)
				executeNode(res, repos, pdl) shouldBe true
				res = classDecl.extractMethodNode(pdl, "success4", repos)
				executeNode(res, repos, pdl) shouldBe true
			}
			"$smt divByZero"{
				smtPath = smt
				val (model, repos) = load(listOf(Paths.get("src/test/resources/divByZero.abs")))
				val classDecl = model.extractClassDecl("DivByZero", "C")

				var res = classDecl.extractMethodNode(pdl, "fail1", repos)
				executeNode(res, repos, pdl) shouldBe false
				res = classDecl.extractMethodNode(pdl, "fail2", repos)
				executeNode(res, repos, pdl) shouldBe false
				res = classDecl.extractMethodNode(pdl, "fail3", repos)
				executeNode(res, repos, pdl) shouldBe false
				res = classDecl.extractMethodNode(pdl, "fail4", repos)
				executeNode(res, repos, pdl) shouldBe false
				res = classDecl.extractMethodNode(pdl, "success1", repos)
				executeNode(res, repos, pdl) shouldBe true
				res = classDecl.extractMethodNode(pdl, "success2", repos)
				executeNode(res, repos, pdl) shouldBe true
			}
			"$smt let"{
				smtPath = smt
				val (model, repos) = load(listOf(Paths.get("src/test/resources/let.abs")))
				val classDecl = model.extractClassDecl("Let", "C")

				var res = classDecl.extractMethodNode(pdl, "fail1", repos)
				executeNode(res, repos, pdl) shouldBe false
				res = classDecl.extractMethodNode(pdl, "fail2", repos)
				executeNode(res, repos, pdl) shouldBe false
				res = classDecl.extractMethodNode(pdl, "fail3", repos)
				executeNode(res, repos, pdl) shouldBe false
				res = classDecl.extractMethodNode(pdl, "fail4", repos)
				executeNode(res, repos, pdl) shouldBe false
				res = classDecl.extractMethodNode(pdl, "success1", repos)
				executeNode(res, repos, pdl) shouldBe true
				res = classDecl.extractMethodNode(pdl, "success2", repos)
				executeNode(res, repos, pdl) shouldBe true
				res = classDecl.extractMethodNode(pdl, "success3", repos)
				executeNode(res, repos, pdl) shouldBe true
				res = classDecl.extractMethodNode(pdl, "success4", repos)
				executeNode(res, repos, pdl) shouldBe true
			}
		}
	}
}