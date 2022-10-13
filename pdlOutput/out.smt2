(assert (<= (Function(name=/, params=[Function(name=1, params=[]), Function(name=2, params=[])])) (+ (* Const(name=true, concrType=ABS.StdLib.Bool)PPId(id=0)) (* (- 1 Const(name=true, concrType=ABS.StdLib.Bool))PPId(id=1)))
	(assert (<= (0) (+ (* 1PPId(id=0)) (* (- 1 1)0))
	(check-sat)