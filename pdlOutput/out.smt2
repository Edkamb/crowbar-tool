(declare-fun p0 () Real)
	(declare-fun p1 () Real)
	(declare-fun p366 () Real)
	(declare-fun p367 () Real)
	(declare-fun p1096 () Real)
	(declare-fun p1097 () Real)
	(declare-fun p1462 () Real)
	(declare-fun p1463 () Real)
	(declare-fun p2192 () Real)
	(declare-fun p2193 () Real)
	(declare-fun p2558 () Real)
	(declare-fun p2559 () Real)
	(assert (<= 0 p0 ))
	(assert (<= p0 1 ))
	(assert (<= 0 p1 ))
	(assert (<= p1 1 ))
	(assert (<= 0 p366 ))
	(assert (<= p366 1 ))
	(assert (<= 0 p367 ))
	(assert (<= p367 1 ))
	(assert (<= 0 p1096 ))
	(assert (<= p1096 1 ))
	(assert (<= 0 p1097 ))
	(assert (<= p1097 1 ))
	(assert (<= 0 p1462 ))
	(assert (<= p1462 1 ))
	(assert (<= 0 p1463 ))
	(assert (<= p1463 1 ))
	(assert (<= 0 p2192 ))
	(assert (<= p2192 1 ))
	(assert (<= 0 p2193 ))
	(assert (<= p2193 1 ))
	(assert (<= 0 p2558 ))
	(assert (<= p2558 1 ))
	(assert (<= 0 p2559 ))
	(assert (<= p2559 1 ))
	(assert (<= (/  2 3) (+ (* (/  1 3) p0) (* (- 1 (/  1 3)) p1))))
	(assert (<= 1 (+ (* 1 p0) (* (- 1 1) 0))))
	(assert (<= p1 (+ (* (/  1 2) p366) (* (- 1 (/  1 2)) p367))))
	(assert (<= 1 (+ (* 1 p366) (* (- 1 1) 0))))
	(assert (<= 1 (+ (* 1 p367) (* (- 1 1) 0))))
	(assert (<= (/  2 3) (+ (* (/  1 3) p1096) (* (- 1 (/  1 3)) p1097))))
	(assert (<= 1 (+ (* 1 p1096) (* (- 1 1) 0))))
	(assert (<= p1097 (+ (* (/  1 2) p1462) (* (- 1 (/  1 2)) p1463))))
	(assert (<= 1 (+ (* 1 p1462) (* (- 1 1) 0))))
	(assert (<= 1 (+ (* 1 p1463) (* (- 1 1) 0))))
	(assert (<= (/  2 3) (+ (* (/  1 3) p2192) (* (- 1 (/  1 3)) p2193))))
	(assert (<= 1 (+ (* 1 p2192) (* (- 1 1) 0))))
	(assert (<= p2193 (+ (* (/  1 2) p2558) (* (- 1 (/  1 2)) p2559))))
	(assert (<= 1 (+ (* 1 p2558) (* (- 1 1) 0))))
	(assert (<= 1 (+ (* 1 p2559) (* (- 1 1) 0))))
	(check-sat)