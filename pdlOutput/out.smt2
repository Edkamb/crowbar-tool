(declare-fun p0 () Real)
	(declare-fun p1 () Real)
	(assert (<= 0 p0 ))
	(assert (<= p0 1 ))
	(assert (<= 0 p1 ))
	(assert (<= p1 1 ))
	(assert (<= (/  1 4) (+ (* (/  1 2) p0) (* (- 1 (/  1 2)) p1))))
	(assert (<= 1 (+ (* 1 p0) (* (- 1 1) 0))))
	(assert (<= p0 (+ (* 1 0) (* (- 1 1) 0))))
	(assert (<= p1 (+ (* 1 0) (* (- 1 1) 0))))
	(check-sat)