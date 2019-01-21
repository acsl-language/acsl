; Preamble - defining the sort of function literals
(declare-sort flit 0)
; Generic synamic contract functions for the (Int)->Int signature
(declare-fun _requiresII (flit Int) Bool)
(declare-fun _ensuresII (flit Int Int) Bool)
; Properties of the function whose address is being taken
(declare-fun FLIT_inc () flit)
(assert ( forall ((x Int)) (=  (_requiresII FLIT_inc x) true)))
(assert ( forall ((r Int)(x Int)) (=  (_ensuresII FLIT_inc r x) (> r x))))
(declare-fun FLIT_dec () flit)
(assert ( forall ((x Int)) (=  (_requiresII FLIT_dec x) true)))
(assert ( forall ((r Int)(x Int)) (=  (_ensuresII FLIT_dec r x) (< r x))))

(declare-fun fp () flit)          ; Declaration of fp
(assert (= fp FLIT_inc))          ; Assignment of fp
(assert (_requiresII fp 4))       ; Checking the precondition before calling fp
(declare-fun result_fp () Int)    ; Temp variable to hold the result of fp
(assert (_ensuresII fp result_fp 4)) ; Assuming the postcondition
(declare-fun y () Int)            ; Declaring y
(assert (= y result_fp))          ; Assignment to y
(assert (not (distinct y 4)))     ; Negating conclusion to be proved
(check-sat)
