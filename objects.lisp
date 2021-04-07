;replaces the logtypes class
;Defines the objects used in build-pf.l

(defclass skolem-clause() (POSLITS NEGLITS));

(defclass pf-step()
   (FORM       ; form as input
    STD-FORM   ; standardized form
    ENGLISH    ; English paraphrase
    ASSUMPTIONS; list of assumptions
    TYPES      ; Type declarations, as a-list ((VAR1 TYPE1) ...)
    PROOF      ; Proof, as input
    SKOLEM     ; List of skolem clauses. Skolemization of STD-FORM
    NEG-SKOLEM ; Skolemization of negation of STD-FORM
    INTRODUCE-SK)) ; Skolem constants introduced

(defclass pf-type ()
  (atom SYNTAX-TYPE ; either PRED, FUNC, VAR, or CONST
   fixnum NUM-ARGS  ; number of arguments
   exp ARG-TYPES    ; types of arguments
       VAL-TYPE))

(defclass non-logical() (pf-type PF-TYPE exp PF-STEPS))
