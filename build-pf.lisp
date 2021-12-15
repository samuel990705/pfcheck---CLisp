; This is file build-pf.l. It contains the code used in loading
; a proof file

(load "objects.lisp")

;(declare (special *STEPS*         ; list of all steps
;                  *TYPE-CHECK*    ; boolean flag to check types
;                  *LOCAL-TYPES*   ; types declared in step
;                  *QUANT-VARS*    ; quantified variables
;                  *STEP-NAME*     ; name of step
;                  *CAREFUL-SYNTAX* ; boolean flag: check syntax of literals
;      *TRACING*  *NOISY-TYPE-CHECK*)) ; boolean debugging flags

(setf *TYPE-CHECK* t)

(setf *TRACING* t)

(setf *STEPS* nil)

(setf *CAREFUL-SYNTAX* t)

(setf *NOISY-TYPE-CHECK* t)

; (step -step definition-) defines a proof step (see writeup)

(defun step1 (L)
   (step2 (car L) (cdr L)))

; (step2 STEP-NAME L) carries out the step definition

(defun step2 (STEP-NAME L)
   (declare (special *LOCAL-TYPES* *TRACING*))
   (cond (*TRACING* (msg N "Reading " STEP-NAME N)))
   (check-dups STEP-NAME)
   (clear-pf-step STEP-NAME)
   (setf (get STEP-NAME 'DATA-TYPE) 'pf-step)
   (loop for TERM in L
     do (let ((TERM-HANDLER (get (car TERM) 'TERM-HANDLER))
           (cond (TERM-HANDLER
                  (funcall TERM-HANDLER TERM STEP-NAME))
                 (t
                  (msg "Unknown clause " TERM " in " STEP-NAME N)))))
   (let ((*LOCAL-TYPES* (TYPES STEP-NAME)))
     (setf (STD-FORM STEP-NAME) (standardize-form (FORM STEP-NAME))))
   (syntax-check STEP-NAME)
   (show-pf-step STEP-NAME)))

; Initialize fields of step to nil.

(defun clear-pf-step (STEP)
   (setf (FORM STEP) nil)
   (setf (STD-FORM STEP) nil)
   (setf (ENGLISH STEP) nil)
   (setf (ASSUMPTIONS STEP) nil)
   (setf (TYPES STEP) nil)
   (setf (SKOLEM STEP) nil)
   (setf (NEG-SKOLEM STEP) nil)
   (setf (INTRODUCE-SK STEP) nil))

; Since all fields of the pf-step involve basically similar code
; to initialize, I wrote a macro to handle the common part.

(defmacro def-term-handler (KEY FIELD VAL)
   `(setf (get (quote ,KEY) 'TERM-HANDLER)
      (lambda (TERM STEP-NAME)
         (setf (get (pf-step ,FIELD) STEP-NAME) ,VAL))))

; Defines the code to handle each field in turn.

(def-term-handler form FORM (cadr TERM))
(def-term-handler proof PROOF (cadr TERM))
(def-term-handler English ENGLISH (cdr TERM))
(def-term-handler assumptions ASSUMPTIONS (cdr TERM))
(def-term-handler types TYPES (std-types (cdr TERM)))
(def-term-handler introduce-sk INTRODUCE-SK (cdr TERM))

; Checks that the step name has not been duplicated.

(defun check-dups (STEP)
   (declare (special *STEPS*))
    (cond ((memq STEP *STEPS*)
           (msg STEP " already defined " N))))

; Standardizes the form of the step by expanding any variable define
; in the "st" format, and expanding form macros.

(defun standardize-form (FORM)
   (cond ((atom FORM) FORM)
         ((memq (car FORM) '(exists forall))
          (expand-st FORM))
         ((is-formmacro (car FORM))
          (standardize-form (expand-formmacro FORM)))
         (t
          (cons (standardize-form (car FORM))
                (standardize-form (cdr FORM))))))

; (std-types TYPE-LIST) carries out local type definitions

(defun std-types (TYPE-LIST)
   (loop for TYPE-GROUP in TYPE-LIST
     do (splice (std-type-group TYPE-GROUP))))

; (std-type-group TYPE-GROUP) fixes a group of type definitions
(defun std-type-group (TYPE-GROUP)
   (let ((TYPE (car TYPE-GROUP)))
      (cond ((is-log-type TYPE)
             (loop for ELT in (cdr TYPE-GROUP) do (save (list ELT TYPE)))
            (t
             (msg "Type declaration error " TYPE-GROUP)
             nil)))))

(defun is-log-type (TYPE)
   (get TYPE 'LOG-TYPE))

; (expand-st FORM) handles quantified variables defined in an st
;  clause

(defun expand-st (FORM)
   (let ((QUANT (car FORM)) (VARS (cadr FORM)) (BODY (caddr FORM))
         (NEW-VARS nil) (NEW-CLAUSES nil))
     (cond ((cdddr FORM)
            (msg "Too many parts to quantified expression " FORM)))
     (loop for VAR-SPEC in VARS
       do (cond ((atom VAR-SPEC)
                  (push VAR-SPEC NEW-VARS))
                 ((and (eq (cadr VAR-SPEC) 'st)
                       (null (cdddr VAR-SPEC)))
                  (push (car VAR-SPEC) NEW-VARS)
                  (push (caddr VAR-SPEC) NEW-CLAUSES))
                 (t
                  (msg "Erroneous quantified variables " VAR-SPEC N)
                  (push (car VAR-SPEC) NEW-VARS))))
     (setf BODY (standardize-form BODY))
     (list QUANT NEW-VARS
       (cond ((null NEW-CLAUSES) BODY)
             ((eq QUANT 'exists)
              `(and ,@NEW-CLAUSES ,BODY))
             (t
              `(implies (and ,@NEW-CLAUSES) ,BODY))))))

; Hooks for defining form macros

(defun is-formmacro (MAC)
  (and (atom MAC) (get MAC 'formmacro)))

(defun expand-formmacro (FORM)
   (apply (get (car FORM) 'formmacro) (cdr FORM)))

; (syntax-check *STEP-NAME*) checks the syntax of the form of
; *STEP-NAME* using recursive descent. It initializes some global
; variables and then calls the recursive syntax-check1

(defun syntax-check (*STEP-NAME*)
   (declare (special *LOCAL-TYPES* *STEP-NAME* *QUANT-VARS*))
   (let ((*QUANT-VARS* nil) (*LOCAL-TYPES* (TYPES *STEP-NAME*)))
      (syntax-check1 (STD-FORM *STEP-NAME*))))

; syntax-check1 handles the recursive part of the grammar (i.e.
; down to the literals.)

(defun syntax-check1 (FORM)
   (cond ((memq FORM '(contradiction false true))
          t)
         ((atom FORM)
          (msg "Syntax error " FORM N))
         (t
          (selectq (car FORM)
            (lambda (exists forall) (syn-quant-check FORM))
            (lambda (and or)
             (loop for X in (cdr FORM) do (syntax-check1 X)))
            (lambda (implies iff)
             (cond ((= (length FORM) 3)
                    (syntax-check1 (cadr FORM))
                    (syntax-check1 (caddr FORM)))
                   (t
                    (msg "Syntax error: Too many parts " FORM N))))
            (not
             (cond ((= (length FORM) 2)
                    (syntax-check1 (cadr FORM)))
                   (t
                    (msg "Syntax error: Too many parts " FORM N))))
            (otherwise (literal-check FORM))))))

; (syn-quant-check FORM) checks the syntax of a variable list

(defun syn-quant-check (FORM)
   (declare (special *QUANT-VARS*))
  (cond ((not (every 'atom (cadr FORM)))
         (msg "Error in variable list of " FORM N)))
  (let ((*QUANT-VARS* (append (cadr FORM) *QUANT-VARS*)))
     (syntax-check1 (caddr FORM))))

; (literal-check FORM) checks the syntax of literals if
; *CAREFUL-SYNTAX* is set.

(defun literal-check (FORM)
   (declare (special *CAREFUL-SYNTAX*))
   (cond ((atom FORM)
          (msg "Syntax error: Atom where literal expected " FORM N))
         (t
          (cond (*CAREFUL-SYNTAX*
                 (check-non-log (car FORM) (cdr FORM) 'PRED)
                 (loop for TERM in (cdr FORM)
                    do (term-check TERM)))))))

; (term-check FORM) checks the syntax of terms (recursively)

(defun term-check (FORM)
   (declare (special *QUANT-VARS*))
   (cond ((atom FORM)
          (cond ((not (memq FORM *QUANT-VARS*))
                 (check-non-log FORM nil 'CONST))))
         (t
          (check-non-log (car FORM) (cdr FORM) 'FUNC)
          (loop for TERM in (cdr FORM)
            do (term-check TERM)))))

; (check-non-log SYMB ARGS TYPE) does the real work of checking
; that non-logical symbol SYMB, assumed to be of syntactic type
; TYPE (PRED, FUNC, CONST, or VAR) with arguments ARGS, is kosher.

(defun check-non-log (SYMB ARGS TYPE)
   (declare (special *STEP-NAME* *TYPE-CHECK*))
   (cond ((is non-logical SYMB)
          (setf (PF-STEPS SYMB) (cons *STEP-NAME* *-*))
          (decl (pf-type (PF-TYPE (PF-TYPE SYMB)))
             (cond ((not (eq (SYNTAX-TYPE PF-TYPE) TYPE))
                    (msg SYMB " previously used as "
                         (SYNTAX-TYPE PF-TYPE) N))
                   ((and (check-num-args PF-TYPE SYMB ARGS)
                         (cond (*TYPE-CHECK*
                                (check-arg-types SYMB TYPE ARGS PF-TYPE))))))))
          (t
           (build-non-logical SYMB TYPE (length ARGS)
                  (mapcar 'get-type ARGS)
                  (cond ((memq TYPE '(CONST FUNC))
                         (get-type SYMB)))))))


; (check-num-args PF-TYPE SYMB ARGS) checks that symbol SYMB of
; type PF-TYPE is taking the correct number of arguments in ARGS

(defun check-num-args (PF-TYPE SYMB ARGS)
     (let ((NARGS (NUM-ARGS PF-TYPE)))
       (cond (NARGS
              (cond ((eq NARGS (length ARGS)))
                    (t
                     (msg SYMB " previously used with " NARGS
                          " arguments " )
                     nil)))
             (t
              (setf (NUM-ARGS PF-TYPE) (length ARGS))))))

; (check-arg-types SYMB TYPE ARGS PF-TYPE) checks that non-logical
; SYMB, of value-type PF-TYPE and of syntactic type TYPE is taking
; arguments of the right types in ARGS

(defun check-arg-types (SYMB TYPE ARGS PF-TYPE)
      (let (exp (EXPECTED-TYPES (ARG-TYPES PF-TYPE)))
         (cond (EXPECTED-TYPES
                (cond ((every-list
                         (lambda (ETYPE ARG) (match-arg-type ETYPE ARG))
                         EXPECTED-TYPES ARGS))
                       (t
                        (msg "Type error: expected types for " SYMB " are "
                             EXPECTED-TYPES))))
               (t
                (setf (ARG-TYPES PF-TYPE) (mapcar 'get-types ARGS))))))

; (match-arg-type ETYPE ARG) matches the type of ARG to the expected
; type ETYPE

(defun match-arg-type (ETYPE ARG)
   (let ((ARGTYPE (get-type ARG)))
      (cond ((null ETYPE) t)
            ((null ARGTYPE)
             (record-arg-type ARG ETYPE)
             t)
            (t
             (eq ETYPE ARGTYPE)))))

; (record-arg-type ARG ETYPE) records type information for ARG.

(defun record-arg-type (ARG ETYPE)
   (declare (special *QUANT-VARS* *LOCAL-TYPES*))
   (decl (exp (STYPE 'CONST) (LENGTH 0))
      (cond ((listp ARG)
             (setq LENGTH (length (cdr ARG)))
             (setq ARG (car ARG))
             (setq STYPE 'FUNC)))
      (cond ((is non-logical ARG)
             (setf (VAL-TYPE (lambda (non-logical PF-TYPE) ARG)) ETYPE))
            ((memq ARG *QUANT-VARS*)
             (push (list ARG ETYPE) *LOCAL-TYPES*))
            (t
             (build-non-logical ARG STYPE LENGTH nil ETYPE)))))


; (get-type ARG) retrieves the type of ARG, either from the local
; type declarations, or from ARG's property list

(defun get-type (ARG)
   (declare (special *LOCAL-TYPES*))
   (cond ((listp ARG)
          (setq ARG (car ARG))))
   (or (associate ARG *LOCAL-TYPES*)
       (VAL-TYPE ARG)))

; build-non-logical records the properties of the non-logical ARG

(defun build-non-logical (ARG STYPE NUM-ARGS ARG-TYPES VAL-TYPE)
   (declare (special *NOISY-TYPE-CHECK* *STEP-NAME*))
   (cond (*NOISY-TYPE-CHECK*
          (msg "Marking " ARG " as a non-logical symbol " N
            "SYNTAX-TYPE = " STYPE "   NUM-ARGS = " NUM-ARGS
            "   ARG-TYPES = " ARG-TYPES "   VAL-TYPE = " VAL-TYPE)))
   (make non-logical ARG (make pf-type STYPE NUM-ARGS ARG-TYPES VAL-TYPE)
                     (list *STEP-NAME*)))

; types declares symbols as logical types

(defun types1 (L)
   (loop for X in L
      do (setf (get X 'LOG-TYPE) t )))

; funtype declares the type of a function

(defun funtype (L)
  (funtype1 (car L) (cadr L) (caddr L)))

(defun funtype1 (TYPE FUN ARGTYPES)
   (cond ((and (is-log-type TYPE)
               (every 'is-log-type ARGTYPES))
          (init-non-logical FUN 'FUNC
              (cond (ARGTYPES (length ARGTYPES))) ARGTYPES TYPE))
         (t
          (msg "Function type declaration error " TYPE FUN ARGTYPES N))))

; perm-var-types makes global declarations of variable types

(defun perm-var-types (L)
  (mapc 'perm-var-types1 L))

(defun perm-var-types1 (TYPE-GROUP)
   (let ((TYPE (car TYPE-GROUP)))
     (cond ((is-log-type TYPE)
            (loop for VAR in (cdr TYPE-GROUP)
               do (init-non-logical VAR 'VAR nil nil TYPE)))
           (t
            (msg "Variable type declaration error " TYPE-GROUP N)))))

; const-types declares the types of constants

(defun const-types (L)
  (mapc 'const-types1 L))

(defun const-types1 (TYPE-GROUP)
   (let ((TYPE (car TYPE-GROUP)))
     (cond ((is-log-type TYPE)
            (loop for CONST in (cdr TYPE-GROUP)
               do (init-non-logical CONST 'CONST nil nil TYPE)))
           (t
            (msg "Constant type declaration error " TYPE-GROUP N)))))

; predtype declares the type of a predicate

(defun predtype (L)
  (predtype1 (car L) (cadr L)))

(defun predtype1 (PRED ARGTYPES)
   (cond ((every 'is-log-type ARGTYPES)
          (init-non-logical PRED 'PRED (cond (ARGTYPES (length ARGTYPES)))
                            ARGTYPES nil))
         (t
          (msg "Predicate type declaration error " FUN ARGTYPES N))))


; init-non-logical creates a non-logical symbol
(defun init-non-logical (ARG STYPE NUM-ARGS ARG-TYPES VAL-TYPE)
   (make non-logical ARG (make pf-type STYPE NUM-ARGS ARG-TYPES VAL-TYPE)
                     nil))


; show-pf-step pretty prints some important properties of a step

(defun show-pf-step (STEP)
   (msg N "Step: " STEP)
   (msg N "Standard Form:" )
   (pp-form (STD-FORM STEP))
   (terpri)
   (cond ((ENGLISH STEP)
          (msg N "English: ")
          (loop for STRING in (ENGLISH STEP)
             do (msg N STRING))))
   (cond ((SKOLEM STEP)
          (msg N "Skolemized:")
          (loop for CLAUSE in (SKOLEM STEP)
             do (show-skolem-clause CLAUSE))))
   (cond ((NEG-SKOLEM STEP)
          (msg N "Skolemized negation:")
          (loop for CLAUSE in (NEG-SKOLEM STEP)
             do (show-skolem-clause CLAUSE))))
   (msg N N))