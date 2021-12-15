; This is file prove.l. It contains the code to carry out
; the proof checking.

;(dskin skolem unify)

(load "skolem.lisp")
(load "unify.lisp")
(load "objects.lisp")

;(declare (special *MARK*    ; Mark used in extracting all substeps
;                  *CYCLE*   ; Flag set if a circular proof detected
;                  *PROOF-MSGS* ; Tracing flag
;                  *NULL-CLAUSE*)) ; The null clause

;Declare



(setq *PROOF-MSGS* t)

(setq *MARK* 0)

(setf skcl (make-instance 'skolem-clause))
(setf (POSLITS skcl) nil)
(setf (NEGLITS skcl) nil)
(setq *NULL-CLAUSE* skcl)

; (prove "STEP") checks the correctness of the proof of STEP

(defun prove (STEP) (prove1 (car STEP)))

; (prove1 STEP) checks the proof of STEP. First, the list of
; substeps is retrieved, at the same time checking for circularities;
; then each step of the proof is verified.

(defun prove1 (STEP)
   (declare (special *CYCLE*))
  (let ((PROVEN t) (*CYCLE* nil))
   (loop for SUBSTEP in (find-substeps STEP)
     do (setq PROVEN (and PROVEN (check-step SUBSTEP))))
   (and PROVEN (not *CYCLE*))))

; Retrieves all the substeps of STEP, using depth-first search

(defun find-substeps (STEP)
   (declare (special *CYCLE* *MARK*))
 (let ((*CYCLE* nil))
  (setq *MARK* (+ 10 *MARK*))
  (find-substeps1 STEP)))


; Recursive part of the depth-first search. Standard stuff. Steps
; are marked with *MARK* on entrance and with *MARK* + 1 on exit.

(defun find-substeps1 (STEP)
   (declare (special *MARK* *CYCLE*))
  (let ((SUBSTEPS nil))
   (setf (get STEP 'MARK) *MARK*)
   (loop for SUPPORT in (find-supports STEP)
      do (cond ((= (get SUPPORT 'MARK) *MARK*)
                 (cond ((not *CYCLE*)
                        (setq *CYCLE* t)
                        (msg "Circularity in proof: " SUPPORT
                             " depends on itself "))))
                ((not (= (get SUPPORT 'MARK) (add1 *MARK*)))
                 (setq SUBSTEPS (nconc (find-substeps1 SUPPORT) SUBSTEPS)))))
   (setf (get STEP 'MARK) (add1 *MARK*))
   (cons STEP SUBSTEPS)))

; Finds the immediate substeps of STEP

(defun find-supports (STEP)
    (cond ((listp (PROOF STEP))
           (subset (lambda (X) (is pf-step X)) (PROOF STEP)))))


; (Check-step STEP) verifies the particular proof of STEP.
; The code is data-driven, based on the keyword of the given proof.

(defun check-step (STEP)
   (declare (special *PROOF-MSGS*))
  (cond (*PROOF-MSGS* (msg N "Checking " STEP N)))
  (let ((PROOF-CHECKER nil) ANS)
   (cond ((atom (PROOF STEP))
          (setq PROOF-CHECKER (get (PROOF STEP) 'PROOF-CHECKER)))
         (t
          (setq PROOF-CHECKER (get (car (PROOF STEP)) 'PROOF-CHECKER))))
   (cond (PROOF-CHECKER
          (setq ANS (funcall PROOF-CHECKER STEP))
          (cond (ANS
                 (msg N STEP " verified " N))
                (t
                 (msg N STEP " not verified" N)))
          ANS)
         (t
          (msg "Unknown type of proof " (PROOF STEP) " in " STEP N)))))

; Associate keywords with functions.

(setf (get 'axiom 'PROOF-CHECKER) (lambda (STEP) t))
(setf (get 'definition 'PROOF-CHECKER) (lambda (STEP) t))
(setf (get 'assumption 'PROOF-CHECKER) 'assumption-proof)
(setf (get 'universal-spec 'PROOF-CHECKER) 'universal-spec-proof)
(setf (get 'existential-spec 'PROOF-CHECKER) 'existential-spec-proof)
(setf (get 'discharge 'PROOF-CHECKER) 'discharge-proof)
(setf (get 'universal-discharge 'PROOF-CHECKER) 'udischarge-proof)
(setf (get 'existential-abs 'PROOF-CHECKER) 'exist-abs-proof)
(setf (get 'chaining 'PROOF-CHECKER) 'chaining-proof)


; (chaining-proof STEP) verifies a modus-ponens chain.

(defun chaining-proof (STEP)
   (full-and (maintain-assumptions STEP)
         (backwards-chain (set-neg-skolem STEP)
            (loop for SUPPORT in (find-supports STEP)
              do (splice (top-copy (set-skolem SUPPORT)))))))

; (maintain-assumptions STEP) verifies that the assumptions of
; STEP are the union of those of its supports

(defun maintain-assumptions (STEP)
  (verify-assumptions (ASSUMPTIONS STEP)
        (atom-union-over (PROOF STEP)
             (lambda (SUPPORT) (lambda (pf-step ASSUMPTIONS) SUPPORT)))))

; (set-neg-skolem  STEP) either retrieves the NEG-SKOLEM field of STEP
; or sets it to be the skolemization of the negation of its FORM.
; (The code for skolemize is in skolem.l)

(defun set-neg-skolem (STEP)
   (or (NEG-SKOLEM STEP)
       (setf (NEG-SKOLEM STEP)
           (skolemize (list 'not (STD-FORM STEP))))))

; (set-skolem  STEP) either retrieves the SKOLEM field of STEP
; or sets it to be the skolemization of its FORM.
; (The code for skolemize is in skolem.l)

(defun set-skolem (STEP)
   (or (SKOLEM STEP)
       (setf (SKOLEM STEP) (skolemize (STD-FORM STEP)))))

; backward-chain carries out a backwards chaining resolution proof
; by resolving the negation of the goal with each substep in
; backwards order. (The code for resolve is in unify.l)

(defun backwards-chain (GOALS SUPPORTS)
   (declare (special *NULL-CLAUSE*))
   (loop for SUPPORT in (reverse SUPPORTS)
     do (setq GOALS
             (nconc (loop for GOAL in GOALS
                      do (splice (resolve GOAL SUPPORT)))
                    GOALS)))
   (member *NULL-CLAUSE* GOALS))

; universal-spec-proof verifies a proof by universal specification
; It verifies that the assumptions of the step are the same as those
; of its basis, and that the form of the step is a specification
; of the stated variables


(defun universal-spec-proof (STEP)
  (decl (pf-step (BASIS (cadr (PROOF STEP)))
         exp (SPECIFIED (cddr (PROOF STEP))))
    (full-and (verify-assumptions (ASSUMPTIONS STEP)
                                  (ASSUMPTIONS BASIS))
              (substitutional-variant 'forall SPECIFIED
                 (STD-FORM STEP) (STD-FORM BASIS)))))

; assumption-proof verifies an assumption step, by noting any
; Skolem constants introduced, and by checking that the step
; is one of its own assumptions

(defun assumption-proof (STEP)
   (full-and (check-introduce-sk STEP)
             (cond ((memq STEP (ASSUMPTIONS STEP)))
                   (t
                    (msg N "Error: " STEP
                      " should be recorded as one of its own assumptions")
                   nil))))

; existential-spec-proof verifies an existential specification step
; The assumptions must add the new STEP to any assumptions of the
; BASIS; any skolem constants introduced must be noted; and the
; form of the step must correspond to that of the BASIS

(defun existential-spec-proof (STEP)
   (decl (pf-step (BASIS (cadr (PROOF STEP))))
     (full-and (verify-assumptions (ASSUMPTIONS STEP)
                                   (cons STEP (ASSUMPTIONS BASIS)))
               (check-introduce-sk STEP)
               (substitutional-variant 'exists (INTRODUCE-SK STEP)
                     (STD-FORM STEP) (STD-FORM BASIS)))))


; exist-abs-proof verifies an existential abstraction step
; The assumptions contain all the assumptions of the BASIS,
; and the form of the step must correspond to that of the BASIS

(defun exist-abs-proof (STEP)
   (decl (pf-step (BASIS (cadr (PROOF STEP)))
          exp (ABSTRACTED (cddr (PROOF STEP))))
     (full-and (verify-assumptions (ASSUMPTIONS STEP)
                                   (ASSUMPTIONS BASIS))
               (substitutional-variant 'exists ABSTRACTED
                     (STD-FORM BASIS) (STD-FORM STEP)))))

; discharge-proof checks a proof by discharging CONCLUDE against
; ASSUME. We check that all the assumption of CONCLUDE, except
; ASSUME, are present. If ASSUME is proven by assumption, then
; the current step is checked to be a simple implication; if
; ASSUME is proven by existential specification, then the
; current step is checked to be an abstracted implication

(defun discharge-proof (STEP)
   (decl (pf-step (CONCLUDE (cadr (PROOF STEP)))
                  (ASSUME (caddr (PROOF STEP))))
     (full-and (verify-assumptions (ASSUMPTIONS CONCLUDE)
                                   (cons ASSUME (ASSUMPTIONS STEP)))
               (cond ((eq (car (PROOF ASSUME)) 'assumption)
                      (equal (STD-FORM STEP)
                             `(implies ,(STD-FORM ASSUME)
                                       ,(STD-FORM CONCLUDE))))
                     ((eq (car (PROOF ASSUME)) 'existential-spec)
                      (existential-discharge STEP CONCLUDE ASSUME))
                     (t
                      (msg N "Invalid statement being discharged")
                      nil)))))

; existential-discharge checks a discharge of an existential
; specification

(defun existential-discharge (STEP CONCLUDE ASSUME)
   (full-and (verify-assumptions (ASSUMPTIONS CONCLUDE)
                                 (cons ASSUME (ASSUMPTIONS STEP)))
             (cond ((some (lambda (CONST)
                              (inner-member CONST (STD-FORM STEP)))
                          (INTRODUCE-SK ASSUME))
                    (msg N "Erroneous discharge: " STEP " not clear "
                       "of constants introduced in " ASSUME N)
                    nil)
                   ((equal (STD-FORM STEP) (STD-FORM CONCLUDE)))
                   (t
                    (msg N "Erroneous discharge: Change of form " STEP)
                    nil))))

; udischarge-proof checks a proof by universal discharge of
; CONCLUDE against ASSUME. The assumptions of the step are the
; same as those of CONCLUDE, except ASSUME. The form of the step
; is a universal generalization of (implies ASSUME CONCLUDE)

(defun udischarge-proof (STEP)
   (decl (pf-step (CONCLUDE (cadr (PROOF STEP)))
                  (ASSUME (caddr (PROOF STEP))))
     (full-and (verify-assumptions (ASSUMPTIONS CONCLUDE)
                                   (cons ASSUME (ASSUMPTIONS STEP)))
               (substitutional-variant 'forall (INTRODUCE-SK ASSUME)
                 `(implies ,(STD-FORM ASSUME) ,(STD-FORM CONCLUDE))
                 (STD-FORM STEP)))))

; (check-introduce-sk STEP) checks that any skolem constant is
; introduced only once (Strictly speaking, this is neither
; necessary nor sufficient for a correct proof, but its a
; good thing to check.)

(defun check-introduce-sk (STEP)
   (let ((ERROR nil))
    (loop for CONST in (INTRODUCE-SK STEP)
      do (cond ((null (get CONST 'INTRODUCED))
                 (setf (get CONST 'INTRODUCED) STEP))
                ((not (eq (get CONST 'INTRODUCED) STEP))
                 (setq ERROR t)
                 (msg N "Error: Overuse of skolem constant " CONST))))
   (not  ERROR)))

; substitutional-variant checks that the CONSTANT-FORM corresponds to
; the VARIABLE-FORM with the elimination of the quantifier QUANT and
; with the substitution of the constants CONSTANTS for the first
; several quantified variables in  VARIABLE-FORM

(defun substitutional-variant (QUANT CONSTANTS CONSTANT-FORM VARIABLE-FORM)
   (cond ((not (eq (car VARIABLE-FORM) QUANT))
          (msg N "Incorrect quantifier")
          nil)
         ((check-var-subst CONSTANT-FORM (caddr VARIABLE-FORM)
            (mapcar (lambda (SK VAR) (list SK VAR))
                    CONSTANTS (cadr VARIABLE-FORM))))
         (t
          (msg N "Incorrect substitution")
          (pp-form CONSTANT-FORM)
          (terpri)
          (pp-form VARIABLE-FORM)
          nil)))

; verify-assumptions checks that OLD-ASSUMPS are the same as NEW-ASSUMPS

(defun verify-assumptions (OLD-ASSUMPS NEW-ASSUMPS)
    (cond ((atom-subset OLD-ASSUMPS NEW-ASSUMPS)
           (cond ((not (atom-subset NEW-ASSUMPS OLD-ASSUMPS))
                  (msg "Warning : You have introduce new assumptions " N
                       "New assumptions: " NEW-ASSUMPS
                       " Basis assumptions: " OLD-ASSUMPS N)))
           t)
          (t
           (msg "Error: You have dropped some assumptions " N
                       "New assumptions: " NEW-ASSUMPS
                       "Basis assumptions: " OLD-ASSUMPS N)
           nil)))


; check-var-subst checks that CONST-FORM is equal to VAR-FORM
; under the substitutions indicated in PAIRS

(defun check-var-subst (CONST-FORM VAR-FORM PAIRS)
   (cond ((atom CONST-FORM)
          (and (atom VAR-FORM)
               (cond ((assoc CONST-FORM PAIRS)
                      (eq VAR-FORM (associated CONST-FORM PAIRS)))
                     ((some (lambda (PAIR) (eq VAR-FORM (cadr PAIR)))
                            PAIRS)
                      nil)
                     ((eq CONST-FORM VAR-FORM)))))
         ((atom VAR-FORM) nil)
         (t
          (and (check-var-subst (car CONST-FORM) (car VAR-FORM) PAIRS)
               (check-var-subst (cdr CONST-FORM) (cdr VAR-FORM) PAIRS)))))
