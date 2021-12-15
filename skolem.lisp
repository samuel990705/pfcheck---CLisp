; This is file skolem.l. It contains the code to skolemize a PC
; expression

(load "objects.lisp")

;(declare (special *VARS-SO-FAR*)) ; Keeps track of the quantified variables

(defmacro associated (KEY ALIST)
  `(cadr (assoc ,KEY ,ALIST)))

(defmacro push1 (X L)
  `(setq ,L (cons ,X ,L)))

; Skolemization consists of (i) removing all booleans except "and"
; "or" and "not"; (ii) moving "not"s inside, to the literals
; (iii) removing quantifiers; (iv) putting into conjuctive normal form
; (v) map into a skolem clause

(defun skolemize (FORM)
   (sk-normalize (cnf (remquants (move-in-negs t (std-bools FORM))))))

; (std-bools FORM) eliminates "iff" and "implies", and replaces
; "contradiction" by "false"

(defun std-bools (FORM)
   (cond ((atom FORM) (stand-bool FORM))
         ((eq (car FORM) 'implies)
          `(or (not ,(std-bools (cadr FORM))) ,(std-bools (caddr FORM))))
         ((eq (car FORM) 'iff)
          (let ((STD1 (std-bools (cadr FORM)))
                (STD2 (std-bools (caddr FORM))))
            `(and (or (not ,STD1) ,STD2) (or (not ,STD2) ,STD1))))
         (t (sk-pass-in 'std-bools FORM))))

(defun stand-bool (FORM)
  (cond ((eq FORM 'contradiction) 'false)
        (t FORM)))

; (move-in-negs POS FORM) move the negations inward in FORM. If
; POS is nil, then FORM is negated.

(defun move-in-negs (POS FORM)
  (cond ((atom FORM) (neg-flip POS FORM))
        ((memq (car FORM) '(exists forall))
         (list (neg-flip POS (car FORM)) (cadr FORM)
                   (move-in-negs POS (caddr FORM))))
        ((memq (car FORM) '(or and))
         (cons (neg-flip POS (car FORM))
               (mapcar (lambda (X) (move-in-negs POS X)) (cdr FORM))))
        ((eq (car FORM) 'not)
         (move-in-negs (not POS) (cadr FORM)))
        (t
         (cond (POS FORM)
               (t `(not ,FORM))))))

(defun neg-flip (POS KEYWORD)
   (cond (POS KEYWORD)
         (t (get KEYWORD 'NEGATION))))

(setf (get 'true 'NEGATION)  'false)
(setf (get 'false 'NEGATION)'true)
(setf (get 'and 'NEGATION) 'or)
(setf (get 'or 'NEGATION) 'and)
(setf (get 'forall 'NEGATION) 'exists)
(setf (get 'exists 'NEGATION) 'forall)

; (remquants FORM) removes the quantifiers from FORM.

(defun remquants (FORM)
  (declare (special *VARS-SO-FAR*))
  (let ((*VARS-SO-FAR* nil))
     (remquants1 nil nil FORM)))

; remquants1 does the real work of remquants. UNIV-VARS is
; an a-list of universally quantified variables with Skolem
; variables (things of the form (*VAR* X)). EXISTS-VARS is
; an a-list of existentially quantified variables with Skolem
; constants.

(defun remquants1 (UNIV-VARS EXIST-VARS FORM)
  (declare (special *VARS-SO-FAR*))
   (cond ((atom FORM) FORM)
         ((eq (car FORM) 'forall)
          (setq *VARS-SO-FAR* (append (cadr FORM) *VARS-SO-FAR*))
          (remquants1 (nconc (make-uvars (cadr FORM)) UNIV-VARS)
                EXIST-VARS (caddr FORM)))
         ((eq (car FORM) 'exists)
          (remquants1 UNIV-VARS
                   (nconc (make-sk-consts (cadr FORM) UNIV-VARS) EXIST-VARS)
                   (caddr FORM)))
         ((memq (car FORM) '(and or not))
          (sk-pass-in (lambda (X) (remquants1 UNIV-VARS EXIST-VARS X))
                      FORM))
         (t
          (subst-sk-vars UNIV-VARS EXIST-VARS FORM))))

; subst-sk-vars makes the appropriate substitutions for quantified
; variables in the literal FORM.

(defun subst-sk-vars (UNIV-VARS EXIST-VARS FORM)
    (cond ((listp FORM)
           (cons (car FORM)
                 (mapcar (lambda (X) (subst-sk-vars UNIV-VARS EXIST-VARS X))
                         (cdr FORM))))
          ((or (associated FORM UNIV-VARS)
               (associated FORM EXIST-VARS)
               FORM))))

; make-uvars makes an alist of variables in NEW-VARS with skolem variables

(defun make-uvars (NEW-VARS)
   (loop for VAR in NEW-VARS
    do (save (list VAR (list '*VAR* (make-uvar VAR))))))

; make-uvar makes up a new skolem variable for VAR

(defun make-uvar (VAR)
  (declare (special *VARS-SO-FAR*))
   (cond ((memq VAR (cdr (memq VAR *VARS-SO-FAR*)))
          (newsym VAR))
         (t VAR)))

; make-sk-consts makes an alist of variables in NEW-VARS with skolem
; expressions. UNIV-VARS are the universally quantified variables
; of greater scope.

(defun make-sk-consts (NEW-VARS UNIV-VARS)
   (loop for VAR in NEW-VARS
    do (save (list VAR (new-sk-const VAR UNIV-VARS)))))

; new-sk-const makes up a new skolem expression
(defun new-sk-const (VAR UNIV-VARS)
   (let ((NEWSYM (newsym VAR)))
     (cond (UNIV-VARS (cons NEWSYM (mapcar 'cadr UNIV-VARS)))
           (t NEWSYM))))

; sk-pass-in moves a function FUN through the top level of FORM.

(defun sk-pass-in (FUN FORM)
  (selectq (car FORM)
    (lambda (exists forall)
     (list (car FORM) (cadr FORM) (funcall FUN (caddr FORM))))
    (lambda (and or)
     (cons (car FORM) (mapcar FUN (cdr FORM))))
    (not
     (list 'not (funcall FUN (cadr FORM))))
    (otherwise FORM)))

; (cnf FORM) returns FORM in conjunctive normal form.

(defun cnf (FORM)
   (cond ((atom FORM) FORM)
         ((eq (car FORM) 'and)
          (and-reduce (mapcar 'cnf (cdr FORM))))
         ((eq (car FORM) 'or)
          (or-reduce (mapcar 'cnf (cdr FORM))))
         (t FORM)))

; (and-reduce CLAUSES) gets rid of some obvious stupidities, like
; "and" applied to no clauses, or to one clause, or to a list
; of clauses including "false" or "true", or directly imbedded
; "and" clauses

(defun and-reduce (CLAUSES)
   (cond ((null CLAUSES)
          'true)
         ((memq 'false CLAUSES) 'false)
         (t
          (setq CLAUSES (delq 'true CLAUSES))
          (cond ((null (cdr CLAUSES))
                 (car CLAUSES))
                (t
                 (cons 'and (bool-flatten 'and CLAUSES)))))))

; or-reduce gets rid of similar stupidities

(defun or-reduce (CLAUSES)
   (cond ((null CLAUSES) 'false)
         ((memq 'true CLAUSES) 'true)
         (t
          (setq CLAUSES (delq 'false CLAUSES))
          (cond ((null (cdr CLAUSES))
                 (car CLAUSES))
                (t
                 (setq CLAUSES (bool-flatten 'or CLAUSES))
                 (cond ((assoc 'and CLAUSES)
                        (or-and-reduce CLAUSES))
                       (t
                        (cons 'or CLAUSES))))))))

; or-and-reduce (CLAUSES) carries out the distribution of "or"
; over "and".

(defun or-and-reduce (CLAUSES)
   (let ((AND-CLAUSES nil) (SIMPLE-CLAUSES nil))
     (loop for CLAUSE in CLAUSES
       do (cond ((eq (car CLAUSE) 'and)
                  (push1 (cdr CLAUSE) AND-CLAUSES))
                 (t
                  (push1 CLAUSE SIMPLE-CLAUSES))))
     (cons 'and
       (mapcar (lambda (CLAUSE)
                 (cons 'or
                  (nconc (bool-flatten 'or CLAUSE) SIMPLE-CLAUSES)))
               (full-cross-prod AND-CLAUSES)))))


; (bool-flatten BOOL CLAUSES) removes cases where a boolean "and"
; or "or" is directly imbedded with itself.

(defun bool-flatten (BOOL CLAUSES)
   (cond ((assoc BOOL CLAUSES)
          (loop for CLAUSE in CLAUSES
            do (splice (cond ((eq (car CLAUSE) BOOL)
                            (append (cdr CLAUSE) nil))
                           (t
                            (list CLAUSE))))))
          (t CLAUSES)))

; full-cross-prod takes a list of lists L and returns the full
; cross product of all the lists in L.

(defun full-cross-prod (L)
  (cond ((or (null L)
             (memq nil L))
         nil)
        (t
         (loop initially PLACES (mapcar (lambda (X) (cons X X)) L)
                        CROSS-PROD nil
               do (push1 (mapcar 'caar PLACES) CROSS-PROD)
               (while (next-cross-prod PLACES))
               (result CROSS-PROD)))))

(defun next-cross-prod (PLACES)
  (let ((FIRST-PLACE (car PLACES)))
   (cond ((null PLACES) nil)
         ((cdr (car FIRST-PLACE))
          (rplaca FIRST-PLACE (cdr (car FIRST-PLACE))))
         (t
          (rplaca FIRST-PLACE (cdr FIRST-PLACE))
          (next-cross-prod (cdr PLACES))))))

; sk-normalize turns cnf CLAUSE into a list of skolem clauses.

(defun sk-normalize (CLAUSE)
   (cond ((eq CLAUSE 'true) nil)
         ((eq CLAUSE 'false)
          (list (skolem-clause nil nil)))
         ((eq (car CLAUSE) 'and)
          (mapcar 'sk-normalize1 (cdr CLAUSE)))
         (t
          (list (sk-normalize1 CLAUSE)))))

; sk-normalize1 turns CLAUSE into a single skolem clause.

(defun sk-normalize1 (CLAUSE)
   (cond ((eq (car CLAUSE) 'or)
          (let ((POS-LITS nil) (NEG-LITS nil))
            (loop for LIT in (cdr CLAUSE)
              do (cond ((eq (car LIT) 'not)
                         (push1 (cadr LIT) NEG-LITS))
                        (t
                         (push1 LIT POS-LITS))))
            (skolem-clause POS-LITS NEG-LITS)))
          ((eq (car CLAUSE) 'not)
           (skolem-clause nil (list (cadr CLAUSE))))
          (t
           (skolem-clause (list CLAUSE) nil))))

; show-skolem-clause prints out a skolem clause.

(defun show-skolem-clause (CLAUSE)
  (msg "Clause:: Positive literals:")
  (cond ((POSLITS CLAUSE)
         (msg N)
         (loop for LIT in (POSLITS CLAUSE) do (pp-form LIT)))
        (t
         (msg " None" N)))
  (msg N (B 9) "Negative literals:")
  (cond ((NEGLITS CLAUSE)
         (msg N)
         (loop for LIT in (NEGLITS CLAUSE) do (pp-form LIT)))
        (t
         (msg " None" N)))
  (msg N N))
